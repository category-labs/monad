

(setq proof-shell-silent-threshold 10000) ;;; TODO: do this locally, in coq-programmer-loop

;; ;; Buffer-local list that stores the alternating user / assistant messages.
;; (defvar-local gpt-4o-conversation nil
;;   "Conversation history for `gpt-4o-chat'.  Each element is a string, 
;; alternating USER, ASSISTANT, USER, … in the order they were sent.")

;;; ------------------------------------------------------------------
;;;  NEW user-tunable knob
;;; ------------------------------------------------------------------
(defcustom coq-programmer-feedback-extension 15
  "How many extra GPT calls to grant each time the user gives feedback
after a fully successful compile."
  :type 'integer
  :group 'coq-programmer)


(defun gpt-4o--append (role text)
  "Insert ROLE (\"User\" or \"Assistant\") and TEXT at point, then newline."
  (insert (format "%s: %s\n" role text)))

(defun gpt-4o--send (msg)
  "Record MSG, call GPT-4o, return the assistant’s reply."
  ;; store user message
  (push msg gpt-4o-conversation)
  ;; build prompt in chronological order
  (let* ((prompt (llm-make-chat-prompt (reverse gpt-4o-conversation)))
         (reply  (llm-chat llm-provider prompt nil)))
    ;; store assistant reply
    (push reply gpt-4o-conversation)
    reply))

(defvar-local coq-programmer--last-working-with-holes nil
  "Stores the most recent Gallina snippet that *compiled* but still
contained `Admitted.`.  If the LLM-call budget is exhausted, this
snippet is re-inserted into the proof script before the session ends.")


;;; context pruning: 1) on Search response, ask GPT to filter in items it thinks are useful. also omit larger types.
;;;                  2) always keep conversation length to 3 max? ask GPT to summarize other stuff?


;;;; ---------------  shared regexp  ---------------
(defconst gpt--code-block-rx
  "```\\([[:alnum:]-]+\\)[ \t\r\n]+\\(\\(?:.\\|\n\\)*?\\)```"
  "Match a fenced markdown block:   ```lang NEWLINE … ```.
Group 1 = language tag, group 2 = body.")

(defun gpt--extract-last-code-block (text)
  "Return (LANG BODY) for the *last* fenced block in TEXT, or nil.
LANG is down-cased.  BODY has no closing ``` line."
  (let ((pos 0) lang body)
    (while (string-match gpt--code-block-rx text pos)
      (setq lang (downcase (match-string 1 text))
            body (match-string 2 text)
            pos  (match-end 0)))
    (when lang (list lang body))))               ; nil if none found


(defvar max-query-response-strlen  500000)


(defconst coq-query--allowed-prefix-re
  "^[[:space:]]*\\(Search\\|About\\|Print\\|Eval\\|Compute\\|Locate\\|Check\\)\\>"
  "Regexp that every valid Coq query must start with.")

(defun query-coq (queries)
  "Run one or more Coq/utility queries (newline-separated) and return a string.

Recognised commands:

  • Search / About / Print / Locate / Check   → sent to Coq
  • CppDefnOf <FQN>                           → fetch C++ definition

Each processed line is emitted as:

    >>> <original line>
    <response or error>

Blocks are separated by a blank line."
  (message "queries: %s" queries)
  (let* ((coq-prefixes '("Search" "About" "Print" "Locate" "Check" "Compute" "Eval"))
         (blocks '()))
    (dolist (line (split-string queries "\n"))
      (let* ((q (string-trim line)))
        (unless (string-empty-p q)
          (let* ((parts   (split-string q))
                 (prefix  (car parts))
                 (payload (string-trim (mapconcat #'identity (cdr parts) " "))))
            (cond
             ;; ── 1. CppDefnOf ------------------------------------------------
             ((string-equal prefix "CppDefnOf")
              (let* ((raw (condition-case err
                              (defn-of payload)
                            (error (format "Error: %s"
                                           (error-message-string err)))))
                     (res (string-trim (or raw ""))))
                (push (format ">>> %s\n%s"
                              q
                              (cond
                               ((string-empty-p res) "∅ (no results)")
                               ((> (length res) max-query-response-strlen)
                                "That definition is too long — please narrow it.")
                               (t res)))
                      blocks)))
             ;; ── 2. Coq queries ---------------------------------------------
             ((member prefix coq-prefixes)
              (with-current-buffer proof-response-buffer (read-only-mode -1))
              (let* ((raw (proof-shell-invisible-cmd-get-result q))
                     (res (string-trim (or raw ""))))
                (push (format ">>> %s\n%s"
                              q
                              (cond
                               ((string-empty-p res) "∅ (no results)")
                               ((> (length res) max-query-response-strlen)
                                "That query returned too many results — please refine it.")
                               (t res)))
                      blocks)))
             ;; ── 3. Anything else -------------------------------------------
             (t
              (push (format ">>> %s\nNot a valid query.  A query must begin \
with Search/About/Locate/Check/Print/Compute or CppDefnOf." q)
                    blocks)))))))
    (string-join (nreverse blocks) "\n\n")))


(defun wait-for-coq ()
  "Wait until processing is complete."
  (while (or proof-second-action-list-active
             (consp proof-action-list))
    ;; (message "wait for coq/compilation with %d items queued\n"
    ;;          (length proof-action-list))
    ;;
    ;; accept-process-output without timeout returns rather quickly,
    ;; apparently most times without process output or any other event
    ;; to process.
    (accept-process-output nil 0.1)))


;; In the same file as gpt-handle-coq-output ─ above the function definition
(defvar-local coq-programmer--pending-error-region nil
  "Cons of (START . END) markers delimiting the last Gallina block
that failed to compile.  The region stays in the buffer so the
user can read it; on the *next* GPT reply it is deleted just
before the new block (if any) is processed.")


;;;; ------------------------------------------------------------------
;;;;  helpers for detecting and prompting about `Admitted.` holes
;;;; ------------------------------------------------------------------

(defun coq-programmer--buffer-has-admit-p (body)
  "Return non-nil if BODY (a string) contains \"Admitted.\" or \"TOFIXLATER\"."
  (string-match-p "\\(?:Admitted\\.\\|TOFIXLATER\\)" body))

(defvar coq-programmer--admit-prompt
  "
I inserted your solution into emacs, and asked proof general to check it via coqtop.
Congratulations! Proof general reported no errors. However, your solution still contains `Admitted.`/TOFIXLATER holes.
Please pick one or more holes to implement.
In the call chain/tree from the function that is the main task, which you have already implemented,
pick hole(s) which are closest to the root.
If you were asked to implement a function on an Inductive type which is defined mutually inductive with other Inductive types, the task implicitly includes implementing the analogous functions on those types as well, likely as a block of mutually recursive functions. Implementing such holes should be the highest priority.

Once you have chosen the hole(s) to implement, YOU MUST FIRST check whether an implementation of the hole already exists in one of the `Require Import`ed files. To do that, FIRST issue a `Search` query, e.g. `Search ([type of hole]).`. For example, if the type of the hole is `foo -> bar`, issue the query `Search (foo -> bar).`, NOT `Search (_ : foo->bar)`: the latter is equivalent to `Search (_)` which will return everything and will go beyond your context length.
If `Search (foo -> bar)` doesn't yield a result, consider issuing other queries, e.g. reorder arguments, search by possible names.
If it does return a result with a promising name, you must do a `Print` on that name to ensure that it it self does not have holes, especially if the leaf of the fully qualified name matches an admit you introduced in your solution: the queries are done in a context that already has your solution, so the admits of your solution may show up as results in these queries.

Also, double check whether the hole was already implemented in the current conversation and you forgot to include it in the previous message.

If the implementation doesnt exist or you cannot find it using the queries, implement the holes PROPERLY: do NOT just put in dummy implementations to be filled later.
Put in as much effort into each hole as much as you put in the original problem, but always include FULL solutions to the original problem.

Beware that if you plan to implement a hole by structural recursion on an argument, the argument must have an `Inductive` type. Also if the `Inductive` type is defined mutually with other `Inductive` types, you may need to define your function as a mutually-recursive Fixpoint. If you have already implemented parts of this set of mutually recursive Fixpoints, you may need to put the new and old parts together in the same block of mutually-recursive `Fixpoint`s.

The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN. This is important because the non-human, non-LLM programmetic e-lisp loop that is chatting with you does not know to apply partial diffs and merely replaces full old solutions with the new one.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.
")


(defun typeOf (fqn)
  "Return the type information of fqn from the 'Check %s' Coq query, without trailing newline."
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "Check %s." fqn)))
         (type-pos (string-match ": " resp)))
    (if type-pos
        ;; Remove trailing newlines from the substring
        (replace-regexp-in-string "\n\\'" "" (substring resp (+ type-pos 2)))
      nil)))  ; Return nil if ": " is not found

(defun coq-prog--parse-short-module-output (print-output)
  "Given the string produced by `Print Module _` in *short* mode,
return a list of (KIND . NAME) pairs, where KIND is one of the
symbols `parameter`, `definition`, `inductive`."
  (let* (;; isolate the part between \"Struct\" and \"End\"
         (struct-start (string-match "Struct[ \t\n]+" print-output))
         (end-pos      (and struct-start
                            (string-match "[ \t\n]*End\\>" print-output
                                          (+ struct-start 6))))
         (body (if (and struct-start end-pos)
                   (substring print-output (+ struct-start 6) end-pos)
                 ""))                ; if not recognised, parse empty
         (rx "\\_<\\(Parameter\\|Definition\\|Inductive\\)[ \t\n]+\\([[:word:]'._]+\\)")
         (pos 0)
         items)
    (while (and (< pos (length body))
                (string-match rx body pos))
      (let* ((kind-str (match-string 1 body))
             (name     (match-string 2 body))
             (kind-sym (pcase kind-str
                         ("Parameter"  'parameter)
                         ("Definition" 'definition)
                         ("Inductive"  'inductive))))
        (push (cons kind-sym name) items)
        (setq pos (match-end 0))))
    (nreverse items)))


;;;###autoload
(defun coq-prog-show-module-items-at-point ()
  "Parse the short `Print Module` output for the identifier at point.

* Uses `thing-at-point` to obtain the symbol under the cursor.
* Runs `Print Module <symbol>.` via Proof General’s invisible shell.
* Passes the raw output to `coq-prog--parse-short-module-output`.
* Displays the parsed (KIND . NAME) list both in the echo area and in
  a buffer called *Coq-Module-Items*.

Assumes `Set Short Module Printing.` is in effect."
  (interactive)
  (let* ((mod (thing-at-point 'symbol t)))
    (unless mod
      (user-error "No symbol at point"))
    (with-current-buffer proof-response-buffer (read-only-mode -1))
    (let* ((raw (proof-shell-invisible-cmd-get-result
                 (format "Print Module %s." mod)))
           (items (coq-prog--parse-short-module-output raw)))
      ;; echo-area summary
      (message "Module %s items: %s" mod items)
      ;; detailed buffer
      (with-current-buffer (get-buffer-create "*Coq-Module-Items*")
        (read-only-mode -1)
        (erase-buffer)
        (insert (format "Items in module %s (short print):\n\n" mod))
        (dolist (it items)
          (insert (format "- %s: %s\n"
                          (pcase (car it)
                            ('parameter  "Parameter")
                            ('definition "Definition")
                            ('inductive  "Inductive"))
                          (cdr it))))
        (read-only-mode 1)
        (display-buffer (current-buffer))))))


(defun coq-prog-search-queries-for-axioms (names)
  "Build `Search` queries for each axiom NAME (a list of strings).

Looks up the type of each name using `typeOf`, then builds:
  Search (type) (* for hole `name` *) .

Returns a formatted string of all queries + their Coq responses.

If no types can be resolved, returns the empty string."
  (let* ((queries
          (string-join
           (delq nil
                 (mapcar (lambda (name)
                           (let* ((ty (typeOf name))
				  (onelinety (and ty (replace-regexp-in-string "[\n\r]+" " " ty)))
				  )
                             (when onelinety
                               (format "Search (%s) (* for hole `%s` *) ." onelinety name))))
                         names))
           "\n")))
    (if (string-empty-p queries)
        ""
      (concat "\n\n Below, I ran some queries to help you find out whether some of the holes are already implemented somewhere in the avaliable libraries.\n IF YOU NOTICE A RESULT WITH PROMISING NAME, YOU MUST FIRST DO A `Print` on that name to ensure that it it self does not have holes, especially if the leaf of the fully qualified name matches an admit you introduced in your solution: the queries are done in a context that already has your solution, so the admits of your solution may show up as results in these queries.\n\n\n"
              (query-coq queries)))))


(defun coq-programmer--build-admit-prompt ()
    (concat coq-programmer--admit-prompt (coq-prog-search-queries-for-module-params "LLMSOLN"))
    )

(defun trim-module (gallinacode)
  "If GALLINACODE starts with ‘Module <id>. … End <id>.’ (same <id>),
return just the interior; otherwise return it unchanged.

The match is *strict*:
  • ‘Module …’ must be the first non-blank thing.
  • ‘End ….’ (same name + dot) must be the last non-blank thing."
  (let* ((code   (string-trim gallinacode))         ;drop outer whitespace
         (head-r "^Module[[:space:]]+\\([A-Za-z0-9_']+\\)\\.[[:space:]\n]*")
         (tail-f (lambda (id)
                   (format "End[[:space:]]+%s\\.[[:space:]]*$"
                           (regexp-quote id)))))
    (if (string-match head-r code)
        (let* ((id        (match-string 1 code))
               (body-start (match-end 0))
               (tail-r     (funcall tail-f id)))
          (if (string-match tail-r code body-start)
              (string-trim                      ;strip interior edges too
               (substring code body-start (match-beginning 0)))
            code))                               ;mismatching ‘End’
      code)))                                    ;no leading ‘Module’

(defconst coq-prog--infomsg-axiom-re
  ;;   1-identifier                 2-status
  "^[[:space:]\n]*\\(`?\\(?:[[:word:][:digit:]_.'$]\\|[^[:ascii:][:cntrl:]]\\)+`?\\)[[:space:]\n]*is[[:space:]\n]*\\(declared\\|assumed\\)\\b"
  "Matches text inside <infomsg> that announces an axiom.")



(defun coq-prog--axioms-since (pos)
  "Return a list of axiom names logged in *coq* **after** buffer position POS.

It parses the slice with `libxml-parse-html-region` and extracts every
<infomsg> whose text matches `coq-prog--infomsg-axiom-re`."
  (with-current-buffer "*coq*"
    (let* ((dom   (libxml-parse-html-region pos (point-max)))
           (nodes (dom-by-tag dom 'infomsg))
           (ax    '()))
      (message "DOM: %s" dom)
      (message "Raw Coq XML slice:\n%s" (buffer-substring-no-properties pos (point-max)))
      (dolist (n nodes)
        (let ((txt (string-trim (dom-text n))))
          (when (string-match coq-prog--infomsg-axiom-re txt)
            (push (match-string 1 txt) ax))))
      (nreverse ax))))

(defun gpt-handle-coq-output (gpt-text)
  "Interact with Coq according to GPT-TEXT and return the next prompt."
  (set-buffer proof-script-buffer)

  ;; ---------- 0. delete previous kept region ----------
  (when coq-programmer--pending-error-region
    (delete-region (car coq-programmer--pending-error-region)
                   (cdr coq-programmer--pending-error-region))
    (setq coq-programmer--pending-error-region nil))

  ;; ---------- 1. parse GPT reply ----------
  (pcase-let ((`(,lang ,body) (gpt--extract-last-code-block gpt-text)))
    (pcase lang
      ;; =================================================  Gallina
      ("gallina"
       (let ((inhibit-read-only t)
             (beg (point))
             (log-start (with-current-buffer "*coq*" (point-max))))
         (insert body "\n")
         (let ((end (point)))
           (proof-assert-until-point)
           (wait-for-coq)
           (setq coq-programmer--pending-error-region
                 (cons (copy-marker beg) (copy-marker end)))
           (let* ((new-axioms (coq-prog--axioms-since log-start)))
             (cond
              ;; ---------- compile error ----------
              ((eq proof-shell-last-output-kind 'error)
               (concat "Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.\n\n"
                       proof-shell-last-output
                       "\n\nRemember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.\n "))

              ;; ---------- compiles but has Admitted / TOFIXLATER ----------
              ((or (consp new-axioms)
                   (string-match-p "TOFIXLATER" body))
               (setq coq-programmer--last-working-with-holes gpt-text)
               (concat coq-programmer--admit-prompt
                       (coq-prog-search-queries-for-axioms new-axioms)))

              ;; ---------- perfect success ----------
              (t
               "__SUCCESS__"))))))          ;;  <-- marker for main loop

      ;; =================================================  Coq query
      ("coqquery"
       (concat (query-coq (string-trim body))
               "\n\nRemember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.\n"))

      ;; =================================================  parse failure
      (_ "could not parse your response. please follow the formatting guidelines strictly"))))


;;;###autoload
(defun gpt-test-handle-coq-output-region (beg end)
  "Pass the selected region to `gpt-handle-coq-output' and show the result.

With an active region, the text between BEG and END is treated as the
raw GPT reply.  The function:
  1. Feeds that string to `gpt-handle-coq-output'.
  2. Prints the returned value in the echo area.
  3. Also opens (or refreshes) a helper buffer *GPT-Test Result*
     so you can inspect multi-line output or an empty string.

If no region is active, signal an error."
  (interactive "r")
  (unless (use-region-p)
    (user-error "No region selected"))
  (let* ((gpt-text (buffer-substring-no-properties beg end))
         (result   (gpt-handle-coq-output gpt-text)))
    (message "gpt-handle-coq-output → %s"
             (if (string-empty-p result) "<empty string>" result))
    ;; Show detailed/multi-line output in a side buffer
    (with-current-buffer (get-buffer-create "*GPT-Test Result*")
      (read-only-mode -1)
      (erase-buffer)
      (insert (if (string-empty-p result)
                  "<empty string returned by gpt-handle-coq-output>"
                result))
      (read-only-mode 1)
      (display-buffer (current-buffer)))))


(defvar coq-programmer-preamble
  (with-temp-buffer
    (insert-file-contents
     (expand-file-name "../../prompts/coding.md"
                       (file-name-directory load-file-name)))
    (buffer-string)))

(defvar coq-programmer-response-format
  "

# Response Format (IMPORTANT)
You can either give me (an elisp chat loop) the answer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```.
If you do not follow this format, I would not be able to respond to you properly.
Although I log and publish your responses in entirety, to respond to you, I ONLY LOOK AT THE LAST CODE BLOCK (```gallina or ```coqquery) IN YOUR RESPONSE.
If that is a ```coqquery block, I will send the queries to coqtop and give you back the responses.
If that is a ```gallina block, I will insert it into emacs+proof-general+company-coq and ask proof-general to check till the end. If there are coq errors, I will respond with the errors.

An example of a valid response is:
```coqquery
Print Stmt.
Print Expr.
```
An example of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
Definition bar : nat := 1+3.
```

You can include multiple queries in a ```coqquery block: one in each line.
THIS IS IMPORTANT. EVERY QUERY MUST BE IN EXACTLY ONE LINE.
The elisp loop talking to you does not do any fancy parsing to split the coqquery code block in to queries: it just treats every line as a separate query.

DO NOT emit any `Require Import/Export` commands in either types of blocks (coqquery or gallina). All the availble libraries have already been `Require`d, so they are availble, at least with fully qualified names. If needed, you can Import (but not `Require Import`) modules defining notations.

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.
In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.

")


(defun coq-comment-start ()
  (interactive)
  (coq-find-comment-start)
  )

(defun coq-comment-end ()
  (interactive)
  (forward-comment 1)
  )


;;;; ------------------------------------------------------------
;;;;  Helper: extract comment body *and* end position  (fatal-on-error style)
;;;; ------------------------------------------------------------

(defun coq-prog--comment-body ()
  "Return (BODY . pre-comment-code) for the Coq comment around point.
If point is not inside a comment, signal an error."
    (coq-find-comment-start)
    (let ((beg (point)))
      (coq-comment-end)                ; now at char *after* '*)'
      (let ((end (point)))
	(goto-char end)
	(insert "\n Set Printing FullyQualifiedNames.\n")
	(proof-assert-until-point)
	(wait-for-coq)
        (let ((body (buffer-substring-no-properties (+ beg 2) (- end 2))))
          (list body (buffer-substring-no-properties (point-min) beg))))))


(defun coq-prog--split-sections (raw)
  "Parse RAW (string) into (PROMPT queries files).

Sections start with:
  +++ QUERIES
  +++ FILES
Lines before the first +++ belong to PROMPT.  Order is free."
  (let ((current 'prompt)
        prompt-lines query-lines file-lines)
    (dolist (ln (split-string raw "\n"))
      (cond
       ((string-match-p "^\\+\\+\\+[ \t]*QUERIES" ln)
        (setq current 'queries))
       ((string-match-p "^\\+\\+\\+[ \t]*FILES" ln)
        (setq current 'files))
       ((string-match-p "^\\+\\+\\+" ln) ; unknown label
        (setq current 'prompt))
       (t
        (pcase current
          ('prompt  (push ln prompt-lines))
          ('queries (push ln query-lines))
          ('files   (push (string-trim ln) file-lines))))))
    (list (string-trim (string-join (nreverse prompt-lines) "\n"))
          (string-trim (string-join (nreverse query-lines)  "\n"))
          (nreverse file-lines))))

(defun coq-prog--format-query-results (query-block)
  "Run QUERY-BLOCK through `query-coq` and wrap under a markdown header."
  (unless (string-empty-p query-block)
    (concat "\n\n## Results of some relevant queries\n"
	                 (query-coq query-block))))

(defun coq-prog--format-file-blocks (paths base-dir)
  "Concatenate contents of listed Markdown FILES for the GPT prompt.

• `paths` – list of strings (may include blank lines).
• `base-dir` – directory against which relative paths are resolved.
• Every non-blank entry must name a regular, readable file;
  otherwise signal `error` (no silent failure).

Each file’s text is preceded by a single newline; no extra headers."
  (let ((nonblank
         (seq-filter (lambda (s) (not (string-empty-p (string-trim s))))
                     paths)))
    (mapconcat
     (lambda (rel)
       (let* ((abs (expand-file-name (string-trim rel) base-dir)))
         (unless (and (file-regular-p abs) (file-readable-p abs))
           (error "Background file `%s` is missing or unreadable" rel))
         (with-temp-buffer
           (insert-file-contents abs)
           (concat "\n" (string-trim (buffer-string))))))
     nonblank "")))

;;;; ------------------------------------------------------------
;;;;  Shorter coq-programmer-first-prompt (uses new helpers)
;;;; ------------------------------------------------------------

(defun coq-programmer-first-prompt ()
  "Build the initial GPT prompt from the rich comment around point.

Recognised subsections:
  • free text                 → core prompt
  • +++ COQ-QUERIES           → run each line via `query-coq`
  • +++ FILES                 → include those markdown files

A newline is inserted right after the comment so GPT code is added
outside the comment."
  ;; 1. extract body & get end position
  (interactive)
  (pcase-let*  ((`(,body, precode) (coq-prog--comment-body))
               (sections (coq-prog--split-sections body))
               (prompt   (nth 0 sections))
               (queries  (nth 1 sections))
               (files    (nth 2 sections))
               ;; 2. run queries / read files (fatal on error)
               (query-blk  (coq-prog--format-query-results queries))
               (files-blk (coq-prog--format-file-blocks
                           files (file-name-directory (buffer-file-name)))))
    (concat coq-programmer-preamble files-blk "\n\n\n# Current Task\n" prompt query-blk "\n\n# Contents of the current file\n\n```coq\n" precode "\n```\n\n You cannot change the content above. Your response will always be inserted after the above content. Do not repeat the above content in your response.\n\n" coq-programmer-response-format)
    ))



(defcustom coq-programmer-max-llm-calls 30
  "Maximum number of GPT calls allowed during a single `coq-programmer-loop` run.
Set to nil for no limit."
  :type '(choice (const :tag "Unlimited" nil)
                 (integer :tag "Number of calls"))
  :group 'coq-programmer)

;;;; ------------------------------------------------------------------
;;;;  helpers for file-based Markdown log
;;;; ------------------------------------------------------------------

(defun coq-programmer--initial-counts (file)
  "Return (USER . ASSISTANT) heading counts already present in FILE."
    '(0 . 0))

(defun coq-programmer--log-to-file (file role n msg)
  "Append one markdown entry to FILE and flush to disk."
  (append-to-file
   (format "## %s %d\n\n%s\n\n" role n msg)
   nil file))


(defun coq-programmer-loop ()
  "Autonomous GPT-4o ⇄ Coq session.

Logs go to <file>.v.md next to the current .v file.

The call-budget starts from `coq-programmer-max-llm-calls` (if numeric)
and *every time the user supplies feedback after a successful compile*
the budget is reset to CURRENT-CALLS + `coq-programmer-feedback-extension`."
  (interactive)
  (ensure-cpp-lsp-session)               ;; fail fast if no clangd session

  (let* ((coq-file   (buffer-file-name proof-script-buffer))
         (comm-file  (concat coq-file ".md"))
         (counts     (coq-programmer--initial-counts comm-file))
         (user-count    (car counts))
         (assist-count  (cdr counts))
         (llm-calls 0)
         ;; mutable budget that we may extend
         (max-calls (and (numberp coq-programmer-max-llm-calls)
                         coq-programmer-max-llm-calls)))

    ;; start a fresh markdown log
    (with-temp-file comm-file)
    (setq gpt-4o-conversation nil)

    (cl-labels
        ;; ------ tiny logger helper ----------------------------------
        ((log (role msg)
              (pcase role
                ("User"      (setq user-count   (1+ user-count)))
                ("Assistant" (setq assist-count (1+ assist-count))))
              (coq-programmer--log-to-file
               comm-file role
               (if (string= role "User") user-count assist-count)
               msg)))

      ;; ------ 1 · user's initial prompt to GPT ----------------------
      (let* ((first     (coq-programmer-first-prompt))
             (assistant (progn
                          (log "User" first)
                          (setq llm-calls (1+ llm-calls))
                          (gpt-4o--send first))))
        (log "Assistant" assistant)

        ;; ------ 2 · main interaction loop ---------------------------
        (let ((quit nil))
          (while (not quit)
            (let ((skip nil))          ; allows us to restart loop early

              ;; ---- budget guard (interactive) ----------------------
              (when (and max-calls (>= llm-calls max-calls))
                (let ((fb (coq-programmer--read-feedback)))
                  (if (string-empty-p fb)
                      ;; user hit RET  →  optionally re-insert fallback and quit
                      (progn
                        (with-current-buffer proof-script-buffer
                          (when coq-programmer--last-working-with-holes
                            (gpt-handle-coq-output
                             coq-programmer--last-working-with-holes)))
                        (log "System"
                             (format "LLM call budget (%d) exhausted.  Stopping session."
                                     max-calls))
                        (setq quit t)
                        (setq skip t))
                    ;; user gave feedback  →  extend budget & continue
                    (log "User" fb)
                    (setq llm-calls (1+ llm-calls))
                    (setq max-calls (+ llm-calls
                                       coq-programmer-feedback-extension))
                    (setq assistant (gpt-4o--send fb))
                    (log "Assistant" assistant)
                    (setq skip t))))     ; skip rest of loop iteration

              ;; ---- normal processing if not skipped ---------------
              (unless (or quit skip)
                (let* ((next (with-current-buffer proof-script-buffer
                               (gpt-handle-coq-output assistant))))
                  (cond
                   ;; ===== success → ask feedback ====================
                   ((string= next "__SUCCESS__")
                    (let ((fb (coq-programmer--read-feedback)))
                      (if (string-empty-p fb)
                          (setq quit t)
                        (log "User" fb)
                        (setq llm-calls (1+ llm-calls))
                        (setq max-calls (+ llm-calls
                                           coq-programmer-feedback-extension))
                        (setq assistant (gpt-4o--send fb))
                        (log "Assistant" assistant))))

                   ;; ===== GPT produced nothing → end ================
                   ((string-empty-p next)
                    (setq quit t))

                   ;; ===== ordinary continue =========================
                   (t
                    (log "User" next)
                    (setq llm-calls (1+ llm-calls))
                    (setq assistant (gpt-4o--send next))
                    (log "Assistant" assistant)))))))))))


(defun print-coq-programmer-first-prompt ()
  (interactive)
  (let ((ip (coq-programmer-first-prompt)))
    (with-current-buffer (get-buffer-create "*Initial Prompt*")
      (read-only-mode -1)
      (erase-buffer)
      (markdown-mode)
      (insert ip)
      (read-only-mode 1)
      (display-buffer (current-buffer)))))

;;;###autoload
(defun coq-prog-search-queries-at-point ()
  "Build `Search` queries for every `Parameter` in the module at point.

Assumes `Set Short Module Printing.` is active.
The function:
  1. Gets the symbol at point (module name).
  2. Runs `Print Module <name>.`
  3. Parses the short output with `coq-prog--parse-short-module-output`.
  4. For each `Parameter` calls `typeOf` to obtain its type.
  5. Returns a newline-separated string of `Search <type>.` lines and
     also shows it in the echo area.

If no parameters (or no types) are found, it returns nil."
  (interactive)
  (let ((mod (thing-at-point 'symbol t)))
    (unless mod
      (user-error "No symbol at point"))
    ;; Fetch and parse the module signature
    (message "%s "(coq-prog-search-queries-for-module-params mod))
    ))


(with-eval-after-load 'coq
  (define-key coq-mode-map (kbd "C-c l") #'coq-programmer-loop))

(with-eval-after-load 'coq
  (define-key coq-mode-map (kbd "C-c k") #'print-coq-programmer-first-prompt))

;; TODO:
;; GPT often gets some holes correct, but later forgets them in the later/final answer where they go back to Admitted.
;; one solution could be at timeout, give it all non-erroring versions and ask it to take the maximal subset.
;; or do this programattically: easiest would be to see if there is a name match between an axiom in the last version and a
;; Definition in the older version. emacs could put all versions in a module and 
;; put every version in a new module. dont ask GPT to include all code. just the defns that are being added/replaced. (no need to ever delete defns). the unreplaced ones become shallow notations to the previous module version and then add the new/replaced defns in the new module.


;; at the end, allow the user to issue a prompt and continue the discussion. maybe summarize/compress the prev chat to continue discussion (just aggregate query responses keep them in an emacs list so no need to parse the chat. discard the rest, except the initial prompt)


;; make query-coq return an error if there is any error in a query. use this for coq-programmer-first-prompt, but not on GPT-generated queries




;;; defn-of.el --- fetch C++ definition via clangd, annotated -*- lexical-binding:t -*-
(require 'cl-lib)
(require 'lsp-mode)
(require 'cc-mode)


(defun defn-of--sanitize-fqn (raw)
  "Remove surrounding quotes, periods and whitespace from RAW."
  (let ((s (string-trim raw)))
    (setq s (string-trim-left  s "[\"'.]*"))   ; strip left  quotes / dots
    (setq s (string-trim-right s "[\"'.]*"))   ; strip right quotes / dots
    s))


(defun defn-of--pick-workspace ()
  (or (cl-find-if
       (lambda (buf)
         (with-current-buffer buf
           (and (derived-mode-p 'c++-mode) (bound-and-true-p lsp-mode))))
       (buffer-list))
      (user-error "No active C++ LSP buffer (open a dummy.cpp first)")))

(defun defn-of--choose-symbol (syms _query)
  (or (car syms) (user-error "Symbol not found")))

(defun defn-of--extract (file pos-json)
  (let* ((buf  (find-file-noselect file))
         (line (+ 1 (gethash "line" pos-json))) ;; 1-based for point ops
         (col  (gethash "character" pos-json)))
    (with-current-buffer buf
      (goto-char (point-min))
      (forward-line (1- line))
      (forward-char col)
      (c-beginning-of-defun)
      (let ((beg (point)))
        (c-end-of-defun)
        (cons beg (point))))))          ;; (beg . end)

;;;###autoload
(defun defn-of (fqncppp &optional insert-p)
  "Return (or with C-u INSERT-P, insert) the definition of FQNCPP.
Prepends a comment ‘// FILE:LINE’ to the returned text."
  (interactive "sC++ symbol (FQN): \nP")
  (let* ((cpp-buf   (defn-of--pick-workspace))
	 (fqncpp (defn-of--sanitize-fqn fqncppp))
         sym-info file start-pos line-no text-range
         defun-text)
    ;; ── query clangd ──────────────────────────────────────────────────────
    (with-current-buffer cpp-buf
      (setq sym-info
            (defn-of--choose-symbol
             (lsp-request "workspace/symbol" `(:query ,fqncpp))
             fqncpp)))
    (let* ((loc   (gethash "location" sym-info))
           (uri   (gethash "uri" loc))
           (range (gethash "range" loc)))
      (setq file       (lsp--uri-to-path uri))
      (setq start-pos  (gethash "start" range))
      (setq line-no    (+ 1 (gethash "line" start-pos)))
      (setq text-range (defn-of--extract file start-pos)))
    ;; ── assemble result in a temporary buffer ────────────────────────────
    (with-temp-buffer
      (insert (format "// %s:%d\n" file line-no))
      (insert-buffer-substring
       (find-file-noselect file)
       (car text-range) (cdr text-range))
      (setq defun-text (buffer-string)))
    (when insert-p (insert defun-text))
    defun-text))



;; TODO
;; auto add Set Printing FQN
;; ensure a c++ file is open in case spec.md is included


;;; ------------------------------------------------------------------
;;;  NEW: guard that clangd is running in *some* C++ buffer
;;; ------------------------------------------------------------------
(require 'cl-lib)

;;;###autoload
(defun ensure-cpp-lsp-session ()
  "Abort unless there is at least one `c++-mode` buffer with `lsp-mode` on.
Returns that buffer on success."
  (or (cl-find-if
       (lambda (buf)
         (with-current-buffer buf
           (and (derived-mode-p 'c++-mode)
                (bound-and-true-p lsp-mode))))
       (buffer-list))
      (user-error "No active C++ LSP buffer — open any .cpp file first")))


;;; ------------------------------------------------------------------
;;;  NEW: prompt the human for post-success feedback
;;; ------------------------------------------------------------------
;;;###autoload
(defun coq-programmer--read-feedback ()
  "Read one line of feedback from the minibuffer (may be empty)."
  (string-trim
   (read-from-minibuffer
    "✅ Compiled with no errors.  Feedback for GPT (RET to finish): ")))

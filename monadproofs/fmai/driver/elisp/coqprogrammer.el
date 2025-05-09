
;; ;; Buffer-local list that stores the alternating user / assistant messages.
;; (defvar-local gpt-4o-conversation nil
;;   "Conversation history for `gpt-4o-chat'.  Each element is a string, 
;; alternating USER, ASSISTANT, USER, … in the order they were sent.")


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
  "^[[:space:]]*\\(Search\\|About\\|Print\\|Locate\\|Check\\)\\>"
  "Regexp that every valid Coq query must start with.")

(defun query-coq (queries)
  "Run one or more Coq queries (newline-separated) and return a single string.

Rules per line:
  · If it begins with Search / About / Print / Locate / Check,
    execute it via Proof General and include the response.
  · Otherwise, do **not** execute the line; instead include the standard
    \"not a valid query\" error message for that line.

Every processed line is emitted in the form:

    >>> <original line>
    <response or error>

Blocks are separated by a blank line."
  (let* ((valid-prefixes '("Search" "About" "Print" "Locate" "Check"))
         (blocks '()))
    (dolist (line (split-string queries "\n"))
      (let* ((q (string-trim line)))
        (unless (string-empty-p q)
          (let ((prefix (car (split-string q))))
            (if (member prefix valid-prefixes)
                ;; ---------- valid query ----------
                (progn
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
              ;; ---------- invalid line ----------
              (push (format ">>> %s\nNot a valid query.  A query must begin with Search/About/Locate/Check/Print. \
Do not add Require/Import or other vernacular here." q)
                    blocks))))))
    ;; concatenate in original order
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

(defvar coq-programmer--build-admit-prompt
  "
The code now compiles but still contains `Admitted.`/TOFIXLATER holes.
Please pick one or more holes to implement.
In the call chain/tree from the function that is the main task, which you have already implemented,
pick hole(s) which are closest to the root.
If you were asked to implement a function on an Inductive type which is defined mutually inductive with other Inductive types, the task implicitly includes implementing the analogous functions on those types as well, likely as a block of mutually recursive functions. Implementing such holes should be the highest priority.

Once you have chosen the hole(s) to implement, YOU MUST FIRST check whether an implementation of the hole already exists in one of the `Require Import`ed files. To do that, FIRST issue a `Search` query, e.g. `Search ([type of hole]).`. For example, if the type of the hole is `foo -> bar`, issue the query `Search (foo -> bar).`, NOT `Search (_ : foo->bar)`: the latter is equivalent to `Search (_)` which will return everything and will go beyond your context length.
If `Search (foo -> bar)` doesn't yield a result, consider issuing other queries, e.g. reorder arguments, search by possible names.

Also, double check whether the hole was already implemented in the current conversation and you forgot to include it in the previous message.

If the implementation doesnt exist or you cannot find it using the queries, implement the holes PROPERLY: do NOT just put in dummy implementations to be filled later.
Put in as much effort into each hole as much as you put in the original problem, but always include FULL solutions to the original problem.

Beware that if you plan to implement a hole by structural recursion on an argument, the argument must have an `Inductive` type. Also if the `Inductive` type is defined mutually with other `Inductive` types, you may need to define your function as a mutually-recursive Fixpoint. If you have already implemented parts of this set of mutually recursive Fixpoints, you may need to put the new and old parts together in the same block of mutually-recursive `Fixpoint`s.

The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN. This is important because the non-human, non-LLM programmetic e-lisp loop that is chatting with you does not know to apply partial diffs and merely replaces full old solutions with the new one.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.
")


;;;; ------------------------------------------------------------------
;;;;  main entry – replacement for gpt-handle-coq-output
;;;; ------------------------------------------------------------------

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
             (beg (point)))
         (insert body "\n")
         (let ((end (point)))
           (proof-assert-until-point)
           (wait-for-coq)
           (cond
            ;; ---------- compile error ----------
            ((eq proof-shell-last-output-kind 'error)
             (setq coq-programmer--pending-error-region
                   (cons (copy-marker beg) (copy-marker end)))
             (concat "Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.\n\n" proof-shell-last-output))

            ;; ---------- compiles but has Admitted ----------
            ((coq-programmer--buffer-has-admit-p body)
             (setq coq-programmer--pending-error-region
                   (cons (copy-marker beg) (copy-marker end)))
             (setq coq-programmer--last-working-with-holes gpt-text)  ;; NEW
             coq-programmer--build-admit-prompt)

            ;; ---------- perfect success ----------
            (t
             (setq coq-programmer--last-working-with-holes nil)   ;; NEW
             "Success098")))))

      ;; =================================================  Coq query
      ("coqquery" (query-coq (string-trim body)))

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
If that is a ```gallina block, I will insert it into emacs+proof-general+company-coq and ask proof-general to check till the end.
If there are coq errors, I will respond with the errors.

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

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.
DO NOT emit any `Require Import/Export` commands. All the availble libraries have already been `Require`d, so they are availble, at least with fully qualified names. If needed, you can Import (but not `Require Import`) modules defining notations.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.

")

(defun coq-programmer-first-prompt2 (core-prompt)
  (concat coq-programmer-preamble core-prompt coq-programmer-response-format)
  )

(defun coq-programmer-first-prompt-interactive ()
  (let ((core-prompt (read-string "You: ")))
    (coq-programmer-first-prompt2 core-prompt)
    )
  )

(defun coq-comment-start ()
  (interactive)
  (coq-find-comment-start)
  )

(defun coq-comment-end ()
  (interactive)
  (forward-comment 1)
  )

(defun coq-programmer-first-prompt ()
  "Extract the GPT prompt from the Coq comment around point, excluding the `(*` and `*)`.

Inserts a newline after the `*)` so inserted code appears after the comment."
  (coq-find-comment-start)
  (let ((beg (point)))
    (coq-comment-end)
    (let ((end (point)))
      ;; Move point to just after the comment
      (goto-char end)
      (insert "\n")
      (proof-assert-until-point)
      (wait-for-coq)
      (let ((core-prompt (string-trim
                          (buffer-substring-no-properties (+ beg 2) (- end 2)))))
        (coq-programmer-first-prompt2 core-prompt)))))

(with-eval-after-load 'coq
  (define-key coq-mode-map (kbd "C-c l") #'coq-programmer-loop))

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
  (if (file-exists-p file)
      (with-temp-buffer
        (insert-file-contents file)
        (cons (how-many "^## User" (point-min) (point-max))
              (how-many "^## Assistant" (point-min) (point-max))))
    '(0 . 0)))

(defun coq-programmer--log-to-file (file role n msg)
  "Append one markdown entry to FILE and flush to disk."
  (append-to-file
   (format "## %s %d\n\n%s\n\n" role n msg)
   nil file))


;;;###autoload
(defun coq-programmer-loop ()
  "Autonomous GPT-4o ⇄ Coq session.
Dialogue is written to a persistent `comm.md` in the same
directory as the current `.v` file.  Stops when:
 • code compiles with no `Admitted.`
 • user hits C-g
 • `coq-programmer-max-llm-calls` budget is exhausted."
  (interactive)
  (let* ((coq-file (buffer-file-name proof-script-buffer))
         (comm-file (expand-file-name "comm.md"
                                      (file-name-directory coq-file)))
         ;; running heading counters, initialised from existing file
         (counts (coq-programmer--initial-counts comm-file))
         (user-count (car counts))
         (assist-count (cdr counts))
         ;; call budget
         (llm-calls 0))
    ;; ---- 0. truncate / create comm.md so we start from scratch ----
    (with-temp-file comm-file)  ; write nothing => clears file
    ;; fresh conversation history for this session
    (setq gpt-4o-conversation nil)

    ;; helper to log + update counters
    (cl-labels ((log (role msg)
                     (pcase role
                       ("User"      (setq user-count   (1+ user-count)))
                       ("Assistant" (setq assist-count (1+ assist-count))))
                     (coq-programmer--log-to-file
                      comm-file role
                      (if (string= role "User") user-count assist-count)
                      msg)))

      ;; -------- 1. get first prompt from user -----------
      (let* ((first (coq-programmer-first-prompt))
             (assistant (progn
                          (log "User" first)
                          (setq llm-calls (1+ llm-calls))
                          (gpt-4o--send first))))
        (log "Assistant" assistant)

        ;; -------- 2. main loop -----------
        (let ((quit nil))
          (while (not quit)
            ;; stop if cost limit hit
	    (when (and coq-programmer-max-llm-calls
		       (>= llm-calls coq-programmer-max-llm-calls))
	      ;; If we have a fallback snippet with admits, re-insert it
	      (with-current-buffer proof-script-buffer
		(when coq-programmer--last-working-with-holes
		  (gpt-handle-coq-output coq-programmer--last-working-with-holes)))
	      (log "System"
		   (format "LLM call budget (%d) exhausted.  Stopping session."
			   coq-programmer-max-llm-calls))
	      (setq quit t))
            (unless quit
              (let* ((next
                      (with-current-buffer proof-script-buffer
                        (gpt-handle-coq-output assistant))))
                (cond
                 ;; finished
                 ((or (string-empty-p next)
                      (string= next "Success098"))
                  (setq quit t))

                 ;; keep cycling
                 (t
                  (log "User" next)
                  (setq llm-calls (1+ llm-calls))
                  (setq assistant (gpt-4o--send next))
                  (log "Assistant" assistant)))))))))))


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

(defun coq-prog-search-queries-for-module-params (mod)
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
    ;; Fetch and parse the module signature
    (with-current-buffer proof-response-buffer (read-only-mode -1))
    (let* ((raw   (proof-shell-invisible-cmd-get-result
                   (format "Print Module %s." mod)))
           (items (coq-prog--parse-short-module-output raw))
           (queries
            (string-join
             (delq nil
                   (mapcar (lambda (it)
                             (when (eq (car it) 'parameter)
                               (let ((ty (typeOf (concat mod "." (cdr it)))))
                                 (when ty (format "Search (%s)." ty)))))
                           items))
             "\n")))
      (if (string-empty-p queries)
          (message "No parameters (or no types found) in module %s." mod)
        (message "%s" (concat "Below is a suggestion of queries to run to find out whether some of the holes are already implemented somewhere in the avaliable libraries\n"  queries)))
      queries))


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
    (coq-prog-search-queries-for-module-params mod)
    ))

;; TODO:
;; GPT often gets some holes correct, but later forgets them in the later/final answer where they go back to Admitted.
;; one solution could be at timeout, give it all non-erroring versions and ask it to take the maximal subset.
;; or do this programattically: easiest would be to see if there is a name match between an axiom in the last version and a
;; Definition in the older version. emacs could put all versions in a module and 
;; put every version in a new module. dont ask GPT to include all code. just the defns that are being added/replaced. (no need to ever delete defns). the unreplaced ones become shallow notations to the previous module version and then add the new/replaced defns in the new module.

;; allow multiple queries: already implemented

;; at the end, allow the user to issue a prompt and continue the discussion. maybe summarize/compress the prev chat to continue discussion (just aggregate query responses keep them in an emacs list so no need to parse the chat. discard the rest, except the initial prompt)


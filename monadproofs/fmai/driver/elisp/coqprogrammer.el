
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


;;; context pruning: 1) on Search response, ask GPT to filter in items it thinks are useful. also omit larger types.
;;;                  2) always keep conversation ength to 3 max? ask GPT to summarize other stuff?


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


(defun query-coq (query)
  "Return a tuple with the first and second words of the first line starting with 'Module' from the 'Locate %s' Coq query."
  (with-current-buffer proof-response-buffer (read-only-mode -1))
  (let* ((resp (proof-shell-invisible-cmd-get-result
                query)))
    resp))

(defun proof-shell-wait-until-no-output ()
  "Block until Proof General’s action queue is empty."
  (while (proof-shell-busy)
    (sleep-for 1)))

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
  "Return non-nil if BODY (a string) contains the substring \"Admitted.\"."
  (string-match-p "Admitted\\." body))

(defvar coq-programmer--build-admit-prompt
  "
The code now compiles but still contains `Admitted.` holes.
Please pick one or more holes to implement.
Prefer picking hole(s) that are more higher level.

IMPORTANT: First check whether what you want to implement is already implemented somewhere.
You can use the `Search` query and then use the `Print` query on promising names/results to confirm that they are implementing exactly what was assumed by the callers.

If the implementation doesnt exist or you cannot find it using the queries, implement the holes PROPERLY: do NOT just put in dummy implementations to be filled later.
Put in as much effort into each hole as much as you put in the original problem, but always include FULL solutions to the original problem.
The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN. This is important because the non-human, non-LLM programmetic e-lisp loop that is chatting with you does not know to apply partial diffs and merely replaces full old solutions with the new one.
")


;;;; ------------------------------------------------------------------
;;;;  main entry – replacement for gpt-handle-coq-output
;;;; ------------------------------------------------------------------

(defun gpt-handle-coq-output (gpt-text)
  "Interpret GPT-TEXT, interact with Coq, and return the next prompt for GPT.
‘Success098’ means finished; any other non-empty string continues the loop.
If a `coqquery` yields no output, return a fixed explanatory string rather
than the empty string."
  ;; Ensure we work inside the proof script buffer
  (set-buffer proof-script-buffer)

  ;; ---------- 0.  delete previous failed snippet, if any ----------
  (when coq-programmer--pending-error-region
    (let ((beg (car coq-programmer--pending-error-region))
          (end (cdr coq-programmer--pending-error-region)))
      (when (and (marker-position beg) (marker-position end))
        (delete-region beg end)))
    (setq coq-programmer--pending-error-region nil))

  ;; ---------- 1.  parse GPT reply ----------
  (pcase-let ((`(,lang ,body) (gpt--extract-last-code-block gpt-text)))
    (pcase lang
      ;; =====================================================
      ;; 1. Gallina code
      ;; =====================================================
      ("gallina"
       (let ((inhibit-read-only t)
             (beg (point)))
         (insert body "\n")
         (let ((end (point)))
           (proof-assert-until-point)
           (wait-for-coq)

           (cond
            ;; compile error
            ((eq proof-shell-last-output-kind 'error)
             (setq coq-programmer--pending-error-region
                   (cons (copy-marker beg) (copy-marker end)))
             proof-shell-last-output)

            ;; compiles but still has Admitted.
            ((coq-programmer--buffer-has-admit-p body)
             (setq coq-programmer--pending-error-region
                   (cons (copy-marker beg) (copy-marker end)))
             coq-programmer--build-admit-prompt)

            ;; perfect success
            (t "Success098")))))

      ;; =====================================================
      ;; 2. Coq query block
      ;; =====================================================
      ("coqquery"
       (let* ((raw (query-coq (string-trim body)))
              (res (string-trim (or raw ""))))
         (if (string-empty-p res)
             "That query has no errors but returned an empty result. For `Search` wueries, this means nothing in the current context matches the search criteria."
           res)))

      ;; =====================================================
      ;; 3. parse failure
      ;; =====================================================
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
You can either give me the anwer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```. 
If you do not follow this format, my automated engine cannot parse your response.
An example of a valid response is:
```coqquery
Print Stmt.
```
An example of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
```

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.
")

(defun coq-programmer-first-prompt2 (core-prompt)
  (concat coq-programmer-preamble core-prompt coq-programmer-response-format)
  )

(defun coq-programmer-first-prompt ()
  (let ((core-prompt (read-string "You: ")))
    (coq-programmer-first-prompt2 core-prompt)
    )
  )


(defcustom coq-programmer-max-llm-calls 50
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


 n;; ;; Buffer-local list that stores the alternating user / assistant messages.
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

(defun coq-programmer--buffer-has-admit-p ()
  "Return non-nil if the current buffer still contains an `Admitted.` line."
  (save-excursion
    (goto-char (point-min))
    (re-search-forward "^[ \t]*Admitted\\." nil t)))

(defun coq-programmer--build-admit-prompt ()
  "Construct a follow-up prompt for GPT asking to fill one of NAMES."
  (format
   (concat
    "The code now compiles but still contains `Admitted.` holes.\n"
    "Here are the remaining ones (choose the most **high-level** to implement next):\n%s\n\n"
    "Please replace the **entire admitted definition** (not just its body) "
    "and output the full replacement inside a ```gallina``` block.  "
    "End your message with exactly one ```gallina``` or ```coqquery``` block as per the guidelines.")))

(defvar coq-programmer-response-format
  "
The code now compiles but still contains `Admitted.` holes.
Please pick one or more holes to implement.
Prefer picking hole(s) that are more higher level.
The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN.
")


;;;; ------------------------------------------------------------------
;;;;  main entry – replacement for gpt-handle-coq-output
;;;; ------------------------------------------------------------------

(defun gpt-handle-coq-output (gpt-text)
  "Interpret GPT-TEXT, talk to Coq, and return the string to feed back.
If GPT did not end with a valid ```gallina``` or ```coqquery``` block,
return the fixed error prompt demanded by the guidelines.
If compilation succeeds but `Admitted.` holes remain, return a prompt
asking GPT to implement one of them; otherwise return \"Success098\"."
  ;; ----- 0.  Clean up any *previous* failed block -----
  (when coq-programmer--pending-error-region
    (let ((beg (car coq-programmer--pending-error-region))
          (end (cdr coq-programmer--pending-error-region)))
      (when (and (marker-position beg) (marker-position end))
        (delete-region beg end)))
    (setq coq-programmer--pending-error-region nil))

  ;; ----- 1.  Parse the *new* GPT reply -----
  (pcase-let ((`(,lang ,body) (gpt--extract-last-code-block gpt-text)))
    (pcase lang
      ;; ---------- Gallina code ----------
      ("gallina"
       (let ((beg (point)) (inhibit-read-only t))
         (insert body "\n")
         (let ((end (point)))
           (proof-assert-until-point)
           (wait-for-coq)
           (if (eq proof-shell-last-output-kind 'error)
               ;; ---- still a compile error ----
               (progn
                 (setq coq-programmer--pending-error-region
                       (cons (copy-marker beg) (copy-marker end)))
                 proof-shell-last-output)
             ;; ---- compiled OK ----
             (if (coq-programmer--buffer-has-admit-p)
                 ;; ask GPT to fill a hole
                 (coq-programmer--build-admit-prompt
                  (coq-programmer--list-admit-names))
               ;; no holes left – success sentinel
               "Success098")))))

      ;; ---------- Coq query ----------
      ("coqquery"
       (query-coq (string-trim body)))

      ;; ---------- Un-parsable ----------
      (_
       "could not parse your response. please follow the formatting guidelines strictly"))))

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
An examplf of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
```

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasnt available in the queries you have issued so far.
")

(defun coq-programmer-first-prompt2 (core-prompt)
  (concat coq-programmer-preamble core-prompt coq-programmer-response-format)
  )

(defun coq-programmer-first-prompt ()
  (let ((core-prompt (read-string "You: ")))
    (coq-programmer-first-prompt2 core-prompt)
    )
  )

;;;###autoload
(defun coq-programmer-loop ()
  "Run an autonomous GPT-4o ⇄ Coq session, logging the dialogue in Markdown
with numbered headings:

    ## User 1
    ...
    ## Assistant 1
    ...

Counts restart when you open a fresh *Coq Programmer* buffer."
  (interactive)
  (let* ((coq-buf  (current-buffer))                 ; the .v buffer
         (chat-buf (get-buffer-create "*Coq Programmer*")))
    ;; show / select the chat window but keep handle on script buffer
    (pop-to-buffer chat-buf)
    (with-current-buffer chat-buf
      (text-mode)

      ;; ---------------- buffer-local state ----------------
      (unless (local-variable-p 'gpt-4o-conversation)
        (setq-local gpt-4o-conversation nil))
      (unless (local-variable-p 'coq-prog-user-count)
        (setq-local coq-prog-user-count 0))
      (unless (local-variable-p 'coq-prog-assist-count)
        (setq-local coq-prog-assist-count 0))

      ;; ---------------- markdown logger ----------------
      (cl-labels
          ((log (role msg)
                (goto-char (point-max))
                (let ((n (pcase role
                           ("User"      (setq coq-prog-user-count
                                              (1+ coq-prog-user-count)))
                           ("Assistant" (setq coq-prog-assist-count
                                              (1+ coq-prog-assist-count))))))
                  (insert (format "## %s %d\n\n%s\n\n"
                                  role n msg))
                  (goto-char (point-max)))))

        ;; ------------- 1. first prompt -------------
        (let* ((first (coq-programmer-first-prompt))
               (assistant (progn
                            (log "User" first)
                            (gpt-4o--send first))))
          (log "Assistant" assistant)

          ;; ------------- 2. conversation loop -------------
          (let ((quit nil))
            (while (not quit)
              (let* ((next
                      (with-current-buffer coq-buf
                        (gpt-handle-coq-output assistant))))
                (cond
                 ;; successful compile + no admits  → stop
                 ((or (string-empty-p next)
                      (string= next "Success098"))
                  (setq quit t))

                 ;; otherwise keep cycling
                 (t
                  (log "User" next)
                  (setq assistant (gpt-4o--send next))
                  (log "Assistant" assistant)))))))))))

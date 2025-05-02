;; Buffer-local list that stores the alternating user / assistant messages.
(defvar-local gpt-4o-conversation nil
  "Conversation history for `gpt-4o-chat'.  Each element is a string, 
alternating USER, ASSISTANT, USER, … in the order they were sent.")


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

;;;###autoload
(defun gpt-4o-chat-loop ()
  "Open *GPT-4o Chat* buffer and keep chatting until the user quits.
Type an empty line (or press C-g) to exit the loop."
  (interactive)
  (let ((buf (get-buffer-create "*GPT-4o Chat*")))
    (pop-to-buffer buf)
    (with-current-buffer buf
      (text-mode)                          ; simple major mode
      (unless (local-variable-p 'gpt-4o-conversation)
        (setq-local gpt-4o-conversation nil))
      ;; main REPL-style loop
      (let ((quit nil))
        (while (not quit)
          (condition-case nil
              (let ((user (read-string "You: ")))
                (if (string-blank-p user)
                    (setq quit t)          ; empty input ⇒ leave loop
                  ;; show user line
                  (goto-char (point-max))
                  (gpt-4o--append "User" user)
                  ;; get assistant reply
                  (let ((assistant (gpt-4o--send user)))
                    (gpt-4o--append "Assistant" assistant)
                    (goto-char (point-max)))))
            (quit                            ; C-g to abort read-string
             (setq quit t))))))))

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

;;;; ---------------  main entry point ---------------
(defun gpt-handle-coq-output (gpt-text)
  "Interpret GPT-TEXT, talk to Coq, and return the string to feed back.
If GPT did not end with a valid ```gallina``` or ```coqquery``` block,
return the fixed error prompt demanded by the guidelines."
  (pcase-let ((`(,lang ,body) (gpt--extract-last-code-block gpt-text)))
    (pcase lang
      ;; ---------------- 1. Gallina code ----------------
      ("gallina"
       (let ((beg (point)) (inhibit-read-only t))
         (insert body "\n")                       ; literal paste
         (proof-assert-until-point)               ; type-check:contentReference[oaicite:0]{index=0}
         (proof-shell-wait)       ; helper below
         (if (eq proof-shell-last-output-kind 'error) ; PG tells us:contentReference[oaicite:1]{index=1}
             proof-shell-last-output            ; relay error
           "Success098")))                                  ; success ⇒ empty prompt

      ;; ---------------- 2. Coq query -------------------
      ("coqquery"
         (query-coq (string-trim body)))

      ;; ---------------- 3. Anything else ---------------
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

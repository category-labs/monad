;;
;; Copyright © 2024-2025 BlueRock Security, Inc. (“BlueRock”)
;;
;; This file is CONFIDENTIAL AND PROPRIETARY to BlueRock. All rights reserved.
;;
;; Use of this file is only permitted subject to a separate written license agreement with BlueRock.
;;

(require 'company-coq)
(require 'proof-general)


(defun extract-tag-content (input tag)
  "Extract the content between the given TAG from the INPUT string."
  (let ((start-tag (concat "<" tag ">"))
        (end-tag (concat "</" tag ">"))
        (start-pos nil)
        (end-pos nil))
    (setq start-pos (string-match (regexp-quote start-tag) input))
    (when start-pos
      (setq start-pos (+ start-pos (length start-tag)))
      (setq end-pos (string-match (regexp-quote end-tag) input start-pos))
      (when end-pos
        (substring input start-pos end-pos)))))

(defun parse-emacs-request (input)
  "Parse the EmacsRequest string and return a native Emacs Lisp representation."
  (let ((proofscript nil)
        (exec nil)
        (cont nil))
    (cond
     ;; Check for EBacktrack
     ((and (string-match "<BACKTRACK>" input) (string-match "</BACKTRACK>" input))
      (setq proofscript (extract-tag-content input "PROOFSTEPS"))
      (setq cont (extract-tag-content input "CONTINUATION"))
      `(:type backtrack :proofscript ,proofscript :continuation ,cont))
     ;; Check for NoBacktrack
     ((and (string-match "<NOBACKTRACK>" input) (string-match "</NOBACKTRACK>" input))
      (setq proofscript (extract-tag-content input "PROOFSTEPS"))
      (setq exec (extract-tag-content input "EXECUTECOMMANDS"))
      (setq cont (extract-tag-content input "CONTINUATION"))
      `(:type nobacktrack :proofscript ,proofscript :exec ,exec :continuation ,cont))
     (t
      (error "Unrecognized EmacsRequest format")))))

(defun escape-quotes-for-coq (input)
  "Replace all occurrences of \" in INPUT with \"\"."
  (replace-regexp-in-string "\"" "\"\"" input))

;;parse-emacs-request and extract-tag-content written by : https://chatgpt.com/share/90abc0fe-aaef-4931-87f7-e9db679de834

(defun next-continuation (base-pos actual-proof-offset cur-cont)
  "Process the next continuation step."
  (interactive "r")
  (let* ((_ (message "executing cont: %s" cur-cont))
         (input1 (proof-shell-invisible-cmd-get-result cur-cont))
         (parsed (parse-emacs-request input1))
         (proofscript (plist-get parsed :proofscript))
         (continuation (plist-get parsed :continuation))
         (cur-pos (point)))
    (message "response was: %s" input1)
    ;; Delete content from base-pos to current-pos
    (delete-region base-pos cur-pos)
    ;; Insert proofscript at base-pos
    (goto-char base-pos)
    (insert (substring proofscript actual-proof-offset))
    (insert continuation)
    ;; Clean the continuation string
    (setq continuation (string-trim continuation)) ;; move it to the let*
    ;; Call next-continuation with updated base-pos and new continuation if not empty
    (unless (string-empty-p continuation)
      (next-continuation base-pos actual-proof-offset (concat "ltac2:("continuation " \"" (escape-quotes-for-coq proofscript) "\").")))))

;; precondition: the cursor is just beginning of the following line:
;; Lemma foo_proof: denoteModule module ** callee1_spec ** callee2_spec ... |-- foo_spec.
(defun prove-fun ()
  (interactive)
  (save-excursion;; revert to current point after executing the below. important to undo the proof steps done in ltac2 before executing the proofscript it produced
    (let* ((lemma-start (point))
           (_ (proof-assert-next-command-interactive))
           (_ (with-current-buffer proof-script-buffer
                (insert "Proof.")))
           (_ (proof-assert-next-command-interactive))
           (lemma-end (point))
           (proof-statement (with-current-buffer proof-script-buffer
                              (buffer-substring-no-properties lemma-start lemma-end))))
      (while proof-shell-busy
        (sit-for 1))
      (next-continuation lemma-end (+ (- lemma-end lemma-start) 1)
                         (concat "ltac2:(stepUntilEmacsInteract false \"" proof-statement "\" 0 [] 0)."))
      ))
  )

(defun exec-command ()
  "Process the next continuation step."
  (interactive)
  (message "executing cont: [%s]" (proof-shell-invisible-cmd-get-result "iExists 0")))

(provide 'ltac2driver)

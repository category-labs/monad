;;
;; Copyright © 2024-2025 BlueRock Security, Inc. (“BlueRock”)
;;
;; This file is CONFIDENTIAL AND PROPRIETARY to BlueRock. All rights reserved.
;;
;; Use of this file is only permitted subject to a separate written license agreement with BlueRock.
;;

(require 'company-coq)
(require 'proof-general)

(defun br/shortName (fqn)
  "Shorter name of a fully qualified name."
  (interactive)
  (with-current-buffer proof-response-buffer (read-only-mode -1))
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "About %s." fqn)))
         (match-pos (string-match " :" resp)))
    (message "shortName %s: %s" fqn resp)
    (if match-pos
        (substring resp 0 match-pos)
      "")));; in this case, ideally we should check that the output of coqtop was fqn is not a defined object

(defun typeAndShortName (fqn)
  "Return a tuple: (short name, type) of a fully qualified name."
  (with-current-buffer proof-response-buffer (read-only-mode -1))
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "About %s." fqn)))
         (short-name-pos (string-match " :" resp))
         (short-name (if short-name-pos
                         (substring resp 0 short-name-pos)
                       ""))
         (expands-to-pos (string-match "^Expands to:" resp))
         (type (when expands-to-pos
                 (nth-word-after resp expands-to-pos 0))))
    (list short-name type)))

(defun nth-word-after (string pos n)
  "Extract the second word in the string after the given position."
  (let* ((sub-str (substring string (+ pos (length "Expands to:"))))
         (words (split-string sub-str "[ \n\r]+" t)))
    (nth n words)))


(defun fullyQualifiedName (shortName)
  "Return a tuple: (short name, type) of a fully qualified name."
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "About %s." shortName)))
         (expands-to-pos (string-match "^Expands to:" resp))
         (type (when expands-to-pos
                 (nth-word-after resp expands-to-pos 1))))
    type))

(defun typeOf (fqn)
  "Return the type information of fqn from the 'Check %s' Coq query, without trailing newline."
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "Check %s." fqn)))
         (type-pos (string-match ": " resp)))
    (if type-pos
        ;; Remove trailing newlines from the substring
        (replace-regexp-in-string "\n\\'" "" (substring resp (+ type-pos 2)))
      nil)))  ; Return nil if ": " is not found

(defun appendShortNames (fqns)
  "Append short names to each line in fqns."
  (let* ((lines (split-string fqns "\n" t))
         (processed-lines (butlast lines))
         (result '()))
    (dolist (line processed-lines)
      (let ((short-name (br/shortName line)))
        (push (concat line ", " short-name) result)))
    (mapconcat 'identity (nreverse result) "\n")))

(defun export-current-coq-sentence-to-file (filename)
  "Export the current Coq sentence to the specified file."
  (interactive "FEnter the filename for export: ")
  ;; Save the current point
  (save-excursion
    ;; Move to the start of the sentence
    (proof-goto-command-start)
    ;; Mark the start position
    (let ((start (point)))
      ;; Move to the end of the sentence
      (proof-goto-command-end)
      ;; Extract the sentence text
      (let ((sentence-text (buffer-substring start (point))))
        ;; Write to the specified file
        (with-temp-file filename
          (insert sentence-text))))))

(defun proof-shell-wait-command (cmd)
  "Send CMD to the proof process and wait for the command to finish."
  (proof-shell-invisible-command cmd t))

(defun importLtac2WalkerIfNeeded ()
  "Import Ltac2 Walker if needed."
  (interactive)
  (save-excursion
    (proof-goto-command-end);; needed so that we do not insert in the middle of current sentence
    ;; (proof-goto-point);; TODO: work around this issue (https://github.com/ProofGeneral/PG/issues/728) by only doing this if the endpoint of the checked region is not the endpoint of the sentence in which the cursor was before doing proof-goto-command-end.
    (let* ((result (br/shortName "bedrock.prelude.tactics.ltac2.upstream.printConstantDepsNonRec"))
           (_ (message "importWalker: %s" result))
           )
      (when (string-empty-p result)
        (proof-shell-wait-command "\nRequire Import bedrock.prelude.tactics.ltac2.upstream.\n")))))

(defun closeSections (name)
  "Close sections for a given definition based on its fully qualified name."
  (let* ((qn (fullyQualifiedName name))  ; Assuming fullyQualifiedName is a defined function
         (qualifiers (split-string qn "\\." t))  ; Split FQN into qualifiers
         (lq (nth (- (length qualifiers) 2) qualifiers)))  ; Get the last qualifier
    ;; Base case: if lq is nil or empty, stop recursion
    (unless (or (not lq) (string= lq ""))
      ;; Attempt to end the section
      (let ((resp (proof-shell-invisible-cmd-get-result
                   (format "End %s." lq))))
        ;; Continue recursion if response does not contain "Error:"
        (unless (string-match-p "Error:" resp)
          (closeSections name))))))

(defun butlastline (str)
  "Delete the last two lines from a string containing multiple lines."
  (if (string-empty-p str)
      str
    (let* ((str-reversed (reverse str))
           (first-newline-pos (cl-position ?\n str-reversed))
           (second-newline-pos (and first-newline-pos
                                    (cl-position ?\n str-reversed :start (+ first-newline-pos 1)))))
      (if second-newline-pos
          (substring str 0 (- (length str) second-newline-pos 1))
        (if first-newline-pos
            ""
          str)))))

(defun splitGoalAndRefs (str)
  "Split str into two strings: before and after the line ', False.', excluding the last line in refs."
  (let* ((lines (split-string str "\n" t))
         (split-index (cl-position ", False." lines :test 'string=)))
    (if split-index
        (let ((goal (mapconcat 'identity (cl-subseq lines 0 (1+ split-index)) "\n"))
              ;; Exclude the last line from the refs part
              (refs (mapconcat 'identity (cl-subseq lines (1+ split-index) (max 0 (- (length lines) 1))) "\n")))
          (list goal refs))
      (list str ""))))  ; Return the whole string as the first part if ', False.' is not found


(defun br/addTypes (vars)
  "Process each line in vars (except the last) to get variable names and their types.
   Returns a list of tuples (variable name, variable type)."
  (let* ((lines (split-string vars "\n" t))  ; Split into lines and ignore empty lines
         (processed-lines (butlast lines))  ; Ignore the last line
         (result '()))
    (dolist (var processed-lines)
      (let ((type (typeOf var)))
        (push (list var type) result)))  ; Add tuple (var, type) to result
    (nreverse result)))  ; Reverse the result list for correct order


(defun br/coq-export ()
  "export definition at cursor for moving to another file using coq-import. TODO: check that no goal is open. otherwise, About treats section variables as hypotheses of the goal and confuses the computation of section variables"
  (interactive)
  (with-current-buffer proof-response-buffer (read-only-mode -1))
  (export-current-coq-sentence-to-file "/builds/bedrocksystems/bhv/upstream_coq_98324880_srcdefn")
  (importLtac2WalkerIfNeeded)
  (let* ((symbol-at-point (company-coq-symbol-at-point))
         (varsRefss (proof-shell-invisible-cmd-get-result
                     (format "Ltac2 Eval (bedrock.prelude.tactics.ltac2.upstream.printVarDepsNonRec reference:(%s))." symbol-at-point)))
         (varsRefs (splitGoalAndRefs varsRefss))
         (vars (car varsRefs))
         (refs (cadr varsRefs))
         (_ (message "combined: %s, vars: %s, refs: %s" varsRefss vars refs))
         (_ (closeSections symbol-at-point))
         (_ (importLtac2WalkerIfNeeded));; this was done earlier but then we closed sections
         (constants (proof-shell-invisible-cmd-get-result
                     (format "Ltac2 Eval (bedrock.prelude.tactics.ltac2.upstream.printConstantDepsNonRec reference:(%s))." symbol-at-point)))
         (comb (appendShortNames (concat refs "\n" constants)))
         )
    (progn
      (with-temp-file "/builds/bedrocksystems/bhv/upstream_coq_98324880_constants"
        (insert comb))
      (with-temp-file "/builds/bedrocksystems/bhv/upstream_coq_98324880_sectionvars"
        ;;	(insert (substVarsInTypes vars)))
        (insert vars))
      (rewind-one-step)
      (br/compile) ;; if the to-be-exported defn uses constants from current file added/modifled after last compilation, the importer may run into an error when it loads a stale .vo file. before importing, the user must wait until this compilation finishes. this tool can also be used for downstreaming despite the name. we can add a flag or a variant to enforce upstreaming: that would abort at export time if the definition refers to something in the current file
      )
    ))

(defun rewind-one-step ()
  (message "queue-or-locked pos was %s" (proof-queue-or-locked-end))
  (if (= (proof-queue-or-locked-end) 0);; once, this value was 1 at the beginning. this is fragile any way. a more reliable way to do this is to remember the current position and then do proof-undo-last-successful-command and then check whether the locked/queued position changed, possibly after (proof-shell-wait). if it didnt, do proof-shell-exit
      (proof-shell-exit);; this didnt happen once
    (proof-undo-last-successful-command)
    ))
(defun declare-secvars-and-wrapup (svars srcDefn)
  "svars is the goal printed by Ltac2 printVarDepsNonRec: all the section vars mentioned in the upstreame defn are existential quantifications in the goal, ending with False. now we try to instantiate those vars using the stuff in the current text"
  (insertIntoVfileAndCheck "Section AutoImport90832904.\n")
  (proof-shell-wait-command (concat "Require Import bedrock.prelude.tactics.ltac2.upstream. Goal " svars))
  (proof-shell-invisible-cmd-get-result "printNeededSectionVars.")
  (sleep-for 1);; it may take a while to update the proof response buffer
  (let ((svars (with-current-buffer proof-response-buffer
                 (buffer-string))))
    (progn
      (with-current-buffer proof-script-buffer
        (insert (concat "Context " svars ".\n" srcDefn)));; only do this if svars has a {
      (rewind-one-step) ;; to do the stuff we did on the side, e.g. the new sectionvar goal
      )
    ))



(defun coq-import ()
  "see br/coq-export. this is the consumer of what that produces"
  (interactive)
  (proof-goto-point-and-wait)
  (let ((constants (with-temp-buffer
                     (insert-file-contents "/builds/bedrocksystems/bhv/upstream_coq_98324880_constants")
                     (buffer-string)))
        (svars (with-temp-buffer
                 (insert-file-contents "/builds/bedrocksystems/bhv/upstream_coq_98324880_sectionvars")
                 (buffer-string)))
        (srcDefn (with-temp-buffer
                   (insert-file-contents "/builds/bedrocksystems/bhv/upstream_coq_98324880_srcdefn")
                   (buffer-string)))
        (result '()))
    (dolist (line (split-string constants "\n" t))
      (let* ((line-parts (split-string line ", "))
             (fqn (nth 0 line-parts))
             (shortName (nth 1 line-parts))
             (processed (reqImportsToMatchShortnameOfFqn fqn shortName))
             )
        (push processed result)))
    (declare-secvars-and-wrapup svars srcDefn)))

(defun proof-goto-point-and-wait-aux ()
  "Call proof-goto-point and then wait for 2 seconds."
  (proof-goto-point)
  (sleep-for 3)
  (proof-shell-wait))

(defun proof-goto-point-and-wait ()
  "Call proof-goto-point and then wait for 2 seconds, with error handling."
  (proof-activate-scripting) ;; proof-goto-point does not work in an empty file
  (if (not (= (proof-queue-or-locked-end) (point)))
      (condition-case err
          (proof-goto-point-and-wait-aux)
        (error (message "An error occurred: %s" (error-message-string err))))))


(defun relative_fqn (vfile_fqn short-namer fqn)
  "compute the name of this definition as expected to be in the .glob file in the line corresponding to the declartion side. fqn is the fully qualified name (fqn) of this definition. vfile_fqn is the fqn of the .v file corresponding to the .glob file. shortname is the leaf of fqn"
  (message "short-namer: %s" short-namer)
  (if (string= (concat vfile_fqn "." short-namer) fqn)
      short-namer
    (let ((relative_fqn_except_leaf (substring fqn (1+(length vfile_fqn)) (-(1+(length short-namer))))));; the middle part of fqn excluding the fully qualified name for the file and excluding the leaf
      (concat relative_fqn_except_leaf "." short-namer))))

(defun insertIntoVfileAndCheck (str)
  (with-current-buffer proof-script-buffer
    (insert str)
    (proof-shell-wait-command str)))

(defun br/locateModule (const)
  "Return a tuple with the first and second words of the first line starting with 'Module' from the 'Locate %s' Coq query."
  (with-current-buffer proof-response-buffer (read-only-mode -1))
  (let* ((resp (proof-shell-invisible-cmd-get-result
                (format "Locate %s." const)))
         (lines (split-string resp "\n" t)))
    ;; Find the first line that starts with "Module" using seq-find
    (let ((module-line (seq-find (lambda (line) (string-prefix-p "Module" line)) lines)))
      ;; Process the module line
      (when module-line
        (let ((words (split-string module-line "[ \n\r]+" t)))
          (list (nth 0 words) (nth 1 words)))))))


(defun addImport (fqnOfConstant nextPrefix vfile-fqn shortNameAtDst)
  "Conditionally import namespaces based on the result of br/locateConst."
  (let* ((locate-result (br/locateModule nextPrefix))
         (fqnOfNextPrefix (nth 1 locate-result)))
    (message "addImport called with fqnOfConstant: %s, nextPrefix: %s, vfile-fqn: %s. fqnOfNextPrefix: %s, shortNameAtDst: %s" fqnOfConstant nextPrefix vfile-fqn fqnOfNextPrefix shortNameAtDst)
    (if (<= (length fqnOfConstant) (+ (length vfile-fqn) (length shortNameAtDst)))
        (insertIntoVfileAndCheck (format "Import %s.\n" vfile-fqn))
      (if (not (string-prefix-p fqnOfNextPrefix fqnOfConstant))
          (insertIntoVfileAndCheck (format "Import %s. Import %s.\n" vfile-fqn nextPrefix))
        (insertIntoVfileAndCheck (format "Import %s.\n" nextPrefix))))
    ))

(defun addImports (fqn shortNameAtSrc vfile-fqn)
  "Assume that the .vo file containing the fully qualified name has been Require Imported. Now add Imports so that the short name of fqn is shortNameAtSrr (ideally) or a suffix of it."
  ;; Calculate br/shortName fqn for use in the debug message.
  (let ((shortNameAtDst (br/shortName fqn)))
    ;; Debug: Print all arguments along with br/shortName fqn result.
    (message "addImports called with fqn: %s, shortNameAtSrc: %s, br/shortName: %s"
             fqn shortNameAtSrc shortNameAtDst)
    (if (<= (length shortNameAtDst) (length shortNameAtSrc))
        ;; Else branch: if condition is false, split relName and call recursively.
        (message "then branch")
      (let* ((split-rel-name (split-string shortNameAtDst "\\." t))
             (prefix (car split-rel-name))
             (rest-rel-name (mapconcat 'identity (cdr split-rel-name) ".")))  ; Handle empty base case
        (progn
          (addImport fqn prefix vfile-fqn shortNameAtDst)
          (addImports fqn shortNameAtSrc vfile-fqn)
          )
        ))))


(defun reqImportsToMatchShortnameOfFqn (fqn shortNameAtSrc)
  "add missing Requires and/or Imports so that fqn (fully qualified name) is visible in the context and its shortname is shortName"
  (let* ((shortNameAtDst (br/shortName fqn))
         (loc (company-coq--loc-fully-qualified-name fqn))
         (vfile-fqn (cdr loc))
         (leaf-name (replace-regexp-in-string "\\`.*\\." "" fqn))
         (relname (relative_fqn vfile-fqn leaf-name fqn)))
    (if (string= shortNameAtDst "")
        (insertIntoVfileAndCheck (format "Require Import %s.\n" vfile-fqn)))
    (addImports fqn shortNameAtSrc vfile-fqn)
    ));;first check that About rest-rel-name returns fqn and not some other constant. in the latter case, do the Import above instead of Require Import, to change resolution priorities

(provide 'upstream)

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
(set-default 'fstar-executable "~/FStar/bin/fstar.exe")
(global-flycheck-mode)
(set-face-font 'default "Terminus-14")



;;set fstar includes, these should work for most tutorial examples, except those using hyperheap
(setq fstar-subp-prover-args '("--include" "/home/build/FStar/ucontrib/Platform/fst" "--include" "/home/build/FStar/ucontrib/CoreCrypto/fst"))


;;this is what the above corresponds to on the command line:
;fstar --include /home/FStar/FStar/ucontrib/Platform/fst --include /home/FStar/FStar/ucontrib/CoreCrypto/fst

;;set fstar includes, these work for the the Encrypt-then-MAC example:
;(setq fstar-subp-prover-args '("--include" "/home/FStar/FStar/ulib/hyperheap" "--include" "/home/FStar/FStar/ucontrib/Platform/fst" "--include" "/home/FStar/FStar/ucontrib/CoreCrypto/fst"))

;;this is what the above corresponds to on the command line:
;fstar --include /home/FStar/FStar/ulib/hyperheap --include /home/FStar/FStar/ucontrib/Platform/fst --include /home/FStar/FStar/ucontrib/CoreCrypto/fst

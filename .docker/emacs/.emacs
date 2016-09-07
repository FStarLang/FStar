(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)
(set-default 'fstar-executable "~/FStar/bin/fstar.exe")
(global-flycheck-mode)
(set-face-font 'default "Terminus-14")



;;set fstar includes, these should work for most tutorial examples, except those using hyperheap
(setq fstar-subp-prover-args '("--include" "~/FStar/ucontrib/Platform/fst" "--include" "~/FStar/ucontrib/CoreCrypto/fst"))


;;this is what the above corresponds to on the command line:
;fstar --include ~/FStar/ucontrib/Platform/fst --include ~/FStar/ucontrib/CoreCrypto/fst

;;set fstar includes, these work for the the Encrypt-then-MAC example:
;(setq fstar-subp-prover-args '("--include" "~/FStar/ulib/hyperheap" "--include" "~/FStar/ucontrib/Platform/fst" "--include" "~/FStar/ucontrib/CoreCrypto/fst"))

;;this is what the above corresponds to on the command line:
;fstar --include ~/FStar/ulib/hyperheap --include ~/FStar/ucontrib/Platform/fst --include ~/FStar/ucontrib/CoreCrypto/fst

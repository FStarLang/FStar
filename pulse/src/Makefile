# This Makefile is meant to regenerate the OCaml source snapshot of
# the Steel plugin and the header files for the Steel C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: extract-ocaml
extract-ocaml: extract-tactics extract-extraction

.PHONY: extract-tactics
extract-tactics:
	+$(MAKE) -C ocaml -f extract-tactics.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C extraction

.PHONY: verify
verify: extract-tactics
	+$(MAKE) -C .. verify

.PHONY: extract-c
extract-c: verify
	+$(MAKE) -C c extract

.PHONY: extract
extract: extract-ocaml extract-c

.PHONY: boot
boot: extract
	+$(MAKE) -C .. all

.PHONY: full-boot
full-boot:
	rm -rf ocaml/generated include/steel/Steel_SpinLock.h
	+$(MAKE) boot

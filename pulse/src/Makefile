# This Makefile is meant to regenerate the OCaml source snapshot of
# the Steel plugin and the header files for the Steel C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: extract-ocaml
extract-ocaml: extract-steel-plugin extract-extraction extract-pulse-plugin

.PHONY: extract-steel-plugin
extract-steel-plugin:
	+$(MAKE) -C ocaml/plugin -f extract-steel.Makefile

.PHONY: extract-pulse-plugin
extract-pulse-plugin: verify-steel
	+$(MAKE) -C ocaml/plugin -f extract-pulse.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C extraction

.PHONY: verify-steel
verify-steel: extract-steel-plugin
	+$(MAKE) -C .. verify-steel

.PHONY: extract-c
extract-c: verify-steel
	+$(MAKE) -C c extract

.PHONY: extract
extract: extract-ocaml extract-c

.PHONY: boot
boot: extract
	+$(MAKE) -C .. all

.PHONY: full-boot
full-boot:
	rm -rf ocaml/*/generated ../include/steel/Steel_SpinLock.h
	+$(MAKE) boot

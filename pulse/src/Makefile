# This Makefile is meant to regenerate the OCaml source snapshot of
# the Steel plugin and the header files for the Steel C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: extract-ocaml
extract-ocaml: extract-steel-plugin extract-extraction extract-syntax-extension extract-pulse-plugin

.PHONY: extract-steel-plugin
extract-steel-plugin:
	+$(MAKE) -C ocaml/plugin -f extract-steel.Makefile

.PHONY: extract-pulse-plugin
extract-pulse-plugin: rebuild-and-verify-steel
	+$(MAKE) -C ocaml/plugin -f extract-pulse.Makefile

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C extraction

.PHONY: extract-syntax-extension
extract-syntax-extension:
	+$(MAKE) -C syntax_extension

# NOTE: while verification of Steel does not in itself need extracting
# the krml extraction rules, the following `rebuild-and-verify-steel`
# rule also recompiles the Steel plugin, so it is not possible to
# extract the extraction rules in parallel with this rule. Adding a
# dependency on `extract-extraction` is one way to solve this
# problem. This solution also solves 2 more problems:
#
# * the Steel plugin is recompiled 2 times instead of 3: once instead
#   of twice for Steel + extraction with this rule, in addition to the
#   one time for Pulse with the `boot` rule.
#
# * extracting LibSteel may need the krml extraction rules compiled
#   into the Steel plugin

.PHONY: rebuild-and-verify-steel
rebuild-and-verify-steel: extract-steel-plugin extract-extraction
	+$(MAKE) -C .. verify-steel

.PHONY: extract-c
extract-c: rebuild-and-verify-steel
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

.PHONY: proofs
proofs:
	+$(MAKE) -C $@

.PHONY: share
share:
	+$(MAKE) -C ../share/steel

.PHONY: test
test: proofs share

.PHONY: check-for-changes
check-for-changes:
	# Test if no new files appeared
	git status ..
	test "" = "$$(git ls-files --others --exclude-standard -- ..)"
	# Test if nothing has changed
	if ! git diff-index --exit-code HEAD .. ; then git diff .. ; false ; fi

.PHONY: ci
ci:
	+$(MAKE) full-boot
	+$(MAKE) check-for-changes
	+$(MAKE) test

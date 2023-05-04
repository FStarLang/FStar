# This Makefile is meant to regenerate the OCaml source snapshot of
# the Steel plugin and the header files for the Steel C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

# Step 1: we build the initial plugin and the Steel and Pulse library
# as they are now, and then we blast all generated files

.PHONY: initial-build
initial-build:
	+$(MAKE) -C .. all
	rm -rf ocaml/*/generated ../include/steel/Steel_SpinLock.h

.PHONY: extract-ocaml
extract-ocaml: extract-steel-plugin extract-extraction extract-pulse-plugin

.PHONY: extract-steel-plugin
extract-steel-plugin: initial-build
	+$(MAKE) -C ocaml/plugin -f extract-steel.Makefile

.PHONY: extract-pulse-plugin
extract-pulse-plugin: initial-build
	+$(MAKE) -C ocaml/plugin -f extract-pulse.Makefile

.PHONY: extract-extraction
extract-extraction: initial-build
	+$(MAKE) -C extraction

.PHONY: extract-c
extract-c: initial-build
	+$(MAKE) -C c extract

.PHONY: extract
extract: extract-ocaml extract-c

.PHONY: boot
boot: extract
	+$(MAKE) -C .. all

.PHONY: full-boot
full-boot: boot

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

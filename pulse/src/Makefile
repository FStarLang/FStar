# This Makefile is meant to regenerate the OCaml source snapshot of
# the Pulse plugin and the header files for the Pulse C library. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: build
build:
	+$(MAKE) -C .. all

# Extraction rules assume that a snapshot has already been compiled.

.PHONY: extract-ocaml
extract-ocaml: extract-extraction extract-syntax-extension extract-pulse-plugin

.PHONY: extract-pulse-plugin
extract-pulse-plugin:
	+$(MAKE) -C checker extract

.PHONY: extract-extraction
extract-extraction:
	+$(MAKE) -C extraction


.PHONY: extract-syntax-extension
extract-syntax-extension:
	+$(MAKE) -C syntax_extension

.PHONY: extract
extract: extract-ocaml

.PHONY: boot
boot:
	+$(MAKE) extract
	+$(MAKE) build

.PHONY: clean-snapshot
clean-snapshot:
	rm -rf ocaml/*/generated
	rm -f ocaml/plugin/FStar_Parser_Parse.mly

.PHONY: full-boot
full-boot:
	+$(MAKE) clean-snapshot
	+$(MAKE) boot

.PHONY: test
test:
	+$(MAKE) -C .. test

.PHONY: check-for-changes
check-for-changes:
	# Test if no new files appeared
	git status ..
	test "" = "$$(git ls-files --others --exclude-standard -- ..)"
	# Test if nothing has changed
	if ! git diff-index --exit-code HEAD .. ; then git diff .. ; false ; fi

pulse2rust:
	+$(MAKE) -C .. pulse2rust

.PHONY: ci
ci:
	+$(MAKE) full-boot
	+$(MAKE) check-for-changes
	+$(MAKE) test
	+$(MAKE) pulse2rust

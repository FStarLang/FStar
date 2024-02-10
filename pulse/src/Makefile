# This Makefile is meant to regenerate the OCaml source snapshot of
# the Pulse plugin. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot
.PHONY: all

.PHONY: build-lib-core build-lib-main

build-lib-core:
	+$(MAKE) -C ../lib/pulse/core

build-lib-main:
	+$(MAKE) -C ../lib/pulse pulse

.PHONY: build
build:
	+$(MAKE) -C .. all

# this file cannot be copied to `generated` because of a bug with
# Dune's `menhir` stanza
# (cf. https://github.com/ocaml/dune/issues/4381 )
fstar_parser_parse=ocaml/plugin/FStar_Parser_Parse.mly

ifeq (,$(FSTAR_HOME))
$(fstar_parser_parse):
	echo "Cannot find the F* parser. Please point FSTAR_HOME to a source repository clone of F*"
	false
else
$(fstar_parser_parse): $(FSTAR_HOME)/ocaml/fstar-lib/FStar_Parser_Parse.mly
	cp $^ $@
endif

.PHONY: extract-ocaml
extract-ocaml: extract-extraction extract-syntax-extension extract-checker $(fstar_parser_parse)

.PHONY: extract-checker
extract-checker: build-lib-core build-lib-main
	+$(MAKE) -C checker

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

.PHONY: boot-checker
boot-checker:
	+$(MAKE) extract-checker
	+$(MAKE) build

.PHONY: clean-snapshot
clean-snapshot:
	rm -rf ocaml/*/generated
	rm -f $(fstar_parser_parse)

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

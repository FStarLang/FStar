# This Makefile is meant to regenerate the OCaml source snapshot of
# the Pulse plugin. The
# end-user shouldn't need to do that explicitly, and the
# main ../Makefile should be enough for them.

all: boot

ifeq (,$(PULSE_HOME))
  PULSE_HOME := ..
endif

# dune install --prefix needs the Windows absolute path
PULSE_HOME := $(realpath $(PULSE_HOME))
ifeq ($(OS),Windows_NT)
  PULSE_HOME := $(shell cygpath -m $(PULSE_HOME))
endif

include $(PULSE_HOME)/share/pulse/Makefile.locate-fstar

.PHONY: all build-lib-core build-lib-main

build-lib-core:
	+$(MAKE) -C $(PULSE_HOME)/lib/pulse/core

build-lib-main:
	+$(MAKE) -C $(PULSE_HOME)/lib/pulse main

.PHONY: build
build:
	+$(MAKE) -C .. all

.PHONY: build-ocaml
build-ocaml:
	cd ocaml && dune build && dune install --prefix=$(PULSE_HOME)

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
	+$(MAKE) -C $(PULSE_HOME)/share/pulse CACHE_DIRECTORY=

.PHONY: check-for-changes
check-for-changes:
	# Test if no new files appeared
	git status ..
	test "" = "$$(git ls-files --others --exclude-standard -- ..)"
	# Test if nothing has changed
	if ! git diff-index --exit-code HEAD .. ; then git diff .. ; false ; fi

pulse2rust:
	+$(MAKE) -C $(PULSE_HOME) pulse2rust

verify:
	+$(MAKE) -f verify.Makefile

.PHONY: ci
ci:
	+$(MAKE) build-ocaml
	+$(MAKE) clean-snapshot
	+$(MAKE) verify
	+$(MAKE) extract
	+$(MAKE) check-for-changes
	+$(MAKE) build-ocaml
	+$(MAKE) test
	+$(MAKE) pulse2rust

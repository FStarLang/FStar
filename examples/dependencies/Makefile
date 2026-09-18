# This makefile is meant as an example for new projects, and intentionally
# does not import any other Makefile in this repo to make this directory standalone.

FSTAR_EXE ?= $(shell which fstar.exe)
# ^ Take F* from the path, but allow to override it.

V != $(FSTAR_EXE) --version

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)
# NB: This is overriden (to empty) when testing the binary package
# so we skip the build test. (Variables given in the command line, not
# the environment, override those defined in the script.)

ifeq ($(V),)
$(error "fstar.exe --version failed... place a valid F* in your PATH or set FSTAR_EXE")
endif

OUT_DIR   = out
CACHE_DIR = cache
ROOTS     = Test.fst

FSTAR_FLAGS = $(OTHERFLAGS) --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) \
  --cache_checked_modules --already_cached 'Prims FStar'

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

.PHONY: all test clean run

all:
	+$(MAKE) test

# 1. Verify
# - generate the F* dependency graph of $(ROOTS) with `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
.depend:
	$(FSTAR) --dep full $(ROOTS) -o $@

include .depend

$(CACHE_DIR)/%.checked:
	$(FSTAR) $< && \
	touch $@

# 2. Extract, once, for the whole program.
#
# Custard compiles a program rather than a module: one run over everything
# reachable from the entry point, and one OCaml file out.  So there is no
# per-module extraction rule and no separate compilation step here -- the
# prerequisite is every .checked file, because the program is allowed to
# reach any of them.
#
# This program has no [main]: it is a module whose top-level effect prints.
# --custard_entry_module is the request for that -- every top-level definition
# of the named module is a root and its top-level effects run, which is what
# --extract_module meant.  A program with a [main] would say
# --custard_main Test.main instead.
$(OUT_DIR)/test.ml: $(ALL_CHECKED_FILES) | $(OUT_DIR)
	$(FSTAR) --codegen Custard --custard_entry_module Test $(ROOTS) -o $@

$(OUT_DIR):
	mkdir -p $(OUT_DIR)

$(OUT_DIR)/test.exe: $(OUT_DIR)/test.ml
	$(FSTAR_EXE) --ocamlopt $< -o $@

# If we don't have OCaml, just extract.
ifneq (,$(HAS_OCAML))
test: run
else
test: $(OUT_DIR)/test.ml
endif

run: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)

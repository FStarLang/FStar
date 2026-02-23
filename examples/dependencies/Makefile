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

FSTAR_FLAGS = $(OTHERFLAGS) --cmi --odir $(OUT_DIR) --cache_dir $(CACHE_DIR) \
  --cache_checked_modules --already_cached 'Prims FStar'

FSTAR = $(FSTAR_EXE) $(FSTAR_FLAGS)

.PHONY: all test clean run

all:
	rm -f .depend && $(MAKE) .depend # Always re-generate dependencies
	+$(MAKE) test

# 1. Extract .ml files
# - generate the F* dependency graph of $(ROOTS) with `fstar --dep full`
# - verify every F* file in parallel to generate .checked files
# - extract each .checked file into a .ml file in parallel
.depend:
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' -o $@

include .depend

$(CACHE_DIR)/%.checked:
	$(FSTAR) $< && \
	touch $@

# 2. Compile all .ml files to .cmx and link them to get an executable
$(OUT_DIR)/%.ml:
	$(FSTAR) --codegen OCaml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<)) && \
	touch $@

%.cmx:
	$(FSTAR_EXE) --ocamlopt -I $(OUT_DIR) -c $< -o $@

$(OUT_DIR)/test.exe: $(subst .ml,.cmx,$(ALL_ML_FILES)) | $(OUT_DIR)
	$(FSTAR_EXE) --ocamlopt -I $(OUT_DIR) -o $(OUT_DIR)/test.exe $(subst .ml,.cmx,$(ALL_ML_FILES))

# If we don't have OCaml, just extract the ML files.
ifneq (,$(HAS_OCAML))
test: run
else
test: $(ALL_ML_FILES)
endif

run: $(OUT_DIR)/test.exe
	$(OUT_DIR)/test.exe

clean:
	rm -rf $(OUT_DIR) $(CACHE_DIR)

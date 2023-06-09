
# Assuming share/steel/tests/krml
STEEL_HOME ?= ../../../..

RECENT_GCC	= $(shell [ "$$(gcc -dumpversion | cut -c -1)" -ge 5 ] && echo yes)

ifdef FSTAR_HOME
  # Assume there is a F* source tree
  FSTAR_EXE=$(FSTAR_HOME)/bin/fstar.exe
else
  FSTAR_EXE=$(shell which fstar.exe)
  ifeq ($(FSTAR_EXE),)
    $(error "fstar.exe not found, please install F*")
  endif
  # Assume F* in the PATH, in some ..../bin directory
  FSTAR_HOME=$(dir FSTAR_EXE)/..
endif

TEST_OPTS	= -warn-error @4 -verbose -skip-makefiles
KRML_BIN	= $(KRML_HOME)/krml
KRML		= $(KRML_BIN) $(KOPTS) $(TEST_OPTS)

# TODO: disambiguate between broken tests that arguably should work (maybe
# HigherOrder6?) and helper files that are required for multiple-module tests
# For Layered.test: see F* bug 2641 and associated PR
BROKEN		=

# Lowlevel is not really broken, but its test shouldn't be run since it's a
# special file and doesn't have a main.

FILES		= \
  $(patsubst %.fst,%.test,$(filter-out $(BROKEN),$(wildcard *.fst)))

ifneq ($(RECENT_GCC),"yes")
  FILES 	:= $(filter-out Debug.test,$(FILES))
endif

WASM_FILES	= \
   Wasm11.wasm-test

NEGATIVE	= false

WEB_DIR		?= web
CACHE_DIR	= .cache
OUTPUT_DIR	= .output
HINTS_DIR	= .hints

FSTAR_OPTIONS = --cache_checked_modules \
  --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
  --include $(KRML_HOME)/krmllib/compat --include $(KRML_HOME)/krmllib/obj \
  --include $(KRML_HOME)/krmllib --include $(KRML_HOME)/runtime \
  --include $(STEEL_HOME)/lib/steel --load_cmxs steel \
  --use_hints --record_hints \
  --already_cached 'Prims,FStar,C,TestLib,Spec.Loops,-C.Compat,-C.Nullity,LowStar,WasmSupport,Steel' \
  --trivial_pre_for_unannotated_effectful_fns false \
  --cmi --warn_error -274 \
  $(OTHERFLAGS)

FSTAR		= $(FSTAR_EXE) $(FSTAR_OPTIONS)

all: world

.PHONY: world base

# This just needs F* + KaRaMeL
base: $(FILES) $(CUSTOM)

# Needs node
wasm: $(WASM_FILES)

# All of the above
everything: base wasm

_check_node := $(shell node --version)
ifeq (0,$(.SHELLSTATUS))
world: everything
else
world: base
endif

.PRECIOUS: %.krml

# Use F*'s dependency mechanism and fill out the missing rules.

ifndef MAKE_RESTARTS
ifndef NODEPEND
.depend: .FORCE
	$(FSTAR) --dep full $(subst .wasm-test,.fst,$(WASM_FILES)) $(subst .test,.fst,$(FILES)) \
	  $(BROKEN) $(KRML_HOME)/runtime/WasmSupport.fst --extract 'krml:*,-Prims' > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend

$(HINTS_DIR):
	mkdir -p $@

$(CACHE_DIR)/%.checked: | .depend $(HINTS_DIR)
	$(FSTAR) --hint_file $(HINTS_DIR)/$*.hints $< && \
	touch $@

$(OUTPUT_DIR)/%.krml: | .depend
	$(FSTAR) --codegen krml \
	  --extract_module $(basename $(notdir $(subst .checked,,$<))) \
	  $(notdir $(subst .checked,,$<))

.PRECIOUS: $(OUTPUT_DIR)/%.exe
$(OUTPUT_DIR)/%.exe: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) $(EXTRA) -tmpdir $(subst .exe,.out,$@) -no-prefix $(notdir $*) \
	  -I $(STEEL_HOME)/include/steel \
	  -add-include '"steel_base.h"' \
	  $(STEEL_HOME)/lib/steel/libsteel.a \
	  -o $@ $(filter %.krml,$^) -bundle $(subst _,.,$*)=WindowsHack,\*

.SECONDEXPANSION:
%.test: $(OUTPUT_DIR)/$$(notdir $$(subst .,_,$$*)).exe
	@(if $(NEGATIVE); then ! $^; else $^; fi) && echo "\033[01;32m✔\033[00m [TEST,$*]" || (echo "\033[01;31m✘\033[00m [TEST,$*]" && false)

# Various flags to be passed to some targets...
$(OUTPUT_DIR)/SteelArrayArith.exe: EXTRA=-static-header Steel.ArrayArith -no-prefix Steel.ArrayArith
$(OUTPUT_DIR)/SteelLock.exe: EXTRA=-bundle Steel.* -add-include 'Steel:"steel_types.h"'
$(OUTPUT_DIR)/SizeT.exe: EXTRA=-ccopt -std=c2x

# A pseudo-target for WASM compilation that does not match any specific file.
# All WASM targets get the -wasm flag; some specific targets may override
# NEGATIVE for negative tests.
.PRECIOUS: $(OUTPUT_DIR)/%.wasm
$(OUTPUT_DIR)/%.wasm: $(ALL_KRML_FILES) $(KRML_BIN)
	$(KRML) -minimal -bundle WasmSupport= -bundle 'FStar.*' -bundle Prims \
	  -bundle C -bundle C.Endianness -bundle C.Nullity -bundle C.String \
	  -bundle TestLib \
	  -bundle $(subst _,.,$*)=WindowsHack,\* \
	  -wasm $(EXTRA) -tmpdir $@ $(JSFILES) -no-prefix $* $(filter %.krml,$^)
	[ x$(JSFILES) != x ] && cp $(JSFILES) $@ || true

%.wasm-test: $(OUTPUT_DIR)/%.wasm
	cd $^ && \
	  if ! $(NEGATIVE); then node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); \
	  else ! node main.js && echo "\033[01;32m✔\033[00m [WASM-TEST,$*]" || (echo "\033[01;31m✘\033[00m [WASM-TEST,$*]" && false); fi

clean:
	rm -rf $(WEB_DIR) .output

distclean: clean
	rm -rf .cache

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

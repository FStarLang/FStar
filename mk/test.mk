# Include this makefile for unit tests. It mostly has all you need.
# This is NOT meant for external consumption. Do not point to this.

ifeq ($(FSTAR_ROOT),)
  $(error FSTAR_ROOT is not set. Please set it to the root of your F* repository)
endif
include $(FSTAR_ROOT)/mk/common.mk
.DEFAULT_GOAL := all

# Set a default FSTAR_EXE for most clients.
FSTAR_EXE ?= $(FSTAR_ROOT)/bin/fstar.exe

OCAMLOPT := $(FSTAR_EXE) --ocamlenv ocamlfind opt

HINTS_ENABLED?=--use_hints

# This warning is really useless.
OTHERFLAGS += --warn_error -321
OTHERFLAGS += --ext context_pruning

# Set ADMIT=1 to admit queries
ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

OUTPUT_DIR ?= _output
CACHE_DIR ?= _cache

FSTAR = $(FSTAR_EXE) $(SIL) 				\
	--cache_checked_modules				\
	--odir $(OUTPUT_DIR)				\
	--cache_dir $(CACHE_DIR)			\
	--already_cached Prims,FStar			\
	 $(OTHERFLAGS) $(MAYBE_ADMIT) $(HINTS_ENABLED)

ifeq ($(NODEPEND),)
FSTAR_FILES ?= $(wildcard *.fst) $(wildcard *.fsti)
$(call need, FSTAR_FILES, "List of F* files to verify. It defaults to all fst/fsti in the directory (none were found)")

.depend: $(FSTAR_FILES)
	$(call msg, "DEPEND", $(CURDIR))
	$(FSTAR) --dep full $(FSTAR_FILES) --output_deps_to $@
depend: .depend
include .depend
endif

%.fst.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) $<
	touch -c $@

%.fsti.checked:
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(FSTAR) $<
	touch -c $@

%.fst.output: %.fst
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format human -f --print_expected_failures $< >$@ 2>&1

%.fsti.output: %.fsti
	$(call msg, "OUTPUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format human -f --print_expected_failures $< >$@ 2>&1

%.fst.json_output: %.fst
	$(call msg, "JSONOUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format json -f --print_expected_failures $< >$@ 2>&1

%.fsti.json_output: %.fsti
	$(call msg, "JSONOUT", $(basename $(notdir $@)))
	$(FSTAR) --message_format json -f --print_expected_failures $< >$@ 2>&1

$(OUTPUT_DIR)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(FSTAR) $(subst .checked,,$(notdir $<)) --codegen OCaml --extract_module $(subst .fst.checked,,$(notdir $<))

verify-all: $(ALL_CHECKED_FILES)

common_clean:
	rm -rf $(OUTPUT_DIR) $(CACHE_DIR) .depend

# Client makefiles can extend the clean, inheriting the common step
clean: common_clean

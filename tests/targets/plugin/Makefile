# A plugin whose implementation is target-specific: Tac.fsti is common,
# Tac-ocaml.fst implements it.  --codegen Plugin must name the extracted unit
# and entry module Tac, not Tac-ocaml, and the plugin must then serve the
# common file UseTac.fst.

FSTAR_ROOT ?= ../../..
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))

CACHE_DIR := _cache
OUTPUT_DIR := _output

FSTAR = $(FSTAR_EXE) --cache_dir $(CACHE_DIR) --odir $(OUTPUT_DIR) \
	--already_cached Prims,FStar $(OTHERFLAGS)

all: verify

verify:
	mkdir -p $(CACHE_DIR) $(OUTPUT_DIR)
	$(FSTAR) --cache_checked_modules Tac.fsti
	$(FSTAR) --cache_checked_modules Tac-ocaml.fst
	$(FSTAR) --codegen Plugin Tac-ocaml.fst
	$(FSTAR_EXE) --ocamlopt_plugin -o $(OUTPUT_DIR)/Tac.cmxs $(OUTPUT_DIR)/Tac.ml
	$(FSTAR) --load_cmxs Tac UseTac.fst

accept depend:

clean:
	rm -rf $(CACHE_DIR) $(OUTPUT_DIR)

.PHONY: all verify accept depend clean

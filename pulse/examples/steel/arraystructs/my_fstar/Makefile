all: world

MY_OBJ=$(CURDIR)/lib/steel_c/ExtractSteelC.cmxs

world: $(MY_OBJ)

FSTAR_HOME ?= $(realpath $(dir $(shell which fstar.exe))/..)
FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe

include $(FSTAR_HOME)/.common.mk
include $(FSTAR_HOME)/ulib/gmake/z3.mk    # This pins $(Z3) ...
include $(FSTAR_HOME)/ulib/gmake/fstar.mk # and $(FSTAR) for all sub-make calls
include $(FSTAR_HOME)/src/Makefile.boot.common

OUTPUT_DIRECTORY = $(CURDIR)
FSTAR_C=$(RUNLIM) $(FSTAR_EXE) $(SIL) $(FSTAR_BOOT_OPTIONS)

EXTRACT_FILES=ExtractSteelC.ml
extract: $(EXTRACT_FILES)

# And then, in a separate invocation, from each .checked.lax we
# extract an .ml file
$(EXTRACT_FILES): %.ml: %.fst
	$(call msg, "EXTRACT", $(notdir $@))
	$(Q)$(BENCHMARK_PRE) $(FSTAR_C) $< \
		   --odir "$(OUTPUT_DIRECTORY)" \
                   --codegen OCaml \
                   --extract_module $(basename $(notdir $<))

$(MY_OBJ): ExtractSteelC.fst ExtractSteelC.fsti Makefile
	OCAMLPATH=$(FSTAR_HOME)/lib dune build && dune install --prefix=$(CURDIR)

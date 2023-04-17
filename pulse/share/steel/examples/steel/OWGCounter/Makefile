all: counter

# assuming share/steel/examples/steel/OWGCounter
STEEL_HOME ?= $(realpath ../../../../..)
FSTAR_FILES=../OWGCounter.fst
OUTPUT_DIRECTORY=generated
FSTAR_OPTIONS += --include .. --already_cached '*,' --extract 'OWGCounter' --odir $(OUTPUT_DIRECTORY)

include $(STEEL_HOME)/share/steel/Makefile.include

.PHONY: counter

CODEGEN = OCaml
OUTPUT_EXE=_build/default/OWGCounterTest.exe

$(OUTPUT_EXE): $(OUTPUT_DIRECTORY)/OWGCounter.ml OWGCounterTest.ml
	dune build

counter: $(OUTPUT_EXE)
	$<

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(OTHERFLAGS) --include $(STEEL_HOME)/lib/steel --include .. --cache_checked_modules --odir $(OUTPUT_DIRECTORY) --warn_error @241 --already_cached '*'

$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))

clean::
	rm -rf $(OUTPUT_DIRECTORY) _build

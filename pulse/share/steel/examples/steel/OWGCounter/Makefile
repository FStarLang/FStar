all: counter

# assuming share/steel/examples/steel/OWGCounter
STEEL_HOME ?= $(realpath ../../../../..)

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(STEEL_HOME)/lib);$(OCAMLPATH)
else
  OCAMLPATH := $(STEEL_HOME)/lib:$(OCAMLPATH)
endif

ifneq (,$(FSTAR_HOME))
  FSTAR=$(FSTAR_HOME)/bin/fstar.exe
  ifeq ($(OS),Windows_NT)
    OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
  else
    OCAMLPATH := $(FSTAR_HOME)/lib:$(OCAMLPATH)
  endif
else
  FSTAR=fstar.exe
endif

export OCAMLPATH

.PHONY: all counter

CODEGEN = OCaml
OUTPUT_DIRECTORY=generated
OUTPUT_EXE=_build/default/OWGCounterTest.exe

$(OUTPUT_EXE): $(OUTPUT_DIRECTORY)/OWGCounter.ml OWGCounterTest.ml
	dune build

counter: $(OUTPUT_EXE)
	$<

MY_FSTAR=$(RUNLIM) $(FSTAR) $(SIL) $(OTHERFLAGS) --include $(STEEL_HOME)/lib/steel --include .. --cache_checked_modules --odir $(OUTPUT_DIRECTORY) --warn_error @241 --already_cached '*'
EXTRACT_MODULES=--extract 'OWGCounter'
FSTAR_FILES=../OWGCounter.fst

$(OUTPUT_DIRECTORY)/%.ml:
	$(call msg, "EXTRACT", $(basename $(notdir $@)))
	$(Q)$(MY_FSTAR) $(subst .checked,,$(notdir $<)) --codegen $(CODEGEN) --extract_module $(basename $(notdir $(subst .checked,,$<)))

$(OUTPUT_DIRECTORY)/.depend: $(FSTAR_FILES)
	mkdir -p $(OUTPUT_DIRECTORY)
	$(call msg, "DEPEND")
	$(Q)true $(shell mkdir -p $(OUTPUT_DIRECTORY)) $(shell rm -f $@.rsp) $(foreach f,$(FSTAR_FILES),$(shell echo $(f) >> $@.rsp))
	$(Q)$(MY_FSTAR) --dep full $(EXTRACT_MODULES) $(addprefix --include , $(INCLUDE_PATHS)) @$@.rsp > $@.tmp
	mv $@.tmp $@

include $(OUTPUT_DIRECTORY)/.depend

.PHONY: clean
	rm -rf $(OUTPUT_DIRECTORY) _build

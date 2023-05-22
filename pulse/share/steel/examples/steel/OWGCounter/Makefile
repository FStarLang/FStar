all: counter

# assuming share/steel/examples/steel/OWGCounter
STEEL_HOME ?= ../../../../..
FSTAR_FILES=../OWGCounter.fst
OUTPUT_DIRECTORY=generated
FSTAR_OPTIONS += --include .. --already_cached '*,' --odir $(OUTPUT_DIRECTORY)
FSTAR_DEP_OPTIONS += --extract 'OWGCounter'
FSTAR_ML_CODEGEN = OCaml

include $(STEEL_HOME)/share/steel/Makefile.include

.PHONY: counter

OUTPUT_EXE=_build/default/OWGCounterTest.exe

$(OUTPUT_EXE): $(OUTPUT_DIRECTORY)/OWGCounter.ml OWGCounterTest.ml
	dune build

counter: $(OUTPUT_EXE)
	$<

clean::
	rm -rf $(OUTPUT_DIRECTORY) _build

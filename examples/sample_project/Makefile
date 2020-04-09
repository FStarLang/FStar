################################################################################
# Customize these variables for your project
################################################################################
# The root files of your project, from which to begin scanning dependences
FSTAR_FILES=$(wildcard *.fst)

# The executable file you want to produce
PROGRAM=myprogram

# A driver in ML to call into your program
TOP_LEVEL_FILE=ml/main.ml

# A place to put all the emitted .ml files
OUTPUT_DIRECTORY=_output

################################################################################
FSTAR=fstar.exe --cache_checked_modules --odir $(OUTPUT_DIRECTORY) --use_hints $(OTHERFLAGS)
ML_FILES=$(addprefix $(OUTPUT_DIRECTORY)/,$(addsuffix .ml,$(subst .,_, $(subst .fst,,$(FSTAR_FILES)))))
OCAML_EXE=$(PROGRAM).ocaml.exe
KREMLIN_EXE=$(PROGRAM).exe

all: verify-all

# a.fst.checked is the binary, checked version of a.fst
%.checked: %
	$(FSTAR) $*
	touch $@

# The _tags file is a directive to ocamlbuild
# The extracted ML files are precious, because you may want to examine them,
#     e.g., to see how type signatures were transformed from F*
.PRECIOUS: _tags $(ML_FILES) $(addsuffix .checked,$(FSTAR_FILES)) $(OUTPUT_DIRECTORY)/out.krml

_tags:
	echo "<ml>: traverse" > $@
	echo "<$(OUTPUT_DIRECTORY)>: traverse" >> $@
	echo "<$(OUTPUT_DIRECTORY)/c>: -traverse" >> $@

# To extract an A.ml ML file from an A.fst, we just reload its A.fst.checked file
# and then with the --codegen OCaml option, emit an A.ml
# Note, by default F* will extract all files in the dependency graph
# With the --extract_module, we instruct it to just extract A.ml
$(OUTPUT_DIRECTORY)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$<)

$(OCAML_EXE): _tags $(ML_FILES) $(TOP_LEVEL_FILE)
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -I $(OUTPUT_DIRECTORY) -use-ocamlfind -pkg fstarlib $(subst .ml,.native,$(TOP_LEVEL_FILE))
	mv _build/$(subst .ml,.native,$(TOP_LEVEL_FILE)) $@

test.ocaml: $(OCAML_EXE)
	./$< hello

$(OUTPUT_DIRECTORY)/c/out.krml: $(addsuffix .checked,$(FSTAR_FILES))
	krml -fsopts --cache_checked_modules -tmpdir $(OUTPUT_DIRECTORY)/c -skip-translation $(FSTAR_FILES)

$(KREMLIN_EXE): $(OUTPUT_DIRECTORY)/c/out.krml
	krml -add-include '"kremlin/internal/compat.h"' $< -tmpdir $(OUTPUT_DIRECTORY)/c -no-prefix A -o $@ -drop WasmSupport

test.kremlin: $(KREMLIN_EXE)
	./$< hello

test: test.kremlin test.ocaml

clean:
	rm -rf _build $(OUTPUT_DIRECTORY) *~ *.checked $(OCAML_EXE) $(KREMLIN_EXE) .depend

.depend:
	$(FSTAR) --dep full $(FSTAR_FILES) --extract '* -FStar -Prims' > .depend

depend: .depend

include .depend

# The default target is to verify all files, without extracting anything
# It needs to be here, because it reads the variable ALL_FST_FILES in .depend
verify-all: $(addsuffix .checked, $(ALL_FST_FILES))

extract-all: $(ALL_ML_FILES)

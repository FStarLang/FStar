#All the .fst files in your project
MAIN_FILES=A.fst B.fst

#The executable file you want to produce
PROGRAM=myprogram

#A driver in ML to call into your program
TOP_LEVEL_FILE=ml/main.ml

#A place to put all the emitted .ml files
OUTPUT_DIRECTORY=_output

################################################################################
FSTAR=fstar --cache_checked_modules --odir $(OUTPUT_DIRECTORY)
ML_FILES=$(addprefix $(OUTPUT_DIRECTORY)/,$(addsuffix .ml,$(subst .,_, $(subst .fst,,$(MAIN_FILES)))))
OCAML_EXE=$(PROGRAM).ocaml.exe
KREMLIN_EXE=$(PROGRAM).exe

# The default target is to verify all files, without extracting anything
all: $(addsuffix .checked, $(MAIN_FILES))

# The a.fst.checked is the binary, checked version of a.fst
%.checked: %
	$(FSTAR) $*

# The _tags file is a directive to ocamlbuild
# The extracted ML files are precious, because you may want to examine them,
#     e.g., to see how type signatures were transformed from F*
.PRECIOUS: _tags $(ML_FILES) $(addsuffix .checked,$(MAIN_FILES)) $(OUTPUT_DIRECTORY)/out.krml

_tags:
	echo -e "<ml>:traverse\n<$(OUTPUT_DIRECTORY)>:traverse\n" > $@

# To extract an A.ml ML file from an A.fst, we just reload its A.fst.checked file
# and then with the --codegen OCaml option, emit an A.ml
# Note, by default F* will extract all files in the dependency graph
# With the --extract_module, we instruct it to just extract A.ml
$(OUTPUT_DIRECTORY)/%.ml:
	$(FSTAR) $(subst .checked,,$<) --codegen OCaml --extract_module $(subst .fst.checked,,$<)

$(OCAML_EXE): _tags $(ML_FILES) $(TOP_LEVEL_FILES) $(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa
	OCAMLPATH="$(FSTAR_HOME)/bin" ocamlbuild -I $(OUTPUT_DIRECTORY) -use-ocamlfind -pkg fstarlib $(subst .ml,.native,$(TOP_LEVEL_FILE))
	mv _build/$(subst .ml,.native,$(TOP_LEVEL_FILE)) $@

test.ocaml: $(OCAML_EXE)
	./$<

$(OUTPUT_DIRECTORY)/out.krml: $(addsuffix .checked,$(MAIN_FILES))
	echo $^
	krml -fsopts --cache_checked_modules -tmpdir $(OUTPUT_DIRECTORY) -skip-translation $(MAIN_FILES)

$(KREMLIN_EXE): $(OUTPUT_DIRECTORY)/out.krml
	krml $< -tmpdir $(OUTPUT_DIRECTORY) -no-prefix A -o $@

test.kremlin: $(KREMLIN_EXE)
	./$< hello

$(FSTAR_HOME)/bin/fstarlib/fstarlib.cmxa:
	make -C $(FSTAR_HOME)/ulib/ml


.depend:
	$(FSTAR) --dep make $(MAIN_FILES) > .depend

depend: .depend

clean:
	rm -rf _build $(OUTPUT_DIRECTORY) *~ *.checked $(OCAML_EXE) $(KREMLIN_EXE)

include .depend


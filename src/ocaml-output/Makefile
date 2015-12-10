.PHONY: all __force__

OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    -w -8 # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) -w -8 # add other options for ocamlopt here

FSTAR_STDLIB=FStar_ST.cmx FStar_All.cmx FStar_Option.cmx FStar_List.cmx FStar_Char.cmx FStar_String.cmx
COMPILER_ML_LIB=FStar_Util.cmx FStar_Bytes.cmx FStar_Getopt.cmx FStar_Range.cmx FStar_Platform.cmx FStar_Unionfind.cmx
PARSER_ML_LIB=FStar_Parser_Util.cmx
FSTAR_OBJS=prims.cmx $(FSTAR_STDLIB) $(COMPILER_ML_LIB) $(PARSER_ML_LIB) FStar_Version.cmx FStar_Options.cmx FStar_Absyn_Syntax.cmx FStar_Absyn_Const.cmx FStar_Absyn_Visit.cmx FStar_Absyn_Util.cmx FStar_Absyn_Print.cmx FStar_Absyn_SSyntax.cmx FStar_Tc_Env.cmx FStar_Tc_Recheck.cmx FStar_Tc_Normalize.cmx FStar_Tc_Errors.cmx FStar_Tc_Rel.cmx FStar_Tc_Util.cmx FStar_Tc_Tc.cmx FStar_Parser_AST.cmx FStar_Parser_DesugarEnv.cmx FStar_Parser_Desugar.cmx FStar_Parser_Parse.cmx FStar_Parser_Lexhelp.cmx FStar_Parser_LexFStar.cmx FStar_Parser_ParseIt.cmx FStar_Parser_Driver.cmx FStar_Parser_Dep.cmx FStar_ToSMT_Term.cmx FStar_ToSMT_Z3.cmx FStar_ToSMT_SplitQueryCases.cmx FStar_ToSMT_Encode.cmx FSharp_Format.cmx FStar_Extraction_ML_Syntax.cmx FStar_Extraction_ML_Env.cmx FStar_Extraction_ML_Util.cmx FStar_Extraction_ML_Code.cmx FStar_Extraction_ML_ExtractTyp.cmx FStar_Extraction_ML_ExtractExp.cmx FStar_Extraction_ML_ExtractMod.cmx FStar_FStar.cmx
GENERATED_FILES=prims.cmx $(FSTAR_STDLIB:.cmx=.ml) $(COMPILER_ML_LIB:.cmx=.ml) $(PARSER_ML_LIB) main.ml parse.mly parse.ml FStar_Parser_Parse.ml FStar_Parser_LexFStar.ml lex.mll FStar_Parser_ParseIt.ml FStar_Parser_Dep.ml

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar
# The string "Madoko" if madoko is installed, something else otherwise.
MADOKO = $(shell madoko --version 2>/dev/null | cut -c -6)

# FIXME this target is always rebuilt, regardless of whether the sources have
# changed or not
all:
	make prep
	make fstar.exe

prep: parser copy_lib_files depend

parser:
	cat ../parser/parse.fsy | sed 's/^[/][/].*//g' | sed 's/^[#].*//g' | sed 's/^open .*//g' > parse.mly
	ocamlyacc parse.mly
	rm -f FStar_Parser_Parse.ml
	echo "open Prims" > FStar_Parser_Parse.ml
	echo "open FStar_List" >> FStar_Parser_Parse.ml
	echo "open FStar_Util" >> FStar_Parser_Parse.ml
	echo "open FStar_Range" >> FStar_Parser_Parse.ml
	echo "open FStar_Options" >> FStar_Parser_Parse.ml
	echo "open FStar_Absyn_Syntax" >> FStar_Parser_Parse.ml
	echo "open FStar_Absyn_Const" >> FStar_Parser_Parse.ml
	echo "open FStar_Absyn_Util" >> FStar_Parser_Parse.ml
	echo "open FStar_Parser_AST" >> FStar_Parser_Parse.ml
	echo "open FStar_Parser_Util" >> FStar_Parser_Parse.ml
	cat parse.ml >> FStar_Parser_Parse.ml
	ocamllex ../parser/ml/lex.mll -o FStar_Parser_LexFStar.ml
	cp ../parser/ml/parseit.ml FStar_Parser_ParseIt.ml

copy_lib_files:../../lib/ml/native_int/prims.ml $(addprefix ../../lib/ml/, $(FSTAR_STDLIB:.cmx=.ml)) $(addprefix ../basic/ml/, $(COMPILER_ML_LIB:.cmx=.ml)) ../parser/ml/$(PARSER_ML_LIB:.cmx=.ml) ../fstar/ml/main.ml
	cp $^ .

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.ml > .depend


fstar.exe: $(FSTAR_OBJS) main.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o fstar.exe $^
	cp fstar.exe ../../bin/fstar.exe

# always bump version for a release
VERSION=$(shell head -n 1 ../../version.txt)
ifeq ($(OS),Windows_NT)
     PLATFORM=Windows_x64
else
     PLATFORM=$(shell echo `uname`_`uname -m`)
endif
COMPILER = OCaml $(shell ocamlc -version)
DATE = $(shell date -Iseconds)
COMMIT = $(shell git log --pretty=format:'%h' -n 1)
FStar_Version.ml:__force__
	echo 'let version = "$(VERSION)"' > FStar_Version.ml
	echo 'let platform = "$(PLATFORM)"' >> FStar_Version.ml
	echo 'let compiler = "$(COMPILER)"' >> FStar_Version.ml
	echo 'let date = "$(DATE)"' >> FStar_Version.ml
	echo 'let commit= "$(COMMIT)"' >> FStar_Version.ml

# Common rules
.SUFFIXES: .ml .cmx

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Copy the contents of $(1) into $(PREFIX)/$(2) while setting the right file
# permissions and creating directories on the fly as needed.
# (JP: the package version of this command is based on git but for OPAM
#  installs we cannot assume the user has git installed.)
install_dir = cd ../../$(1) && find . -type f -exec install -m 644 -D {} $(PREFIX)/$(2)/{} \;

# Install FStar into $(PREFIX) using the standard Unix directory structure.
install: all
        # Install the binary
	install -m 755 -D -T fstar.exe $(PREFIX)/bin/fstar.exe
        # Then the rest of the static files.
	$(call install_dir,lib,lib/fstar)
	$(call install_dir,examples,share/fstar/examples)
	$(call install_dir,contrib,share/fstar/contrib)
ifeq ($(MADOKO),Madoko)
        # Build the tutorial first
	$(MAKE) -C ../../doc/tutorial
endif
	$(call install_dir,doc/tutorial,share/fstar/tutorial)

NAME=fstar_$(VERSION)_$(PLATFORM)

# the `fexport` function takes a path relative to the top of the F* repo
# and exports the contents of that directory to the $(PREFIX) dir
fexport = cd ../.. && git archive "--format=tar" "--prefix=$(1)/" HEAD:$(1)/ |\
          tar -x -C $(PREFIX)

# Create a zip / tar.gz package of FStar that contains a Z3 binary and
# proper license files.
package: all
        # Clean previous packages.
	rm -f $(NAME).zip $(NAME).tar.gz
	if [ -d "$(PREFIX)" ]; then rm -dfr fstar; fi
        # Install the F* binary
	mkdir -p $(PREFIX)/bin/
	install -m 755 fstar.exe $(PREFIX)/bin/fstar.exe
        # Then the rest of the static files.
	$(call fexport,lib)
	$(call fexport,examples)
	$(call fexport,contrib)
ifeq ($(MADOKO),Madoko)
        # Build the tutorial
	$(MAKE) -C ../../doc/tutorial
else
	@echo " ********** WARNING: You don't have Madoko installed. Binary package will not include tutorial in html form."
endif
	$(call fexport,doc/tutorial)
        # Documentation and licenses
	cp ../../README.md ../../INSTALL.md ../../LICENSE ../../LICENSE-fsharp.txt ../../setenv.sh $(PREFIX)
	wget https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt -O fstar/LICENSE-z3.txt
        # Copy Z3 binary
	@cp ../../bin/*z3* $(PREFIX)/bin &> /dev/null || cp `which z3` $(PREFIX)/bin &> /dev/null || echo " ********** WARNING: you don't have Z3 in \\$FSTAR_HOME/bin or in your \\$PATH, skipped from package ************** "
        # JP: actually this only makes sense for the F# build of F*. Why are we
        # copying these files while this directory builds an OCaml-compiled,
        # Windows-native version of F*?
	make -C ../VS install-packages
	cp ../../bin/FSharp.PowerPack.* $(PREFIX)/bin
ifeq ($(OS),Windows_NT)
	cp ../../bin/msvc*dll $(PREFIX)
	zip -r -9 $(NAME).zip fstar
else
	tar czf $(NAME).tar.gz fstar
endif


# Clean up all files generated by targets in _this_ Makefile
clean:
	rm -dfr fstar
	rm -f .depend fstar.exe *.cmi *.cmx *.cmo *.o
	rm -f $(GENERATED_FILES)
	rm -f *.tar.gz *.zip

# Purge (clean + delete *all* automatically generated files)
# if you do this you'll need to run `make ocaml` in `src` to get them back
purge: clean
	rm -f *.ml || true

-include .depend

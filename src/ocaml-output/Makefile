.PHONY: all __force__

FSTAR_HOME=../..

OPTIONS=-thread -package batteries -linkpkg -g -w "-28"

OCAMLC=ocamlfind ocamlc $(OPTIONS)
OCAMLOPT=ocamlfind ocamlopt $(OPTIONS)
OCAMLDEP=ocamldep
INCLUDES=-I $(FSTAR_HOME)/lib/ml/native_int -I $(FSTAR_HOME)/lib/ml/ # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    -w -8  # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) -w -8  # add other options for ocamlopt here

COMPILER_ML_LIB=FStar_Util.cmx FStar_Bytes.cmx FStar_Getopt.cmx FStar_Range.cmx FStar_Platform.cmx FStar_Unionfind.cmx
PARSER_ML_LIB=FStar_Parser_Util.cmx
FSTAR_OBJS=$(COMPILER_ML_LIB) $(PARSER_ML_LIB) FStar_Version.cmx FStar_Options.cmx FStar_Ident.cmx FStar_Const.cmx FStar_Absyn_Syntax.cmx FStar_Absyn_Const.cmx FStar_Absyn_Visit.cmx FStar_Absyn_Util.cmx FStar_Absyn_Print.cmx FStar_Syntax_Syntax.cmx FStar_Syntax_Const.cmx FStar_Syntax_Subst.cmx FStar_Syntax_Free.cmx FStar_Syntax_InstFV.cmx FStar_Syntax_Util.cmx FStar_Syntax_Print.cmx FStar_Tc_Env.cmx FStar_Tc_Recheck.cmx FStar_Tc_Normalize.cmx FStar_Tc_Errors.cmx FStar_Tc_Rel.cmx FStar_Tc_Util.cmx FStar_Tc_Tc.cmx FStar_Parser_AST.cmx FStar_Parser_DesugarEnv.cmx FStar_Parser_Desugar.cmx FStar_Parser_Env.cmx FStar_Parser_ToSyntax.cmx FStar_Parser_Parse.cmx FStar_Parser_Lexhelp.cmx FStar_Parser_LexFStar.cmx FStar_Parser_ParseIt.cmx FStar_Parser_Driver.cmx FStar_Parser_Dep.cmx FStar_ToSMT_Term.cmx FStar_ToSMT_Z3.cmx FStar_ToSMT_SplitQueryCases.cmx FStar_ToSMT_Encode.cmx FStar_Format.cmx FStar_Extraction_ML_Syntax.cmx FStar_Extraction_ML_Env.cmx FStar_Extraction_ML_Util.cmx FStar_Extraction_ML_Code.cmx FStar_Extraction_ML_ExtractTyp.cmx FStar_Extraction_ML_ExtractExp.cmx FStar_Extraction_ML_ExtractMod.cmx FStar_TypeChecker_Common.cmx FStar_TypeChecker_Env.cmx FStar_TypeChecker_Normalize.cmx  FStar_TypeChecker_Recheck.cmx FStar_TypeChecker_Errors.cmx FStar_TypeChecker_Rel.cmx FStar_TypeChecker_Util.cmx FStar_TypeChecker_Tc.cmx FStar_SMTEncoding_Term.cmx FStar_SMTEncoding_ErrorReporting.cmx FStar_SMTEncoding_SplitQueryCases.cmx FStar_SMTEncoding_Z3.cmx FStar_SMTEncoding_Encode.cmx FStar_Dependences.cmx FStar_Interactive.cmx FStar_Stratified.cmx FStar_Universal.cmx FStar_FStar.cmx

GENERATED_FILES=$(COMPILER_ML_LIB:.cmx=.ml) $(PARSER_ML_LIB) main.ml parse.mly parse.ml FStar_Parser_Parse.ml FStar_Parser_LexFStar.ml lex.mll FStar_Parser_ParseIt.ml 

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar
# The string "Madoko" if madoko is installed, something else otherwise.
MADOKO = $(shell madoko --version 2>/dev/null | cut -c -6)

# Detect the GNU utilities
INSTALL_EXEC := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
DATE_EXEC := $(shell gdate --version 2>/dev/null | cut -c -4 | head -n 1)
ifdef INSTALL_EXEC
   INSTALL_EXEC := ginstall
else
   INSTALL_EXEC := install
endif

ifdef DATE_EXEC
   DATE_EXEC := gdate
else
   DATE_EXEC := date
endif

# FIXME this target is always rebuilt, regardless of whether the sources have
# changed or not
all:
	$(MAKE) -C $(FSTAR_HOME)/lib/ml PRIMS_DIR=native_int
	$(MAKE) prep
	$(MAKE) -j 8 fstar.exe

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
	echo "open FStar_Const" >> FStar_Parser_Parse.ml
	echo "open FStar_Ident" >> FStar_Parser_Parse.ml
	cat parse.ml >> FStar_Parser_Parse.ml
	ocamllex ../parser/ml/lex.mll -o FStar_Parser_LexFStar.ml
	cp ../parser/ml/parseit.ml FStar_Parser_ParseIt.ml

copy_lib_files: $(addprefix ../basic/ml/, $(COMPILER_ML_LIB:.cmx=.ml)) ../parser/ml/$(PARSER_ML_LIB:.cmx=.ml) ../fstar/ml/main.ml
	cp $^ .

# Dependencies
depend:
	$(OCAMLDEP) *.ml > .depend


fstar.exe: $(FSTAR_OBJS) main.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) $(FSTAR_HOME)/lib/ml/fstarlib.cmxa -o fstar.exe $^
	cp fstar.exe ../../bin/fstar.exe

# always bump version for a release
VERSION=$(shell head -n 1 ../../version.txt)
ifeq ($(OS),Windows_NT)
  ifeq ($(PROCESSOR_ARCHITECTURE),AMD64)
     PLATFORM=Windows_x64
  else
     PLATFORM=Windows_x86
  endif
else
     PLATFORM=$(shell echo `uname`_`uname -m`)
endif
COMPILER = OCaml $(shell ocamlc -version)
DATE = $(shell $(DATE_EXEC) -Iseconds)
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
install_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(PREFIX)/$(2)/{} \;

# Install FStar into $(PREFIX) using the standard Unix directory structure.
install: all
        # Install the binary
	$(INSTALL_EXEC) -m 755 -D -T fstar.exe $(PREFIX)/bin/fstar.exe
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
	$(INSTALL_EXEC) -m 755 fstar.exe $(PREFIX)/bin/fstar.exe
        # Then the rest of the static files.
	$(call fexport,lib)
	$(call fexport,examples)
	$(call fexport,contrib)
	$(call fexport,doc/tutorial)
ifeq ($(MADOKO),Madoko)
        # Build the tutorial
	$(MAKE) -C fstar/doc/tutorial
else
	@echo " ********** WARNING: You don't have Madoko installed. Binary package will not include tutorial in html form."
endif
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
	$(MAKE) -C $(FSTAR_HOME)/lib/ml clean
	rm -dfr fstar
	rm -f .depend fstar.exe *.cmi *.cmx *.cmo *.o
	rm -f $(GENERATED_FILES)
	rm -f *.tar.gz *.zip

# Purge (clean + delete *all* automatically generated files)
# if you do this you'll need to run `make ocaml` in `src` to get them back
purge: clean
	rm -f *.ml || true

-include .depend

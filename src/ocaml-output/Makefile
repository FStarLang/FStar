HAS_MENHIR := $(shell command -v menhir 2> /dev/null)
ifdef HAS_MENHIR
HAS_VALID_MENHIR := $(shell expr `menhir --version | sed -e 's/.*version \([0-9]*\)/\1/'` \>= 20161115)
else
HAS_VALID_MENHIR := 0
endif

MENHIR=menhir #--explain --infer -la 1 --table
OCAMLLEX=ocamllex
OCAMLBUILD=cd ../../ && ocamlbuild -cflag '-g' -I src/ocaml-output -I src/basic/ml \
  -I src/parser/ml -I src/fstar/ml -j 24 -build-dir src/ocaml-output/_build \
  -I src/prettyprint/ml -I src/ocaml-output/bootlibs -use-ocamlfind
COMPILER_ML_LIB=FStar_Util.cmx FStar_Bytes.cmx FStar_Getopt.cmx FStar_Range.cmx FStar_Platform.cmx FStar_Unionfind.cmx
PARSER_ML_LIB=FStar_Parser_Util.cmx
PRETTYPRINT_ML_LIB=FStar_Pprint.cmx
GENERATED_FILES=parse.mly FStar_Parser_Parse.ml FStar_Version.ml

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

# Final sanity check for the OCaml version
_UNUSED=$(shell echo 'if Sys.ocaml_version < "4.02.3" then (print_endline "We need OCaml >= 4.02.3"; exit 0)' | ocaml -noinit -noprompt -nostdin)

# Complete build: generate fstar.exe and derive a fresh F#-compatible parser
# from our reference parser (i.e. ../parser/parse.mly) using Menhir (if
# possible).
all: ../parser/parse.fsy fstar.exe

# We derive parse.mly in two ways:
# - if we have menhir, we generate it from from the Menhir parser
#   ../parser/parse.mly (and save a copy of the generated mly in ../parser/ml)
# - if we don't have menhir, we take the saved copy above that is under version
#   control
parse.mly: ../parser/parse.mly
ifeq ($(HAS_VALID_MENHIR), 1)
	# TODO : call menhir directly when positions are fixed instead of
	# letting OCamlbuild go through ocamlyacc
	$(MENHIR) --only-preprocess-for-ocamlyacc $< > $@
	# Save a copy of the dumb parse.mly for whoever doesn't have menhir.
	cp parse.mly ../parser/ml/
else
	cp ../parser/ml/parse.mly ./parse.mly
endif

# This is about the F# parser, which we sed-transform from the parse.mly
# obtained via the rule above.
../parser/parse.fsy: parse.mly
	echo "%{" > $@
	echo "#light \"off\"" >> $@
	echo "// (c) Microsoft Corporation. All rights reserved" >> $@
	echo "open Prims" >> $@
	echo "open FStar.Errors" >> $@
	echo "open FStar.List" >> $@
	echo "open FStar.Util" >> $@
	echo "open FStar.Range" >> $@
	echo "open FStar.Options" >> $@
	echo "open FStar.Syntax.Syntax" >> $@
	echo "open FStar.Syntax.Const" >> $@
	echo "open FStar.Syntax.Util" >> $@
	echo "open FStar.Parser.AST" >> $@
	echo "open FStar.Parser.Util" >> $@
	echo "open FStar.Const" >> $@
	echo "open FStar.Ident" >> $@
	echo "open FStar.String" >> $@
	# TODO : fsyacc seems to complain as soon as there is an arrow -> in a %type declaration...
	cat parse.mly | sed -e '/%{/d' \
	                    -e '/^open /d' \
	                    -e '/%token/s/[a-zA-Z0-9_]*\.//g' \
	                    -e '/%type/s/[a-zA-Z0-9_]*\.//g' \
	                    -e '/%token.*->.*/d' \
	                    -e '/%type.*->.*/d' \
	                    >> $@

.PHONY: fstar.exe
fstar.exe: $(GENERATED_FILES)
	$(OCAMLBUILD) main.native
	cp _build/src/fstar/ml/main.native ../../bin/$@
	cp _build/src/fstar/ml/main.native ../../bin/fstar.ocaml

FStar_Parser_Parse.ml: parse.mly
	# We are opening the same module twice but we need these modules
	# open for the definition of tokens
	echo "open Prims" > $@
	echo "open FStar_Errors" >> $@
	echo "open FStar_List" >> $@
	echo "open FStar_Util" >> $@
	echo "open FStar_Range" >> $@
	echo "open FStar_Options" >> $@
	echo "open FStar_Syntax_Syntax" >> $@
	echo "open FStar_Syntax_Const" >> $@
	echo "open FStar_Syntax_Util" >> $@
	echo "open FStar_Parser_AST" >> $@
	echo "open FStar_Parser_Util" >> $@
	echo "open FStar_Const" >> $@
	echo "open FStar_Ident" >> $@
	echo "open FStar_String" >> $@
	# TODO: create a proper OCamlbuild rule for this production so that
	# OCamlbuild knows how to generate parse.mly first (possibly using
	# menhir) and removes the production as needed.
	ocamlyacc parse.mly
	cat parse.ml >> $@
	rm parse.ml parse.mli

# always bump version for a release; always bump it when recompiling so that one
# can easily help debugging
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
COMMIT = $(shell ../tools/get_commit)

.PHONY: version
FStar_Version.ml:
	echo 'let version = "$(VERSION)"' > $@
	echo 'let platform = "$(PLATFORM)"' >> $@
	echo 'let compiler = "$(COMPILER)"' >> $@
	echo 'let date = "$(DATE)"' >> $@
	echo 'let commit= "$(COMMIT)"' >> $@


# ------------------------------------------------------------------------------
# Preparing a release... these targets are not optimized and the Makefile is
# actually used for scripting a bunch of stuff.
# ------------------------------------------------------------------------------

# Copy the contents of $(1) into $(PREFIX)/$(2) while setting the right file
# permissions and creating directories on the fly as needed.
# (JP: the package version of this command is based on git but for OPAM
#  installs we cannot assume the user has git installed.)
install_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(PREFIX)/$(2)/{} \;

# Install FStar into $(PREFIX) using the standard Unix directory structure.
install: all
        # Install the binary
	$(INSTALL_EXEC) -m 755 -D -T _build/src/fstar/ml/main.native $(PREFIX)/bin/fstar.exe
        # Then the rest of the static files.
	$(call install_dir,ulib,lib/fstar)
	$(call install_dir,examples,share/fstar/examples)
	$(call install_dir,ucontrib,share/fstar/contrib)
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
	$(call fexport,ulib)
	$(call fexport,examples)
	$(call fexport,contrib)
	$(call fexport,ucontrib)
	$(call fexport,doc/tutorial)
ifeq ($(MADOKO),Madoko)
        # Build the tutorial
	$(MAKE) -C fstar/doc/tutorial
else
	@echo " ********** WARNING: You don't have Madoko installed. Binary package will not include tutorial in html form."
endif
        # Documentation and licenses
	cp ../../README.md ../../INSTALL.md ../../LICENSE ../../LICENSE-fsharp.txt $(PREFIX)
	wget https://raw.githubusercontent.com/Z3Prover/z3/master/LICENSE.txt -O fstar/LICENSE-z3.txt
        # Copy Z3 binary
	@cp ../../bin/*z3* $(PREFIX)/bin &> /dev/null || cp `which z3` $(PREFIX)/bin &> /dev/null || echo " ********** WARNING: you don't have Z3 in \\$(FSTAR_HOME)/bin or in your \\$PATH, skipped from package ************** "
        # JP: actually this only makes sense for the F# build of F*. Why are we
        # copying these files while this directory builds an OCaml-compiled,
        # Windows-native version of F*?
        # CH: Nik added these, and if I remember right it might be related to bootstrapping?
	make -C ../VS install-packages
	cp ../../bin/FSharp.PowerPack.* $(PREFIX)/bin
        # Some new things used by examples/Makefile
	mkdir -p $(PREFIX)/src/gmake/
	cp ../../src/gmake/fstar.mk ../../src/gmake/nubuild.mk $(PREFIX)/src/gmake/
ifeq ($(OS),Windows_NT)
	cp ../../bin/msvc*dll $(PREFIX)
	zip -r -9 $(NAME).zip fstar
else
	tar czf $(NAME).tar.gz fstar
endif


.PHONY: clean
# Clean up all files generated by targets in _this_ Makefile
clean:
	# JP: delete this line and the script once every member of the team has
	# run ./clean.sh once
	./clean.sh
	rm -rf _build
	rm -f $(GENERATED_FILES)
	rm -f *.tar.gz *.zip

# Purge (clean + delete *all* automatically generated files)
# if you do this you'll need to run `make ocaml` in `src` to get them back
purge: clean
	rm -f *.ml || true

-include .depend

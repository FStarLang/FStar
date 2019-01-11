HAS_MENHIR := $(shell command -v menhir 2> /dev/null)
MENHIR_MIN_VERSION:=20161115
ifdef HAS_MENHIR
HAS_VALID_MENHIR := $(shell expr `menhir --version | sed -e 's/.*version \([0-9]*\)/\1/'` \>= $(MENHIR_MIN_VERSION))
else
HAS_VALID_MENHIR := 0
endif

MENHIR=menhir #--explain --infer -la 1 --table
OCAMLLEX=ocamllex
FSTAR_OCAMLBUILD_EXTRAS ?= -cflag -g
OCAMLBUILD=cd ../../ && ocamlbuild $(FSTAR_OCAMLBUILD_EXTRAS) -I src/ocaml-output -I src/basic/ml \
  -I src/parser/ml -I src/fstar/ml -I src/extraction/ml \
  -I src/prettyprint/ml -I src/tactics/ml -I src/tests/ml -I ulib/ml \
  -j 24 -build-dir src/ocaml-output/_build -use-ocamlfind
COMPILER_ML_LIB=FStar_Util.cmx FStar_Compiler_Bytes.cmx			\
		FStar_Getopt.cmx FStar_Range.cmx FStar_Platform.cmx	\
		FStar_Unionfind.cmx
PARSER_ML_LIB=FStar_Parser_Util.cmx
PRETTYPRINT_ML_LIB=FStar_Pprint.cmx
GENERATED_FILES=parse.mly FStar_Parser_Parse.ml FStar_Version.ml

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar
PATH_TO_FILE=$(PREFIX)/bin/z3.exe
# The string "Madoko" if madoko is installed, something else otherwise.
MADOKO = $(shell madoko --version 2>/dev/null | cut -c -6)
DOS2UNIX=$(shell which dos2unix >/dev/null 2>&1 && echo dos2unix || echo true)

# Detect the GNU utilities
INSTALL_EXEC := $(shell ginstall --version 2>/dev/null | cut -c -8 | head -n 1)
FIND=$(shell which gfind >/dev/null 2>&1 && echo gfind || echo find)
ifdef INSTALL_EXEC
   INSTALL_EXEC := ginstall
else
   INSTALL_EXEC := install
endif

# Final sanity check for the OCaml version
OCAML_BRANCH=$(shell ocaml get_branch.ml)

# Complete build: generate fstar.exe and derive a fresh F#-compatible parser
# from our reference parser (i.e. ../parser/parse.mly) using Menhir (if
# possible).
all:  ../parser/parse.fsy ../../bin/fstar.exe ../../bin/fstar.ocaml ../../bin/tests.exe install-compiler-lib

# We derive parse.mly in two ways:
# - if we have menhir, we generate it from from the Menhir parser
#   ../parser/parse.mly (and save a copy of the generated mly in ../parser/ml)
# - if we don't have menhir, we take the saved copy above that is under version
#   control
parse.mly: ../parser/parse.mly
ifeq ($(HAS_VALID_MENHIR), 1)
	@# TODO : call menhir directly when positions are fixed instead of
	@# letting OCamlbuild go through ocamlyacc
	$(MENHIR) --only-preprocess-for-ocamlyacc $< > $@
else
	$(error Correct version of menhir not found (needs a version newer than $(MENHIR_MIN_VERSION)))
endif

# This is about the F# parser, which we sed-transform from the parse.mly
# obtained via the rule above.
../parser/parse.fsy: parse.mly
	echo "%{" > $@
	echo "#light \"off\"" >> $@
	echo "// (c) Microsoft Corporation. All rights reserved" >> $@
	echo "open Prims" >> $@
	echo "open FStar" >> $@
	echo "open FStar.Errors" >> $@
	echo "open FStar.List" >> $@
	echo "open FStar.Util" >> $@
	echo "open FStar.Range" >> $@
	echo "open FStar.Options" >> $@
	echo "open FStar.Parser.Const" >> $@
	echo "open FStar.Parser.AST" >> $@
	echo "open FStar.Parser.Util" >> $@
	echo "open FStar.Const" >> $@
	echo "open FStar.Ident" >> $@
	echo "open FStar.String" >> $@
	@# TODO : fsyacc seems to complain as soon as there is an arrow -> in a %type declaration...
	cat parse.mly | sed -e '/%{/d' \
	                    -e '/^open /d' \
	                    -e '/%token/s/[a-zA-Z0-9_]*\.//g' \
	                    -e '/%type/s/[a-zA-Z0-9_]*\.//g' \
	                    -e '/%token.*->.*/d' \
	                    -e '/%type.*->.*/d' \
	              | cat -s >> $@

# https://stackoverflow.com/questions/38294095/ocaml-how-to-solve-findlib-warnings-of-multiple-cmis
FSTAR_MAIN_NATIVE=_build/src/fstar/ml/main.native
$(FSTAR_MAIN_NATIVE): export OCAMLFIND_IGNORE_DUPS_IN = $(shell ocamlfind query compiler-libs)
$(FSTAR_MAIN_NATIVE): $(GENERATED_FILES)
	$(OCAMLBUILD) $(notdir $(FSTAR_MAIN_NATIVE)) src/ocaml-output/FStar_Syntax_Syntax.inferred.mli

../../bin/fstar.exe: $(FSTAR_MAIN_NATIVE)
	cp $^ $@

../../bin/fstar.ocaml: $(FSTAR_MAIN_NATIVE)
	cp $^ $@

install-compiler-lib: $(FSTAR_MAIN_NATIVE)
	mkdir -p ../../bin/fstar-compiler-lib/
	@# VD: forcing the recompilation of modules in ulib/tactics_ml whenever the compiler is rebuilt
	@# in order to avoid inconsistent assumption errors between fstartaclib and compiler-lib
	$(FIND) ../../ulib/tactics_ml \( -name '*.cmi' -or -name '*.cmx' \) -exec rm {} \;
	$(FIND) . \( -name '*.cmi' -or -name '*.cmx' \) -exec cp {} ../../bin/fstar-compiler-lib/ \;
	touch $@

FStar_Parser_Parse.ml: parse.mly
	@# We are opening the same module twice but we need these modules
	@# open for the definition of tokens
	echo "open Prims" > $@
	echo "open FStar_Errors" >> $@
	echo "open FStar_List" >> $@
	echo "open FStar_Util" >> $@
	echo "open FStar_Range" >> $@
	echo "open FStar_Options" >> $@
	echo "open FStar_Syntax_Syntax" >> $@
	echo "open FStar_Parser_Const" >> $@
	echo "open FStar_Syntax_Util" >> $@
	echo "open FStar_Parser_AST" >> $@
	echo "open FStar_Parser_Util" >> $@
	echo "open FStar_Const" >> $@
	echo "open FStar_Ident" >> $@
	echo "open FStar_String" >> $@
	@# TODO: create a proper OCamlbuild rule for this production so that
	@# OCamlbuild knows how to generate parse.mly first (possibly using
	@# menhir) and removes the production as needed.
	ocamlyacc parse.mly 2> yac-log
	cat yac-log
	@if [ "0$$(grep "shift/reduce" yac-log | sed 's/^\([0-9]\+\).*/\1/')" -gt 6 ]; then \
	  echo "shift-reduce conflicts have increased; please fix" && exit 255; \
	fi
	@if grep -q "reduce/reduce" yac-log ; then \
	  echo "A reduce-reduce conflict was introduced; please fix" && exit 255; \
	fi
	cat parse.ml >> $@
	rm parse.ml parse.mli

../../bin/tests.exe: export OCAMLFIND_IGNORE_DUPS_IN = $(shell ocamlfind query compiler-libs)
../../bin/tests.exe: ../../bin/fstar.exe
	$(OCAMLBUILD) FStar_Tests_Main.native
	cp -f _build/src/tests/ml/FStar_Tests_Main.native $@

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
DATE = $(shell date '+%Y-%m-%dT%H:%M:%S%z')
COMMIT = $(shell ../tools/get_commit)

.PHONY: FStar_Version.ml
FStar_Version.ml:
	echo 'open FStar_Util' > $@.tmp
	echo 'let dummy () = ();;' >> $@.tmp
	echo 'FStar_Options._version := "$(VERSION)";;' >> $@.tmp
	echo 'FStar_Options._platform := "$(PLATFORM)";;' >> $@.tmp
	echo 'FStar_Options._compiler := "$(COMPILER)";;' >> $@.tmp
	echo 'FStar_Options._commit:= "$(COMMIT)";;' >> $@.tmp
	./copy_if_diff.sh $@.tmp $@


# ------------------------------------------------------------------------------
# Preparing a release... these targets are not optimized and the Makefile is
# actually used for scripting a bunch of stuff.
# ------------------------------------------------------------------------------

# Copy the contents of $(1) into $(PREFIX)/$(2) while setting the right file
# permissions and creating directories on the fly as needed.
# (JP: the package version of this command is based on git but for OPAM
#  installs we cannot assume the user has git installed.)
install_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(PREFIX)/$(2)/{} \;

# install the standard library binary files
install_fstarlib = $(INSTALL_EXEC) -m 755 -D ../../$(1)/$(2) $(PREFIX)/lib/fstar/$(2)

# Install FStar into $(PREFIX) using the standard Unix directory
# structure.  NOTE: this rule needs ocamlfind to install the fstarlib,
# fstar-tactics-lib and fstar-compiler-lib packages. It works with the
# opam package, but it has not been tested in any other settings.
install: all
	@# Install the binary
	$(INSTALL_EXEC) -m 755 -D $(FSTAR_MAIN_NATIVE) $(PREFIX)/bin/fstar.exe
	@# Then the standard library
	$(call install_dir,ulib,lib/fstar)
	@# Then the binary library
	cd ../../bin/fstarlib && ocamlfind install fstarlib *
	cd ../../bin/fstar-compiler-lib && ocamlfind install fstar-compiler-lib *
	cd ../../bin/fstar-tactics-lib && ocamlfind install fstar-tactics-lib *
	@# Then the rest of the static files.
	@# (those are not used in the opam package, not sure if their Makefiles work)
	$(call install_dir,examples,share/fstar/examples)
	$(call install_dir,ucontrib,share/fstar/contrib)
	@# Then the tutorial
ifeq ($(MADOKO),Madoko)
	@# Build the tutorial first
	$(MAKE) -C ../../doc/tutorial
endif
	$(call install_dir,doc/tutorial,share/fstar/tutorial)

NAME=fstar_$(VERSION)_$(PLATFORM)

# the `fexport` function takes a path relative to the top of the F* repo
# and exports the contents of that directory to the $(PREFIX) dir
fexport = cd ../.. && git archive "--format=tar" "--prefix=$(1)/" HEAD:$(1)/ |\
          tar -x -C $(PREFIX)

# Similar, but exports every file instead of only those in version control.
fexport-all = cp -a ../../$(1) $(PREFIX)/$(1)

ifeq ($(OS),Windows_NT)
  Z3_NAME=z3.exe
else
  Z3_NAME=z3
endif
Z3_DIR=$(shell dirname $$(which $(Z3_NAME)))
Z3_LICENSE=$(shell dirname $(Z3_DIR))/LICENSE.txt

.PHONY: ulib
ulib:
	make -C ../../ulib install-fstarlib
	make -C ../../ulib install-fstar-tactics

# Create a zip / tar.gz package of FStar that contains a Z3 binary and
# proper license files.
package: all
	$(MAKE) ulib
	@# Clean previous packages.
	rm -f $(NAME).zip $(NAME).tar.gz
	if [ -d "$(PREFIX)" ]; then rm -dfr fstar; fi
	@# Install the F* binary
	mkdir -p $(PREFIX)/bin/
	$(INSTALL_EXEC) -m 755 $(FSTAR_MAIN_NATIVE) $(PREFIX)/bin/fstar.exe
	@# Then the standard library.
	$(call fexport,ulib)
	@# Then the rest of the static files.
	$(call fexport,examples)
	$(call fexport,ucontrib)
	$(call fexport,doc/tutorial)
	$(call fexport-all,bin/fstarlib)
	$(call fexport-all,bin/fstar-compiler-lib)
	$(call fexport-all,bin/fstar-tactics-lib)

ifeq ($(MADOKO),Madoko)
	@# Build the tutorial
	$(MAKE) -C fstar/doc/tutorial
else
	@echo " ********** You don't have Madoko installed. Binary package will not include tutorial in html form."
	false
endif
	@# Documentation and licenses
	cp ../../README.md ../../INSTALL.md ../../LICENSE ../../LICENSE-fsharp.txt $(PREFIX)
	cp $(Z3_LICENSE) $(PREFIX)/LICENSE-z3.txt

	@# Z3
ifeq ($(OS),Windows_NT)
	cp $(shell which libgmp-10.dll) $(PREFIX)/bin
	cp $(Z3_DIR)/*.exe $(Z3_DIR)/*.dll $(Z3_DIR)/*.lib $(PREFIX)/bin
	chmod a+x $(PREFIX)/bin/z3.exe $(PREFIX)/bin/*.dll
	zip -r -9 $(NAME).zip fstar
else
	cp $(Z3_DIR)/z3 $(PREFIX)/bin
	tar czf $(NAME).tar.gz fstar
endif


.PHONY: clean
# Clean up all files generated by targets in _this_ Makefile
# Also clean up the standard library
clean:
	$(MAKE) -C ../../ulib clean
	rm -rf _build
	rm -f $(GENERATED_FILES)
	rm -f *.tar.gz *.zip
	rm -f ../../bin/fstar-compiler-lib/*.cm[aiox]
	rm -f ../../bin/fstar-compiler-lib/*.cmx[as]

# Purge (clean + delete *all* automatically generated files)
# if you do this you'll need to run `make ocaml` in `src` to get them back
purge: clean
	rm -f *.ml || true

-include .depend

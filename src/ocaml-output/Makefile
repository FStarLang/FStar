HAS_MENHIR := $(shell command -v menhir 2> /dev/null)
MENHIR_MIN_VERSION:=20161115
ifdef HAS_MENHIR
HAS_VALID_MENHIR := $(shell expr `menhir --version | sed -e 's/.*version \([0-9]*\)/\1/'` \>= $(MENHIR_MIN_VERSION))
else
HAS_VALID_MENHIR := 0
endif

include ../../.common.mk

MENHIR=menhir #--explain --infer -la 1 --table
OCAMLLEX=ocamllex
FSTAR_OCAMLBUILD_EXTRAS ?= -cflag -g

FSTAR_HOME = ../..
DUNE_SNAPSHOT ?= $(realpath $(FSTAR_HOME)/ocaml)
export DUNE_SNAPSHOT

FStar_Parser_Parse_ml=$(DUNE_SNAPSHOT)/fstar-lib/generated/FStar_Parser_Parse.ml
FStar_Version_ml=$(DUNE_SNAPSHOT)/fstar-lib/dynamic/FStar_Version.ml

GENERATED_ML_FILES=$(FStar_Parser_Parse_ml) $(FStar_Version_ml)

GENERATED_FILES=$(GENERATED_ML_FILES) parse.mly

# The directory where we install files when doing "make install".
# Overridden via the command-line by the OPAM invocation.
PREFIX=$(shell pwd)/fstar
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

all: dune-snapshot

# We derive parse.mly in two ways:
# - if we have menhir, we generate it from from the Menhir parser
#   ../parser/parse.mly (and save a copy of the generated mly in ../parser/ml)
# - if we don't have menhir, we take the saved copy above that is under version
#   control
parse.mly: ../parser/parse.mly
ifeq ($(HAS_VALID_MENHIR), 1)
	@# TODO : call menhir directly when positions are fixed instead of
	@# letting OCamlbuild go through ocamlyacc
	@echo "[MENHIR PREPROCESS]"
	$(Q)$(MENHIR) --only-preprocess-for-ocamlyacc $< > $@
else
	$(error Correct version of menhir not found (needs a version newer than $(MENHIR_MIN_VERSION)))
endif

.PHONY: generated-files
generated-files: $(GENERATED_ML_FILES)

.PHONY: dune-stdlib-snapshot dune-taclib-snapshot dune-snapshot dune-fstar-snapshot dune-verify-ulib source-files

# FIXME: dune-fstar-snapshot should also depend on dune-verify-ulib,
# once we no longer lax-typecheck
dune-fstar-snapshot:
	+$(MAKE) -C .. ocaml

dune-verify-ulib:
	+$(MAKE) -C ../../ulib

dune-stdlib-snapshot: dune-verify-ulib
	$(MAKE) -C ../../ulib -f Makefile.extract-stdlib dune-snapshot

dune-taclib-snapshot: dune-verify-ulib
	$(MAKE) -C ../../ulib -f Makefile.extract-taclib dune-snapshot

dune-snapshot: generated-files dune-fstar-snapshot dune-stdlib-snapshot dune-taclib-snapshot

$(FStar_Parser_Parse_ml): parse.mly
	@# We are opening the same module twice but we need these modules
	@# open for the definition of tokens
	$(Q)echo "open Prims" > $@
	$(Q)echo "open FStar_Errors" >> $@
	$(Q)echo "open FStar_Compiler_List" >> $@
	$(Q)echo "open FStar_Compiler_Util" >> $@
	$(Q)echo "open FStar_Compiler_Range" >> $@
	$(Q)echo "open FStar_Options" >> $@
	$(Q)echo "open FStar_Syntax_Syntax" >> $@
	$(Q)echo "open FStar_Parser_Const" >> $@
	$(Q)echo "open FStar_Syntax_Util" >> $@
	$(Q)echo "open FStar_Parser_AST" >> $@
	$(Q)echo "open FStar_Parser_Util" >> $@
	$(Q)echo "open FStar_Const" >> $@
	$(Q)echo "open FStar_Ident" >> $@
	$(Q)echo "open FStar_String" >> $@
	@# TODO: create a proper OCamlbuild rule for this production so that
	@# OCamlbuild knows how to generate parse.mly first (possibly using
	@# menhir) and removes the production as needed.
	@echo "[OCAMLYACC]"
	$(Q)ocamlyacc parse.mly 2> yac-log
	$(Q)cat yac-log
	@if [ "0$$(grep "shift/reduce" yac-log | sed 's/^\([0-9]\+\).*/\1/')" -gt 6 ]; then \
	  echo "shift-reduce conflicts have increased; please fix" && rm -f $@ && false; \
	fi
	@if grep -q "reduce/reduce" yac-log ; then \
	  echo "A reduce-reduce conflict was introduced; please fix" && rm -f $@ && false; \
	fi
	$(Q)cat parse.ml >> $@
	$(Q)rm parse.ml parse.mli

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
COMMITDATE = $(shell git log --pretty=format:%ci -n 1 2>/dev/null || echo unset) # If a system does not have git, or we are not in a git repo, fallback with "unset"

.PHONY: $(FStar_Version_ml)
$(FStar_Version_ml):
	@echo '[MAKE      FStar_Version.ml]'
	$(Q)rm -rf $@
	$(Q)mkdir -p $(dir $@)
	$(Q)echo 'let dummy () = ();;' >> $@
	$(Q)echo 'FStar_Options._version := "$(VERSION)";;' >> $@
	$(Q)echo 'FStar_Options._platform := "$(PLATFORM)";;' >> $@
	$(Q)echo 'FStar_Options._compiler := "$(COMPILER)";;' >> $@
	@# We deliberately use commitdate instead of date, so that rebuilds are no-ops
	$(Q)echo 'FStar_Options._date := "$(COMMITDATE)";;' >> $@
	$(Q)echo 'FStar_Options._commit:= "$(COMMIT)";;' >> $@


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
install:
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
	$(call install_dir,tests,share/fstar/tests)
	$(call install_dir,ucontrib,share/fstar/contrib)
	@# Then the tutorial
ifeq ($(MADOKO),Madoko)
	@# Build the tutorial first
	+$(MAKE) -C ../../doc/tutorial
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
# Z3_LICENSE MUST be explicitly overridden if z3 is installed from an opam package.
# See for instance $(FSTAR_HOME)/.docker/package.Dockerfile
Z3_LICENSE?=$(shell dirname $(Z3_DIR))/LICENSE.txt

# Create a zip / tar.gz package of FStar that contains a Z3 binary and
# proper license files.
package:
	@# Clean previous packages.
	! [ -d "$(PREFIX)" ]
	rm -f $(NAME).zip $(NAME).tar.gz
	mkdir -p $(PREFIX)
	@# Install the F* binary
	$(call fexport-all,bin)
	@# Then the standard library.
	$(call fexport-all,ulib)
	mkdir -p $(PREFIX)/src/ocaml-output/
	cp ../../src/ocaml-output/FStar_Pervasives.ml $(PREFIX)/src/ocaml-output/
	cp ../../version.txt $(PREFIX)/
	cp ../../_tags $(PREFIX)/
	cp ../../.common.mk $(PREFIX)/
	@# Then the rest of the static files.
	$(call fexport,ucontrib)
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

# This rule produces the package into an archive file fstar.tar.gz (or
# fstar.zip), whose filename does not contain the version and
# platform, and stores the original file name into
# version_platform.txt

package_unknown_platform: package
ifeq ($(OS),Windows_NT)
	echo $(NAME).zip > version_platform.txt
	mv $(NAME).tar.gz fstar.zip
else
	echo $(NAME).tar.gz > version_platform.txt
	mv $(NAME).tar.gz fstar.tar.gz
endif

.PHONY: clean
# Clean up all files generated by targets in _this_ Makefile
clean:
	@echo "[CLEAN     src/ocaml-output]"
	$(Q)rm -f $(GENERATED_FILES)
	$(Q)rm -f *.tar.gz *.zip

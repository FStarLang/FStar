include ../../.common.mk

FSTAR_HOME = ../..
DUNE_SNAPSHOT ?= $(call maybe_cygwin_path,$(realpath $(FSTAR_HOME)/ocaml))
export DUNE_SNAPSHOT

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
export INSTALL_EXEC

all: dune-snapshot

.PHONY: dune-stdlib-snapshot dune-snapshot dune-fstar-snapshot dune-verify-ulib source-files

# FIXME: dune-fstar-snapshot should also depend on dune-verify-ulib,
# once we no longer lax-typecheck
dune-fstar-snapshot:
	+$(MAKE) -C .. ocaml

dune-verify-ulib:
	+$(MAKE) -C ../../ulib core

dune-stdlib-snapshot: dune-verify-ulib
	$(MAKE) -C ../../ulib -f Makefile.extract dune-snapshot

dune-snapshot: dune-fstar-snapshot dune-stdlib-snapshot
	+$(Q)$(MAKE) overlay-snapshots

overlay-snapshots:
	@# These copies MUST be done in this order to make sure
	@# we avoid races and always end in a consistent state.
	$(call msg, "OVERLAY SNAPSHOTS")
	$(Q)install -m0644 -t $(DUNE_SNAPSHOT)/fstar-lib/generated/ fstarc/*.ml
	$(Q)install -m0644 -t $(DUNE_SNAPSHOT)/fstar-lib/generated/ fstarlib/*.ml

# ------------------------------------------------------------------------------
# Preparing a release... these targets are not optimized and the Makefile is
# actually used for scripting a bunch of stuff.
# ------------------------------------------------------------------------------

# Copy the contents of $(1) into $(PREFIX)/$(2) while setting the right file
# permissions and creating directories on the fly as needed.
# (JP: the package version of this command is based on git but for OPAM
#  installs we cannot assume the user has git installed.)
install_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(PREFIX)/$(2)/{} \;

# Install FStar into $(PREFIX) using the standard Unix directory
# structure.

# On Cygwin, the `--prefix` option to dune only
# supports Windows paths.
FSTAR_PREFIX=$(call maybe_cygwin_path,$(PREFIX))

FSTAR_BUILD_PROFILE ?= release

install:
	@# Rebuild everything
	+$(MAKE) -C $(FSTAR_HOME)
	@# Install the binary and the binary library
	cd $(DUNE_SNAPSHOT) && dune install --profile=$(FSTAR_BUILD_PROFILE) --prefix=$(FSTAR_PREFIX)
	@# Then the standard library sources and checked files
	+$(MAKE) -C $(FSTAR_HOME)/ulib install
	@# Then the rest
	+$(MAKE) install-sides

# The `install-sides` rule is intended to be run only by the nix flake.
# Indeed, nix needs to patch binaries created by OCaml (here fstar.exe),
# thus nix cannot use `dune install`

.PHONY: install-sides
install-sides:
	@# Then the examples (those now work from any F* installation flavor, sources, binary package or opam)
	@# ucontrib is needed by examples/crypto
	$(call install_dir,examples,share/fstar/examples)
	$(call install_dir,ucontrib,share/fstar/contrib)
	@# Then the tutorial
ifeq ($(MADOKO),Madoko)
	@# Build the tutorial first
	+$(MAKE) -C ../../doc/old/tutorial
endif
	$(INSTALL_EXEC) -m 644 -D ../../doc/Makefile.include $(PREFIX)/share/fstar/doc/Makefile.include
	$(call install_dir,doc/old/tutorial,share/fstar/doc/old/tutorial)

PACKAGE_NAME ?= fstar

ifeq ($(OS),Windows_NT)
  Z3_NAME=z3.exe
else
  Z3_NAME=z3
endif
Z3_DIR=$(dir $(shell which $(Z3_NAME)))
# Z3_LICENSE MUST be explicitly overridden if z3 is installed from an opam package.
# See for instance $(FSTAR_HOME)/.docker/package.Dockerfile
ifndef Z3_LICENSE
  Z3_LICENSE?=$(shell if test -f $(Z3_DIR)/LICENSE.txt ; then echo $(Z3_DIR)/LICENSE.txt ; elif test -f $(Z3_DIR)/../LICENSE.txt ; then echo $(Z3_DIR)/../LICENSE.txt ; fi)
endif

# Create a zip / tar.gz package of FStar that contains a Z3 binary and
# proper license files.

# On Cygwin, the `--prefix` option to dune only
# supports Windows paths.
package_prefix=$(call maybe_cygwin_path,$(CURDIR)/fstar)

package_dir = cd ../../$(1) && find . -type f -exec $(INSTALL_EXEC) -m 644 -D {} $(package_prefix)/$(2)/{} \;

package:
	if test -z "$(Z3_LICENSE)" ; then echo Please set Z3_LICENSE to the location of the license file for Z3 ; false ; fi
	@# Clean previous packages.
	! [ -d "$(package_prefix)" ]
	rm -f $(PACKAGE_NAME).zip $(PACKAGE_NAME).tar.gz
	@# Install F* into the package
	+PREFIX=$(package_prefix) $(MAKE) install
	@# Make the F* ulib F# DLL (NOT the nuget package)
	+PREFIX=$(package_prefix) $(MAKE) -C $(FSTAR_HOME)/ulib ulib-in-fsharp-dll
	@# Then the version file.
	cp ../../version.txt $(package_prefix)/
	@# Documentation and licenses
	cp ../../README.md ../../INSTALL.md ../../LICENSE ../../LICENSE-fsharp.txt $(package_prefix)
	cp $(Z3_LICENSE) $(package_prefix)/LICENSE-z3.txt
	@# Z3
ifeq ($(OS),Windows_NT)
	cp $(shell which libgmp-10.dll) $(package_prefix)/bin
	cp $(Z3_DIR)/*.exe $(Z3_DIR)/*.dll $(Z3_DIR)/*.lib $(package_prefix)/bin
	chmod a+x $(package_prefix)/bin/z3.exe $(package_prefix)/bin/*.dll
	zip -r -9 $(PACKAGE_NAME).zip fstar
else
	cp $(Z3_DIR)/z3 $(package_prefix)/bin
	tar czf $(PACKAGE_NAME).tar.gz fstar
endif

.PHONY: clean
# Clean up all files generated by targets in _this_ Makefile
# We only remove the dynamic/ part of the OCaml snapshot. The rest
# should be removed only through the `clean-dune-snapshot` rule in the
# root Makefile. This is because `make all` no longer performs any
# bootstrapping, so `make clean` shouldn't clean up the whole
# snapshot.
clean:
	$(call msg, "CLEAN", "src/ocaml-output")
	$(Q)rm -f *.tar.gz *.zip
	$(Q)rm -f version_platform.txt
	$(Q)rm -rf fstar

FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/common.mk

ifeq ($(V),)
FSTAR_DUNE_OPTIONS += --no-print-directory
FSTAR_DUNE_OPTIONS += --display=quiet
endif

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)
ifeq ($(FSTAR_DUNE_RELEASE),1)
FSTAR_DUNE_BUILD_OPTIONS += --release
endif

.NOTPARALLEL:
# Sorry, but dune seems to get confused when its OCAMLPATH is changing

.PHONY: _force
_force:

fstarc-bare: _force
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS) fstarc-bare

fstarc-full: _force
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS) fstarc-full

libapp: _force
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS) libapp

libplugin: _force
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS) libplugin

clean: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune
	rm -rf out

# In a local build, we prefer to symlink the library and checked file
# directories to get better IDE integration, but of course we cannot do
# that on actual install, and must copy all files.
ifeq ($(FSTAR_LINK_LIBDIRS),1)
INSTALL_DIR := ln -Tsrf
else
INSTALL_DIR := cp -H -p -r
endif

# NOTE: We install ulib/ and src/ as symlinks, which is useful for
# local installs so VS Code can properly jump between these files,
# and we also avoid unnecessary copies. When building packages, we use
# tar's -h to follow and eliminate all these links.
install: PREFIX ?= ./out
install: fstarc-bare fstarc-full libapp libplugin
	@# Seems to need one final build?
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS)
	cd dune && dune install $(FSTAR_DUNE_OPTIONS) --prefix=$(abspath $(PREFIX))
	@# Install library and its checked files
	$(INSTALL_DIR) ulib $(PREFIX)/lib/fstar/ulib
	$(INSTALL_DIR) ulib.checked $(PREFIX)/lib/fstar/ulib.checked
	echo 'ulib'          > $(PREFIX)/lib/fstar/fstar.include
	echo 'ulib.checked' >> $(PREFIX)/lib/fstar/fstar.include
	@# Install checked files for FStarC
	mkdir -p $(PREFIX)/lib/fstar/fstarc/
	$(INSTALL_DIR) $(FSTAR_ROOT)/src $(PREFIX)/lib/fstar/fstarc/src
	$(INSTALL_DIR) fstarc.checked    $(PREFIX)/lib/fstar/fstarc/src.checked
	echo 'src'          > $(PREFIX)/lib/fstar/fstarc/fstar.include
	echo 'src.checked' >> $(PREFIX)/lib/fstar/fstarc/fstar.include

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

CP=cp -p # preserve timestamps
install: fstarc-bare fstarc-full libapp libplugin
	# Seems to need one final build?
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS)
	cd dune && dune install $(FSTAR_DUNE_OPTIONS) --prefix=$(abspath $(CURDIR)/out)
	# Install library
	$(CP) -t out/lib/fstar ulib/*.fst
	$(CP) -t out/lib/fstar ulib/*.fsti
	$(CP) -t out/lib/fstar ulib/fstar.include
	$(CP) -r -t out/lib/fstar ulib/experimental
	$(CP) -r -t out/lib/fstar ulib/legacy
	# Install checked files for the library
	mkdir -p out/lib/fstar/.checked
	$(CP) -r -t out/lib/fstar/.checked ulib.checked/*
	# Should we make sure checked files have newer timestamp?

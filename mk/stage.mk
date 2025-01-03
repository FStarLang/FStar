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

install: fstarc-bare fstarc-full libapp libplugin
	@# Seems to need one final build?
	cd dune && dune build $(FSTAR_DUNE_BUILD_OPTIONS)
	cd dune && dune install $(FSTAR_DUNE_OPTIONS) --prefix=$(abspath $(CURDIR)/out)
	@# Install library
	cp -H -p -r ulib out/lib/fstar/ulib
	echo 'ulib' >> out/lib/fstar/fstar.include
	rm -f out/lib/fstar/ulib/*.config.json
	@# Install checked files for the library
	mkdir -p out/lib/fstar/ulib/.checked
	cp -p ulib.checked/* out/lib/fstar/ulib/.checked/
	echo '.checked' >> out/lib/fstar/ulib/fstar.include
	@# Install get_fstar_z3 script
	cp ../.scripts/get_fstar_z3.sh $(CURDIR)/out/bin
	@# License and extra files
	cp ../LICENSE* $(CURDIR)/out/
	cp ../README.md $(CURDIR)/out/
	cp ../INSTALL.md $(CURDIR)/out/
	cp ../version.txt $(CURDIR)/out/

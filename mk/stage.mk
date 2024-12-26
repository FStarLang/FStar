FSTAR_ROOT ?= ..
include $(FSTAR_ROOT)/mk/common.mk

# We cannot simply use --release as that implies `--root .`, and we are explictly
# changing it. Maybe we can just chdir instead?
FSTAR_DUNE_RELEASE_OPTIONS :=
FSTAR_DUNE_RELEASE_OPTIONS += --ignore-promoted-rules
FSTAR_DUNE_RELEASE_OPTIONS += --no-config
FSTAR_DUNE_RELEASE_OPTIONS += --profile release
FSTAR_DUNE_RELEASE_OPTIONS += --always-show-command-line
FSTAR_DUNE_RELEASE_OPTIONS += --promote-install-files
FSTAR_DUNE_RELEASE_OPTIONS += --require-dune-project-file
FSTAR_DUNE_RELEASE_OPTIONS += --ignore-lock-dir
FSTAR_DUNE_RELEASE_OPTIONS += --default-target @install

ifeq ($(V),)
FSTAR_DUNE_OPTIONS += --no-print-directory
FSTAR_DUNE_OPTIONS += --display=quiet
endif

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)
ifeq ($(FSTAR_DUNE_RELEASE),1)
FSTAR_DUNE_BUILD_OPTIONS += $(FSTAR_DUNE_RELEASE_OPTIONS)
endif

.NOTPARALLEL:
# Sorry, but dune seems to get confused when its OCAMLPATH is changing

.PHONY: _force
_force:

fstarc-bare: _force
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS) fstarc-bare

fstarc-full: _force
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS) fstarc-full

libapp: _force
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS) libapp

libplugin: _force
	dune build --root=dune $(FSTAR_DUNE_BUILD_OPTIONS) libplugin

clean: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=dune
	rm -rf out

CP=cp -p # preserve timestamps
install: fstarc-bare fstarc-full libapp libplugin
	# Seems to need one final build?
	dune build $(FSTAR_DUNE_BUILD_OPTIONS) --root=dune
	dune install $(FSTAR_DUNE_OPTIONS) --root=dune --prefix=$(CURDIR)/out
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

# This makefile is for OCaml source distributions and is
# modeled after stage{1,2}/Makefile, but
# 1- is standalone, does use common.mk or others
# 2- does not install the library as it will not be there on
#    OCaml source distributions
#
# FSTAR_DUNE_OPTIONS += --no-print-directory
# FSTAR_DUNE_OPTIONS += --display=quiet

FSTAR_DUNE_BUILD_OPTIONS := $(FSTAR_DUNE_OPTIONS)

.NOTPARALLEL:
# Sorry, but dune seems to get confused when its OCAMLPATH is changing

.DEFAULT_GOAL:= all

.PHONY: _force
_force:

fstar-bare: bare/bin/fstar.exe
bare/bin/fstar.exe: _force
	dune build $(FSTAR_DUNE_BUILD_OPTIONS) --root=bare
	dune install --root=bare --prefix=$(CURDIR)/out fstar-guts
	dune install --root=bare --prefix=$(CURDIR)/out fstarc-bare

fstar: full/bin/fstar.exe
full/bin/fstar.exe: fstar-bare _force
	env OCAMLPATH="$(CURDIR)/out/lib" \
	  dune build --root=full $(FSTAR_DUNE_BUILD_OPTIONS)
	dune install --root=full --prefix=$(CURDIR)/out
	# Install library (cp -u: don't copy unless newer)
	mkdir -p out/ulib
	cp -u -t out/ulib ulib/*.fst
	cp -u -t out/ulib ulib/*.fsti
	cp -u -t out/ulib ulib/fstar.include
	cp -u -r -t out/ulib ulib/experimental
	cp -u -r -t out/ulib ulib/legacy

fstarlib: _force
	dune build   --root=fstarlib $(FSTAR_DUNE_BUILD_OPTIONS)
	dune install --root=fstarlib --prefix=$(CURDIR)/out
	# Install checked files for the library
	mkdir -p out/ulib/.cache

fstar-pluginlib: fstarlib _force
	env OCAMLPATH="$(CURDIR)/out/lib" \
	  dune build --root=fstar-pluginlib $(FSTAR_DUNE_BUILD_OPTIONS)
	dune install --root=fstar-pluginlib --prefix=$(CURDIR)/out

clean: _force
	dune clean $(FSTAR_DUNE_OPTIONS) --root=bare
	dune clean $(FSTAR_DUNE_OPTIONS) --root=full
	dune clean $(FSTAR_DUNE_OPTIONS) --root=fstarlib
	dune clean $(FSTAR_DUNE_OPTIONS) --root=fstar-pluginlib
	rm -rf inst
	rm -rf out

all: fstar fstarlib fstar-pluginlib

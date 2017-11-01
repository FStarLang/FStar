all: verify-all

# Makefile.verify has been split off because it is the actual
# Makefile that is distributed in the binary package. This
# Makefile here is not.
include Makefile.verify

include ml/Makefile.include

REALIZED=$(addsuffix .fst, $(NOEXTRACT_MODULES))

FSTARLIB_MODULES=$(filter-out $(REALIZED) FStar.Crypto.fst FStar.Tcp.fst FStar.Reflection.% FStar.Tactics.%,$(wildcard FStar.*.fst FStar.*.fsti))

FSTAR_TAC_LIB_MODULES=$(filter-out $(REALIZED),$(wildcard FStar.Reflection.*.fst FStar.Reflection.*.fsti FStar.Tactics.*.fst FStar.Tactics.*.fsti))

FSTAR_TAC_LIB_DROPPED_FST=$(FSTAR_TAC_LIB_MODULES:.fst=)
FSTAR_TAC_LIB_DROPPED_EXTENSIONS=$(FSTAR_TAC_LIB_DROPPED_FST:.fsti=)
FSTAR_TAC_LIB_EXTRACT=$(addprefix --extract_module ,$(sort $(FSTAR_TAC_LIB_DROPPED_EXTENSIONS)))

../bin/fstar.ocaml:
	make -C ../src/ocaml-output

fstarlib.mgen: *.fst *.fsti ../bin/fstar.ocaml
	mkdir -p ml/extracted
	$(FSTAR) --expose_interfaces --lax --codegen OCaml --odir ml/extracted $(FSTAR_DEFAULT_ARGS) $(FSTARLIB_MODULES)
	cp ../src/ocaml-output/FStar_Pervasives.ml ml/extracted
	touch fstarlib.mgen

FSTARLIB_LEFTOVERS=$(shell python fstarlib_leftovers.py +ml +ml/extracted -../bin/fstar-compiler-lib/)
fstartaclib.mgen: fstarlib.mgen
	mkdir -p tactics_ml/extracted
	$(FSTAR) --expose_interfaces --lax --codegen tactics --odir tactics_ml/extracted $(FSTAR_DEFAULT_ARGS) $(FSTAR_TAC_LIB_EXTRACT) $(FSTAR_TAC_LIB_MODULES)
	mkdir -p tactics_ml/fstarlib_leftovers
	cp $(FSTARLIB_LEFTOVERS) tactics_ml/fstarlib_leftovers
	touch fstartaclib.mgen

######################################################
# OCaml extraction of fstarlib and fstar-tactics-lib #
######################################################

# relative path to build directory, which is ulib/ml/_build
OCAMLPATH=../../../bin/

FSTAR_OCAMLBUILD_EXTRAS ?= -cflag -g
OCAMLBUILD=cd ../ && OCAMLPATH="$(OCAMLPATH)" ocamlbuild $(FSTAR_OCAMLBUILD_EXTRAS) -use-ocamlfind

FSTARLIB_OCAMLBUILD=$(OCAMLBUILD) -build-dir ulib/ml/_build \
  -I ulib/ml \
  -I ulib/ml/extracted

TACLIB_OCAMLBUILD=$(OCAMLBUILD) -build-dir ulib/tactics_ml/_build \
  -I ulib/tactics_ml/ \
  -I ulib/tactics_ml/extracted \
  -I ulib/tactics_ml/fstarlib_leftovers

ml/fstarlib.mllib: fstarlib.mgen $(wildcard ml/*.ml ml/extracted/*.ml)
	./gen_mllib.sh ml ml/extracted > $@

# Please don't create an empty fstartactics.ml: ocamlbuild < 0.11 gives higher
# priority to its cmx -> cmxs rule than to the cmxa -> cmx one, so an empty
# fstartactics.ml will yield an empty fstarlib.cmxs (unless you add a .mldylib).
# (see `https://github.com/ocaml/ocamlbuild/releases/tag/0.11.0')
# ---
# Having to isolate fstarlib_leftovers is unpleasant.  Ideally, we'd much rather
# dynlink fstarlib into the compiler before dynlinking fstartaclib.  But doing
# this naively is causes random segfaults, bus errors, and OOM errors coming
# from the GC.  We (CPC, VD) surmise the issue stems from loading the same
# modules twice, once from the compiler and once from fstarlib (the compiler
# relies on some realized files from ulib/ml).  Our workaround is to include in
# fstartaclib all fstarlib modules not already in the compiler.
TACLIB_ML=$(wildcard tactics_ml/*.ml tactics_ml/extracted/*.ml tactics_ml/fstarlib_leftovers/*.ml)
tactics_ml/fstartaclib.mllib: fstartaclib.mgen $(TACLIB_ML)
	./gen_mllib.sh tactics_ml tactics_ml/extracted tactics_ml/fstarlib_leftovers > $@

FSTARLIB_OBJECTS=fstarlib.a fstarlib.cma fstarlib.cmxs fstarlib.cmxa
TACLIB_OBJECTS=fstartaclib.cma fstartaclib.cmxs fstartaclib.cmxa

_fstarlib: ml/fstarlib.mllib
	$(FSTARLIB_OCAMLBUILD) $(FSTARLIB_OBJECTS)
_fstartaclib: tactics_ml/fstartaclib.mllib
	$(TACLIB_OCAMLBUILD) $(TACLIB_OBJECTS)

$(FSTARLIB_OBJECTS): _fstarlib
$(TACLIB_OBJECTS): _fstartaclib

FSTARLIB_DIR=../bin/fstarlib/
TACLIB_DIR=../bin/fstar-tactics-lib/

FSTARLIB_OUTPUTS=$(addprefix ml/_build/ulib/ml/, \
	*.cmi extracted/*.cmi $(FSTARLIB_OBJECTS))
TACLIB_OUTPUTS=$(addprefix tactics_ml/_build/ulib/tactics_ml/, \
	*.cmi fstarlib_leftovers/*.cmi extracted/*.cmi $(TACLIB_OBJECTS))

install-fstarlib: $(FSTARLIB_OBJECTS)
	mkdir -p $(FSTARLIB_DIR)
	cp $(FSTARLIB_OUTPUTS) $(FSTARLIB_DIR)
install-fstar-tactics: $(TACLIB_OBJECTS)
	mkdir -p $(TACLIB_DIR)
	cp $(TACLIB_OUTPUTS) $(TACLIB_DIR)

clean: basic_clean
	rm -f *.mgen
	rm -fr ml/extracted tactics_ml/extracted tactics_ml/fstarlib_leftovers
	rm -f ml/*.mllib tactics_ml/*.mllib tactics_ml/*.mldylib *~
	rm -f $(FSTARLIB_DIR)/*.cm[aiox]
	rm -f $(FSTARLIB_DIR)/*.cmx[as]
	rm -f $(TACLIB_DIR)/*.cm[aiox]
	rm -f $(TACLIB_DIR)/*.cmx[as]
	rm -rf ml/_build tactics_ml/_build # ← ocamlbuild -clean does not work on Cygwin

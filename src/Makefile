# -*- Makefile -*-
include Makefile.config
export FSTAR_HOME # because of the recursive calls to `make`

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

.PHONY: clean boot ocaml

$(BIN)/fstar.exe:
	+$(MAKE) -C ocaml-output all

clean: clean-ocaml

# --------------------------------------------------------------------
# Bootstrapping in OCaml: The main logic is in Makefile.boot.
# --------------------------------------------------------------------

clean_boot:
	rm -rf .cache.boot
	rm -f .depend

# --------------------------------------------------------------------------------
# Now we have some make targets wrap calls to other makefiles,
# Notably, Makefile.boot, to extract ocaml from the compiler sources
# And ocaml-output/Makefile, to actually build the compiler in OCaml
# --------------------------------------------------------------------------------
ocaml:
	$(Q)+$(MAKE) -f Makefile.boot all-ml

fstar-ocaml: ocaml
	+$(MAKE) $(BIN)/fstar.exe

# Fastest way to refresh the snapshot (if it works)
ocaml-fstar-ocaml: $(BIN)/fstar.exe
	+$(MAKE) ocaml
	+$(MAKE) $(BIN)/fstar.exe

clean-ocaml: clean_boot
	+$(MAKE) -C ocaml-output clean

# Very aggressive cleaning: remove all extracted files
clean_extracted:
	rm -f ocaml-output/FStar_*.ml

rebuild:
	+$(MAKE) ocaml
	+$(MAKE) -C ../ulib clean_ocaml
	+$(MAKE) -C ocaml-output
	+$(MAKE) -C ../ulib rebuild
# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------
utest:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions

# The first tests have to be performed sequentially (but each one may use some parallelism)
utest-prelude: $(BIN)/fstar.exe
	+$(MAKE) clean_extracted   #ensures that there is no leftover from previous extraction
	+$(MAKE) fstar-ocaml       #extract the compiler again and build the result
	+$(MAKE) ocaml-unit-tests  #run the unit tests
	+$(MAKE) .fstarlib
	+$(MAKE) ulib-in-fsharp    #build ulibfs

ocaml-unit-tests:
	$(BIN)/tests.exe

ulib-in-fsharp: $(BIN)/fstar.exe
	$(MAKE) -C ../ulib ulib-in-fsharp

# Getting parallelism from this target
uregressions: ulib-extra tutorial utests uexamples

.PHONY: uregressions-raw
uregressions-raw: ulib-extra tutorial-raw utests-raw uexamples-raw

# Getting parallelism from this target as well
# This is a hook for nightly builds (on Linux)
# But, at the moment, it tests the same files as get tested on every push
# We may add more nightly tests here in the future
uregressions-ulong: uregressions

.PHONY: uregressions-ulong-raw
uregressions-ulong-raw: uregressions-raw

# This is not optimal, since if some dependencies
# of fstarlib change we will not rebuild. However
# simply calling the install-fstar-tactics rule
# will unconditionally reinstall everything,
# which is also not good.
.fstarlib: $(FSTARLIB_DIR)/fstarlib.cmxs
	touch $@

$(FSTARLIB_DIR)/fstarlib.cmxs:
	+$(MAKE) -C ../ulib/ml
	+$(MAKE) -C ../ulib install-fstar-tactics
	+$(MAKE) -C ../ulib

ulib-extra:
	+$(MAKE) -C ../ulib extra

tutorial: .fstarlib
	+$(MAKE) $@-raw

.PHONY: tutorial-raw
tutorial-raw:
	+$(MAKE) -C ../doc/tutorial regressions
	+$(MAKE) -C ../doc/book/code

utests: .fstarlib
	+$(MAKE) $@-raw

.PHONY: utests-raw
utests-raw:
	+$(MAKE) -C ../tests all

uexamples: .fstarlib
	+$(MAKE) $@-raw

.PHONY: uexamples-raw
uexamples-raw:
	+$(MAKE) -C ../examples all
	+$(MAKE) -C ../examples native_tactics.all
	+$(MAKE) -C ../examples semiring.all

ulong:
	+$(MAKE) utest-prelude
	+$(MAKE) uregressions-ulong

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .


# -*- Makefile -*-
include Makefile.config
export FSTAR_HOME # because of the recursive calls to `make`

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

.PHONY: clean boot ocaml

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

clean-ocaml: clean_boot
	+$(MAKE) -C ocaml-output clean

# --------------------------------------------------------------------
# Testing
# --------------------------------------------------------------------

ocaml-unit-tests:
	$(BIN)/tests.exe

ulib-in-fsharp:
	$(MAKE) -C ../ulib ulib-in-fsharp

# Getting parallelism from this target
.PHONY: uregressions
uregressions: ulib-extra tutorial utests uexamples

# Getting parallelism from this target as well
# This is a hook for nightly builds (on Linux)
# But, at the moment, it tests the same files as get tested on every push
# We may add more nightly tests here in the future
.PHONY: uregressions-ulong
uregressions-ulong: uregressions

ulib-extra:
	+$(MAKE) -C ../ulib extra

tutorial:
	+$(MAKE) -C ../doc/tutorial regressions
	+$(MAKE) -C ../doc/book/code

utests:
	+$(MAKE) -C ../tests all

uexamples:
	+$(MAKE) -C ../examples all
	+$(MAKE) -C ../examples native_tactics.all
	+$(MAKE) -C ../examples semiring.all

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .


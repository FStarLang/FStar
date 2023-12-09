# -*- Makefile -*-
include Makefile.config
export FSTAR_HOME # because of the recursive calls to `make`

# --------------------------------------------------------------------
.SUFFIXES:
MAKEFLAGS += --no-builtin-rules

.PHONY: clean boot ocaml

all:
	$(error src/Makefile: Need to specify a rule)

clean: clean-ocaml

# --------------------------------------------------------------------
# Bootstrapping in OCaml: The main logic is in Makefile.boot.
# --------------------------------------------------------------------

clean_boot:
	rm -rf .cache.boot
	rm -f ._depend
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

.PHONY: ocaml-unit-tests
ocaml-unit-tests:
	$(BIN)/fstar_tests.exe

.PHONY: ulib-in-fsharp
ulib-in-fsharp:
	$(MAKE) -C ../ulib ulib-in-fsharp

.PHONY: uregressions
uregressions: ulib-extra tutorial utests uexamples

# This is a hook for nightly builds (on Linux)
# But, at the moment, it tests the same files as get tested on every push
# We may add more nightly tests here in the future
.PHONY: uregressions-ulong
uregressions-ulong: uregressions

.PHONY: ulib-extra
ulib-extra:
	+$(MAKE) -C ../ulib extra

.PHONY: tutorial
tutorial:
	+$(MAKE) -C ../doc/tutorial regressions
	+$(MAKE) -C ../doc/book/code

.PHONY: utests
utests:
	+$(MAKE) -C ../tests all

.PHONY: uexamples
uexamples: examples-all

.PHONY: examples-all
examples-all:
	+$(MAKE) -C ../examples all

ctags:
	ctags --exclude=boot_fsts --exclude=boot_fstis --exclude=ocaml-output -R .

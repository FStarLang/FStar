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
	$(Q)rm -rf .cache.boot
	$(Q)rm -f ._depend
	$(Q)rm -f .depend

# --------------------------------------------------------------------------------
# Now we have some make targets wrap calls to other makefiles,
# Notably, Makefile.boot, to extract ocaml from the compiler sources
# And ocaml-output/Makefile, to actually build the compiler in OCaml
# --------------------------------------------------------------------------------
ocaml:
	# Note: we add all-checked in support of Pulse and other
	# projects that code against compiler internals, to make
	# sure we generate all possible .checked files, instead of
	# just the ones needed for extracting.
	$(Q)+$(MAKE) -f Makefile.boot all-ml all-checked

clean-ocaml: clean_boot
	+$(Q)$(MAKE) -C ocaml-output clean

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
uregressions: tutorial utests uexamples

.PHONY: tutorial
tutorial: book-code tutorial-old

.PHONY: book-code
book-code:
	+$(MAKE) -C ../doc/book/code

.PHONY: tutorial-old
tutorial-old:
	+$(MAKE) -C ../doc/old/tutorial regressions

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

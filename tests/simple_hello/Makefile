# This is probably the simplest makefile to build an F* application, and can be adapted easily.
# We should not need to include any other internal makefiles.
# Dune also works fine under the --ocamlenv.

# In this repository, we inherit this variable. Externally we
# just take fstar.exe from the PATH.
FSTAR_EXE ?= fstar.exe

all: Hello.exe.test

# In a Cygwin build, somehow this dll is not the search path (copying it
# to this directory does make the test work). Just skip it for now.
# $ ./Hello.byte
# Fatal error: cannot load shared library dllzarith
# Reason: No such file or directory
ifneq ($(OS),Windows_NT)
all: Hello.byte.test
endif

# The same program through the reference-counted C backend.
all: Hello.cherry.test

Hello.%.test: Hello.%
	./$< | grep "Hello F\*!"

%.checked: %
	$(FSTAR_EXE) $< --cache_checked_modules

%.ml: %.fst.checked
	$(FSTAR_EXE) --codegen OCaml --custard_entry_module $* $< -o $@

%.exe: %.ml
	$(FSTAR_EXE) --ocamlopt $< -o $@

%.byte: %.ml
	$(FSTAR_EXE) --ocamlc $< -o $@

CHERRY_INC = $(shell $(FSTAR_EXE) --locate_lib)/ulib/c
CHERRY_CC ?= $(CC)
%.c: %.fst.checked
	$(FSTAR_EXE) --codegen Cherry --custard_main $* $< -o $@

%.cherry: %.c
	$(CHERRY_CC) -I$(CHERRY_INC) $< $(CHERRY_INC)/cherry.c -o $@

clean:
	rm -f *.ml *.c *.h *.exe *.byte *.cherry *.cm* *.o *.checked

# Keep intermediate files
.SECONDARY:

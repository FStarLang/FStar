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

Hello.%.test: Hello.%
	./$< | grep "Hello F\*!"

%.checked: %
	$(FSTAR_EXE) $< --cache_checked_modules

%.ml: %.fst.checked
	$(FSTAR_EXE) --codegen OCaml $<

%.exe: %.ml
	$(FSTAR_EXE) --ocamlopt $< -o $@

%.byte: %.ml
	$(FSTAR_EXE) --ocamlc $< -o $@

clean:
	rm -f *.ml *.exe *.byte *.cm* *.o

# Keep intermediate files
.SECONDARY:

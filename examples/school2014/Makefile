.PHONY: all verify-% __force__

ifeq ($(OS),Windows_NT)
RUNTIME =
MSBUILD = msbuild
else
RUNTIME = mono
MSBUILD = xbuild
endif

FSTAR_HOME = ../..

STDLIB = $(addprefix $(FSTAR_HOME)/lib/, $(LIB_FILES))
FSTAR      = $(RUNTIME) ../../bin/fstar.exe --fstar_home $(FSTAR_HOME) $(STDLIB)

EXERCISES =\
  ex7a-stlc-typed-step\
  ex7b-stlc-pairs\
  ex7c-stlc-let\
  ex7d-stlc-eval

all: $(EXERCISES:%=verify-%)

verify-%: __force__
	-$(FSTAR) $*.fst

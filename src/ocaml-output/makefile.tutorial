.PHONY: all verify-% __force__

ifeq ($(OS),Windows_NT)
SUFFIX = .exe
else
SUFFIX =
endif

# This will be called from subdirs
FSTAR_HOME = ../../..

STDLIB = $(addprefix $(FSTAR_HOME)/lib/, $(LIB_FILES))
FSTAR  = $(FSTAR_HOME)/bin/fstarml$(SUFFIX) --fstar_home $(FSTAR_HOME) $(STDLIB)

EXERCISES =\
  ex1a-safe-read-write\
  ex2a-can-read-write-types\
  ex3a-factorial-types\
  ex3b-fibonacci\
  ex3c-fibonacci\
  ex4a-append-intrinsic\
  ex4b-append-extrinsic\
  ex4c-mem\
  ex4d-reverse\
  ex4e-find\
  ex4f-fold-left\
  ex4g-hd-tl\
  ex4h-nth\
  ex7a-stlc-typed-step\
  ex7b-stlc-pairs\
  ex7c-stlc-let\
  ex7d-stlc-eval\

all: $(EXERCISES:%=verify-%)

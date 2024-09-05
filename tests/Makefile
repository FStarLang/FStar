FSTAR_HOME=..
export OTHERFLAGS += --ext context_pruning
include ../examples/Makefile.include

ALL_TEST_DIRS += bug-reports
ALL_TEST_DIRS += coercions
ALL_TEST_DIRS += error-messages
ALL_TEST_DIRS += friends
ALL_TEST_DIRS += ide
ALL_TEST_DIRS += incl
ALL_TEST_DIRS += machine_integers
ALL_TEST_DIRS += micro-benchmarks
ALL_TEST_DIRS += prettyprinting
ALL_TEST_DIRS += projectors
ALL_TEST_DIRS += restricted_includes
ALL_TEST_DIRS += semiring
ALL_TEST_DIRS += struct
ALL_TEST_DIRS += tactics
ALL_TEST_DIRS += typeclasses
ALL_TEST_DIRS += vale
ALL_TEST_DIRS += hacl
HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))
ALL_TEST_DIRS += extraction
endif

all: $(addsuffix .all, $(ALL_TEST_DIRS))
clean: $(addsuffix .clean, $(ALL_TEST_DIRS))

%.all: %
	+$(MAKE) -C $^ all

%.clean: %
	+$(MAKE) -C $^ clean

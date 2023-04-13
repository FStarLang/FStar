all: verify # counter llist2 llist3

# assuming share/steel/examples/steel
STEEL_HOME ?= ../../../..

EXCLUDE_FILES=ParDivWP.fst Semantics.WP.fst $(wildcard DList*)

include $(STEEL_HOME)/share/steel/Makefile.include

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))

OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIRECTORY) -w -31
counter: _output/OWGCounter.ml OWGCounterTest.ml | verify
	$(OCAMLOPT) -thread -o counter.exe $^

else

counter:

endif

ifdef KRML_HOME

llist2: verify
	+$(MAKE) -C $@

llist3: verify
	+$(MAKE) -C $@

else

llist2:

llist3:

endif

.PHONY: counter llist2 llist3

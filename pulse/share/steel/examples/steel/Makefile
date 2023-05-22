all: verify counter llist2 llist3

# assuming share/steel/examples/steel
STEEL_HOME ?= ../../../..

EXCLUDE_FILES=ParDivWP.fst Semantics.WP.fst $(wildcard DList*)

include $(STEEL_HOME)/share/steel/Makefile.include

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))

OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIRECTORY) -w -31
counter: OWGCounter.fst.checked
	+$(MAKE) -C OWGCounter

else

counter:

endif

ifdef KRML_HOME

llist2: Selectors.LList2.fst.checked
	+$(MAKE) -C $@

llist3: Selectors.LList3.fst.checked
	+$(MAKE) -C $@

else

llist2:

llist3:

endif

.PHONY: counter llist2 llist3

ALL := stlc bool_refinement dependent_bool_refinement

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

all:
	+$(MAKE) examples

examples: $(addsuffix .all, $(ALL))

%.all: %
	+$(MAKE) -C $^ all

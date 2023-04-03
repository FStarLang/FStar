ALL := stlc bool_refinement dependent_bool_refinement mini_steel

all:
	+$(MAKE) examples

examples: $(addsuffix .all, $(ALL))

%.all: %
	+$(MAKE) -C $^ all

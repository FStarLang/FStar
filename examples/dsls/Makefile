ALL := stlc bool_refinement mini_steel
  #dependent_bool_refinement

all:
	+$(MAKE) -C core all
	+$(MAKE) examples

examples: $(addsuffix .all, $(ALL))

%.all: %
	+$(MAKE) -C $^ all

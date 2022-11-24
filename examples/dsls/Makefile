ALL := stlc mini_steel
  #bool_refinement \
  #dependent_bool_refinement

all:
	+$(MAKE) -C core all
	+$(MAKE) examples

examples: $(addsuffix .all, $(ALL))

%.all: %
	+$(MAKE) -C $^ all

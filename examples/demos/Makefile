DIRS=low-star

all: $(addsuffix .all, $(DIRS))

%.all: %
	+$(MAKE) -C $^ all

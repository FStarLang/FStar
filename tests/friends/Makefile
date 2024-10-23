# FSTAR_ROOT ?= ../..
# include $(FSTAR_ROOT)/mk/test.mk

DIRS=1 2 3

all: $(addsuffix .all, $(DIRS))
clean: $(addsuffix .clean, $(DIRS))

%.all: %
	+$(MAKE) -C $* all

%.clean: %
	+$(MAKE) -C $* clean

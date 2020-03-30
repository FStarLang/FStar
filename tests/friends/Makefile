DIRS=1 2 3

all: $(addsuffix .all, $(DIRS))
clean: $(addsuffix .clean, $(DIRS))

FSTAR_HOME=../..
include $(FSTAR_HOME)/examples/Makefile.include

%.all: %
	+$(MAKE) -C $* all

%.clean: %
	+$(MAKE) -C $* clean

DIRS=1 2 3

all: $(addsuffix .ver, $(DIRS))

FSTAR_HOME=../..
include $(FSTAR_HOME)/examples/Makefile.include

%.ver:
	+$(MAKE) -C $* verify-all

DIRS=1 2 3

all: $(addsuffix .ver, $(DIRS))

FSTAR_HOME=../..
include ../Makefile.include



%.ver:
	$(MAKE) -C $* verify-all

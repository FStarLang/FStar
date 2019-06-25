DIRS=1 2 3

FSTAR_HOME=../../..
include ../../Makefile.include

all-dirs: $(addsuffix .ver, $(DIRS))

%.ver:
	$(MAKE) -C $* verify-all

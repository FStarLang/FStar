FSTAR_HOME=../..
include ../Makefile.include

all: uall

uall:
	$(FSTAR) 2015/Problem01.fst

CFSTAR=$(subst CURRENT_DIR,examples/verifythis,$(CVERFSTAR))
all-cver: 
	$(CFSTAR) 2015/Problem01.fst

FSTAR_HOME=../..
include ../Makefile.include

VERFILES=\
	SimpleTest.fst

all:  ver

ver: $(VERFILES)
	$(SFSTAR) --codegen JavaScript --odir src  $^
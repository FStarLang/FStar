FSTAR_HOME=../..
include ../Makefile.include

all: $(patsubst %.fst,%.fst-ver,$(wildcard *.fst))

%.fst-ver:%.fst
	$(FSTAR) $^


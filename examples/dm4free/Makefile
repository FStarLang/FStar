FSTAR_HOME=../..
OTHERFLAGS=
include ../Makefile.include

all: uall

uall: NewPrims.uver

%.uver: %.fst
	$(FSTAR) --verify_module $* $^

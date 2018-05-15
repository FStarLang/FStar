FSTAR_HOME=../..
include ../Makefile.include

OTHERFLAGS+=--include ../tactics

all:uall

uall: shallow examples

all: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver	\
	SL.Shallow.uver Examples.uver SL.Examples.uver		\
	SL.ExamplesAuto.uver

#Excludes extracted interfaces for these examples
SL.Examples.uver: OTHERFLAGS+= --use_extracted_interfaces false
SL.ExamplesAuto.uver: OTHERFLAGS+= --use_extracted_interfaces false --cache_off

%.fst-in:
	@echo $(OTHERFLAGS)

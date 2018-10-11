FSTAR_HOME=../..
include ../Makefile.include

OTHERFLAGS+=--include ../tactics

all: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver	\
	SL.Shallow.uver Examples.uver SL.ExamplesAuto.custom SL.Examples.custom

SL.Examples.custom: OTHERFLAGS+=--cache_off
SL.ExamplesAuto.custom: OTHERFLAGS+=--cache_off

#Excludes extracted interfaces for these examples
%.custom: %.fst
	$(FSTAR) --use_extracted_interfaces true $^

%.fst-in:
	@echo $(OTHERFLAGS)

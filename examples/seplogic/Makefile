FSTAR_HOME=../..
include ../Makefile.include

OTHERFLAGS+=--include ../tactics

all: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver	\
	SL.Shallow.uver Examples.uver \
	SL.ExamplesAuto.custom

#SL.Examples.uver --disabling for now, since it takes ~18mins on Linux CI

SL.ExamplesAuto.custom: OTHERFLAGS+=--cache_off

#Excludes extracted interfaces for these examples
%.custom: %.fst
	$(FSTAR) --use_extracted_interfaces true $^

%.fst-in:
	@echo $(OTHERFLAGS)

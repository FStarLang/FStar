FSTAR_HOME=../..
include ../Makefile.include

OTHERFLAGS+=--include ../tactics

all: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver	\
	SL.Shallow.uver Examples.custom SL.Examples.custom		\
	SL.ExamplesAuto.custom

#Excludes 2-phase tc and extracted interfaces
%.custom: %.fst
	$(FSTAR) --use_two_phase_tc false --use_extracted_interfaces false $^

%.fst-in:
	@echo $(OTHERFLAGS)

include ../Makefile.include

OTHERFLAGS+=--include ../tactics --compat_pre_core 1

all: SepLogic.Heap.uver Shallow.uver SL.Heap.uver SL.Effect.uver	\
	SL.Shallow.uver Examples.uver \
	SL.ExamplesAuto.custom

#SL.Examples.uver disable for now
SL.ExamplesAuto.custom: OTHERFLAGS+=--cache_off

#Excludes extracted interfaces for these examples
%.custom: %.fst
	$(FSTAR) $^

%.fst-in:
	@echo $(OTHERFLAGS)

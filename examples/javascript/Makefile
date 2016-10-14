FSTAR_HOME=../..
include ../Makefile.include

VERFILES=\
	SimpleTest.fst\
	#PatternMatching.fst\
	#TypesPM.fst\
	#ListPM.fst

FSTAR_REALIZED_MODULES=All BaseTypes Char Float Heap Int8 Int16 Int32 Int64 \
  UInt8 UInt16 UInt32 UInt64 Int_Cast IO List Option Set ST String HyperHeap HyperStack \
  HST Buffer Mul FunctionalExtensionality PredicateExtensionality PropositionalExtensionality\
  TSet

FSTAR_DEFAULT_ARGS=$(addprefix --no_extract FStar.,$(FSTAR_REALIZED_MODULES))

all:  ver

ver: $(VERFILES)  
	$(SFSTAR) $(FSTAR_DEFAULT_ARGS) --codegen JavaScript --odir src > xxxx.txt $^
	#$(SFSTAR) $(FSTAR_DEFAULT_ARGS) --codegen FSharp --odir fs $^
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
  TSet Array

FSTAR_DEFAULT_ARGS=$(addprefix --no_extract FStar.,$(FSTAR_REALIZED_MODULES))

FLOW_DIR = $(wildcard js/*.flow)

JS_DIR = $(FLOW_DIR:%.flow=%.js)

all: ver pp-print
                       
js/%.js: js/%.flow
	esformatter --plugins=esformatter-flow $< > $@
	rm -f $<

pp-print: $(JS_DIR)

ver:  	$(VERFILES) 
	mkdir -p js
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) --codegen JavaScript --odir js --lax  $^	
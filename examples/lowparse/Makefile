FSTAR_HOME=../..
include ../Makefile.include

FST_FILES := \
	LowParse.Bytes.fst \
	LowParse.Spec.Base.fst \
	LowParse.SLow.Base.fst \
	LowParse.Spec.Combinators.fst \
	LowParse.SLow.Combinators.fst \


OTHERFLAGS+=$(addprefix --include , $(INCLUDE_PATHS))

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)

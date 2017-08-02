FSTAR_HOME=../..
include ../Makefile.include

FST_FILES= Slice.fst \
	   KeyValue.fst \
	   PureParser.fst \
	   PureValidator.fst \
	   Validator.fst \
	   SkipChecksParsing.fst \
	   ValidatedParser.fst \
	   PureEncoder.fst \
	   Serializer.fst \
	   EnumParsing.fst

EXTRACT_FILES= 	Validator.fst \
		ValidatedParser.fst \
		Serializer.fst \
		EnumParsing.fst

FSTAR_INCLUDE_PATHS=--include ../../../kremlin/kremlib

OTHERFLAGS+=$(FSTAR_INCLUDE_PATHS)

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(FSTAR_INCLUDE_PATHS)


extract-c: $(EXTRACT_FILES)
	krml -skip-compilation -warn-error +11 $(EXTRACT_FILES)

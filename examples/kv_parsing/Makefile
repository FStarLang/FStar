FSTAR_HOME=../..
include ../Makefile.include

FST_FILES :=	Slice.fst \
		KeyValue.fst \
		Parsing.fst \
		Serializing.fst \
		PureParser.fst \
		PureValidator.fst \
		Validator.fst \
		ValidatedParser.fst \
		ValidatedAccess.fst \
		PureEncoder.fst \
		Serializer.fst \
		EnumParsing.fst \
		VectorParsing.fst

EXTRACT_FILES := Validator.fst \
		 ValidatedParser.fst \
		 ValidatedAccess.fst \
		 Serializer.fst \
		 EnumParsing.fst

FSTAR_INCLUDE_PATHS:=--include $(KREMLIN_HOME)/kremlib

OTHERFLAGS+=$(FSTAR_INCLUDE_PATHS)

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)


extract-c: $(EXTRACT_FILES)
	krml -skip-compilation -warn-error +11 $(EXTRACT_FILES)

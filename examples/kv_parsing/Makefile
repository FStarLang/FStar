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
	   Serializer.fst

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo "--include ../../../kremlin/kremlib"


extract-c: Serializer.fst Validator.fst ValidatedParser.fst
	krml -skip-compilation -warn-error +11 Serializer.fst Validator.fst ValidatedParser.fst

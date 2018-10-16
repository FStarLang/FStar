FSTAR_HOME=../..
include ../Makefile.include

FST_FILES :=	Slice.fst \
		Parsing.fst \
		Serializing.fst \
		IntegerParsing.fst \
		KeyValue.fst \
		PureParser.fst \
		PureValidator.fst \
		Validator.fst \
		ValidatedParser.fst \
		ValidatedAccess.fst \
		PureEncoder.fst \
		Serializer.fst \
		EnumParsing.fst \
		VectorParsing.fst

EXTRACT_FILES := IntegerParsing.fst \
		 Validator.fst \
		 ValidatedParser.fst \
		 ValidatedAccess.fst \
		 Serializer.fst \
		 EnumParsing.fst \
		 VectorParsing.fst

FSTAR_INCLUDE_PATHS:=--include $(KREMLIN_HOME)/kremlib --include $(KREMLIN_HOME)/kremlib/compat

OTHERFLAGS+=$(FSTAR_INCLUDE_PATHS) --z3rlimit_factor 4

all: $(FST_FILES:.fst=.uver)

%.fst-in:
	@echo $(OTHERFLAGS)


extract-c: $(EXTRACT_FILES)
	krml -skip-compilation -warn-error +11 $(EXTRACT_FILES)

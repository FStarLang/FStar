FSTAR_HOME=../..
FSTAR_FILES= LowParse.Bytes.fst LowParse.Bytes32.fst		  \
	     LowParse.Spec.Base.fst LowParse.SLow.Base.fst	  \
	     LowParse.Spec.Combinators.fst			  \
	     LowParse.SLow.Combinators.fst LowParse.Spec.Enum.fst \
	     LowParse.SLow.Enum.fst

all:
	mkdir -p $(CACHE_DIR)
	$(MAKE) verify-all

include ../Makefile.common

verify-all: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

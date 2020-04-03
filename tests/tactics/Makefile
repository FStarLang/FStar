FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)

all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES))) \
            Erasable.ml-cmp \
            $(CACHE_DIR)/Coercions1Phase.fst.checked

clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output

FSTAR_HOME=../..

FSTAR_FILES = $(wildcard *.fst *.fsti)
OTHERFLAGS += --ext context_pruning --z3rlimit_factor 2
all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

clean:
	rm -f .depend
	rm -rf _cache
	rm -rf _output

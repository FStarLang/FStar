FSTAR_HOME=../..

FSTAR_FILES=$(wildcard *.fst)

all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

clean:
	@echo "[CLEAN]"
	$(Q)rm -f .depend
	$(Q)rm -rf _cache
	$(Q)rm -rf _output

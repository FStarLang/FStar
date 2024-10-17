#
# This does nothing but the default validation as these are validation time test modules.
# Most are let _ = assert(...) which is extremely cool to test at validation time! 
# 

WARN_ERROR=--warn_error -321
FSTAR_HOME=../..
FSTAR_FILES=$(wildcard *.fst)
FSTAR_EXAMPLES=$(realpath ../../examples)
include $(FSTAR_EXAMPLES)/Makefile.include

all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

clean:
	$(call msg, "CLEAN")
	$(Q)rm -f .depend
	$(Q)rm -rf _cache
	$(Q)rm -rf _output

INCLUDE_PATHS=../tactics
EXCLUDED_FSTAR_FILES=
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))
OTHERFLAGS += --compat_pre_core 1

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

%.fst-in:
	@echo $(OTHERFLAGS) $(HINTS_EMNABLED) $(addprefix --include , $(INCLUDE_PATHS))

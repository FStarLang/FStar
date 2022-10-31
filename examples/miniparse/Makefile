
# Inspired from: ../tactics/Makefile

ifdef KRML_HOME
INCLUDE_PATHS+=$(KRML_HOME)/krmllib
endif
FSTAR_FILES=$(wildcard *.fst) $(wildcard *.fsti)

all: verify-all

$(CACHE_DIR):
	mkdir -p $(CACHE_DIR)

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

# TODO: use separate compilation here

ifdef KRML_HOME
miniparse: $(CACHE_DIR)
	 [ ! -f $(KRML_HOME)/krml ] || [ ! -x $(KRML_HOME)/krml ] || $(KRML_HOME)/krml -tmpdir miniparse -bundle 'MiniParse.\*' -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' MiniParseExample3.fst -skip-linking
else
miniparse:
endif

.PHONY: miniparse

%.fst-in:
	@echo $(OTHERFLAGS) $(addprefix --include , $(INCLUDE_PATHS))

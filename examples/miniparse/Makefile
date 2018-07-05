FSTAR_HOME=../..

# Inspired from: ../tactics/Makefile

KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
FSTAR_FILES=$(wildcard *.fst) $(wildcard *.fsti)

all: verify-all

$(CACHE_DIR):
	mkdir -p $(CACHE_DIR)

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

# TODO: use separate compilation here

ifdef KREMLIN_HOME
miniparse: $(CACHE_DIR)
	 [ ! -f $(KREMLIN_HOME)/krml ] || [ ! -x $(KREMLIN_HOME)/krml ] || $(KREMLIN_HOME)/krml -tmpdir miniparse -bundle 'MiniParse.\*' -drop 'FStar.Tactics.\*' -drop 'FStar.Reflection.\*' MiniParseExample.fst -skip-linking
else
miniparse:
endif

.PHONY: miniparse

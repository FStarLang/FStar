FSTAR_HOME=../..
KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=$(KREMLIN_HOME)/kremlib
FSTAR_FILES = $(wildcard *.fst)

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

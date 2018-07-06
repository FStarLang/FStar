FSTAR_HOME=../..
FSTAR_FILES=$(wildcard *.fst) $(wildcard *.fsti)

all:
	mkdir -p $(CACHE_DIR)
	$(MAKE) verify-all

include ../Makefile.common

verify-all: $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

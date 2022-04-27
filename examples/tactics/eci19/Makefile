FSTAR_HOME?=../../..
EXCLUDED_FSTAR_FILES=
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

OTHERFLAGS += --warn_error -274-321

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

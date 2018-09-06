FSTAR_HOME=../..
# KREMLIN_HOME?=$(FSTAR_HOME)/../Kremlin
INCLUDE_PATHS=../tactics
EXCLUDED_FSTAR_FILES=
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

native_bench1:
	$(FSTAR) --debug Loop2 --debug_level TCDeclTime Loop2.fst

native_bench2:
	rm -f FStar_Tactics_Typeclasses.*
	$(FSTAR) $(FSTAR_HOME)/ulib/FStar.Tactics.Typeclasses.fst --extract FStar.Tactics.Typeclasses --codegen Plugin
	$(FSTAR) Loop2.fst --timing --load FStar.Tactics.Typeclasses

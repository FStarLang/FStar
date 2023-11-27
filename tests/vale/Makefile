FSTAR_HOME=../..

OTHERFLAGS += \
--z3cliopt smt.QI.EAGER_THRESHOLD=100 \
--z3cliopt smt.CASE_SPLIT=3 \
--z3cliopt smt.arith.nl=false \
--smtencoding.elim_box true \
--smtencoding.l_arith_repr native \
--smtencoding.nl_arith_repr wrapped\
--max_fuel 1 \
--max_ifuel 1 \
--initial_ifuel 0

FSTAR_FILES=$(wildcard *.fst)

all: verify-all

include $(FSTAR_HOME)/examples/Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

clean:
	$(call msg, "CLEAN")
	$(Q)rm -f .depend
	$(Q)rm -rf _cache
	$(Q)rm -rf _output

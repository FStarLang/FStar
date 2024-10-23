FSTAR_ROOT ?= ../..
FSTAR_FILES=$(wildcard *.fst)
FSTAR_FILES:=$(filter-out X64.Poly1305.fst,$(FSTAR_FILES))
include $(FSTAR_ROOT)/mk/test.mk
all: verify-all

OTHERFLAGS += \
--z3cliopt smt.QI.EAGER_THRESHOLD=100 \
--z3cliopt smt.CASE_SPLIT=3 \
--z3cliopt smt.arith.nl=false \
--smtencoding.elim_box true \
--smtencoding.l_arith_repr native \
--smtencoding.nl_arith_repr wrapped\
--max_fuel 1 \
--max_ifuel 1 \
--initial_ifuel 0 \
--warn_error -350
# ^ 350: deprecated lightweight do notation

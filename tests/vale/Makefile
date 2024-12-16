FSTAR_FILES=$(wildcard *.fst)
FSTAR_FILES:=$(filter-out X64.Poly1305.fst,$(FSTAR_FILES))

OTHERFLAGS += \
--z3smtopt '(set-option :smt.qi.eager_threshold 100)' \
--z3smtopt '(set-option :smt.arith.nl false)' \
--smtencoding.elim_box true \
--smtencoding.l_arith_repr native \
--smtencoding.nl_arith_repr wrapped\
--max_fuel 1 \
--max_ifuel 1 \
--warn_error -350
# ^ 350: deprecated lightweight do notation

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

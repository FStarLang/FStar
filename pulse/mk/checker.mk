SRC := src/checker/
TAG := checker
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
ROOTS += lib/common/Pulse.Lib.Tactics.fsti
# ^ List files with plugins here

FSTAR_OPTIONS += --already_cached 'Prims,FStar'
FSTAR_OPTIONS += --include lib/common
FSTAR_OPTIONS += --smtencoding.elim_box true
FSTAR_OPTIONS += --z3smtopt '(set-option :smt.arith.nl false)'
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'

# This only verifies the checker; it is lax-checked again and extracted,
# together with the syntax extension, by mk/plugin.mk.

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := verify

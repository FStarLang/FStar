SRC := src/checker/
TAG := checker
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Plugin
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
ROOTS += lib/common/Pulse.Lib.Tactics.fsti
# ^ List files with plugins here

FSTAR_OPTIONS += --already_cached 'Prims,FStar'
FSTAR_OPTIONS += --include lib/common
FSTAR_OPTIONS += --proof_recovery # temporary, until universe branch lands
EXTRACT += --extract '-*,+Pulse,+PulseSyntaxExtension'
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := ocaml

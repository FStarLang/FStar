TAG := syntax_extension
SRC := src/syntax_extension
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Custard
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --with_fstarc
EXTRACT += --extract '-*,+PulseSyntaxExtension'
FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --include src/checker
FSTAR_OPTIONS += --include lib/common

DEPFLAGS += --already_cached 'Prims,FStarC,FStar'

# The Custard pipeline.  This unit sees both the compiler and the checker,
# so it links against both .cui files, in that order.
CUSTARD_UNIT    := PulseSyntaxExtension
CUSTARD_ROOT    := src/syntax_extension/PulseSyntaxExtension.ASTBuilder.fst \
                   src/syntax_extension/PulseSyntaxExtension.Printing.fst
CUSTARD_ENTRIES := --custard_entry PulseSyntaxExtension.ASTBuilder
CUSTARD_ENTRIES += --custard_entry PulseSyntaxExtension.Printing
CUSTARD_ENTRIES += --custard_entrypoints src/syntax_extension/custard-entrypoints.txt
CUSTARD_LINK     = $(FSTARC_CUI) build/checker.ml/PulseChecker.cui
CUSTARD_DEPS    := src/syntax_extension/custard-entrypoints.txt
CUSTARD_FLAGS   += --ext fly_deps=false

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := custard

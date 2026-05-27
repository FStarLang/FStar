TAG := syntax_extension
SRC := src/syntax_extension
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --with_fstarc
EXTRACT += --extract '-*,+PulseSyntaxExtension'
FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --include src/checker
FSTAR_OPTIONS += --include lib/common

DEPFLAGS += --already_cached 'Prims,FStarC,FStar'

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := ocaml

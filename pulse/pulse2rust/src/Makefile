PULSE_ROOT ?= ../..
include $(PULSE_ROOT)/mk/locate.mk

TAG := pulse2rust
SRC := .
CACHE_DIR := _cache
OUTPUT_DIR := ocaml/generated
CODEGEN := PluginNoLib
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --with_fstarc
EXTRACT += --extract '-*,+Pulse2Rust'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect

DEPFLAGS += --already_cached 'FStarC'

include $(PULSE_ROOT)/mk/boot.mk

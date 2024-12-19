PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/locate.mk

TAG := extraction
SRC := src/extraction
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Plugin
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src
FSTAR_OPTIONS += --include $(FSTAR_HOME)/src/.cache.boot
EXTRACT += --extract '-*,+ExtractPulse,+ExtractPulseC'
FSTAR_OPTIONS += --lax --MLish --MLish_effect FStarC.Compiler.Effect

DEPFLAGS += --already_cached 'FStarC'

include $(PULSE_ROOT)/mk/boot.mk

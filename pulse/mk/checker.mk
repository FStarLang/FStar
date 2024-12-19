SRC := src/checker/
TAG := checker
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Plugin
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --already_cached 'Prims,FStar'
EXTRACT += --extract '-*,+Pulse,+PulseSyntaxExtension'
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

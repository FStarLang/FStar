SRC := lib/common
CACHE_DIR := lib/pulse/_cache
OUTPUT_DIR := lib/pulse/_output
CODEGEN := NONE
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=common
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify # no extraction

SRC := lib/core
CACHE_DIR := build/lib.core.checked/
OUTPUT_DIR := build/lib.core.ml/
CODEGEN := NONE
FSTAR_OPTIONS += --include lib/common
FSTAR_OPTIONS += --include build/lib.common.checked
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=core
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify # no extraction

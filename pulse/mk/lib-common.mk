SRC := lib/common
CACHE_DIR := build/lib.common.checked
OUTPUT_DIR := build/lib.common.ml
CODEGEN := NONE
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=common
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/fstar-tree.mk
export FSTAR_LIB ?= $(FSTAR_ROOT)/ulib
INCLUDE_PATHS ?= $(FSTAR_ROOT)/stage2/ulib.checked
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify # no extraction

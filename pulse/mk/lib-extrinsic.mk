SRC := lib/extrinsic
CACHE_DIR := build/lib.extrinsic.checked
OUTPUT_DIR := build/lib.extrinsic.ml
FSTAR_OPTIONS += --include lib/core
FSTAR_OPTIONS += --include lib/common
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=extrinsic
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/fstar-tree.mk
FSTAR_EXE ?= $(FSTAR3_EXE)
FSTAR_EXE := $(abspath $(FSTAR_EXE))
export FSTAR_LIB ?= $(FSTAR_ROOT)/ulib
INCLUDE_PATHS ?= $(FSTAR_ROOT)/stage2/ulib.checked
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify

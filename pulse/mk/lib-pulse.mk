SRC := lib/pulse
CACHE_DIR := build/lib.pulse.checked/
OUTPUT_DIR := build/lib.pulse.ml/
CODEGEN := NONE
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/fstar-tree.mk
FSTAR_EXE ?= $(FSTAR3_EXE)
FSTAR_EXE := $(abspath $(FSTAR_EXE))
export FSTAR_LIB ?= $(FSTAR_ROOT)/ulib
INCLUDE_PATHS ?= $(FSTAR_ROOT)/stage2/ulib.checked
# If being called by F* stage3, no need to include plugin
ifeq ($(STAGE3),)
FSTAR_OPTIONS += --include build/ocaml/installed/lib/pulse
endif
FSTAR_OPTIONS += --include build/lib.common.checked
FSTAR_OPTIONS += --include lib/common
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=pulse
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify # no extraction

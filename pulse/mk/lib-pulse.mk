SRC := lib/pulse
CACHE_DIR := build/lib.pulse.checked/
OUTPUT_DIR := build/lib.pulse.ml/
CODEGEN := NONE
FSTAR_OPTIONS += --include build/ocaml/installed/lib/pulse
FSTAR_OPTIONS += --include build/lib.common.checked
FSTAR_OPTIONS += --include lib/common
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'
TAG=pulse
PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := verify # no extraction

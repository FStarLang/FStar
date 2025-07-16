#
# This Makefile is used to generate EverCrypt_*.h and L0*.h files,
#   which are further used to generate Rust bindings using the Rust bindgen tools
#
# It is invoked by the gen-rust-bindings.sh script
#

CODEGEN=none
SRC=.
TAG=dpe
PULSE_ROOT ?= ../..
OUTPUT_DIR=_output
CACHE_DIR=cache
DICE_DIR=$(PULSE_ROOT)/share/pulse/examples/dice/
INCLUDE_PATHS += $(DICE_DIR)/external $(DICE_DIR)/dpe $(DICE_DIR)/engine $(DICE_DIR)/l0 $(DICE_DIR)/external/hacl $(DICE_DIR)/external/l0
INCLUDE_PATHS += $(PULSE_HOME)/out/lib/pulse
ROOTS := $(DICE_DIR)/dpe/DPE.fst
# ALREADY_CACHED_LIST = *,-HACL,-EverCrypt,-Spec.Hash.Definitions,-L0Core
OTHERFLAGS += --warn_error -342 --cmi
DEPFLAGS += --extract '+EverCrypt +L0Core'
all: verify extract

include $(PULSE_ROOT)/mk/boot.mk
.DEFAULT_GOAL := all


$(call need_dir,KRML_HOME)

KRML ?= $(KRML_HOME)/krml

.PHONY: extract
extract: $(ALL_KRML_FILES)
	$(KRML) -skip-makefiles -skip-compilation -bundle 'EverCrypt.Hash.Incremental=Spec.Hash.Definitions[rename=EverCrypt_Hash]' -warn-error @4 -tmpdir $(OUTPUT_DIR) -add-include '"EverCrypt_Base.h"' -add-include '"compat.h"' -no-prefix 'L0Core' $^

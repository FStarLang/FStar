#
# This Makefile is used to generate EverCrypt_*.h and L0*.h files,
#   which are further used to generate Rust bindings using the Rust bindgen tools
#
# It is invoked by the gen-rust-bindings.sh script
#
# This is not run as part of CI,
#   rather we check-in the generated bindings
#

PULSE_HOME ?= ../..
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
DICE_DIR=$(PULSE_HOME)/share/pulse/examples/dice/
INCLUDE_PATHS += $(DICE_DIR)/external $(DICE_DIR)/dpe $(DICE_DIR)/engine $(DICE_DIR)/l0 $(DICE_DIR)/external/hacl $(DICE_DIR)/external/l0
FSTAR_FILES := $(DICE_DIR)/dpe/DPE.fst
ALREADY_CACHED_LIST = *,-HACL,-EverCrypt,-Spec.Hash.Definitions,-L0Core
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS=--extract '+EverCrypt +L0Core'
all: verify extract

include $(PULSE_HOME)/share/pulse/Makefile.include

KRML ?= $(KRML_HOME)/krml

.PHONY: extract
extract: $(ALL_KRML_FILES)
	$(KRML) -skip-makefiles -skip-compilation -bundle 'EverCrypt.Hash.Incremental=Spec.Hash.Definitions[rename=EverCrypt_Hash]' -warn-error @4 -tmpdir $(OUTPUT_DIRECTORY) -add-include '"EverCrypt_Base.h"' -add-include '"compat.h"' -no-prefix 'L0Core' $^

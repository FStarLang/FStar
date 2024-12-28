# PULSE_HOME ?= ../../../../..
# OUTPUT_DIRECTORY=_output
# CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
# INCLUDE_PATHS += .. hacl
# ifneq (,$(wildcard ../../_output/cache))
#   INCLUDE_PATHS += ../../_output/cache
# endif
# ALREADY_CACHED_LIST = *,-HACL,-EverCrypt,-Spec.Hash.Definitions
# FSTAR_OPTIONS += --warn_error -342
# FSTAR_DEP_OPTIONS=--extract '+EverCrypt'
# all: verify extract

# include $(PULSE_HOME)/share/pulse/Makefile.include

# KRML ?= $(KRML_HOME)/krml

# .PHONY: extract
# extract: $(ALL_KRML_FILES)
#         $(KRML) -skip-makefiles -skip-compilation -bundle 'EverCrypt.Hash.Incremental=Spec.Hash.Definitions[rename=EverCrypt_Hash]' -warn-error @4 -tmpdir $(OUTPUT_DIRECTORY) -add-include '"EverCrypt_Base.h"' $^

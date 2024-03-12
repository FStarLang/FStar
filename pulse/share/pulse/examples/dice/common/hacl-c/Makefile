PULSE_HOME ?= ../../../../../..
OUTPUT_DIRECTORY=_output
CACHE_DIRECTORY=$(OUTPUT_DIRECTORY)/cache
ALREADY_CACHED_LIST = *,-HACL,-EverCrypt
FSTAR_OPTIONS += --warn_error -342
FSTAR_DEP_OPTIONS=--extract '+EverCrypt,'
all: extract

include $(PULSE_HOME)/share/pulse/Makefile.include

KRML ?= $(KRML_HOME)/krml

.PHONY: extract
extract: $(ALL_KRML_FILES)
	$(KRML) -skip-makefiles -skip-compilation -bundle 'EverCrypt.Hash.Incremental=[rename=EverCrypt_Hash]' -warn-error @4+9 -tmpdir $(OUTPUT_DIRECTORY) $^

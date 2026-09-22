TAG := extraction
SRC := src/extraction
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Custard
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
FSTAR_OPTIONS += --with_fstarc
EXTRACT += --extract '-*,+ExtractPulse,+ExtractPulseC,+ExtractPulseOCaml'
FSTAR_OPTIONS += --lax

DEPFLAGS += --already_cached 'Prims,FStarC'

# The Custard pipeline.  This unit sees the compiler and nothing of Pulse's:
# it depends on the krml backend only.
CUSTARD_UNIT    := PulseExtraction
CUSTARD_ROOT    := src/extraction/ExtractPulse.fst \
                   src/extraction/ExtractPulseC.fst \
                   src/extraction/ExtractPulseOCaml.fst
CUSTARD_ENTRIES := --custard_entry ExtractPulse --custard_entry ExtractPulseC
CUSTARD_ENTRIES += --custard_entry ExtractPulseOCaml
# It needs nothing of the checker's or the syntax extension's, but it is
# linked against both all the same.  A unit emits its own copies of the
# definitions it specializes, into files named after the module the name
# comes from, and two *sibling* units therefore produce two files of the same
# name -- which the one flat directory the plugin is linked from, and dune,
# both reject.  A linked unit's file names are names this one then avoids
# (Split.fst's [avoid]), so a chain is all it takes.
CUSTARD_LINK     = $(FSTARC_CUI) build/syntax_extension.ml/PulseSyntaxExtension.cui
CUSTARD_FLAGS   += --ext fly_deps=false

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := custard

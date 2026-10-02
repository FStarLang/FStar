SRC := src/checker/
TAG := checker
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
CODEGEN := Custard
ROOTS := $(shell find $(SRC) -name '*.fst' -o -name '*.fsti')
ROOTS += lib/common/Pulse.Lib.Tactics.fsti
# ^ List files with plugins here

FSTAR_OPTIONS += --already_cached 'Prims,FStar'
FSTAR_OPTIONS += --include lib/common
FSTAR_OPTIONS += --smtencoding.elim_box true
FSTAR_OPTIONS += --z3smtopt '(set-option :smt.arith.nl false)'
EXTRACT += --extract '-*,+Pulse,+PulseSyntaxExtension'
DEPFLAGS += --already_cached 'Prims,FStar,FStarC'

# The Custard pipeline.  One link unit, extracted against the compiler's
# (doc/ref/custard.md, section 13); the roots are the modules carrying
# [@@plugin], which need a registration each (section 13.4), plus the unit's
# own entry point.
CUSTARD_UNIT    := PulseChecker
CUSTARD_ROOT    := src/checker/Pulse.Main.fst lib/common/Pulse.Lib.Tactics.fsti
CUSTARD_ENTRIES := --custard_entry Pulse.Main --custard_entry Pulse.Lib.Tactics
# NB: deferred (=), FSTARC_CUI is defined by boot.mk, included below.
CUSTARD_LINK     = $(FSTARC_CUI)
# Registering a plugin reaches the compiler's own modules -- the
# interpretation functions the normalizer calls -- so they have to be in this
# invocation's dependency graph, which is what --with_fstarc does.  Checking
# the unit does not need them and does not ask for them, so it is on the
# extraction only.
#
# --with_fstarc also puts the compiler's *prelude* on the path, and its
# bundle hashes are not the ones these checked files were written against;
# the failure is Error 317 about Pulse.Main, with no mention of a prelude.
# ulib's checked files come last so that the prelude found is ulib's.
CUSTARD_FLAGS   += --with_fstarc --include $(FSTAR_LIBDIR)/ulib.checked
# fly_deps allows only one file on the command line, and this unit has two
# roots.
CUSTARD_FLAGS   += --ext fly_deps=false

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := custard

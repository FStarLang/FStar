# The Pulse plugin: the checker (src/checker) and the syntax extension
# (src/syntax_extension), lax-checked and extracted together by a single
# whole-program Custard pass, like the compiler itself (mk/fstar-12.mk).
#
# The checker is verified separately, by mk/checker.mk; here it is only
# lax-checked, with the compiler visible (--with_fstarc), as the syntax
# extension and the implementations of some of the checker's interfaces
# (Pulse.RuntimeUtils, Pulse.Extract.CompilerLib,
# PulseSyntaxExtension.ASTBuilder) call the compiler directly.
TAG := plugin
SRC := src
CACHE_DIR := build/$(TAG).checked
OUTPUT_DIR := build/$(TAG).ml
ROOTS := src/checker/Pulse.Main.fst
ROOTS += lib/common/Pulse.Lib.Tactics.fsti
ROOTS += src/syntax_extension/PulseSyntaxExtension.Printing.fst
FSTAR_OPTIONS += --with_fstarc
FSTAR_OPTIONS += --lax
FSTAR_OPTIONS += --include src/checker
FSTAR_OPTIONS += --include src/syntax_extension
FSTAR_OPTIONS += --include lib/common
# --with_fstarc puts the compiler's checked files on the path, which have
# only the part of ulib the compiler uses; the rest comes from ulib's own.
# They come last, so that the prelude found is ulib's: the compiler's has
# other bundle hashes (Error 317).
FSTAR_OPTIONS += --include $(FSTAR_LIBDIR)/ulib.checked

DEPFLAGS += --already_cached 'Prims,FStarC,FStar'

# The Custard pipeline.  One link unit, extracted against the compiler's
# (doc/ref/custard.md, section 13).  The entries are the modules carrying
# [@@plugin], which need a registration each (section 13.4), and the modules
# whose top-level effects register the syntax extension with the compiler.
# PulseSyntaxExtension.ASTBuilder is not a root file: Pulse.Main uses its
# interface (in src/checker), and the implementation is found from there.
CUSTARD_UNIT    := Pulse
CUSTARD_ROOT    := $(ROOTS)
CUSTARD_ENTRIES := --custard_entry Pulse.Main --custard_entry Pulse.Lib.Tactics
CUSTARD_ENTRIES += --custard_entry PulseSyntaxExtension.ASTBuilder
CUSTARD_ENTRIES += --custard_entry PulseSyntaxExtension.Printing
# NB: deferred (=), FSTARC_CUI is defined by boot.mk, included below.
CUSTARD_LINK     = $(FSTARC_CUI)
# fly_deps allows only one file on the command line, and this unit has
# several roots.
CUSTARD_FLAGS   += --ext fly_deps=false

PULSE_ROOT ?= .
include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := custard

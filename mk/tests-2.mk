FSTAR_OPTIONS += --lax
# HACK ALERT! --MLish passed by generic.mk to FStarC modules
# only. Passing it here would mean the library is checked with
# --MLish, which fails.
FSTAR_OPTIONS += --MLish_effect 'FStarC.Effect'
# Suppress unpopped #push-options warning from per-file MLish pragmas
FSTAR_OPTIONS += --warn_error '-361'

DEPFLAGS += --already_cached '+FStarC.*,-FStarC.Tests.*'

# All other files have been extracted already into fstar-guts.
EXTRACT :=
EXTRACT += --extract +FStarC.Tests

# hack, reuse checked files from guts
OTHERFLAGS += --include $(CACHE_DIR)/../fstarc.checked
DEPFLAGS += --include $(CACHE_DIR)/../fstarc.checked

ROOTS :=
ROOTS += $(SRC)/tests/FStarC.Tests.Test.fst

include mk/generic-1.mk

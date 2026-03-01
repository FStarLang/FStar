FSTAR_OPTIONS += --lax
# HACK ALERT! --MLish passed by generic.mk to FStarC modules
# only. Passing it here would mean the library is checked with
# --MLish, which fails.
FSTAR_OPTIONS += --MLish_effect 'FStarC.Effect'
# Suppress unpopped #push-options warning from per-file MLish pragmas
FSTAR_OPTIONS += --warn_error '-361'

DEPFLAGS += --already_cached '+Prims,+FStar,+FStarC,-FStarC.Tests'

DEPFLAGS += --already_cached '-FStar'
# ^ FIXME: This should be removed. All of the modules we *actually* depend on
# in the FStar namespace are indeed already checked. But, if we claim that, the
# dependency analysis will complain about modules such as
# FStar.Stubs.Reflection.V2.Builtins not being checked, which is irrelevant.

# All other files have been extracted already into fstar-guts.
EXTRACT :=
EXTRACT += --extract +FStarC.Tests

# hack, reuse checked files from guts
OTHERFLAGS += --include $(CACHE_DIR)/../fstarc.checked
DEPFLAGS += --include $(CACHE_DIR)/../fstarc.checked

ROOTS :=
ROOTS += $(SRC)/tests/FStarC.Tests.Test.fst

include mk/generic-0.mk

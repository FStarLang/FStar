FSTAR_OPTIONS += --lax

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

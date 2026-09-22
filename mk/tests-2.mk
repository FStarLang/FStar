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

# The Custard pipeline: the tests are a second link unit, compiled against
# the compiler's .cui (doc/ref/custard.md, section 13) rather than into it,
# exactly as an out-of-tree plugin is.  The entry point is the one the
# executable's own main file calls.
CUSTARD_UNIT    := fstarctests
CUSTARD_ROOT    := $(SRC)/tests/FStarC.Tests.Test.fst
CUSTARD_ENTRIES := --custard_entry FStarC.Tests.Test.main
CUSTARD_LINK    := $(OUTPUT_DIR)/../fstarc.ml/fstarc.cui

include mk/generic-1.mk

# The module A.B.C lives in the file A/B/C.fst. F* resolves it hierarchically
# in the include path (here, the cwd).

# Unlike the other incl tests, run real dependency analysis (do not set
# NODEPEND) so that we exercise 'fstar --dep' / the generated .depend and the
# checked-file naming logic.
NODEPEND :=
OTHERFLAGS += --include .

include ../Makefile.sub

# In addition to verifying Test.fst, require the checked file for the nested
# module A.B.C. Both this target's name and its prerequisites come from the
# generated .depend, so this asserts that dependency analysis names the checked
# file after the full module path (A.B.C.fst.checked, not C.fst.checked) and
# that it can actually be produced.
check-pos: $(CACHE_DIR)/A.B.C.fst.checked

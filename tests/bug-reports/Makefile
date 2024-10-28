SUBDIRS += closed

# "X declared but no definition found", we allow this here
OTHERFLAGS+=--warn_error -240

# ^ Add more directories if needed, all files there will be
# checked, plus you can specify which ones to extract+build.

# - closed: meant for regression testing of closed issues.
#   When an issue is fixed, please add a test here (usually just drop
#   it in the directory). All files here will be checked.
# - open: for open issues. We do *not* check this directory. We could
#   consider checking it and using @@expect_failure for things that are
#   *meant to work*, and that way we would know that the repro is up-to-date
#   and also if the issue gets fixed.
# - old: old tests, not checked and not clear that it's worthwhile to bring
#   them back.
# - unclear: from issues where it's not clear whether it's an actual bug
#   or not (maybe just a limitation etc). This directory is also not checked.

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

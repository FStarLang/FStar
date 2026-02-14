# "X declared but no definition found", we allow this here
OTHERFLAGS+=--warn_error -240

# extract, build, and run these files to make sure they work
# (i.e. do not crash)
RUN += Bug086.fst
RUN += Bug314.fst
RUN += Bug540.fst
RUN += Bug541.fst
RUN += Bug589.fst
RUN += ExtractionBug2.fst
RUN += Bug1101.fst
RUN += Bug1485.fst
RUN += Bug734.fst
RUN += Bug310.fst
RUN += Bug2058.fst
RUN += PushPopProjectors.fst
RUN += Bug2412.fst
RUN += Bug2595.fst
RUN += Bug2699.fst
RUN += Bug2895.fst
RUN += ValLetRec.fst
RUN += Bug3473.fst
RUN += Bug490.fst
RUN += Bug1714.fst
RUN += Bug4104.fst

# Just extract these. Note: there are .fs.expected files in this directory,
# so the diff rule triggers automatically, even without these lines.
# EXTRACT += RemoveUnusedTypars_B.fst
# EXTRACT += RemoveUnusedTyparsIFace_B.fst

FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

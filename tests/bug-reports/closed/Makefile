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

# Just extract these. Note: there are .fs.expected files in this directory,
# so the diff rule triggers automatically, even without these lines.
# EXTRACT += RemoveUnusedTypars_B.fst
# EXTRACT += RemoveUnusedTyparsIFace_B.fst
#
# Those four .fs goldens were written for a per-module extractor and each is a
# module that holds nothing but a type or a polymorphic function:
# `let t (a:Type) (b:Type) = list a`, `let f a b (x:A.t a b) = x`. Custard
# compiles a whole program, but --custard_entry_module roots every definition
# of the module, and on the OCaml and F# backends that includes a polymorphic
# one: those targets have type variables, so the definition is emitted as
# written rather than once per instantiation. RecordExtraction's and
# Bug3865b's goldens are empty; an empty golden still asserts that extraction
# succeeds, which is what those bug reports were about.

FSTAR_ROOT ?= ../../..
include $(FSTAR_ROOT)/mk/test.mk

# The expected output prints the unique ids of names, which depend on how
# many fresh names were created before, and so on whether phase 2 is TcTerm
# or Core (--ext phase2_core). See doc/ref/phase2_core.md.
$(OUTPUT_DIR)/Bug4274.fst.output: OTHERFLAGS+=--ext phase2_core=off

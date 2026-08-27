################################################################################
### Regression test for a divergence of extraction.
###
### A.fsti declares a function that is defined in A.fst by a looping recursive
### equation (like FStar.Pervasives.false_elim). Because A.fsti also contains an
### inline_for_extraction definition, cross-module inlining loads A.fst when
### extracting B, so A's definitions become delta-unfoldable at extraction time.
### Extraction normalizes *types* with delta, so a type computed by that looping
### function used to make extraction diverge, allocating without bound.
###
### Marking the looping definition irreducible stops the unfolding without
### changing the extracted code.
################################################################################

FSTAR_ROOT ?= ../../../..
include $(FSTAR_ROOT)/mk/test.mk

# Extraction of B must terminate; B.ml.expected pins the output.

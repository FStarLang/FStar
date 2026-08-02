RUN += Huffman.fst
RUN += IntervalIntersect.fst

# GC.fst is written against the WP-based state effect (STATE_h), which the
# simplified effect system does not provide: an effect is now just a name, and
# effect abbreviations cannot take extra parameters.  Porting it means writing
# the whole development against an explicit state monad.
EXCLUDED_FSTAR_FILES = GC.fst
FSTAR_FILES = $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst) $(wildcard *.fsti))

FSTAR_ROOT ?= ../..
include $(FSTAR_ROOT)/mk/test.mk

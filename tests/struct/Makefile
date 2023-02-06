# Test the 'include' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/.common.mk

# was: $(wildcard *.pos)
POSTESTS=\
  array.pos \
  disjoint.pos \
  point.pos \
  point-with-nesting.pos \
  nested.pos \
  union.pos \
  taggedunion.pos \

POSTARGETS=$(addsuffix .pver,$(POSTESTS))

# was: $(wildcard *.neg)
NEGTESTS=
NEGTARGETS=$(addsuffix .nver,$(NEGTESTS))

all: uall

uall: $(POSTARGETS) $(NEGTARGETS)

$(POSTARGETS): %.pver: %
	$(call msg, "CHECK", $(basename $(notdir $@)))
	$(Q)$(FSTAR) $(SIL) --include $(FSTAR_HOME)/ulib --include $^ --odir $^ Test.fst

$(NEGTARGETS): %.nver: %
	$(call msg, "CHECKFAIL", $(basename $(notdir $@)))
	$(Q)! $(FSTAR) $(SIL) --include $(FSTAR_HOME)/ulib --include $^ --odir $^ Test.fst > $^/error.log 2>&1
	@echo $^ failed as expected

clean:
	$(call msg, "CLEAN")
	$(Q)for f in $(NEGTESTS) ; do rm -f $$f/error.log ; done

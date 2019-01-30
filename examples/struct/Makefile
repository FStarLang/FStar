# Test the 'include' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/gmake/fstar.mk

# was: $(wildcard *.pos)
POSTESTS=\
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
	$(FSTAR) --include $(FSTAR_HOME)/ulib --include $^ --odir $^ Test.fst

$(NEGTARGETS): %.nver: %
	! $(FSTAR) --include $(FSTAR_HOME)/ulib --include $^ --odir $^ Test.fst > $^/error.log 2>&1
	@echo $^ failed as expected

clean:
	for f in $(NEGTESTS) ; do rm -f $$f/error.log ; done

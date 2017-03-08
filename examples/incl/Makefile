# Test the 'include' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/fstar.mk

POSTESTS=$(wildcard *.pos)
POSTARGETS=$(addsuffix .pver,$(POSTESTS))

NEGTESTS=$(wildcard *.neg)
NEGTARGETS=$(addsuffix .nver,$(NEGTESTS))

all: uall

uall: $(POSTARGETS) $(NEGTARGETS)

$(POSTARGETS): %.pver: %
	$(FSTAR) --include $^ --odir $^ Test.fst

$(NEGTARGETS): %.nver: %
	! $(FSTAR) --include $^ --odir $^ Test.fst > $^/error.log 2>&1
	@echo $^ failed as expected

clean:
	for f in $(NEGTESTS) ; do rm -f $$f/error.log ; done


CFSTAR=$(subst CURRENT_DIR,examples/incl,$(CVERFSTAR))

CPOSTARGETS=$(addsuffix .cpver,$(POSTESTS))
$(CPOSTARGETS): %.cpver: %
	$(CFSTAR) --include $^ --odir $^ Test.fst

all-cver: $(CPOSTARGETS)

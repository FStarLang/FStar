# Test the 'include' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/src/gmake/nubuild.mk

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

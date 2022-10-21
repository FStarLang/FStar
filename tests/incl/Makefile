# Test the 'include' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/.common.mk

# Do not warn about missing checked files in these tests.
OTHERFLAGS += --warn_error -241

POSTESTS=$(wildcard *.pos)
POSTARGETS=$(addsuffix .pver,$(POSTESTS))

NEGTESTS=$(wildcard *.neg)
NEGTARGETS=$(addsuffix .nver,$(NEGTESTS))

all: uall

uall: $(POSTARGETS) $(NEGTARGETS)

$(POSTARGETS): %.pver: %
	@echo "[CHECK     $(basename $(notdir $@))]"
	$(Q)$(FSTAR) $(SIL) --include $^ --odir $^ Test.fst

$(NEGTARGETS): %.nver: %
	@echo "[CHECKFAIL $(basename $(notdir $@))]"
	$(Q)! $(FSTAR) $(SIL) --include $^ --odir $^ Test.fst > $^/error.log 2>&1
	@echo $^ failed as expected

clean:
	for f in $(NEGTESTS) ; do rm -f $$f/error.log ; done

# Test the 'struct' functionality

FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/gmake/fstar.mk
include $(FSTAR_HOME)/.common.mk

POSTESTS=$(wildcard *.pos)
POSTESTS:=$(filter-out jsonparser.pos, $(POSTESTS))
POSTARGETS=$(addsuffix .pver,$(POSTESTS))

NEGTESTS=$(wildcard *.neg)
NEGTARGETS=$(addsuffix .nver,$(NEGTESTS))

all: uall

uall: $(POSTARGETS) $(NEGTARGETS)

$(POSTARGETS): %.pver: %
	$(MAKE) -C $< check-pos

$(NEGTARGETS): %.nver: %
	$(MAKE) -C $< check-neg

clean:
	$(call msg, "CLEAN")
	$(Q)for f in $(NEGTESTS) ; do $(MAKE) -C $$f clean; done
	$(Q)for f in $(POSTESTS) ; do $(MAKE) -C $$f clean; done

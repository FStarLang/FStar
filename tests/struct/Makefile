# Test the 'struct' functionality

FSTAR_ROOT ?= ../..
NODEPEND=1
include $(FSTAR_ROOT)/mk/test.mk

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

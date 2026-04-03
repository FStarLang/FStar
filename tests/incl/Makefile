# Test the 'include' functionality

# Do not warn about missing checked files in these tests.
OTHERFLAGS += --warn_error -241

POSTESTS=$(wildcard *.pos)
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

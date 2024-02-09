TARGETS=examples

all: $(TARGETS)

$(TARGETS): %:
	+$(MAKE) -C $@

.PHONY: all $(TARGETS)

.PHONY: install %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(PULSE_INSTALL_PREFIX)/share/pulse/$<

install: $(addsuffix .install,Makefile.include)

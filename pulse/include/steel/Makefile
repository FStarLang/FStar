all:

.PHONY: install %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/include/steel/$<

install: $(addsuffix .install,$(wildcard *.h))

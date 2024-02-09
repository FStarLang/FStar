TARGETS=examples

all: $(TARGETS)

$(TARGETS): %:
	+$(MAKE) -C $@

.PHONY: all $(TARGETS)

.PHONY: install %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(PREFIX)/share/pulse/$<

install: $(addsuffix .install,Makefile.include)

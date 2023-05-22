TARGETS=examples tests tutorial

all: $(TARGETS)

$(TARGETS): %:
	+$(MAKE) -C $@

.PHONY: all $(TARGETS)

.PHONY: install %.install

%.install: %
	$(INSTALL) -m 644 -D $< $(STEEL_INSTALL_PREFIX)/share/steel/$<

install: $(addsuffix .install,Makefile.include)

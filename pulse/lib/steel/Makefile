all: pulse

.PHONY: pulse
pulse:
	+$(MAKE) -C $@

clean:
	+$(MAKE) -C pulse clean

.PHONY: all clean %.fst-in %.fsti-in

%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

.PHONY: install-pulse install
install: install-pulse

install-pulse:
	+$(MAKE) -C pulse install

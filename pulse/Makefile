include mk/common.mk
include mk/locate.mk

# Pulse's `Makefile`s rely on recent GNU Make's "shortest stem" rule,
# so we need to rule out older `make`s.
# GM: ifeq? That sounds oddly specific?
# Also is this still true?
ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif

# NOTE: this default goal will not build pulse2rust. We do check
# PulseCore implementation files (lib/core) by choice, but that could be
# omitted. Use `make all` to build all of this plus pulse2rust.
.DEFAULT_GOAL := default

.PHONY: default
default: local-install lib-core

.PHONY: all
all: local-install # build plugin and library, and install in out/
all: lib-core      # also check implentation files in core
all: pulse2rust    # and pulse2rust tool

.PHONY: .force
.force:

## Checking and extracting the plugin
checker.src: .force
	$(MAKE) -f mk/checker.mk

extraction.src: .force
	$(MAKE) -f mk/extraction.mk

syntax_extension.src: .force
	$(MAKE) -f mk/syntax_extension.mk

plugin.src: checker.src extraction.src syntax_extension.src

## Building the plugin with dune
plugin.build: plugin.src .force
	$(FSTAR_EXE) --ocamlenv \
	  dune build --root=build/ocaml

## Installing the plugin into out/
plugin: plugin.build .force
	$(FSTAR_EXE) --ocamlenv \
	  dune install --root=build/ocaml --prefix=$(abspath build/ocaml/installed)

# Checking the library. Modules in common are shared between core and pulse, but core
# and pulse are independent otherwise.
lib-common: .force
	$(MAKE) -f mk/lib-common.mk

lib-core: lib-common .force
	$(MAKE) -f mk/lib-core.mk

lib-pulse: plugin lib-common .force
	$(MAKE) -f mk/lib-pulse.mk

local-install: override PREFIX=$(CURDIR)/out
local-install: do-install

.PHONY: do-install
do-install: plugin lib-pulse
	rm -rf $(PREFIX)/lib/pulse
	rm -rf $(PREFIX)/share/pulse
	mkdir -p $(PREFIX)/lib/pulse
	mkdir -p $(PREFIX)/lib/pulse/lib
	mkdir -p $(PREFIX)/share/pulse
	# Install plugin.
	$(FSTAR_EXE) --ocamlenv \
	  dune install --root=build/ocaml --prefix=$(abspath $(PREFIX))
	# Install library (cp -u: don't copy unless newer, -p: preserve time/perms)
	# We install it flat. Note that lib/core is not included, but still some PulseCore
	# checked files make it in. We could add:
	#   \( -not -name 'PulseCore.*' \)
	# to the condition but we do need PulseCore.FractionalPermission and others,
	# so I'm keeping this for now (it's already the case) and will do a PR later
	# to change their namespace.
	find lib/pulse lib/common \
		\( -name '*.fst' -o -name '*.fsti' -o -name '*.checked' -o -name '*.ml' \) -and \
		-exec cp -p -u -t $(PREFIX)/lib/pulse/lib {} \;
	# Set up fstar.include so users only include lib/pulse
	echo 'lib' > $(PREFIX)/lib/pulse/fstar.include

	# Install share/ too, as-is.
	cp -p -t $(PREFIX) -r share/

.PHONY: clean
clean:
	$(MAKE) -f mk/checker.mk clean
	$(MAKE) -f mk/extraction.mk clean
	$(MAKE) -f mk/syntax_extension.mk clean
	$(MAKE) -f mk/lib-pulse.mk clean
	$(MAKE) -f mk/lib-core.mk clean
	$(MAKE) -f mk/lib-common.mk clean

.PHONY: test-pulse
test-pulse: local-install
	+$(MAKE) -C test

.PHONY: test-share
test-share: local-install
	+$(MAKE) -C share/pulse

.PHONY: test-pulse2rust
test-pulse2rust: test-share # test-pulse2rust uses .checked files from share/
	+$(MAKE) -C pulse2rust
	+$(MAKE) -C pulse2rust test

.PHONY: test
test: test-pulse test-share test-pulse2rust test-qs

.PHONY: test-qs
test-qs: local-install
	$(MAKE) -C qs test

.PHONY: pulse2rust
pulse2rust: lib-pulse plugin
	+$(MAKE) -C pulse2rust

# Make can figure out internal dependencies between all and test.
.PHONY: ci
ci: all test

.PHONY: install
install: PREFIX ?= /usr/local
install: do-install

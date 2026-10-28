# Verify the effects library independently of its executable examples.
# Default `make` and `make verify` check the interfaces and implementations;
# `make clean` removes this directory's generated cache, output, and .depend.
# The common Pulse rules select the installed stage3 compiler. This file adds
# local-cache bootstrapping so an installed copy cannot hide changed sources.
# See README.md for the dependency graph and editor setup.

# Locate Pulse's shared build rules, relative to this directory.
PULSE_ROOT ?= ../../../..
# Keep the cache path stable between standalone and recursive example builds.
CACHE_DIR ?= $(CURDIR)/_cache
# Prefer local sources/caches and use the same proof budget as the examples.
OTHERFLAGS += --include . --include $(CACHE_DIR) --z3rlimit 10
# Trust installed prerequisites, but check the effects development from source.
OTHERFLAGS += --already_cached 'Prims,FStar,Pulse.Nolib,Pulse.Lib,Pulse.Class,PulseCore,Pulse.Main,-Pulse.Lib.Effects'
# Discover the authored module files; generated files live below _cache/_output.
FSTAR_FILES := $(wildcard *.fst) $(wildcard *.fsti)
# Both interfaces and implementations must exist locally before dependency scan.
EFFECTS_CHECKED = $(addprefix $(CACHE_DIR)/,$(addsuffix .checked,$(FSTAR_FILES)))

# Supply compiler discovery, generated F* dependencies, verify/all, and clean.
include $(PULSE_ROOT)/mk/test.mk

# Materialize local checked files before dependency analysis can select
# installed copies. Once seeded, F* supplies the complete dependency graph.
# The directory prerequisite catches source additions/removals; Makefile changes
# invalidate checked outputs as well as the generated dependency information.
.depend: Makefile . $(EFFECTS_CHECKED) | $(OUTPUT_DIR)
$(EFFECTS_CHECKED): Makefile | $(CACHE_DIR)

# Order-only creation avoids rebuilding proofs when cache directory contents grow.
$(CACHE_DIR) $(OUTPUT_DIR):
	mkdir -p $@

# Check an interface into this cache explicitly, even if an installed cache
# exists. Refresh its timestamp after success so make observes the update.
$(CACHE_DIR)/%.fsti.checked: %.fsti
	$(call msg, "CHECK", $(notdir $<))
	$(FSTAR) $< -o $@
	touch -c $@

# Check an implementation only after its own interface is available. The -o
# selects the local output rather than merely touching an installed checked file.
$(CACHE_DIR)/%.fst.checked: %.fst $(CACHE_DIR)/%.fsti.checked
	$(call msg, "CHECK", $(notdir $<))
	$(FSTAR) $< -o $@
	touch -c $@

# Bootstrap the cross-module interface edge before .depend exists. Additional
# library interfaces may need corresponding bootstrap edges when introduced.
$(CACHE_DIR)/Pulse.Lib.Effects.Exception.fsti.checked: $(CACHE_DIR)/Pulse.Lib.Effects.Core.fsti.checked
$(CACHE_DIR)/Pulse.Lib.Effects.Rules.fsti.checked: $(CACHE_DIR)/Pulse.Lib.Effects.Exception.fsti.checked

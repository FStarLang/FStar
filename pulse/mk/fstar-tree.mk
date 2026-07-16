# Defaults for building Pulse as part of an F* source tree.
#
# When Pulse lives inside an F* source tree (pulse/ directly under the F*
# root), we set defaults for the variables that the top-level F* Makefile
# would otherwise pass down in the environment. This makes `make -C pulse
# ...` (and the pulse sub-makefiles) work directly, without having to go
# through the top-level F* Makefile.
#
# When building Pulse standalone (as its own repository), none of this
# triggers and the usual defaults (fstar.exe on PATH, etc.) apply.
#
# Requires PULSE_ROOT to be set before inclusion.

# FSTAR_ROOT is exported by the top-level F* Makefile. If it is not set
# (e.g. running `make -C pulse ...` directly), detect whether we live
# inside an F* tree by looking for a sibling stage2/ directory.
ifeq ($(FSTAR_ROOT),)
ifneq ($(wildcard $(PULSE_ROOT)/../stage2/.),)
FSTAR_ROOT := $(abspath $(PULSE_ROOT)/..)
endif
endif

ifneq ($(FSTAR_ROOT),)
FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
# Flatten to a simply-expanded value: pulse's need_exe inspects the raw
# variable definition with $(value ...), so it must not contain $(...).
FSTAR_EXE := $(abspath $(FSTAR_EXE))
KRML_HOME ?= $(FSTAR_ROOT)/karamel
STAGE3    ?= 1
endif

# Defaults for building Pulse, which always lives inside an F* source
# tree (pulse/ sits directly under the F* root).
#
# These are the variables that the top-level F* Makefile would otherwise
# pass down in the environment. Setting them here makes `make -C pulse
# ...` (and the pulse sub-makefiles) work directly, without having to go
# through the top-level F* Makefile.
#
# Requires PULSE_ROOT to be set before inclusion.

# FSTAR_ROOT is exported by the top-level F* Makefile. When running
# `make -C pulse ...` directly it is not set, so derive it from PULSE_ROOT.
FSTAR_ROOT ?= $(abspath $(PULSE_ROOT)/..)

FSTAR_EXE ?= $(FSTAR_ROOT)/out/bin/fstar.exe
# Flatten to a simply-expanded value: pulse's need_exe inspects the raw
# variable definition with $(value ...), so it must not contain $(...).
FSTAR_EXE := $(abspath $(FSTAR_EXE))
KRML_HOME ?= $(FSTAR_ROOT)/karamel
STAGE3    ?= 1

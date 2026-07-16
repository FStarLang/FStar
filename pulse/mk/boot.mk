FSTAR_OPTIONS += --warn_error -321

# Silence krml extraction warnings that pollute CI logs
FSTAR_OPTIONS += --warn_error -242
FSTAR_OPTIONS += --warn_error -250

FSTAR_OPTIONS += --ext optimize_let_vc
FSTAR_OPTIONS += --ext fly_deps
FSTAR_OPTIONS += $(addprefix --include , $(INCLUDE_PATHS))

include $(PULSE_ROOT)/mk/fstar-tree.mk
# Default to the installed stage3 compiler. This file is included by the
# test, example and pulse2rust makefiles; the plugin- and library-building
# makefiles set FSTAR_EXE (to the stage2 / stage3-dune compiler) before
# including it, so their choice takes precedence over this default.
FSTAR_EXE ?= $(FSTAR_ROOT)/stage3/out/bin/fstar.exe
FSTAR_EXE := $(abspath $(FSTAR_EXE))
include $(PULSE_ROOT)/mk/generic.mk

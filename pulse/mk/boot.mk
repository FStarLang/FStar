FSTAR_OPTIONS += --warn_error -321

# Silence krml extraction warnings that pollute CI logs
FSTAR_OPTIONS += --warn_error -242
FSTAR_OPTIONS += --warn_error -250

FSTAR_OPTIONS += --ext optimize_let_vc
FSTAR_OPTIONS += --ext fly_deps
FSTAR_OPTIONS += $(addprefix --include , $(INCLUDE_PATHS))

FSTAR_EXE ?= fstar.exe
include $(PULSE_ROOT)/mk/generic.mk

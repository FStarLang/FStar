FSTAR_OPTIONS += --warn_error -321
FSTAR_OPTIONS += --ext optimize_let_vc
FSTAR_OPTIONS += --ext compat:open_metas
FSTAR_OPTIONS += --z3version 4.13.3
FSTAR_OPTIONS += $(addprefix --include , $(INCLUDE_PATHS))

FSTAR_EXE ?= fstar.exe
include $(PULSE_ROOT)/mk/generic.mk

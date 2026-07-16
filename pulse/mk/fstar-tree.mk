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

# There is no single "the F* compiler" for Pulse: the plugin, the library
# and the tests are built with different stages of the compiler. We expose
# the relevant executables here; each makefile then picks the right one as
# its FSTAR_EXE (see the uses of FSTAR2_EXE / FSTAR3_EXE).
#
#  - FSTAR2_EXE: the installed stage2 compiler. The Pulse plugin is both
#    extracted and dune-built with it (stage3 is itself built from stage2
#    plus the plugin, and stage2's --ocamlenv exposes fstar.pluginlib).
#  - FSTAR3_EXE: the freshly-built stage3 dune executable, used to check
#    the Pulse library and run the tests. We deliberately do not use
#    $(FSTAR_ROOT)/out/bin/fstar.exe: the latter only exists once stage3
#    has been *installed*, which itself requires the Pulse library.
#
# The flatten (`:=` after `?=`) is needed because pulse's need_exe inspects
# the raw variable definition with $(value ...), so it must not contain an
# unexpanded $(...).
FSTAR2_EXE ?= $(FSTAR_ROOT)/stage2/out/bin/fstar.exe
FSTAR2_EXE := $(abspath $(FSTAR2_EXE))

FSTAR3_EXE ?= $(FSTAR_ROOT)/stage3/dune/_build/default/fstarc-full/fstarc3_full.exe
FSTAR3_EXE := $(abspath $(FSTAR3_EXE))

KRML_HOME ?= $(FSTAR_ROOT)/karamel
STAGE3    ?= 1

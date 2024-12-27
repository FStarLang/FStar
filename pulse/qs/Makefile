OTHERFLAGS += --include ../out/lib/pulse
OTHERFLAGS += --include ../share/pulse/examples
OTHERFLAGS += --ext pulse:extract_ocaml_bare

DEPFLAGS += --extract '-*'
DEPFLAGS += --extract +Quicksort
# DEPFLAGS += --extract +Pulse.Lib.Dv
# DEPFLAGS += --extract +Pulse.Lib.Task
# DEPFLAGS += --extract +Pulse.Class.Duplicable
# DEPFLAGS += --extract +FStar.Dyn # wrong. it's int FStarC_Dyn.ml

include fstar.mk

# This makefile only does something if a 5.1.1 OPAM switch is available.
HAVE_511 != opam env --switch=5.1.1 2>/dev/null # only outputs to stdout on success

ifeq ($(HAVE_511),)
_ != echo "OPAM switch 5.1.1 does not seem installed, not doing anything" > /dev/tty
.PHONY: all test
all:
test:
else

.PHONY: all
all: dune

.PHONY: dune
dune: $(ALL_ML_FILES)
	opam exec --switch=5.1.1 -- dune build --root=dune

.PHONY: test
test: run

.PHONY: run
run: dune
	./dune/_build/default/driver.exe
endif

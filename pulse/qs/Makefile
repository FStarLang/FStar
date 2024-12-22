OTHERFLAGS += --include ../out/lib/pulse
OTHERFLAGS += --include ../share/pulse/examples
OTHERFLAGS += --ext pulse:extract_ocaml_bare

DEPFLAGS += --extract '-*'
DEPFLAGS += --extract +Quicksort
DEPFLAGS += --extract +Pulse.Lib.Dv
# DEPFLAGS += --extract +Pulse.Lib.Task
# DEPFLAGS += --extract +Pulse.Class.Duplicable
# DEPFLAGS += --extract +FStar.Dyn # wrong. it's int FStarC_Dyn.ml

include fstar.mk

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

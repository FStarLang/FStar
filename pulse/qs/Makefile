OTHERFLAGS += --include ../lib
OTHERFLAGS += --include ../share/pulse/examples
OTHERFLAGS += --ext pulse:extract_ocaml_bare

DEPFLAGS += --extract '-*'
DEPFLAGS += --extract +Quicksort
DEPFLAGS += --extract +Pulse.Lib.Dv
# DEPFLAGS += --extract +NuPool
# DEPFLAGS += --extract +Pulse.Class.Duplicable
# DEPFLAGS += --extract +FStar.Dyn # wrong. it's int FStarC_Dyn.ml

include fstar.mk
all: _output/Quicksort_Task.exe

_output/Quicksort_Task.exe: $(ALL_ML_FILES)
	eval $$(OPAMSWITCH=5.1.1 opam env) && /home/guido/.opam/5.1.1/bin/dune build --root=dune

run:
	./dune/_build/default/driver.exe

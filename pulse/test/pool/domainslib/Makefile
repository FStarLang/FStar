PULSE_ROOT ?= ../../..
OTHERFLAGS += --include $(PULSE_ROOT)/out/lib/pulse
OTHERFLAGS += --include $(PULSE_ROOT)/share/pulse/examples
OTHERFLAGS += --ext pulse:extract_ocaml_bare
OTHERFLAGS += --cmi

DEPFLAGS += --extract '-*'
DEPFLAGS += --extract +Quicksort

CACHE_DIR  := _cache
OUTPUT_DIR := _output
CODEGEN    := OCaml
SRC        := .
ROOTS      := Quicksort.Task.fst
TAG        := pool

include $(PULSE_ROOT)/mk/boot.mk

.DEFAULT_GOAL := all

.PHONY: all
all: test

.PHONY: all_ml
all_ml: $(ALL_ML_FILES)
	# The extraction plugin does get called on names in pattern
	# match branches, so we must replace them explicitly.
	sed -i 's/FStar_Pervasives_Native\.None/None/' $(ALL_ML_FILES)
	sed -i 's/FStar_Pervasives_Native\.Some/Some/' $(ALL_ML_FILES)

.PHONY: dune
dune: all_ml
	opam exec -- dune build --root=dune --no-print-directory

.PHONY: test
test: run

.PHONY: run
run: dune
	./dune/_build/default/driver.exe

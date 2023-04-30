include Makefile.include

# Note: native_tactics is not included in the list below, it is called
# explicitly by the uexamples rule from the Makefile in ../src/Makefile.
# These examples are excluded since the binary package can't verify
# them.

ALL_EXAMPLE_DIRS += algorithms
ALL_EXAMPLE_DIRS += calc
ALL_EXAMPLE_DIRS += crypto
ALL_EXAMPLE_DIRS += data_structures
ALL_EXAMPLE_DIRS += demos
ALL_EXAMPLE_DIRS += doublylinkedlist
ALL_EXAMPLE_DIRS += dsls
ALL_EXAMPLE_DIRS += generic
ALL_EXAMPLE_DIRS += indexed_effects
ALL_EXAMPLE_DIRS += layeredeffects
ALL_EXAMPLE_DIRS += low-mitls-experiments
ALL_EXAMPLE_DIRS += maths
ALL_EXAMPLE_DIRS += metatheory
ALL_EXAMPLE_DIRS += misc
ALL_EXAMPLE_DIRS += oplss2021
ALL_EXAMPLE_DIRS += paradoxes
ALL_EXAMPLE_DIRS += param
ALL_EXAMPLE_DIRS += preorders
ALL_EXAMPLE_DIRS += printf
ALL_EXAMPLE_DIRS += regional
ALL_EXAMPLE_DIRS += rel
ALL_EXAMPLE_DIRS += sequence
ALL_EXAMPLE_DIRS += software_foundations
ALL_EXAMPLE_DIRS += tactics
ALL_EXAMPLE_DIRS += termination
ALL_EXAMPLE_DIRS += typeclasses
ALL_EXAMPLE_DIRS += verifythis

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifneq (,$(HAS_OCAML))
ALL_EXAMPLE_DIRS += hello
ALL_EXAMPLE_DIRS += extraction
endif

ifdef KRML_HOME
ALL_EXAMPLE_DIRS += kv_parsing
ALL_EXAMPLE_DIRS += miniparse
endif

ifneq (,$(CHECK_OLD_EXAMPLES))
ALL_EXAMPLE_DIRS += old/csl
ALL_EXAMPLE_DIRS += old/seplogic
endif

# low-level \  ... NS: removing from CI for this branch

all: $(addsuffix .all, $(ALL_EXAMPLE_DIRS))

%.all: %
	+$(MAKE) -C $^ all

test: all

stdlib: $(addprefix ../lib/, FStar.List.fst FStar.String.fsti partialmap.fst FStar.ST.fst)
	mkdir -p ../cache
	$(FSTAR) $^ --serialize_mods

clean:
	rm ../cache/*.cache

wc:
	find . -name "*.fst" | grep -v -e to_be_ported | xargs sloccount

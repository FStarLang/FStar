EXCLUDED_FSTAR_FILES=ParDivWP.fst Semantics.WP.fst $(wildcard DList*) CQueue.fst
OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel NMST MST NMSTTotal MSTTotal' --compat_pre_typed_indexed_effects
FSTAR_FILES = DList1.fst $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all counter

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

HAS_OCAML := $(shell which ocamlfind 2>/dev/null)

ifdef HAS_OCAML

OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIRECTORY) -w -31
counter: _output/OWGCounter.ml OWGCounterTest.ml | verify-all
	$(OCAMLC) -thread -o counter.exe $^

else

counter:

endif

.PHONY: all verify-all counter

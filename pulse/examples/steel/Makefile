EXCLUDED_FSTAR_FILES=ParDivWP.fst Semantics.WP.fst $(wildcard DList*)
OTHERFLAGS+=--already_cached 'Prims FStar LowStar Steel NMST MST NMSTTotal MSTTotal'
FSTAR_FILES = DList1.fst $(filter-out $(EXCLUDED_FSTAR_FILES), $(wildcard *.fst))

all: verify-all

$(CACHE_DIR):
	mkdir -p $@

include ../Makefile.common

verify-all: $(CACHE_DIR) $(addsuffix .checked, $(addprefix $(CACHE_DIR)/, $(FSTAR_FILES)))

OCAML_DEFAULT_FLAGS += -I $(OUTPUT_DIRECTORY) -w -31

counter: _output/OWGCounter.ml OWGCounterTest.ml
	$(OCAMLC) -o counter.exe $^

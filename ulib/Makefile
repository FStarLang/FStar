.PHONY: indent

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst FStar.StructNG.fst

ALL=$(filter-out $(FLAKY) ,$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL))

indent: $(addsuffix -indent, $(ALL))

%-ver: %
	$(FSTAR) $^
	touch $@

%.fst-indent: %.fst
	$(FSTAR) --indent $^ > $^.indent.fst

%.fsti-indent: %.fsti
	$(FSTAR) --indent $^ > $^.indent.fsti

verify-indent: $(addsuffix -verindent, $(wildcard *.indent.fst))

%-verindent: %
	$(FSTAR) $^

wc:	
	wc -l prims.fst $(ALL)

##

mgen:
	mkdir -p ml/extracted
	$(FSTAR) --lax --codegen OCaml --odir ml/extracted --no_extract FStar.List.Tot --no_extract FStar.List.Tot.Base --no_extract FStar.Heap --no_extract FStar.List.Tot.Properties --no_extract FStar.Set FStar.TSet.fst FStar.Map.fst FStar.HyperHeap.fst FStar.HyperStack.fst

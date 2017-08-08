.PHONY: indent all extra

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

EXTRA=
FLAKY=$(EXTRA) FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst

ALL=$(filter-out $(FLAKY) ,$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL))

extra: $(addsuffix -ver, $(EXTRA))

indent: $(addsuffix -indent, $(ALL))

%-ver: %
	$(FSTAR) $^
	touch $@

%.fst-in:
	@echo --use_hints --hint_info

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

include ml/Makefile.include

REALIZED=$(addsuffix .fst, $(NOEXTRACT_MODULES))
EXTRACT_FSTARLIB=$(filter-out $(REALIZED) FStar.Crypto.fst FStar.Tcp.fst FStar.Reflection.% FStar.Tactics.%,$(wildcard FStar.*.fst FStar.*.fsti))
EXTRACT_COMPILER=$(wildcard FStar.Reflection.*.fst FStar.Reflection.*.fsti FStar.Tactics.*.fst FStar.Tactics.*.fsti)

../bin/fstar.ocaml:
	make -C ../src/ocaml-output

.mgen: *.fst *.fsti ../bin/fstar.ocaml
	mkdir -p ml/extracted
	mkdir -p ml/compiler-extracted
	cp ../src/ocaml-output/FStar_*.ml                      ml/compiler-extracted/
	cp ../src/basic/ml/*.ml                                ml/compiler-extracted/
	cp ../src/prettyprint/ml/*.ml                          ml/compiler-extracted/
	cp ../src/extraction/ml/FStar_Extraction_ML_PrintML.ml ml/compiler-extracted/
	cp ../src/parser/ml/FStar_Parser_LexFStar.mll          ml/compiler-extracted/
	cp ../src/parser/ml/FStar_Parser_ParseIt.ml            ml/compiler-extracted/
	cp ../src/parser/ml/FStar_Parser_Util.ml               ml/compiler-extracted/
	cp ../src/tactics/ml/FStar_Tactics_Native.ml           ml/compiler-extracted/
	cp ../src/tactics/ml/FStar_Tactics_Load.ml             ml/compiler-extracted/
	cp ../src/tactics/ml/FStar_Tactics_Builtins.ml         ml/compiler-extracted/
	$(FSTAR) --lax --codegen OCaml --odir ml/extracted $(FSTAR_DEFAULT_ARGS) $(EXTRACT_FSTARLIB)
	$(FSTAR) --lax --codegen OCaml --odir ml/compiler-extracted $(FSTAR_DEFAULT_ARGS) $(EXTRACT_COMPILER)
	cp ml/compiler-extracted/FStar_Pervasives.ml ml/extracted
	@# creating a dummy file so that the target is not regenerated unless a file has changed
	touch .mgen


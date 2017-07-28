.PHONY: indent

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst FStar.StructNG.fst

ALL=$(filter-out $(FLAKY) ,$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL))

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
EXTRACT_ALL=$(filter-out $(REALIZED),$(wildcard FStar.*.fst FStar.*.fsti))

../bin/fstar.ocaml:
	make -C ../src/ocaml-output

.mgen: *.fst *.fsti ../bin/fstar.ocaml
	mkdir -p ml/extracted
	cp ../src/ocaml-output/FStar_*.ml                      ml/extracted/
	cp ../src/basic/ml/*.ml                                ml/extracted/
	cp ../src/prettyprint/ml/*.ml                          ml/extracted/
	cp ../src/extraction/ml/FStar_Extraction_ML_PrintML.ml ml/extracted/
	cp ../src/parser/ml/FStar_Parser_LexFStar.mll          ml/extracted/
	cp ../src/parser/ml/FStar_Parser_ParseIt.ml            ml/extracted/
	cp ../src/parser/ml/FStar_Parser_Util.ml               ml/extracted/
	cp ../src/tactics/ml/FStar_Tactics_Native.ml           ml/extracted/
	cp ../src/tactics/ml/FStar_Tactics_Load.ml             ml/extracted/
	cp ../src/tactics/ml/FStar_Tactics_Builtins.ml         ml/extracted/
	$(FSTAR) --lax --codegen OCaml --odir ml/extracted $(FSTAR_DEFAULT_ARGS) $(EXTRACT_ALL)
	@# creating a dummy file so that the target is not regenerated unless a file has changed
	touch .mgen

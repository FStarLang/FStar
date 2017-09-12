# Makefile.verify has been split off because it is the actual
# Makefile that is distributed in the binary package. This
# Makefile here is not.
include Makefile.verify

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
	cp ../src/parser/ml/FStar_Parser_LexFStar.ml           ml/compiler-extracted/
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


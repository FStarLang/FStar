OCAMLC=ocamlfind ocamlc -thread -package batteries -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -thread -package batteries -linkpkg -g
OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

ifeq ($(OS),Windows_NT)
SUFFIX=.exe
else
SUFFIX=
endif

FSTARML=fstarml$(SUFFIX)

# prog1 should be compiled to bytecode, and is composed of three
# units: mod1, mod2 and mod3.

# The list of object files for prog1
FSTAR_OBJS=support.cmx Microsoft_FStar_Options.cmx Microsoft_FStar_Absyn_Syntax.cmx Microsoft_FStar_Absyn_Const.cmx Microsoft_FStar_Absyn_Visit.cmx Microsoft_FStar_Absyn_Util.cmx Microsoft_FStar_Absyn_Print.cmx Microsoft_FStar_Absyn_SSyntax.cmx Microsoft_FStar_Tc_Env.cmx Microsoft_FStar_Tc_Recheck.cmx Microsoft_FStar_Tc_Normalize.cmx Microsoft_FStar_Tc_Errors.cmx Microsoft_FStar_Tc_Rel.cmx Microsoft_FStar_Tc_Util.cmx Microsoft_FStar_Tc_Tc.cmx Microsoft_FStar_Parser_AST.cmx Microsoft_FStar_Parser_DesugarEnv.cmx Microsoft_FStar_Parser_Desugar.cmx Microsoft_FStar_Parser_Parse.cmx Microsoft_FStar_Parser_Lexhelp.cmx Microsoft_FStar_Parser_LexFStar.cmx Microsoft_FStar_Parser_ParseIt.cmx Microsoft_FStar_Parser_Driver.cmx Microsoft_FStar_ToSMT_Term.cmx Microsoft_FStar_ToSMT_Z3.cmx Microsoft_FStar_ToSMT_SplitQueryCases.cmx Microsoft_FStar_ToSMT_Encode.cmx FSharp_Format.cmx Microsoft_FStar_Backends_NameEnv.cmx Microsoft_FStar_Backends_ML_Syntax.cmx Microsoft_FStar_Backends_ML_Util.cmx Microsoft_FStar_Backends_ML_Env.cmx Microsoft_FStar_Backends_ML_Extraction.cmx Microsoft_FStar_Backends_ML_ExtractExp.cmx Microsoft_FStar_Backends_OCaml_ASTTrans.cmx Microsoft_FStar_Backends_OCaml_Code.cmx Microsoft_FStar_FStar.cmx

all: $(FSTARML)

package: $(FSTARML)
	rm -dfr fstar && mkdir fstar
	cp ../../LICENSE fstar/
	mkdir fstar/bin
	cp README fstar/
#	cp /usr/bin/ocamlopt fstar/bin/ocamlopt || true
#	cp /usr/bin/ocamlrun fstar/bin/fsocamlrun || true
	cp ../../setenv.sh fstar/
	cd ../.. && git archive --format=tar --prefix=lib/ HEAD:lib/ | tar -x -C src/ocaml-output/fstar
	cp $(FSTARML) fstar/bin/fstar.exe
	@cp ../../bin/*z3* fstar/bin || cp `which z3` fstar/bin || echo " ********** WARNING: you don't have Z3 in \\$FSTAR_HOME/bin or in your \\$PATH, skipped from package ************** "
	cd ../.. && git archive --format=tar --prefix=examples/ HEAD:examples/ | tar -x -C src/ocaml-output/fstar
	cd ../.. && git archive --format=tar --prefix=doc/tutorial/ HEAD:doc/tutorial/ | tar -x -C src/ocaml-output/fstar
#	mkdir fstar/mllib || true
#	cp ~/.opam/system/lib/num/* fstar/mllib || true
#	cp ~/.opam/system/lib/bytes/* fstar/mllib || true
#	cp ~/.opam/system/lib/batteries/* fstar/mllib || true
#	cp ~/.opam/system/lib/fstar/* fstar/mllib || true
#	cp /usr/lib/ocaml/unix.cmxa /usr/lib/ocaml/nums.cmxa /usr/lib/ocaml/bigarray.cmxa /usr/lib/ocaml/str.cmxa fstar/mllib || true
#	cp /usr/lib/ocaml/unix.a /usr/lib/ocaml/nums.a /usr/lib/ocaml/bigarray.a /usr/lib/ocaml/str.a fstar/mllib || true
ifeq ($(OS),Windows_NT)
	zip -r -9 fstar_`git log --pretty=format:'%h' -n 1`_`uname`_`uname -m`.zip fstar
else
	tar czf fstar_`git log --pretty=format:'%h' -n 1`_`uname`_`uname -m`.tar.gz fstar
endif

parser:
	cat ../parser/parse.fsy | sed 's/^[/][/].*//g' | sed 's/^[#].*//g' | sed 's/^open .*//g' > parse.mly
	ocamlyacc parse.mly
	rm Microsoft_FStar_Parser_Parse.ml
	echo "open Support.Microsoft.FStar.Util" > Microsoft_FStar_Parser_Parse.ml
	echo "open Support.Microsoft.FStar.Range" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Options" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Syntax" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Const" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Util" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Parser_AST" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Support.Microsoft.FStar.Parser.Util" >> Microsoft_FStar_Parser_Parse.ml
	cat parse.ml >> Microsoft_FStar_Parser_Parse.ml
#	cp ../support/ocaml/fstar-lang/src/FSLangLexer.mll lex.mll
	ocamllex ../lex.mll -o Microsoft_FStar_Parser_LexFStar.ml
	cp ../parseit.ml Microsoft_FStar_Parser_ParseIt.ml
	cp ../support/ocaml/fstar-lib/src/support.ml .
	$(OCAMLDEP) $(INCLUDES) *.ml > .depend

fstarml.ml: ../main.ml
		cp $^ $@

$(FSTARML): $(FSTAR_OBJS) fstarml.ml
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -o $(FSTARML) $^
	cp fstarml.exe ../../bin/fstar.exe || cp fstarml ../../bin/fstar.exe

# Common rules
.SUFFIXES: .ml .mli .cmo .cmi .cmx

.ml.cmo:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.mli.cmi:
	$(OCAMLC) $(OCAMLFLAGS) -c $<

.ml.cmx:
	$(OCAMLOPT) $(OCAMLOPTFLAGS) -c $<

# Clean up
clean:
	rm -fr fstar || true
	rm -f System_* Microsoft_FStar_* FSharp_Format.* support.* parse.* fstarml.* .depend $(FSTARML) || true

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.ml > .depend

-include .depend

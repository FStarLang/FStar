OCAMLC=ocamlfind ocamlc -package fstar -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -package fstar -linkpkg -g
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
FSTAR_OBJS=Microsoft_FStar_Options.cmx Microsoft_FStar_LazySet.cmx Microsoft_FStar_Absyn_Syntax.cmx Microsoft_FStar_Absyn_Const.cmx Microsoft_FStar_Absyn_Visit.cmx Microsoft_FStar_Absyn_Util.cmx Microsoft_FStar_Absyn_Print.cmx Microsoft_FStar_Absyn_SSyntax.cmx Microsoft_FStar_Parser_AST.cmx Microsoft_FStar_Parser_DesugarEnv.cmx Microsoft_FStar_Parser_Desugar.cmx Microsoft_FStar_Parser_Parse.cmx Microsoft_FStar_Parser_Lexhelp.cmx Microsoft_FStar_Parser_LexFStar.cmx Microsoft_FStar_Parser_ParseIt.cmx Microsoft_FStar_Parser_Driver.cmx Microsoft_FStar_Tc_Env.cmx Microsoft_FStar_Tc_Normalize.cmx Microsoft_FStar_Tc_Errors.cmx Microsoft_FStar_Tc_Rel.cmx Microsoft_FStar_Tc_Util.cmx Microsoft_FStar_Tc_Tc.cmx Microsoft_FStar_ToSMT_Term.cmx Microsoft_FStar_ToSMT_Z3.cmx Microsoft_FStar_ToSMT_Encode.cmx FSharp_Format.cmx Microsoft_FStar_Backends_NameEnv.cmx Microsoft_FStar_Backends_OCaml_Syntax.cmx Microsoft_FStar_Backends_OCaml_ASTTrans.cmx Microsoft_FStar_Backends_OCaml_Code.cmx

all: $(FSTARML)

package: $(FSTARML)
	mkdir fstar || true
	mkdir fstar/bin || true
	cp ../../setenv.sh fstar/
	cp -R ../../lib fstar/ || true
	cp $(FSTARML) fstar/bin/ || true
	cp ../../bin/z3* fstar/bin || true
	cp ../../bin/libz3* fstar/bin || true
	mkdir fstar/code || true
	cp -R ../../examples/school2014 fstar/code/tutorial || true
	cp -R ../../examples/unit-tests fstar/code/examples || true
	cp makefile.ml fstar/code/examples/Makefile || true
	cp makefile.tutorial.ml fstar/code/tutorial/Makefile.include || true
	mkdir fstar/mllib || true
	cp ~/.opam/system/lib/num/* fstar/mllib || true
	cp ~/.opam/system/lib/bytes/* fstar/mllib || true
	cp ~/.opam/system/lib/batteries/* fstar/mllib || true
	cp ~/.opam/system/lib/fstar/* fstar/mllib || true
	cp /usr/lib/ocaml/unix.cmxa /usr/lib/ocaml/nums.cmxa /usr/lib/ocaml/bigarray.cmxa /usr/lib/ocaml/str.cmxa fstar/mllib || true
	cp /usr/lib/ocaml/unix.a /usr/lib/ocaml/nums.a /usr/lib/ocaml/bigarray.a /usr/lib/ocaml/str.a fstar/mllib || true
	tar czvf fstar_`git log --pretty=format:'%h' -n 1`_`uname`_`uname -m`.tar.gz fstar

parser:
	cat ../parser/parse.fsy | sed 's/^[/][/].*//g' | sed 's/^[#].*//g' | sed 's/^open .*//g' > parse.mly
	ocamlyacc parse.mly
	echo "open Fstar.Support.Microsoft.FStar.Util" > Microsoft_FStar_Parser_Parse.ml
	echo "open Fstar.Support.Microsoft.FStar.Range" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Syntax" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Const" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Util" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Parser_AST" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Fstar.Support.Microsoft.FStar.Parser.Util" >> Microsoft_FStar_Parser_Parse.ml
	cat parse.ml >> Microsoft_FStar_Parser_Parse.ml
#	cp ../support/ocaml/fstar-lang/src/FSLangLexer.mll lex.mll
	ocamllex ../lex.mll -o Microsoft_FStar_Parser_LexFStar.ml
	cp ../parseit.ml Microsoft_FStar_Parser_ParseIt.ml
	$(OCAMLDEP) $(INCLUDES) *.ml > .depend

$(FSTARML): $(FSTAR_OBJS)
	ocamlfind ocamlopt -p -package fstar -o fstarml $(FSTAR_OBJS) ../fstarml.ml -linkpkg -g
	cp $(FSTARML) ../../bin/


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
	rm -fr fstar
	rm -f fstarml
	rm -f Microsoft_FStar_*.cm[iox] FSharp_Format.cm[iox] parse.ml *.o *.gz

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.ml ../fstarml.ml > .depend

-include .depend

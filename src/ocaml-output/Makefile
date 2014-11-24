OCAMLC=ocamlfind ocamlopt -p -package fstar -linkpkg -g
OCAMLOPT=ocamlfind ocamlopt -p -package fstar -linkpkg -g
OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

# prog1 should be compiled to bytecode, and is composed of three
# units: mod1, mod2 and mod3.

# The list of object files for prog1
FSTAR_OBJS=Microsoft_FStar_Options.cmx Microsoft_FStar_LazySet.cmx Microsoft_FStar_Absyn_Syntax.cmx Microsoft_FStar_Absyn_Const.cmx Microsoft_FStar_Absyn_Visit.cmx Microsoft_FStar_Absyn_Util.cmx Microsoft_FStar_Absyn_Print.cmx Microsoft_FStar_Absyn_SSyntax.cmx Microsoft_FStar_Parser_AST.cmx Microsoft_FStar_Parser_DesugarEnv.cmx Microsoft_FStar_Parser_Desugar.cmx Microsoft_FStar_Parser_Parse.cmx Microsoft_FStar_Parser_Lexhelp.cmx Microsoft_FStar_Parser_LexFStar.cmx Microsoft_FStar_Parser_ParseIt.cmx Microsoft_FStar_Parser_Driver.cmx Microsoft_FStar_Tc_Env.cmx Microsoft_FStar_Tc_Normalize.cmx Microsoft_FStar_Tc_Errors.cmx Microsoft_FStar_Tc_Rel.cmx Microsoft_FStar_Tc_Util.cmx Microsoft_FStar_Tc_Tc.cmx Microsoft_FStar_ToSMT_Term.cmx Microsoft_FStar_ToSMT_Z3.cmx Microsoft_FStar_ToSMT_Encode.cmx

all: fstarml

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


# The following uses a local parser.mly to avoid issues with Mac OS X sed version.
lparser:
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

fstarml: $(FSTAR_OBJS)
	ocamlfind ocamlopt -p -package fstar -o fstarml $(FSTAR_OBJS) ../fstarml.ml -linkpkg -g

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
	rm -f fstarml
	rm -f Microsoft_FStar_*.ml Microsoft_FStar_*.cm[iox] parse.ml[iy] parse.ml

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.ml ../fstarml.ml > .depend

-include .depend

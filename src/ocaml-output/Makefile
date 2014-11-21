OCAMLC=ocamlfind ocamlc -package fstar -linkpkg
OCAMLOPT=ocamlopt
OCAMLDEP=ocamldep
INCLUDES=                 # all relevant -I options here
OCAMLFLAGS=$(INCLUDES)    # add other options for ocamlc here
OCAMLOPTFLAGS=$(INCLUDES) # add other options for ocamlopt here

# prog1 should be compiled to bytecode, and is composed of three
# units: mod1, mod2 and mod3.

# The list of object files for prog1
FSTAR_OBJS=Microsoft_FStar_Options.cmo Microsoft_FStar_LazySet.cmo Microsoft_FStar_Absyn_Syntax.cmo Microsoft_FStar_Absyn_Const.cmo Microsoft_FStar_Absyn_Visit.cmo Microsoft_FStar_Absyn_Util.cmo Microsoft_FStar_Absyn_Print.cmo Microsoft_FStar_Absyn_SSyntax.cmo Microsoft_FStar_Parser_AST.cmo Microsoft_FStar_Parser_DesugarEnv.cmo Microsoft_FStar_Parser_Desugar.cmo Microsoft_FStar_Parser_Parse.cmo Microsoft_FStar_Parser_Lexhelp.cmo Microsoft_FStar_Parser_Driver.cmo Microsoft_FStar_Tc_Env.cmo Microsoft_FStar_Tc_Normalize.cmo Microsoft_FStar_Tc_Errors.cmo Microsoft_FStar_Tc_Rel.cmo Microsoft_FStar_Tc_Util.cmo Microsoft_FStar_Tc_Tc.cmo Microsoft_FStar_ToSMT_Term.cmo Microsoft_FStar_ToSMT_Z3.cmo Microsoft_FStar_ToSMT_Encode.cmo 

all: fstarml

parser:
	cat ../parser/parse.fsy | sed ':a;N;$$!ba;s/^%[{][^%]*%[}]//g' > parse.mly
	ocamlyacc parse.mly
	echo "open Fstar.Support.Microsoft.FStar.Util" > Microsoft_FStar_Parser_Parse.ml
	echo "open Fstar.Support.Microsoft.FStar.Range" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Syntax" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Const" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Absyn_Util" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Microsoft_FStar_Parser_AST" >> Microsoft_FStar_Parser_Parse.ml
	echo "open Fstar.Support.Microsoft.FStar.Parser.Util" >> Microsoft_FStar_Parser_Parse.ml
	cat parse.ml >> Microsoft_FStar_Parser_Parse.ml

fstarml: $(FSTAR_OBJS)
	ocamlfind ocamlc -package fstar -o fstarml $(FSTAR_OBJS) ../fstarml.ml -linkpkg

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
	rm -f *.cm[iox]

.depend:
	touch .depend

# Dependencies
depend:
	$(OCAMLDEP) $(INCLUDES) *.ml > .depend

include .depend

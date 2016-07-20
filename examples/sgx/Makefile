# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile
OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

X86_ODIR=x86Interpreter
X86_EXTRACTED=Ast.ml Helper.ml LowInterpreter.ml X86Interpreter.ml 

# OCaml variables
OCAMLOPT := $(OCAMLOPT_) -I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa -w -8-20-26

.PHONY: lib-ver x86Interpreter-ver

all: x86Interpreter-ml

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

x86Interpreter-ver:
	$(FSTAR) X86Interpreter.fst Ast.fst

x86Interpreter-ml: lexer.ml parser.ml
	mv parser.ml ml/parser.ml
	mv lexer.ml ml/lexer.ml	
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(X86_ODIR)
	$(FSTAR) $(OPTIONS_OCAML) X86Interpreter.fst Ast.fst  Helper.fst LowInterpreter.fst --odir $(X86_ODIR)
	$(MAKE) x86Interpreter-compile

lexer.ml : lexer.mll
	ocamllex -q $< 

lexer.cmo : parser.cmi ml/lexer.ml
	ocamlc -g -c ml/lexer.ml

parser.ml : parser.mly
	ocamlyacc -q $< 

parser.mli : parser.mly
	ocamlyacc -q $<

x86Interpreter-compile:
	$(OCAMLOPT) -I ml -I $(X86_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix $(X86_ODIR)/,$(X86_EXTRACTED)) ml/parser.ml ml/lexer.ml ml/main.ml -o test.exe
	./test.exe testcases/t.s

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(X86_ODIR) *~ *.exe ml/lexer.ml ml/parser.ml parser.mli

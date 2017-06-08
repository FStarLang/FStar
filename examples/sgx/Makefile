# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile
OPTIONS_OCAML=--llax --codegen OCaml --no_location_info

X86_ODIR=Interpreter
X86_EXTRACTED=Ast.ml Test.ml Util.ml SGXState.ml Interpreter.ml 

# OCaml variables
OCAMLOPT := $(OCAMLOPT_) -I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa -w -8-20-26
OCAMLCOPT := $(OCAMLC_) -I $(ULIB_ML)/hyperheap  $(ULIB_ML)/fstarlib-hyperheap.a 

.PHONY: lib-ver x86Interpreter-ver

all: x86Interpreter-ml

x86Interpreter-ml: 
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(X86_ODIR)
	$(FSTAR) $(OPTIONS_OCAML) Test.fst Interpreter.fst Ast.fst SGXState.fst Util.fst --odir $(X86_ODIR)
	$(MAKE) x86Interpreter-compile

x86Interpreter-compile:
	$(OCAMLOPT) -I ml -I $(X86_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(X86_ODIR)/FStar_List_Tot.ml \
	  $(addprefix $(X86_ODIR)/,$(X86_EXTRACTED)) ml/main.ml -o test.exe
	./test.exe 

# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(X86_ODIR) *~ *.exe 

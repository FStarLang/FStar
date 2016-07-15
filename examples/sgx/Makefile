
# FStar variables
FSTAR_HOME=../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_OCAML=--lax --codegen OCaml --no_location_info

CHACHA_ODIR=x86Interpreter

# OCaml variables
OCAMLOPT := ocamlfind opt -package batteries,stdint,zarith -linkpkg -g -I $(ULIB_ML) \
	-I $(ULIB_ML)/hyperheap $(ULIB_ML)/fstarlib-hyperheap.cmxa -w -8-20-26

REALIZED_MLI=
REALIZED=FStar_HyperStack FStar_HST
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))


CHACHA_EXTRACTED=X86Interpreter.ml

.PHONY: lib-ver x86Interpreter-ver 

all: x86Interpreter-ml 

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) FStar.HyperStack.fst FStar.HST.fst FStar.Buffer.fst

x86Interpreter-ver:
	$(FSTAR) X86Interpreter.fst 

x86Interpreter-ml:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml hyperheap
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) X86Interpreter.fst --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_x86Interpreter.ml -o test_x86Interpreter.exe
	./test_x86Interpreter.exe 

x86Interpreter-compile:
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_x86Interpreter.ml -o test_x86Interpreter.exe
	./test_x86Interpreter.exe


# Cleaning
clean:
	$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	@rm -f $(addprefix ml/, *.cmx *.o *.cmi *~)
	@rm -rf $(CHACHA_ODIR) *~ *.exe

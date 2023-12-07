# FStar variables
FSTAR_HOME=../../../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=--universes
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

CHACHA_ODIR=chacha

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int
REALIZED_MLI=
REALIZED=FStar_HyperStack FStar_HST FStar_StackArray FStar_Buffer
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

CHACHA_EXTRACTED=Chacha.ml

.PHONY: lib-ver chacha-ver chacha-ml

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) $(OPTIONS_VER) FStar.HyperStack.fst FStar.HST.fst FStar.StackArray.fst FStar.Buffer.fst

# AES targets
chacha-ver:
	$(FSTAR) $(OPTIONS_VER) chacha.fst 

chacha-ml:
	+$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(CHACHA_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) chacha.fst --odir $(CHACHA_ODIR) 
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha.ml -o test_chacha.exe
	./test_chacha.exe 

chacha-compile:
	$(OCAMLOPT) -I ml -I $(CHACHA_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix $(CHACHA_ODIR)/,$(CHACHA_EXTRACTED)) ml/test_chacha.ml -o test_chacha.exe
	./test_chacha.exe

clean:
	+$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	rm -rf $(CHACHA_ODIR) *~ ./ml/*.cmi ./ml/*.cmx ./ml/*.cmo ./ml/*.o test_chacha.exe

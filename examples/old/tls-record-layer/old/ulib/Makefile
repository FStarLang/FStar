# FStar variables
FSTAR_HOME=../../..
include $(FSTAR_HOME)/ulib/ml/Makefile.include
FSTAR=$(FSTAR_HOME)/bin/fstar.exe $(FSTAR_DEFAULT_ARGS) # from the included Makefile

OPTIONS_VER=--universes
OPTIONS_OCAML=--lax --codegen OCaml --universes --no_location_info --use_native_int

AES_ODIR=aes

# OCaml variables
OCAMLOPT := $(OCAMLOPT) -I $(ULIB_ML)/native_int
REALIZED_MLI=SInt_UInt8
REALIZED=FStar_StackHeap2 FStar_SST FStar_StackArray FStar_Buffer
REALIZED_MODULE=$(subst _,., $(REALIZED))
REALIZED_ML=$(addsuffix .mli,$(REALIZED_MLI)) $(addsuffix .ml,$(REALIZED_MLI) $(REALIZED))
NO_CODEGEN=$(addprefix --no_extract , SInt $(REALIZED_MODULE))

AES_EXTRACTED=AES.ml

.PHONY: lib-ver chacha-ver chacha-ml poly-ver poly-ml

# Verification target for the low-level libraries of F* in universes
lib-ver:
	$(FSTAR) $(OPTIONS_VER) FStar.StackHeap2.fst FStar.SST.fst FStar.StackArray.fst FStar.Buffer.fst

# AES targets
aes-ver:
	$(FSTAR) $(OPTIONS_VER) aes.fst 

aes-ml:
	+$(MAKE) -C $(FSTAR_HOME)/ulib/ml PRIMS_DIR=native_int
	mkdir -p $(AES_ODIR)
	$(FSTAR) $(NO_CODEGEN) $(OPTIONS_OCAML) $(FSTAR_LIB) aes.fst --odir $(AES_ODIR) 
	$(OCAMLOPT) -I ml -I $(AES_ODIR) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix ml/,$(REALIZED_ML)) \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) ml/test_aes.ml -o test_aes.exe
	./test_aes.exe 

aes-compile:
	$(OCAMLOPT) -I ml -I $(AES_ODIR) $(addprefix ml/,$(REALIZED_ML)) \
	  $(FSTAR_HOME)/ulib/ml/FStar_UInt32.ml \
	  $(addprefix $(AES_ODIR)/,$(AES_EXTRACTED)) ml/test_aes.ml -o test_aes.exe
	./test_aes.exe

clean:
	+$(MAKE) -C $(FSTAR_HOME)/ulib/ml clean
	rm -rf $(AES_ODIR) *~ ./ml/*.cmi ./ml/*.cmx ./ml/*.cmo ./ml/*.o

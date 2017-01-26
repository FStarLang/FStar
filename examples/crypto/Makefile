.PHONY: all verify-% __force__

VERFILES=AES.fst \
Encrypt_SymEnc.fst\
Encrypt_Sample.fst \
SHA1.fst \
MAC.fst \
Sig.fst 


HH_VERFILES= \
EtM.Plain.fst \
EtM.MAC.fst \
EtM.CPA.fst \
EtM.AE.fst \
HyE.RSA.fst \
HyE.PlainPKE.fst \
HyE.Plain.fst \
HyE.AE.fst \
HyE.CCA2.fst \
HyE.HCCA2.fst

LIB = ../../contrib/CoreCrypto/ml

ifeq ($(OS),Windows_NT)
  EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
else
    EXTRA_PATH = LD_LIBRARY_PATH=.:$(LIB)
    UNAME_S := $(shell uname -s)
endif

FSTAR_HOME=../..
include ../Makefile.include

%.fst-in: 
	@echo --include $(FSTAR_HOME)/ulib/hyperstack \
	      --include $(FSTAR_HOME)/ucontrib/Platform/fst \
	      --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
	      --z3rlimit 20
	      --verify_module $(basename $(notdir $@))

verify-%: __force__
	$(FSTAR) --include $(FSTAR_HOME)/ucontrib/Platform/fst \
		 --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
		 --z3rlimit 20 $*

verify_hh-%: __force__
	$(FSTAR) --include $(FSTAR_HOME)/ulib/hyperstack \
		 --include $(FSTAR_HOME)/ucontrib/Platform/fst \
		 --include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
		 --z3rlimit 20 $*

all: uall

uall: $(VERFILES:%=verify-%) $(HH_VERFILES:%=verify_hh-%) rpc CntProtocol


export CONTRIB=../../contrib

acls-cap: SHA1.fst MAC.fst ../security/ACLs_simplified.fst Cap.fst
	$(FSTAR) --z3rlimit 10 \
	--verify_module ACLs_simplified --verify_module Cap \
	--include $(FSTAR_HOME)/ucontrib/Platform/fst \
	--include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst \
	$^

rpc: Formatting.fst SHA1.fst MAC.fst RPC.fst
	$(FSTAR) --z3rlimit 10 --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC   \
		--include $(FSTAR_HOME)/ucontrib/Platform/fst \
		--include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst RPC.fst

.PHONY: mllibs

mllibs:
	$(MAKE) -C $(FSTAR_HOME)/contrib/Platform/ml clean all
	$(MAKE) -C $(FSTAR_HOME)/contrib/CoreCrypto/ml clean all test

RPC.ml: SHA1.fst MAC.fst Formatting.fst RPC.fst
	$(FSTAR_ALWAYS) --no_location_info --lax \
		--include $(FSTAR_HOME)/ucontrib/Platform/fst \
		--include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst RPC.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen-lib SeqProperties --codegen OCaml --use_native_int 

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/ulib/ml/native_int $(FSTAR_HOME)/ulib/ml)
OCAMLC=ocamlfind ocamlopt -ccopt -L$(LIB) -package batteries -linkpkg -g -thread
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/ulib/ml/, MkPrims.ml native_int/prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_Char.ml FStar_String.ml FStar_IO.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, CoreCrypto/ml/CoreCrypto.cmxa)

$(CONTRIB_LIBS):
	$(MAKE) -C $(FSTAR_HOME)/contrib/

RPC.exe: RPC.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml FStar_SeqProperties.ml FStar_List_Tot.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

rpc-test: RPC.exe
	$(EXTRA_PATH) ./RPC.exe

CntProtocol: CntFormat.fst MAC.fst SHA1.fst CntProtocol.fst
	$(FSTAR) --z3rlimit 10 --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
		--include $(FSTAR_HOME)/ucontrib/Platform/fst \
		--include $(FSTAR_HOME)/ucontrib/CoreCrypto/fst CntProtocol.fst

CntProtocol.ml: CntFormat.fst MAC.fst SHA1.fst CntProtocol.fst
	$(FSTAR_ALWAYS) --z3rlimit 10  --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst CntProtocol.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml

CntProtocol.exe: CntProtocol.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml ../../ulib/ml/FStar_Set.ml FStar_SeqProperties.ml SHA1.ml MAC.ml CntFormat.ml CntProtocol.ml

cnt-test: CntProtocol.exe
	$(EXTRA_PATH) ./CntProtocol.exe

deploy-tutorial:
	cp EtM.AE.fst  EtM.CPA.fst  EtM.Ideal.fsti  EtM.MAC.fst  EtM.Plain.fst ../../doc/tutorial/code/solutions/
	cp EtM.AE.fst  EtM.CPA.fst  EtM.Ideal.fsti  EtM.MAC.fst  EtM.Plain.fst ../../doc/tutorial/code/exercises/


clean:
	rm -fr RPC *.ml *.cmi *.cmx *.o *.exe *~

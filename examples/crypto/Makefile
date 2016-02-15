VERFILES=CCA2.RSA.fst CCA2.Plain.fst CCA2.CCA2.fst # encrypt3.fst formatting.fst rpc.fst

LIB = ../../contrib/CoreCrypto/ml

ifeq ($(OS),Windows_NT)
  CC =
  EXTRA_PATH = PATH="/usr/x86_64-w64-mingw32/sys-root/mingw/bin/:$(PATH)"
else
    EXTRA_PATH = LD_LIBRARY_PATH=.:$(LIB)
    UNAME_S := $(shell uname -s)
    ifeq ($(UNAME_S),Darwin)
        CC = -cc gcc-5
    else
        CC = -cc gcc
    endif
endif

include ../Makefile.include
all: .all.crypto.ver merkle_tree mac padding mac3 rpc CntProtocol acls-cap statefulEnc


.all.crypto.ver: $(VERFILES)
	$(FSTAR) --z3timeout 20 $^

export CONTRIB=../../contrib

mac: sha1.fst mac.fst
	$(FSTAR) --z3timeout 10 --verify_module MAC --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1  \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst \
		$^

sig: sig.fst
	$(FSTAR) $^

padding: Padding.Pad.fst Padding.BMAC.fst Padding.MAC2.fst Padding.TMAC.fst
	$(FSTAR) --z3timeout 20 --verify_module Padding.Pad --verify_module Padding.BMAC --verify_module Padding.MAC2 --verify_module Padding.TMAC --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst \
		$^

mac3: mac3.fst
	$(FSTAR) --z3timeout 10 --verify_module MAC3 --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst \
		$^

merkle_tree: MerkleTree.fst
	$(FSTAR) --verify_module MerkleTree \
	--include $(FSTAR_HOME)/contrib/Platform/fst \
	--include $(FSTAR_HOME)/contrib/CoreCrypto/fst \
	$^

acls-cap: sha1.fst mac.fst ../security/acls2.fst cap.fst
	$(FSTAR) --z3timeout 10 \
	--verify_module ACLs2 --verify_module Cap \
	--include $(FSTAR_HOME)/contrib/Platform/fst \
	--include $(FSTAR_HOME)/contrib/CoreCrypto/fst \
	$^

rpc: formatting.fst sha1.fst mac.fst rpc.fst
	$(FSTAR) --z3timeout 10 --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC   \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst rpc.fst

statefulEnc: statefulEnc-single.fst statefulEnc-twoLevelHeap.fst
	$(FSTAR) --verify_module StatefulEncryption.SingleInstance statefulEnc-single.fst
	$(FSTAR) --verify_module StatefulEncryption.TwoLevelHeap statefulEnc-twoLevelHeap.fst

.PHONY: mllibs

mllibs:
	$(MAKE) -C $(FSTAR_HOME)/contrib/Platform/ml clean all
	$(MAKE) -C $(FSTAR_HOME)/contrib/CoreCrypto/ml clean all test

RPC.ml: sha1.fst mac.fst formatting.fst rpc.fst
	$(FSTAR) --z3timeout 10 --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC   \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst rpc.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --use_native_int

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)
OCAMLC=ocamlfind ocamlopt $(CC) -ccopt -L$(LIB) -package batteries -linkpkg -g -thread
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/lib/ml/, native_int/prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_String.ml FStar_IO.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, CoreCrypto/ml/CoreCrypto.cmxa)

$(CONTRIB_LIBS):
	$(MAKE) -C $(FSTAR_HOME)/contrib/

rpc.exe: RPC.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml FStar_SeqProperties.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

rpc-test: rpc.exe
	$(EXTRA_PATH) ./rpc.exe

CntProtocol: CntFormat.fst mac.fst sha1.fst CntProtocol.fst
	$(FSTAR) --z3timeout 10  --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst CntProtocol.fst

CntProtocol.ml: CntFormat.fst mac.fst sha1.fst CntProtocol.fst
	$(FSTAR) --z3timeout 10  --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
		--include $(FSTAR_HOME)/contrib/Platform/fst \
		--include $(FSTAR_HOME)/contrib/CoreCrypto/fst CntProtocol.fst \
		--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml

CntProtocol.exe: CntProtocol.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml ../../lib/ml/FStar_Set.ml FStar_SeqProperties.ml SHA1.ml MAC.ml CntFormat.ml CntProtocol.ml

cnt-test: CntProtocol.exe
	$(EXTRA_PATH) ./CntProtocol.exe

clean:
	rm -fr rpc *.ml *.cmi *.cmx *.o *.exe *~

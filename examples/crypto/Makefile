VERFILES=cca2.fst # encrypt3.fst formatting.fst rpc.fst

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
all: .all.crypto.ver merkle_tree mac padding mac3 rpc cnt-protocol acls-cap statefulEnc


STDLIB_ADMITS=--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi FStar.SeqProperties
STDLIB=$(addprefix $(FSTAR_HOME)/lib/, FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi \
       FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.String.fst FStar.List.fst seq.fsi FStar.SeqProperties.fst) \
       $(STDLIB_ADMITS)

.all.crypto.ver: $(VERFILES)
	$(FSTAR) --z3timeout 20 $(STDLIB) $^

mac: sha1.fst mac.fst
	$(FSTAR) mac.fst

sig: sig.fst
	$(FSTAR) $^

padding: padding.fst
	$(FSTAR) $^

mac3: mac3.fst
	$(FSTAR) $^

merkle_tree:
	$(FSTAR) --verify_module MerkleTree $(STDLIB) $(FSTAR_HOME)/lib/FStar.Constructive.fst merkle_tree.fst

acls-cap: sha1.fst mac.fst ../security/acls2.fst acls-cap.fst
	$(FSTAR) --z3timeout 10 --admit_fsi FStar.Seq \
	--verify_module Platform.Bytes --verify_module CoreCrypto --verify_module ACLs2 --verify_module Cap \
	$(addprefix $(FSTAR_HOME)/lib/, \
	FStar.FunctionalExtensionality.fst FStar.Classical.fst \
	FStar.Set.fsi FStar.Set.fst \
	FStar.Heap.fst FStar.ST.fst FStar.All.fst \
	FStar.String.fst FStar.List.fst \
	seq.fsi FStar.SeqProperties.fst ) \
	$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
  $^


rpc: formatting.fst sha1.fst mac.fst rpc.fst
	$(FSTAR) --z3timeout 10 --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi FStar.Seq --admit_fsi FStar.IO  \
          $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Classical.fst \
					FStar.Set.fsi FStar.Set.fst \
					FStar.Heap.fst FStar.ST.fst FStar.All.fst \
					FStar.String.fst FStar.IO.fsti FStar.List.fst \
					seq.fsi FStar.SeqProperties.fst )  \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
					sha1.fst mac.fst formatting.fst rpc.fst

statefulEnc: statefulEnc-single.fst statefulEnc-twoLevelHeap.fst
	$(FSTAR) statefulEnc-single.fst
	$(FSTAR) statefulEnc-twoLevelHeap.fst

.PHONY: mllibs

mllibs:
	$(MAKE) -C $(FSTAR_HOME)/contrib/Platform/ml clean all
	$(MAKE) -C $(FSTAR_HOME)/contrib/CoreCrypto/ml clean all test

RPC.ml: sha1.fst mac.fst formatting.fst rpc.fst
	$(FSTAR) --z3timeout 10 --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi FStar.IO  \
          $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Classical.fst \
					FStar.Set.fsi FStar.Set.fst \
					FStar.Heap.fst FStar.ST.fst FStar.All.fst \
					FStar.String.fst FStar.IO.fsti FStar.List.fst \
					FStar.Seq.fst FStar.SeqProperties.fst ) \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
					sha1.fst mac.fst formatting.fst rpc.fst  \
					--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml --use_native_int

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/lib/ml/native_int $(FSTAR_HOME)/lib/ml)
OCAMLC=ocamlfind ocamlopt $(CC) -ccopt -L$(LIB) -package batteries -linkpkg -g -thread
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/lib/ml/, native_int/prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_String.ml FStar_IO.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, CoreCrypto/ml/corecrypto.cmxa)

$(CONTRIB_LIBS):
	$(MAKE) -C $(FSTAR_HOME)/contrib/

rpc.exe: RPC.ml $(CONTRIB_LIBS)
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml FStar_SeqProperties.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

rpc-test: rpc.exe
	$(EXTRA_PATH) ./rpc.exe

cnt-protocol: cnt-format.fst mac.fst sha1.fst cnt-protocol.fst
	make -C $(FSTAR_HOME)/contrib/
	$(FSTAR) --z3timeout 10 --admit_fsi FStar.Seq --admit_fsi FStar.IO --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
          $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Classical.fst \
					FStar.Set.fsi FStar.Set.fst \
					FStar.Heap.fst FStar.ST.fst FStar.All.fst \
					FStar.String.fst FStar.List.fst \
					seq.fsi FStar.SeqProperties.fst FStar.IO.fsti ) \
	  $(FSTAR_HOME)/contrib/Platform/fst/Bytes.fst \
	  $(FSTAR_HOME)/contrib/CoreCrypto/fst/CoreCrypto.fst \
	  cnt-format.fst sha1.fst mac.fst cnt-protocol.fst

CntProtocol.ml: cnt-format.fst mac.fst sha1.fst cnt-protocol.fst
	$(FSTAR) --z3timeout 10 --admit_fsi FStar.IO --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
	  --verify_module CntFormat --verify_module SHA1 --verify_module MAC --verify_module CntProtocol \
          $(addprefix $(FSTAR_HOME)/lib/, FStar.FunctionalExtensionality.fst FStar.Classical.fst \
					FStar.Set.fsi FStar.Set.fst \
					FStar.Heap.fst FStar.ST.fst FStar.All.fst \
					FStar.String.fst FStar.List.fst \
					FStar.Seq.fst FStar.SeqProperties.fst FStar.IO.fsti ) \
	  $(FSTAR_HOME)/contrib/Platform/fst/Bytes.fst \
	  $(FSTAR_HOME)/contrib/CoreCrypto/fst/CoreCrypto.fst \
	  cnt-format.fst sha1.fst mac.fst cnt-protocol.fst --codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml

cnt-protocol.exe: CntProtocol.ml
	$(OCAMLC) -o $@ $(OCAML_INCLUDE_PATHS) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml ../../lib/ml/FStar_Set.ml FStar_SeqProperties.ml SHA1.ml MAC.ml CntFormat.ml CntProtocol.ml

cnt-test: cnt-protocol.exe
	$(EXTRA_PATH) ./cnt-protocol.exe

clean:
	rm -fr rpc *.ml *.cmi *.cmx *.o *.exe *~

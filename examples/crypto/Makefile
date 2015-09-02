VERFILES=cca2.fst #sha1.fst mac.fst sig.fst padding.fst mac3.fst # encrypt3.fst formatting.fst rpc.fst

ifeq ($(OS),Windows_NT)
# internally flexlink uses i686-w64-mingw32-gcc.exe
CC = flexlink -chain mingw -v -v -exe -lgdi32
# flexlink is needed to link in	/cygdrive/c/OCaml/bin/flexdll_initer_mingw.o /cygdrive/c/OCaml/bin/flexdll_mingw.o
LIB = $(FSTAR_HOME)/3rdparty/win32 #place to look for libcrypto.a
else
    LIB = /usr/lib #place to look for libcrypto.a
    ifeq ($(UNAME_S),Darwin)
        CC = gcc-5
    else
        CC = gcc
    endif
endif

include ../Makefile.include
all: .all.crypto.ver merkle_tree mac rpc rpc-extract acls-cap statefulEnc
STDLIB_ADMITS=--admit_fsi FStar.Seq --admit_fsi FStar.Set --admit_fsi FStar.SeqProperties
STDLIB=$(addprefix $(FSTAR_HOME)/lib/, classical.fst ext.fst set.fsi \
       heap.fst st.fst all.fst string.fst list.fst seq.fsi seqproperties.fst) \
			 $(STDLIB_ADMITS)

.all.crypto.ver: $(VERFILES)
	$(FSTAR) --z3timeout 20 $(STDLIB) $^

mac: sha1.fst mac.fst
	$(FSTAR) --verify_module SHA1 --verify_module MAC --admit_fsi FStar.Seq $(addprefix $(FSTAR_HOME)/lib/, \
	ext.fst classical.fst \
	set.fsi set.fst \
	heap.fst st.fst all.fst \
	list.fst \
	seq.fsi seqproperties.fst ) \
	$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
	$^

merkle_tree:
	$(FSTAR) --verify_module MerkleTree $(STDLIB) $(FSTAR_HOME)/lib/constr.fst merkle_tree.fst

acls-cap: sha1.fst mac.fst ../security/acls2.fst acls-cap.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi FStar.Seq \
	--verify_module Platform.Bytes --verify_module CoreCrypto --verify_module ACLs2 --verify_module Cap \
	$(addprefix $(FSTAR_HOME)/lib/, \
	ext.fst classical.fst \
	set.fsi set.fst \
	heap.fst st.fst all.fst \
	string.fst list.fst \
	seq.fsi seqproperties.fst ) \
	$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
  $^


rpc: formatting.fst sha1.fst mac.fst rpc.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi FStar.Seq --admit_fsi FStar.IO  \
          $(addprefix $(FSTAR_HOME)/lib/, ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst all.fst \
					string.fst io.fsti list.fst \
					seq.fsi seqproperties.fst )  \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
					sha1.fst mac.fst formatting.fst rpc.fst

statefulEnc: statefulEnc-single.fst statefulEnc-twoLevelHeap.fst
	$(FSTAR) statefulEnc-single.fst
	$(FSTAR) statefulEnc-twoLevelHeap.fst


mllibs:
	make -C $(FSTAR_HOME)/contrib/Platform/ml clean all
	make -C $(FSTAR_HOME)/contrib/CoreCrypto/ml clean all


rpc-extract: sha1.fst mac.fst formatting.fst rpc.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi FStar.IO  \
          $(addprefix $(FSTAR_HOME)/lib/, ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst all.fst \
					string.fst io.fsti list.fst \
					seq.fst seqproperties.fst ) \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
					sha1.fst mac.fst formatting.fst rpc.fst  \
					--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml

OCAML_INCLUDE_PATHS=$(addprefix -I , $(FSTAR_HOME)/contrib/Platform/ml $(FSTAR_HOME)/contrib/CoreCrypto/ml $(FSTAR_HOME)/lib/ml)
OCAMLC=ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -cclib -lcrypto -o rpc.exe -package batteries -linkpkg -g -thread $(OCAML_INCLUDE_PATHS)
SUPPORT_LIBS=$(addprefix $(FSTAR_HOME)/lib/ml/, prims.ml FStar_ST.ml FStar_All.ml FStar_List.ml FStar_String.ml FStar_IO.ml)
CONTRIB_LIBS=$(addprefix $(FSTAR_HOME)/contrib/, Platform/ml/platform.cmx CoreCrypto/ml/CoreCrypto.cmxa)
rpc-ml: rpc-extract
	$(OCAMLC) $(SUPPORT_LIBS) $(CONTRIB_LIBS) FStar_Seq.ml FStar_SeqProperties.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

cnt-protocol: cnt-format.fst cnt-mac.fst cnt-protocol.fst
	$(FSTAR) cnt-protocol.fst

clean:
	rm -fr rpc *.ml *.cmi *.cmx *.o *.exe *~

VERFILES=cca2.fst #sha1.fst mac.fst sig.fst padding.fst mac3.fst # encrypt3.fst formatting.fst rpc.fst

ifeq ($(OS),Windows_NT)
# internally flexlink uses i686-w64-mingw32-gcc.exe
CC = flexlink -chain mingw -v -v -exe -lgdi32
# flexlink is needed to link in	/cygdrive/c/OCaml/bin/flexdll_initer_mingw.o /cygdrive/c/OCaml/bin/flexdll_mingw.o
LIB = $(FSTAR_HOME)/../openssl #place to look for libcrypto.a
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
STDLIB_ADMITS=--admit_fsi Seq --admit_fsi Set --admit_fsi SeqProperties
STDLIB=$(addprefix $(FSTAR_HOME)/lib/, classical.fst ext.fst set.fsi \
       heap.fst st.fst all.fst string.fst list.fst seq.fsi seqproperties.fst) \
			 $(STDLIB_ADMITS)

.all.crypto.ver: $(VERFILES)
	$(FSTAR) --z3timeout 20 $(STDLIB) $^

mac: sha1.fst mac.fst
	$(FSTAR) --verify_module SHA1 --verify_module MAC --admit_fsi Seq $(addprefix $(FSTAR_HOME)/lib/, \
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
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq \
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
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi Seq  \
          $(addprefix $(FSTAR_HOME)/lib/, ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst all.fst \
					string.fst io.fst list.fst \
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
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --verify_module Formatting --verify_module SHA1 --verify_module MAC --verify_module RPC --admit_fsi Seq  \
          $(addprefix $(FSTAR_HOME)/lib/, ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst all.fst \
					string.fst io.fst list.fst \
					seq.fst seqproperties.fst ) \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/fst/Bytes.fst CoreCrypto/fst/CoreCrypto.fst) \
					sha1.fst mac.fst formatting.fst rpc.fst  \
					--codegen-lib Platform --codegen-lib CoreCrypto --codegen OCaml-experimental

rpc-ml: rpc-extract
	ocamlfind ocamlopt -cc "$(CC)" -cclib -L$(LIB) -cclib -lcrypto -o rpc.exe -package batteries -linkpkg -g -thread -I $(FSTAR_HOME)/contrib/Platform/ml -I $(FSTAR_HOME)/contrib/CoreCrypto/ml -I \
	        $(FSTAR_HOME)/src/ocaml-output/ \
					$(FSTAR_HOME)/src/ocaml-output/support.ml \
					$(addprefix $(FSTAR_HOME)/contrib/,  Platform/ml/platform.cmx CoreCrypto/ml/CoreCrypto.cmxa) \
					Seq.ml SeqProperties.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

cnt-protocol: cnt-format.fst cnt-format.fsi cnt-mac.fst cnt-protocol.fst
	$(FSTAR) --admit_fsi Set $(addprefix $(FSTAR_HOME)/lib/, list.fst string.fst partialmap.fst ) cnt-format-deprecated.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
          $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst \
					seq.fsi seqproperties.fst ) cnt-format.fst cnt-mac.fst cnt-protocol.fst

clean:
	rm -fr rpc *.ml *.cmi *.cmx *.o *~

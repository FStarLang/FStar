VERFILES=cca2.fst sha1.fst mac.fst sig.fst padding.fst mac3.fst # encrypt3.fst formatting.fst rpc.fst
include ../Makefile.include
all: .all.crypto.ver acls-cap rpc merkle_tree

.all.crypto.ver: $(VERFILES)
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
	set.fsi set.fst \
	heap.fst st.fst \
	seq.fsi seqproperties.fst ) $^


mac:
	$(FSTAR) $(FSTAR_HOME)/lib/partialmap.fst $(FSTAR_HOME)/lib/st.fst sha1.fst mac.fst

merkle_tree:
	$(FSTAR) $(FSTAR_HOME)/lib/list.fst $(FSTAR_HOME)/lib/constr.fst merkle_tree.fst

acls-cap: sha1.fst mac.fst ../security/acls2.fst acls-cap.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
	set.fsi set.fst \
	heap.fst st.fst \
	seq.fsi seqproperties.fst ) $^

# --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1
rpc: formatting.fst sha1.fst mac.fst rpc.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq  \
          $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst \
					seq.fsi seqproperties.fst ) formatting.fst sha1.fst mac.fst rpc.fst

rpc-extract:
	$(FSTAR) --codegen OCaml --admit_fsi Seq  \
          $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst \
					seq.fsi seqproperties.fst ) sha1.fst mac.fst formatting.fst rpc.fst
	ocamlfind ocamlopt -o rpc -package batteries -linkpkg -thread -I $(FSTAR_HOME)/src/ocaml-output/ $(FSTAR_HOME)/src/ocaml-output/support.ml SHA1.ml MAC.ml Formatting.ml RPC.ml

cnt-protocol: cnt-format.fst cnt-format.fsi cnt-mac.fst cnt-protocol.fst
	$(FSTAR) --admit_fsi Set $(addprefix $(FSTAR_HOME)/lib/, list.fst string.fst partialmap.fst ) cnt-format-deprecated.fst
	$(FSTAR) --z3timeout 10 --prims ../../lib/prims.fst --admit_fsi Seq --max_fuel 4 --initial_fuel 0 --max_ifuel 2 --initial_ifuel 1 \
          $(addprefix $(FSTAR_HOME)/lib/, string.fst list.fst ext.fst classical.fst \
					set.fsi set.fst \
					heap.fst st.fst \
					seq.fsi seqproperties.fst ) cnt-format.fst cnt-mac.fst cnt-protocol.fst

clean:
	rm -fr rpc *.ml *.cmi *.cmx *.o *~

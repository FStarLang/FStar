KREMLIN=Kremlin.native
EXT_TO=./ext

KREMLIN_ARGS+=-tmpdir $(EXT_TO) \
	-drop FStar,Prims,C,C.*,C.Loops.Spec.Loops,Spec.*,Lib.*,WasmSupport \
	-drop Hacl.Cast,Hacl.UInt8,Hacl.UInt16,Hacl.UInt32,Hacl.UInt64,Hacl.UInt128 \
	-drop Hacl.Spec.Endianness,Hacl.Endianness,Seq.Create \
	-drop Hacl.Impl.SHA2_256.Lemmas,Hacl.Impl.SHA2_384.Lemmas,Hacl.Impl.SHA2_512.Lemmas \
	-drop MerkleTree.High \
	-I ../
# -ccopt -march=native -warn-error +9

.PHONY: all ext clean

ext:
	-$(KREMLIN) $(KREMLIN_ARGS) ../MerkleTree.Low.fst lib/connect.c lib/Hacl_SHA2_256.c merkle_tree.c

clean:
	rm -f a.out
	rm -rf ./ext/*

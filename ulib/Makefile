.PHONY: indent

FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst

HYPERSTACK=FStar.Buffer.fst FStar.Buffer.Quantifiers.fst FStar.Monotonic.RRef.fst FStar.Monotonic.Seq.fst FStar.Struct.fst FStar.StructNG.fst

ALL=$(filter-out $(FLAKY) $(HYPERSTACK) $(MATH),$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL)) st m_rref bufferq struct

indent: $(addsuffix -indent, $(ALL))

%.fst-indent: %.fst
	$(FSTAR) --indent $^ > $^.indent.fst

%.fsti-indent: %.fsti
	$(FSTAR) --indent $^ > $^.indent.fsti

verify-indent: $(addsuffix -verindent, $(wildcard *.indent.fst))

%-verindent: %
	$(FSTAR) $^

%-ver: %
	$(FSTAR) $^
list:
	$(FSTAR) FStar.List.Tot.Base.fst FStar.List.Tot.Properties.fst FStar.List.Tot.fst FStar.List.fst

array:
	$(FSTAR) FStar.Seq.Base.fst FStar.Classical.fst FStar.Seq.Properties.fst FStar.Seq.fst FStar.Array.fst

tcp:
	$(FSTAR) FStar.Axiomatic.Array.fst FStar.Char.fsti FStar.Option.fsti FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst

squash:
	$(FSTAR) FStar.Constructive.fst FStar.Squash.fst FStar.SquashProperties.fst FStar.SquashEffect.fst

elogic:
	$(FSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst

ordmap:
	$(FSTAR) FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst FStar.OrdMapProps.fst

pext:
	$(FSTAR) FStar.PredicateExtensionality.fst

st:
	$(FSTAR) FStar.Map.fst FStar.HyperHeap.fst hyperheap/FStar.ST.fst FStar.Util.fst

mref:
	$(FSTAR) FStar.MRef.fst

m_rref:
	$(FSTAR) FStar.Map.fst FStar.HyperStack.fst hyperstack/FStar.ST.fst hyperstack/FStar.All.fst FStar.Monotonic.RRef.fst FStar.Monotonic.Seq.fst

buffer:
	$(FSTAR) FStar.Map.fst FStar.HyperStack.fst hyperstack/FStar.ST.fst hyperstack/FStar.All.fst FStar.Buffer.fst

struct:
	$(FSTAR) hyperstack/FStar.ST.fst hyperstack/FStar.All.fst FStar.Struct.fst

bufferq:
	$(FSTAR) FStar.Map.fst FStar.HyperStack.fst hyperstack/FStar.ST.fst FStar.Buffer.fst FStar.Buffer.Quantifiers.fst

twolevelheap:
	$(FSTAR) FStar.TwoLevelHeap.fst

relational:
	$(FSTAR) FStar.Relational.Relational.fst FStar.Relational.Comp.fst FStar.Relational.State.fst

bitvector:
	$(FSTAR) FStar.Math.Lib.fst FStar.Math.Lemmas.fst FStar.BitVector.fst

int:
	$(FSTAR) FStar.UInt.fst FStar.UInt8.fst FStar.UInt16.fst FStar.UInt31.fst FStar.UInt32.fst FStar.UInt63.fst FStar.UInt64.fst FStar.Int.fst FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst FStar.Int.Cast.fst

wc:	
	wc -l prims.fst $(ALL)

##

mgen:
	mkdir -p ml/extracted
	$(FSTAR) --lax --codegen OCaml --odir ml/extracted FStar.Set.fst FStar.TSet.fst FStar.Map.fst FStar.HyperHeap.fst FStar.HyperStack.fst

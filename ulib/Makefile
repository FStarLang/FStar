FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/src/gmake/nubuild.mk

UFSTAR=$(FSTAR) --universes
ALL=FStar.PredicateExtensionality.fst FStar.TSet.fst FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Mul.fst FStar.UInt.fst FStar.Int.fst FStar.Int8.fst FStar.Int16.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst FStar.UInt8.fst FStar.UInt16.fst FStar.UInt32.fst FStar.UInt63.fst FStar.UInt64.fst FStar.Int.Cast.fst FStar.List.Tot.fst FStar.ListProperties.fst FStar.List.fst FStar.Seq.fst FStar.Classical.fst FStar.Char.fsti FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst FStar.Constructive.fst FStar.Squash.fst FStar.SquashProperties.fst FStar.Ghost.fst FStar.ErasedLogic.fst FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst FStar.PredicateExtensionality.fst FStar.MRef.fst FStar.TwoLevelHeap.fst FStar.Relational.Relational.fst FStar.Relational.Comp.fst FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst FStar.IO.fsti

FLAKY=FStar.Int31.fst FStar.UInt31.fst FStar.Relational.State.fst

HYPERHEAP=FStar.Monotonic.RRef.fst

ALL=$(filter-out $(FLAKY) $(HYPERHEAP),$(wildcard FStar.*.fst FStar.*.fsti))

all: $(addsuffix -ver, $(ALL)) st m_rref

%-ver: %
	$(UFSTAR) $^
list:
	$(UFSTAR) FStar.List.Tot.fst FStar.ListProperties.fst FStar.List.fst

array:
	$(UFSTAR) FStar.Seq.fst FStar.Classical.fst FStar.SeqProperties.fst FStar.Array.fst

tcp:
	$(UFSTAR) FStar.Axiomatic.Array.fst FStar.Char.fsti FStar.Option.fsti FStar.Bytes.fst FStar.Crypto.fst FStar.Tcp.fst

squash:
	$(UFSTAR) FStar.Constructive.fst FStar.Squash.fst FStar.SquashProperties.fst FStar.SquashEffect.fst

elogic:
	$(UFSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst

ordmap:
	$(UFSTAR) FStar.OrdSet.fst FStar.OrdSetProps.fst FStar.OrdMap.fst FStar.OrdMapProps.fst

pext:
	$(UFSTAR) FStar.PredicateExtensionality.fst

st:
	$(UFSTAR) FStar.Map.fst FStar.HyperHeap.fst hyperheap/FStar.ST.fst FStar.Util.fst

mref:
	$(UFSTAR) FStar.MRef.fst

m_rref:
	$(UFSTAR) FStar.Map.fst FStar.HyperHeap.fst hyperheap/FStar.ST.fst hyperheap/FStar.All.fst FStar.Monotonic.RRef.fst 

twolevelheap:
	$(UFSTAR) FStar.TwoLevelHeap.fst

relational:
	$(UFSTAR) FStar.Relational.Relational.fst FStar.Relational.Comp.fst FStar.Relational.State.fst

int:
	$(UFSTAR) FStar.UInt.fst FStar.UInt8.fst FStar.UInt16.fst FStar.UInt31.fst FStar.UInt32.fst FStar.UInt63.fst FStar.UInt64.fst FStar.Int.fst FStar.Int8.fst FStar.Int16.fst FStar.Int31.fst FStar.Int32.fst FStar.Int63.fst FStar.Int64.fst FStar.Int.Cast.fst

wc:	
	wc -l prims.fst $(ALL)

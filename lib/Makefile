FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/src/gmake/nubuild.mk

all:
	$(FSTAR) FStar.SeqProperties.fst FStar.Array.fst
	$(FSTAR) FStar.Axiomatic.Array.fst
	$(FSTAR) FStar.Char.fsti
	$(FSTAR) FStar.Classical.fst
	$(FSTAR) FStar.Constructive.fst
	$(FSTAR) FStar.Crypto.fst
	$(FSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(FSTAR) FStar.FunctionalExtensionality.fst
	$(FSTAR) FStar.HyperHeap.fst
	$(FSTAR) FStar.Int8.fst
	$(FSTAR) FStar.Int16.fst
	$(FSTAR) FStar.Int31.fst
	$(FSTAR) FStar.Int32.fst
	$(FSTAR) FStar.Int63.fst
	$(FSTAR) FStar.Int64.fst
	$(FSTAR) FStar.ListProperties.fst
	$(FSTAR) FStar.List.Tot.fst
	$(FSTAR) FStar.Map.fst
	$(FSTAR) FStar.MRef.fst
	$(FSTAR) FStar.Option.fsti
	$(FSTAR) FStar.OrdSet.fst
	$(FSTAR) FStar.OrdMap.fst
	$(FSTAR) FStar.OrdMapProps.fst
	$(FSTAR) FStar.OrdSetProps.fst
	$(FSTAR) FStar.PredicateExtensionality.fst
	$(FSTAR) FStar.Set.fst
#	$(FSTAR) stboot.fsi stboot.fst   -- Unrecognized file extension: stboot.fsi
	$(FSTAR) FStar.Relational.fst
	$(FSTAR) --explicit_deps   FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
	$(FSTAR) FStar.Tcp.fst
	$(FSTAR)   FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.TwoLevelHeap.fst
#	$(FSTAR) --fs_typ_app FStar.Util.fst  # --fs_typ_app needed because automatically generated FStar.Util.fsti will get picked up by automatic dependency tracking and it's not a valid interface file without this flag ... oops, it's actually not valid even with this flag because of the ML exception syntax
	$(FSTAR) FStar.Squash.fst
	$(FSTAR) FStar.SquashProperties.fst
	$(FSTAR) FStar.SquashEffect.fst

wc:
	sloccount .

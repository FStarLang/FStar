FSTAR_HOME=..
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/src/gmake/nubuild.mk

SFSTAR=$(FSTAR) --stratified

all:
	$(SFSTAR) FStar.SeqProperties.fst FStar.Array.fst
	$(SFSTAR) FStar.Axiomatic.Array.fst
	$(SFSTAR) FStar.Char.fsti
	$(SFSTAR) FStar.Classical.fst
	$(SFSTAR) FStar.Constructive.fst
	$(SFSTAR) FStar.Crypto.fst
	$(SFSTAR) FStar.Ghost.fst FStar.ErasedLogic.fst
	$(SFSTAR) FStar.FunctionalExtensionality.fst
	$(SFSTAR) FStar.HyperHeap.fst
	$(SFSTAR) FStar.Int8.fst
	$(SFSTAR) FStar.Int16.fst
	$(SFSTAR) FStar.Int31.fst
	$(SFSTAR) FStar.Int32.fst
	$(SFSTAR) FStar.Int63.fst
	$(SFSTAR) FStar.Int64.fst
	$(SFSTAR) FStar.ListProperties.fst
	$(SFSTAR) FStar.List.Tot.fst
	$(SFSTAR) FStar.Map.fst
	$(SFSTAR) FStar.MRef.fst
	$(SFSTAR) FStar.Option.fsti
	$(SFSTAR) FStar.OrdSet.fst
	$(SFSTAR) FStar.OrdMap.fst
	$(SFSTAR) FStar.OrdMapProps.fst
	$(SFSTAR) FStar.OrdSetProps.fst
	$(SFSTAR) FStar.PredicateExtensionality.fst
	$(SFSTAR) FStar.Set.fst
#	$(SFSTAR) stboot.fsi stboot.fst   -- Unrecognized file extension: stboot.fsi
	$(SFSTAR) FStar.Relational.fst
	$(SFSTAR) --explicit_deps   FStar.FunctionalExtensionality.fst FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.List.Tot.fst FStar.HyperHeap.fst stHyperHeap.fst
	$(SFSTAR) FStar.Tcp.fst
	$(SFSTAR)   FStar.Set.fst FStar.Heap.fst FStar.Map.fst FStar.TwoLevelHeap.fst
#	$(SFSTAR) --fs_typ_app FStar.Util.fst  # --fs_typ_app needed because automatically generated FStar.Util.fsti will get picked up by automatic dependency tracking and it's not a valid interface file without this flag ... oops, it's actually not valid even with this flag because of the ML exception syntax
	$(SFSTAR) FStar.Squash.fst
	$(SFSTAR) FStar.SquashProperties.fst
	$(SFSTAR) FStar.SquashEffect.fst

wc:
	sloccount .

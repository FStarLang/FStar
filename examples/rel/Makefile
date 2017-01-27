#FLAGS=
#LIB=

OTHERFLAGS+=$(FLAGS) $(LIB)
FSTAR_HOME=../..
include ../Makefile.include

uall: all

all: ifc\
		 random_tapes\
		 delimited_release\
		 recursive

ifc:
	$(FSTAR) rel.fst whilelanguage.fst ifc.fst ifcExample.fst

random_tapes:
	$(FSTAR) bijection.fst random_tapes.fst

recursive:
	$(FSTAR) recursive.fst

delimited_release:
	$(FSTAR) delimited_release.fst

WhileReify:
	$(FSTAR) --include ../dm4free --include ../../ulib --explicit_deps FStar.List.Tot.fst FStar.ListProperties.fst FStar.Seq.fst FStar.FunctionalExtensionality.fst FStar.DM4F.IntStore.fst WhileReify.fst --verify_module WhileReify

IfcReify:
	$(FSTAR) --include ../dm4free --include ../../ulib --explicit_deps FStar.List.Tot.fst FStar.ListProperties.fst FStar.Seq.fst FStar.FunctionalExtensionality.fst FStar.DM4F.IntStore.fst rel.fst WhileReify.fst FStar.Squash.fsti FStar.Classical.fst IfcReify.fst --verify_module IfcReify

IfcReifyLow:
	$(FSTAR) --debug IfcReify --debug_level Low --debug_level Norm  --debug_level Rel --include ../dm4free --include ../../ulib --explicit_deps FStar.List.Tot.fst FStar.ListProperties.fst FStar.Seq.fst FStar.FunctionalExtensionality.fst FStar.DM4F.IntStore.fst rel.fst WhileReify.fst FStar.Squash.fsti FStar.Classical.fst IfcReify.fst --verify_module IfcReify > bidule

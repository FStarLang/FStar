FSTAR = ../../bin/fstar.exe

all: noninterference\
		 sample_examples\
		 ro_single\
		 simple_st2_examples\
		 smart_meter\
		 spdz\
		 cache\
		 ifc_ts\
		 make -C projection_tests

#		 ro\ ;;unstable

noninterference:
	$(FSTAR) noninterference.fst

sample_examples:
	$(FSTAR) sample_examples.fst

ro_single:
	$(FSTAR) ro_single.fst

ro:
	$(FSTAR) ro.fst

smart_meter:
	$(FSTAR) smart_meter.fst

spdz:
	$(FSTAR) spdz.fst

simple_st2_examples:
	$(FSTAR) simple_st2_examples.fst

cache:
	$(FSTAR) cache.fst

ifc_ts:
	$(FSTAR) ifc_ts.fst

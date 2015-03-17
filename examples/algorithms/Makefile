VERFILES=counters.fst intsort.fst insertionsort.fst mergesort.fst qsc.fst
OTHERFLAGS=
include ../Makefile.include
all: .all.ver downgrade

qsort_seq_libs: qsort_seq_props qsort_seq_perm
	$(FSTAR) 

qsort_seq_props: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqproperties.fst)
	$(FSTAR) $^

qsort_seq_perm: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqpermutation.fsi seqpermutation.fst)
	$(FSTAR) --admit_fsi SeqProperties $^ --initial_fuel 0 --max_fuel 0 --max_ifuel 0 --z3timeout 60

qsort_seq: $(addprefix ../../lib/, classical.fst seq.fst seqproperties.fsi seqpermutation.fsi) qs_seq2.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^  --z3timeout 20

qsort_seq_full: qsort_seq_libs qsort_seq

qsort_arr: $(addprefix ../../lib/, set.fst heap.fst stperm.fst seq.fst  seqproperties.fsi seqpermutation.fsi arr.fst) qsort_arr.fst
	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^ 

downgrade: $(addprefix ../../lib/, classical.fst ext.fst set.fsi set.fst heap.fst seq.fsi seq.fst seqproperties.fst) # arr.fst) downgrade.fst
	$(FSTAR) --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 1 $^ 

# qsort_arr: $(addprefix ../../lib/, classical.fst seq.fstarr.fst) qsort_arr.fst
# 	$(FSTAR) --admit_fsi SeqProperties --admit_fsi SeqPermutation $^  --z3timeout 20

qs_seq2: ../../lib/classical.fst ../../lib/seq.fsi ../../lib/seqproperties.fst qs_seq2.fst
	$(FSTAR) --admit_fsi Seq $^ --max_ifuel 1 --max_fuel 1 --initial_fuel 1

# qsort_seq: qsort_seq.fst
# 	$(FSTAR) ../../lib/seq.fst qsort_seq.fst --max_ifuel 1  --max_fuel 4

binary_search: binary_search.fst
	$(FSTAR) ../../lib/seq.fsi --admit_fsi Seq $^

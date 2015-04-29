mref: ext.fst set.fsi heap.fst st.fst mref.fst
		fstar --admit_fsi Set $^

st2: ext.fst set.fsi heap.fst st.fst st2.fst
	fstar --admit_fsi Set $^ $(OTHERFLAGS)

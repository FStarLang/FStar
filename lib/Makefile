
FSTAR = ../bin/fstar.exe

mref: ext.fst set.fsi heap.fst st.fst mref.fst
	$(FSTAR) --admit_fsi Set $^

st2: ext.fst set.fsi heap.fst st.fst st2.fst
	$(FSTAR) --admit_fsi Set $^

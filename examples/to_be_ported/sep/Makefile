all: hello evens rb

hello: log
	fstar --z3timeout 10000 --monadic_subtyping --dtencoding --skip_translation --z3exe --odir log --prims prims-sep.fst refset.fst dst.fst hello.fst

rb: log
	fstar --z3timeout 10000 --monadic_subtyping --dtencoding --skip_translation --z3exe --odir log --prims prims-sep.fst array.fst refset.fst dst.fst rbsep2.fst

evens: log
	fstar --trace_err --z3timeout 10000 --monadic_subtyping --z3exe --odir log --dtencoding array.fst refset.fst dst.fst evens.fst

log:
	mkdir -p log

FSTAR=fstar --dtencoding --silent --skip_translation #--logQueries --odir log

all: lin state auth auth2 ringbuffer stlc

auth: 
	$(FSTAR) auth.fst

auth2: 
	$(FSTAR) auth2.fst 

state:
	$(FSTAR) state.fs

lin:
	$(FSTAR) lin.fst

asserts:
	$(FSTAR) --dotnet4 --genIL --writePrims --prims prims-asserts.fst asserts.fst

ringbuffer: log prims-rb.fst ringbuffer.fst
	fstar --monadic_subtyping --z3timeout 30000 --skip_translation --z3exe --odir log --dtencoding --prims prims-rb.fst ringbuffer.fst 

stlc: log prims-lighter.fst stlc.fst
	fstar --lighter --prims prims-lighter.fst map.fst stlc.fst --odir log --z3exe --dtencoding

log:
	mkdir -p log

clean:

module MiniAny

noeq
type test = {
  a: FStar.UInt32.t;
  b: Steel.ST.C.Types.Base.void_ptr;
}

let x
  (f: test)
: Tot Steel.ST.C.Types.Base.void_ptr
= f.b

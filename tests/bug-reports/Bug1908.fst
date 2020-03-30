module Bug1908

type w =
  | U32

let t (w:w) =
  match w with
  | U32 -> FStar.UInt32.t

[@expect_failure]
noeq
type r = {
  m : t U32;
  n : x:int{x == m}
}


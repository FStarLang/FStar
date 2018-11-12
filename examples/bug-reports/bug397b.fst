module Bug397b

open Platform.Bytes

type t (i:int) =
  | C of int

let bar (i:int) (s:t i) (d:int) (b:bytes)=
  C 1, 2

(* works *)
let foo2 (i:int) (s: t i) =
  bar i s 0

(* fails, but now error message is OK *)
let foo (i:int) (s: t i) =
  let b = createBytes 1 0uy in
  bar i s 0 b

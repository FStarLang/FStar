module CherryEq
module U32 = FStar.UInt32
open FStar.All

(* Structural equality on reference-counted values: a cell compares by its
   tag and fields, and the last field of the cell's own type by going round
   again, so that two long lists compare in constant stack.  The inputs come
   through [hide] so that extraction cannot fold the comparisons away. *)
let hide (#a: Type) (x: a) : ML a = x

let rec build (n: nat) (acc: list int) : ML (list int) =
  if n = 0 then acc else build (n - 1) (n :: acc)

type tree = | Leaf | Node : tree -> int -> string -> tree -> tree
let rec lefty (n: nat) (t: tree) : ML tree =
  if n = 0 then t else lefty (n - 1) (Node t n "x" Leaf)

(* A by-value record holding counted values, one of them a type with two
   recursive fields. *)
type r = { name: string; xs: list int; t: tree }
type shape = | Circle of int | Rect of int & int | Empty

let eql (x y: list int) : bool = x = y
let neql (x y: list int) : bool = x <> y
let eqt (x y: tree) : bool = x = y
let eqr (x y: r) : bool = x = y
let eqo (x y: option (list string)) : bool = x = y
let eqs (x y: list shape) : bool = x = y

let main () : ML U32.t =
  let big = build 1000000 [] in
  let big2 = build 1000000 [] in
  let big3 = build 999999 [] in
  let one = hide 1 in
  let nil = hide [] in
  let t1 = hide (Node (Node Leaf 1 "a" Leaf) 2 "bb" (Node Leaf 3 "c" Leaf)) in
  let t2 = hide (Node (Node Leaf 1 "a" Leaf) 2 ("b" ^ "b") (Node Leaf 3 "c" Leaf)) in
  let t3 = hide (Node (Node Leaf 1 "a" Leaf) 2 "bb" (Node Leaf 3 "d" Leaf)) in
  let lf = hide Leaf in
  let a = hide "a" in
  let e = hide Empty in
  let ok =
    eql big big2 && eql big big && not (eql big big3) && neql big big3 &&
    not (eql (one :: big) (2 :: big)) && eql nil [] && not (eql nil [one]) &&
    eql (hide [100000000000000000000; 1]) [100000000000000000000; one] &&
    eqt t1 t2 && not (eqt t1 t3) && eqt lf Leaf && not (eqt lf t1) &&
    eqt (lefty 10000 Leaf) (lefty 10000 Leaf) &&
    eqr { name = a; xs = [1; 2]; t = t1 } { name = "a"; xs = [1; 2]; t = t2 } &&
    not (eqr { name = a; xs = [1; 2]; t = t1 } { name = "a"; xs = [1; 3]; t = t1 }) &&
    eqo (Some [a; "b"]) (Some ["a"; "b"]) && not (eqo (hide None) (Some [])) &&
    eqo (hide None) None &&
    eqs [Circle 1; Rect (2, 3); e] [Circle 1; Rect (2, 3); Empty] &&
    not (eqs [Circle 1; Rect (2, 3); e] [Circle 1; Rect (2, 4); Empty]) &&
    not (eqs [e] [Circle 0]) in
  if ok then 0ul else 1ul

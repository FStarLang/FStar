module CherryDyn
module U32 = FStar.UInt32
open FStar.All
open FStar.Dyn

(* The any type (cherry.md, "The any type"): [dyn] is a [cherry_any], a
   value word and the run-time type information of what it holds.  Values
   that fit a word are stored inline, the others in a counted cell; the
   [rtti] carries the increment, decrement and mark functions, so a [dyn]
   held anywhere releases what it holds, which AddressSanitizer's leak check
   sees.  The inputs come through [hide] so that extraction cannot fold
   them. *)
let hide (#a: Type) (x: a) : ML a = x

type tree = | Leaf | Node of tree & int & tree

let rec sum (t: tree) : int = match t with Leaf -> 0 | Node (l, x, r) -> sum l + x + sum r
let rec suml (l: list int) : int = match l with [] -> 0 | x :: xs -> x + suml xs

(* In a datatype. *)
noeq type box = | Box of dyn & string

(* In a global, which the mark pass reaches through the rtti. *)
let g : dyn = mkdyn [10; 20; 30]

let wrap (x: list int) : dyn = mkdyn x
let adder (n: int) : int -> int = fun x -> x + n

let main () : ML U32.t =
  let d1 = wrap (hide [1; 2; 3]) in
  let d2 = mkdyn (hide (Node (Node (Leaf, 1, Leaf), 2, Leaf))) in
  let d3 = mkdyn (hide 42) in
  let d4 = mkdyn (adder (hide 5)) in
  (* Larger than a word: boxed. *)
  let d5 = mkdyn (hide (1, "two", [3])) in
  (* A dyn of a dyn. *)
  let d6 = mkdyn #dyn d1 in
  (* Plain: no counting at all. *)
  let d7 = mkdyn (hide true) in
  let b = Box (mkdyn (hide "boxed"), hide "tag") in
  let l : list int = undyn d1 in
  let t : tree = undyn d2 in
  let i : int = undyn d3 in
  let f : int -> int = undyn d4 in
  let (x, s, ys) : int & string & list int = undyn d5 in
  let d1' : dyn = undyn d6 in
  assume (dyn_has_ty d1' (list int));
  let l' : list int = undyn d1' in
  let bl : bool = undyn d7 in
  let gl : list int = undyn g in
  let Box (bd, tg) = b in
  assume (dyn_has_ty bd string);
  let bs : string = undyn bd in
  let ok1 = suml l = 6 && sum t = 3 && i = 42 && f 10 = 15 in
  let ok2 = x = 1 && s = "two" && suml ys = 3 && suml l' = 6 && bl in
  let ok3 = suml gl = 60 && bs = "boxed" && tg = "tag" in
  if ok1 && ok2 && ok3 then 0ul else 1ul

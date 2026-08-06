module KrmlBasic
module U32 = FStar.UInt32
module I32 = FStar.Int32

(* Enough shapes to exercise the karamel translation: a record, a recursive
   function, a variant with a match, and machine arithmetic throughout. *)
noeq type shape =
  | Square of U32.t
  | Rect   : U32.t -> U32.t -> shape

type point = { px : U32.t; py : U32.t }

let area (s:shape) : U32.t =
  match s with
  | Square w -> U32.mul_mod w w
  | Rect w h -> U32.mul_mod w h

let rec sum (n:U32.t) (acc:U32.t) : Tot U32.t (decreases U32.v n) =
  if U32.eq n 0ul then acc
  else sum (U32.sub_mod n 1ul) (U32.add_mod acc n)

let manhattan (p:point) : U32.t = U32.add_mod p.px p.py

let is_square (s:shape) : bool = Square? s

let main () : I32.t =
  let a = area (Square 3ul) in
  let b = area (Rect 2ul 5ul) in
  let c = manhattan ({ px = sum 10ul 0ul; py = 1ul }) in
  let tot_area = U32.add_mod a (U32.add_mod b c) in
  if U32.eq tot_area 75ul && is_square (Square 1ul) then 0l else 1l

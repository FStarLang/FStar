module KrmlBasic
module U32 = FStar.UInt32
module I32 = FStar.Int32
module U8  = FStar.UInt8
module U16 = FStar.UInt16
module U64 = FStar.UInt64
module SZ  = FStar.SizeT
module Cast = FStar.Int.Cast

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

(* Width conversions: [FStar.Int.Cast] is realized by krmllib, and the
   [FStar.SizeT] ones are coercions. *)
let truncate (x:U32.t) : U8.t = Cast.uint32_to_uint8 x
let roundtrip (x:U32.t) : U32.t = Cast.uint8_to_uint32 (truncate x)
let via_sizet (x:U16.t) : U64.t = SZ.sizet_to_uint64 (SZ.uint16_to_sizet x)

(* Section 6, pass 8: a cycle has no order in which every member precedes its
   uses, so the SCC pass has to find it.  karamel recovers the recursion
   itself, but it still needs the definitions to reach it. *)
let rec even (n:U32.t) : Tot bool (decreases U32.v n) =
  if U32.eq n 0ul then true else odd (U32.sub n 1ul)
and odd (n:U32.t) : Tot bool (decreases U32.v n) =
  if U32.eq n 0ul then false else even (U32.sub n 1ul)

(* Section 6, pass 7: [ph] describes no part of the representation, so it must
   be gone by the time karamel is asked to instantiate the declaration. *)
noeq type tagged (a:Type0) (ph:Type0) =
  | L : a -> tagged a ph
  | R : a -> tagged a ph
let untag (#a:Type0) (#ph:Type0) (x: tagged a ph) : a =
  match x with L v -> v | R v -> v

(* Section 6, pass 1, on the C side: F* discharges the division's precondition
   by reasoning that [&&] does not reach its right operand, so a strict
   translation would divide by zero -- which in C is undefined behaviour, not
   an exception. *)
let safe (x:U32.t) : bool = U32.gt x 0ul && U32.gt (U32.div 100ul x) 5ul

let main () : I32.t =
  let a = area (Square 3ul) in
  let b = area (Rect 2ul 5ul) in
  let c = manhattan ({ px = sum 10ul 0ul; py = 1ul }) in
  let tot_area = U32.add_mod a (U32.add_mod b c) in
  let t = roundtrip 0x1234ff07ul in
  let s = via_sizet 4097us in
  let phantom = U32.add_mod (untag #U32.t #bool (L 3ul)) (untag #U32.t #I32.t (R 4ul)) in
  if U32.eq tot_area 75ul && is_square (Square 1ul)
     && U32.eq t 7ul && U64.eq s 4097uL
     && even 10ul && odd 7ul && U32.eq phantom 7ul
     && not (safe 0ul) && safe 10ul
  then 0l else 1l

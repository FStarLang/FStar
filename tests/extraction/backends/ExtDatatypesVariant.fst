module ExtDatatypesVariant

/// Multi-constructor inductives with payloads: a real tagged union.
///
/// This is where discriminators (`Circle?`) and projectors (`Circle?.radius`)
/// both have to line up with the tag. Reading the wrong union member is a
/// silent wrong value, so we check the projectors both through pattern
/// matching and directly.
///
/// Non-recursive on purpose: recursive inductives live in ExtDatatypesRec.
/// Note that every constructor application is `let`-bound before it is used:
/// applying a projector directly to a constructor application crashes krml,
/// which is pinned down separately in ExtProjectorOfCtor.

module I32 = FStar.Int32
module U32 = FStar.UInt32

let chk (n:I32.t) (b:bool{b}) : I32.t = if b then 0l else n
let ( &&& ) (a b : I32.t) : I32.t = if a = 0l then b else a

let one : U32.t = 1ul
let two : U32.t = 2ul
let three : U32.t = 3ul
let seven : U32.t = 7ul

type shape =
  | Circle : radius:U32.t -> shape
  | Rect   : w:U32.t -> h:U32.t -> shape
  | Empty  : shape

let area (s:shape) : U32.t =
  match s with
  | Circle r -> U32.mul_mod (U32.mul_mod 3ul r) r
  | Rect w h -> U32.mul_mod w h
  | Empty -> 0ul

/// A constructor with exactly one field, which some backends special-case.
type boxed = | Box : U32.t -> boxed

let unbox (b:boxed) : U32.t = match b with | Box v -> v

/// `option` and `either` from Prims/FStar.Pervasives.
let opt_or (o:option U32.t) (d:U32.t) : U32.t =
  match o with
  | Some v -> v
  | None -> d

let main () : I32.t =
  let c1 = Circle one in
  let c7 = Circle seven in
  let r12 = Rect one two in
  let r37 = Rect three seven in
  let e = Empty in
  let b = Box seven in
  let so = Some three in
  let no : option U32.t = None in
     chk 1l (U32.eq (area (Circle two)) 12ul)
 &&& chk 2l (U32.eq (area r37) 21ul)
 &&& chk 3l (U32.eq (area e) 0ul)
 &&& chk 4l (Circle? c1)
 &&& chk 5l (not (Circle? r12))
 &&& chk 6l (not (Circle? e))
 &&& chk 7l (Empty? e)
 &&& chk 8l (U32.eq (Circle?.radius c7) 7ul)
 &&& chk 9l (U32.eq (Rect?.w r12) 1ul)
 &&& chk 10l (U32.eq (Rect?.h r12) 2ul)
     (* the second field must not be read as the first *)
 &&& chk 11l (not (U32.eq (Rect?.w r12) (Rect?.h r12)))
 &&& chk 12l (U32.eq (unbox b) 7ul)
 &&& chk 13l (U32.eq (opt_or so one) 3ul)
 &&& chk 14l (U32.eq (opt_or no seven) 7ul)
 &&& chk 15l (Some? so)
 &&& chk 16l (None? no)

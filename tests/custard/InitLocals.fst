module InitLocals

(* --custard_init_locals: every local the printer declares without an
   initializer gets a zero of its type.  The match results below are
   statement-shaped, so each is a temporary declared before the match and
   assigned in its branches. *)

module U32 = FStar.UInt32

type pair = { left: U32.t; right: bool }

type color = | Red | Green | Blue

type shape =
  | Empty : shape
  | Circle : radius:U32.t -> shape
  | Rect : width:U32.t -> height:U32.t -> shape

type wrapper = { inner: pair; tint: color; outline: shape }

let mk_pair (x:U32.t) : pair =
  match x with
  | 0ul -> let y = U32.add_mod x 1ul in { left = y; right = true }
  | _ -> let y = U32.add_mod x 2ul in { left = y; right = false }

let mk_color (x:U32.t) : color =
  match x with
  | 0ul -> let _ = U32.add_mod x 1ul in Red
  | 1ul -> Green
  | _ -> Blue

let mk_shape (x:U32.t) : shape =
  match x with
  | 0ul -> Empty
  | 1ul -> let r = U32.add_mod x 4ul in Circle r
  | _ -> let w = U32.add_mod x 1ul in Rect w x

let mk_wrapper (x:U32.t) : wrapper =
  match x with
  | 0ul -> let p = mk_pair x in { inner = p; tint = Green; outline = Empty }
  | _ -> let s = mk_shape x in { inner = mk_pair x; tint = mk_color x; outline = s }

let area (s:shape) : U32.t =
  match s with
  | Empty -> 0ul
  | Circle r -> r
  | Rect w h -> U32.mul_mod w h

let pick (x:U32.t) : U32.t =
  let p : pair =
    match x with
    | 0ul -> let y = U32.add_mod x 1ul in { left = y; right = true }
    | _ -> mk_pair x
  in
  let c : color =
    match x with
    | 0ul -> let _ = U32.add_mod x 1ul in Red
    | _ -> mk_color x
  in
  let s : shape =
    match x with
    | 0ul -> let r = U32.add_mod x 4ul in Circle r
    | _ -> mk_shape x
  in
  let w : wrapper =
    match x with
    | 0ul -> let q = mk_pair x in { inner = q; tint = c; outline = s }
    | _ -> mk_wrapper x
  in
  if p.right && Red? c && Red? w.tint then U32.add_mod p.left (area s) else 0ul

let main () : FStar.Int32.t =
  let p = mk_pair 0ul in
  let w = mk_wrapper 2ul in
  let c = mk_color 1ul in
  if U32.eq p.left 1ul && p.right && U32.eq w.inner.left 4ul && Blue? w.tint
     && Green? c && U32.eq (area w.outline) 6ul && U32.eq (area (mk_shape 1ul)) 5ul
     && U32.eq (pick 0ul) 5ul && U32.eq (pick 3ul) 0ul
  then 0l else 1l

module MiniParse.Spec.Int
include MiniParse.Spec.Combinators

module U8 = FStar.UInt8

let parse_u8 : parser U8.t = make_total_constant_size_parser 1 U8.t (fun x -> Seq.index x 0)

let serialize_u8 : serializer parse_u8 = Serializer (fun x -> Seq.create 1 x)

inline_for_extraction
let mk_u8 (n: nat { n < 256 } ) : Tot U8.t = U8.uint_to_t n

inline_for_extraction
let bounded_u8 (b: nat) : Tot eqtype = (x: U8.t { U8.v x < b } )

inline_for_extraction
let bounded_fun (a: Type) (b: nat) : Tot Type =
  a -> Tot (bounded_u8 b)

inline_for_extraction
let map_u8_to_bounded_u8
  (a: Type)
  (bound: nat)
  (f: (a -> Tot U8.t))
  (g: (x: a) -> Tot (squash (U8.v (f x) < bound)))
  (a' : Type)
  (bound' : nat)
  (u1: squash (a == a'))
  (u2: squash (bound == bound'))
: Tot (bounded_fun a' bound')
= fun x ->
  [@inline_let]
  let _ = g x in
  [@inline_let]
  let y' : bounded_u8 bound = f x in
  y'

let pred_pre
  (bound: nat { bound > 0 /\ bound <= 256 } )
  (pred: bounded_u8 bound -> GTot Type0)
  (x: bounded_u8 (bound - 1))
: GTot Type0
= pred (x `U8.add` 1uy)

let pred_large_bound
  (bound: nat { bound > 256 } )
  (pred: bounded_u8 bound -> GTot Type0)
  (x: bounded_u8 (bound - 1))
: GTot Type0
= pred (x <: U8.t)

let rec forall_bounded_u8
  (bound: nat)
  (pred: (bounded_u8 bound -> GTot Type0))
: GTot Type0
= if bound = 0
  then True
  else if bound > 256
  then
    forall_bounded_u8 (bound - 1) (pred_large_bound bound pred)
  else
    pred 0uy /\ forall_bounded_u8 (bound - 1) (pred_pre bound pred)

let rec forall_bounded_u8_elim
  (bound: nat)
  (pred: (bounded_u8 bound -> GTot Type0))
  (x: bounded_u8 bound)
: Lemma
  (requires (forall_bounded_u8 bound pred))
  (ensures (pred x))
  (decreases bound)
= if bound = 0
  then ()
  else if bound > 256
  then
    let x' : bounded_u8 (bound - 1) = x <: U8.t in
    forall_bounded_u8_elim (bound - 1) (pred_large_bound bound pred) x'
  else if x = 0uy
  then ()
  else
    forall_bounded_u8_elim (bound - 1) (pred_pre bound pred) (x `U8.sub` 1uy)

inline_for_extraction
let bounded_u8_eq (b: nat) : Tot (bounded_u8 b -> bounded_u8 b -> Tot bool) =
  op_Equality

let parse_bounded_u8 (b: nat) : Tot (parser (bounded_u8 b)) =
  parse_synth
    (parse_filter parse_u8 (fun x -> U8.v x < b))
    (fun x -> x <: bounded_u8 b)
    (fun x -> x)

let serialize_bounded_u8 (b: nat) : Tot (serializer (parse_bounded_u8 b)) =
  Serializer (fun x -> serialize serialize_u8 x)

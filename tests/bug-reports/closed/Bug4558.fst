module Bug4558

open FStar.UInt

(* A lemma whose body ends in [assert p] is checked by relating
   [squash p <: squash post].  The attempt to unify the two propositions
   used to fully normalize [logand ...] and [dec (enc p)] to compare them,
   which unfolds [to_vec]/[from_vec] on a symbolic 64-bit argument and takes
   time exponential in the width. *)

type pair = p: (uint_t 64 & uint_t 64) { let (a, b) = p in a < 16 /\ b < 16 }

let enc (p: pair) : uint_t 64 =
  let (a, b) = p in
  logor a (shift_left b 4)

let dec (op: uint_t 64) : uint_t 64 & uint_t 64 =
  (logand op (to_uint_t 64 0xF), logand (shift_right op 4) (to_uint_t 64 0xF))

let roundtrip_ok (p: pair) : Lemma (ensures dec (enc p) == p) =
  let (a, b) = p in
  admit ();
  assert (logand (shift_right (enc p) 4) (to_uint_t 64 0xF) == b);
  ()

let roundtrip_final_assert (p: pair) : Lemma (ensures dec (enc p) == p) =
  let (a, b) = p in
  admit ();
  assert (logand (shift_right (enc p) 4) (to_uint_t 64 0xF) == b)

(* The lazy comparison must still descend into a refinement, which carries
   no arguments for the congruence step to recurse on.  Here the two
   refinement formulas differ only by [b2t]. *)

assume val parser (t: Type) : Type0
assume val parse_filter (#t: Type) (f: (t -> GTot bool)) : parser (x: t { f x == true })

let in_bounds (min: nat) (x: nat) : GTot bool = x >= min
let bounded (min: nat) = (x: nat { in_bounds min x })

let parse_bounded (min: nat) : parser (bounded min) = parse_filter (in_bounds min)

(* And it must try congruence before reducing: [serializer p] is a type
   abbreviation, so a whnf replaces the application -- whose argument the
   comparison wants to recurse into -- by a refinement that mentions [p]
   under a binder. *)

assume val correct (#t: Type) (p: parser t) (f: t -> GTot bool) : prop
let serializer (#t: Type) (p: parser t) = (f: (t -> GTot bool) { correct p f })
assume val tagged_union (#t: Type) (p: parser t) (f: t -> GTot t) : parser t
let dep_pair (#t: Type) (p: parser t) : parser t = tagged_union p (fun x -> x)
assume val serialize_tagged_union (#t: Type) (p: parser t) (f: t -> GTot t)
  : serializer (tagged_union p f)

let serialize_dep_pair (#t: Type) (p: parser t) : serializer (dep_pair p) =
  serialize_tagged_union p (fun x -> x)

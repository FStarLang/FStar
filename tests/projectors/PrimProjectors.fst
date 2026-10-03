module PrimProjectors

(* Projectors and discriminators are declaration-only: they are reduced by a
   primitive rule, not by unfolding a definition. *)

inline_for_extraction
noeq
type rcd (a:Type) = {
  fst : a;
  snd : int;
}

inline_for_extraction
type variant =
  | A : x:int -> variant
  | B : y:bool -> variant

noeq
type single = | Single : z:int -> single

(* Reduction happens under iota alone, without any delta step. *)
let _ = assert_norm (norm [iota] (Mkrcd?.snd ({ fst = 0; snd = 3 })) == 3)
let _ = assert_norm (norm [iota] (A?.x (A 7)) == 7)
let _ = assert_norm (norm [iota] (A? (B true)) == false)
let _ = assert_norm (norm [iota] (B? (B true)) == true)

(* A discriminator of a single-constructor type is always true. *)
let _ = assert_norm (norm [iota] (Single? (Single 1)) == true)

(* Projections also reduce in the SMT encoding. *)
let _ = assert (Mkrcd?.fst ({ fst = 'c'; snd = 0 }) == 'c')
let _ = assert (A? (A 1))

(* Over-applied projectors: the selected field is applied to the extra
   arguments. *)
let _ = assert_norm (norm [iota] (Mkrcd?.fst ({ fst = (fun (x:int) -> x + 1); snd = 0 }) 1) == 2)

(* Unapplied, a projector or discriminator is still a first-class function. *)
let _ = assert_norm (List.Tot.map Mkrcd?.snd [{fst=0; snd=1}] == [1])
let _ = assert_norm (List.Tot.filter A? [A 1; B false] == [A 1])

(* #4537: constructor WHNFs retain an environment of field closures. The
   constructor's universes and parameters must not be interpreted in that new
   environment, and a projected function's extra arguments still live in the
   caller's environment, not the constructor's. *)
let make_rcd #a (x:a) : rcd a = { fst = x; snd = 17 }

let project_under_binder #a (x:a) : Lemma ((make_rcd x).fst == x) =
  assert_norm ((make_rcd x).fst == x)

let apply_field (captured caller:int) : int =
  let r : rcd (int -> int) = make_rcd (fun (x:int) -> captured + x) in
  r.fst caller

let _ = assert_norm (apply_field 40 2 == 42)
let _ = assert_norm ((fun x -> apply_field x 2) == (fun x -> x + 2))

(* Reuse the record after projecting from it, in both weak-head and strong
   normalization contexts. A cached open constructor must never be rebuilt
   as though it were a closed term. *)
let reuse (x:int) =
  let r = make_rcd x in
  (r.fst, r, r.snd)

let _ = assert_norm (reuse 42 == (42, {fst=42; snd=17}, 17))

let stuck #a (r:rcd a) : Lemma (Mkrcd?.fst r == r.fst) =
  assert_norm (norm [iota; zeta] (let s = r in Mkrcd?.fst s) == r.fst)

(* Indexed constructors have both parameters and indices before the
   projectee, and their fields need not start at argument zero. *)
noeq
type indexed (a:Type) : nat -> Type =
  | Item : n:nat -> value:a -> indexed a n
  | Other : n:nat -> indexed a n

let make_indexed #a (n:nat) (x:a) : indexed a n = Item n x

let _ = assert_norm (Item?.value (make_indexed 3 42) == 42)
let _ = assert_norm (Item? (make_indexed 3 42) == true)
let _ = assert_norm (Item? (Other #int 3) == false)

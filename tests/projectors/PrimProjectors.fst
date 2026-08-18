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

module UnfoldClass

open FStar.Tactics.V2
open FStar.Tactics.Typeclasses

module L = FStar.List.Tot

(* All fields here are propositional, so F* infers `noeq` for the class. The
`unfold` written by the user must not clash with that inferred qualifier:
refusing the combination would make `unfold class` fail for a reason the
user did not choose. Reduced from Kuiper.Array.Vectorized. *)
inline_for_extraction noextract
unfold
class sized (et : Type) = {
  [@@@no_method] _chunk : nat;
  [@@@no_method] _pf : squash (_chunk == 16);
}

unfold
class uc (a:Type) = {
  um : a -> nat;
}

class pc (a:Type) = {
  pm : a -> nat;
}

instance ui : uc bool = { um = (fun b -> if b then 1 else 0); }
instance pi : pc bool = { pm = (fun b -> if b then 1 else 0); }

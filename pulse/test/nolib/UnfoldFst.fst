module UnfoldFst

#lang-pulse
open Pulse.Nolib
module L = FStar.List.Tot

assume val p : list int -> prop

let p' (xs : list (int & bool)) = p (L.map fst xs)

(* This will fail if the fst is unfolded, as it introduces a lambda
   in the SMT encoding. *)
fn test (xs : list (int & bool))
  requires pure (p' xs)
  ensures  pure (p (L.map fst xs))
{
  ();
}

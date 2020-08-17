module Monotonic.Map

open FStar.HyperStack
open FStar.HyperStack.ST

module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* Partial, dependent maps *)
type map' (a:Type) (b:a -> Type) =
  (x:a -> Tot (option (b x)))

(* Partial, dependent maps, with a whole-map invariant *)
type map (a:Type) (b:a -> Type) (inv:map' a b -> Type0) =
  m:map' a b{inv m}

let grows_aux #a #b #inv :Preorder.preorder (map a b inv) =
  fun (m1 m2:map a b inv) ->
  forall x.{:pattern (Some? (m1 x))}
      Some? (m1 x) ==> Some? (m2 x) /\ Some?.v (m1 x) == Some?.v (m2 x)

[@@"opaque_to_smt"]
let grows #a #b #inv = grows_aux #a #b #inv

// This line fails at extraction
// TODO: Minimize
(* Monotone, partial, dependent maps, with a whole-map invariant *)
//type t r a b inv = m_rref r (map a b inv) grows  //maybe grows can include the inv?

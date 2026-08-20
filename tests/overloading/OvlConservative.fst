module OvlConservative
open OvlInt
open OvlBool

(* When nothing discriminates, resolution must land on exactly the
   candidate it lands on today: the innermost one, here OvlBool's,
   since OvlBool is opened last. *)
let still_first_match : bool = f true

(* A polymorphic candidate is never eliminated, since its formal has no
   rigid head. It stays in the running and, being first, wins. *)
let poly (x:'a) : 'a = x
let poly_wins : int = poly 0

(* An argument whose type we cannot determine eliminates nothing, so
   again the primary candidate is used and the user gets an ordinary
   type error rather than a resolution error. *)
let unknown_arg (x:bool) : bool = f x

(* Deduplication: FStar.Seq re-exports FStar.Seq.Base, so `seq` reaches
   the same definition by two paths. That is one candidate, not two, and
   in particular not an ambiguity. *)
open FStar.Seq
let dedup (s : seq int) : nat = length s

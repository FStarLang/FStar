module Bug4521Abs

(* An abstract type in an interface is indistinguishable, from a client's point
   of view, from an assumed type constructor: both are `Assumption`s whose
   result type is a sort.  So the `constructor_distinct` SMT axiom must *not* be
   inferred from that shape -- the implementation below is free to define `foo`
   to be an existing type, and a client that assumed `foo` distinct from every
   other type could then derive `False` from `foo_eq_int`.

   Writing `new` on `foo` is what would license the axiom, and F* rejects it
   here ("definitions cannot be marked `assume`") precisely because `foo` has a
   definition. *)

val foo : Type0
val foo_eq_int : unit -> Lemma (foo == int)

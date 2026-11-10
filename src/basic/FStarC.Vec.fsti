module FStarC.Vec

open FStarC.Effect

(* Growable arrays, with amortized constant time [push].  Indices are native
   integers; an index out of bounds raises an exception.  A vector is never
   empty: it starts with its first element, which also fills the unused
   capacity where the representation needs it to. *)

assume new
type vec : Type -> Type0

val singleton (#a:Type) (x:a) : ML (vec a)
val length (#a:Type) (v:vec a) : ML FStarC.SmallInt.t
val get (#a:Type) (v:vec a) (i:FStarC.SmallInt.t) : ML a
val push (#a:Type) (v:vec a) (x:a) : ML unit

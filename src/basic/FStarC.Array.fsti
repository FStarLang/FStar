module FStarC.Array

open FStarC.Effect

(* Mutable arrays.  Indices are native integers; an index out of bounds
   raises an exception. *)

assume new
type array : Type -> Type0

val make (#a:Type) (n:FStarC.SmallInt.t) (x:a) : ML (array a)
val length (#a:Type) (arr:array a) : ML FStarC.SmallInt.t
val get (#a:Type) (arr:array a) (i:FStarC.SmallInt.t) : ML a
val set (#a:Type) (arr:array a) (i:FStarC.SmallInt.t) (x:a) : ML unit
val append (#a:Type) (arr1 arr2:array a) : ML (array a)

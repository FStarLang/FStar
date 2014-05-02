(* -------------------------------------------------------------------- *)
type 'a set

(* Create an empty set, using the OCaml default polymorphic
 * ordering. (FIXME: can [empty] can be a value ?) *)
val empty : unit -> 'a set

(* No exception is raised if the set already contains the given
 * element. *)
val add : 'a -> 'a set -> 'a set

(* No exception is raised if the set doesn't contain the given
 * element. *)
val remove : 'a -> 'a set -> 'a set

val mem : 'a -> 'a set -> bool

val count : 'a set -> int

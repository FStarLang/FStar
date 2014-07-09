(* -------------------------------------------------------------------- *)
type ('key, 'a) map

exception KeyNotFoundException

val empty : unit -> ('key, 'a) map

val add : 'key -> 'a -> ('key, 'a) map -> ('key, 'a) map

val remove : 'key -> ('key, 'a) map -> ('key, 'a) map

val find : 'key -> ('key, 'a) map -> 'a

val contains : 'key -> ('key, 'a) map -> bool

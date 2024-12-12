(* -------------------------------------------------------------------- *)
type ('a, 'b) dbmap

val create : DB.db -> ('a, 'b) dbmap
val put    : 'a -> 'b  -> ('a, 'b) dbmap -> unit
val get    : 'a -> ('a, 'b) dbmap -> 'b option

(* -------------------------------------------------------------------- *)
type item =
| IInt    : int -> item
| IString : string -> item
| IUser   : ('a -> string) * 'a -> item

val print1 : string -> item -> string
val print2 : string -> item -> item -> string
val print3 : string -> item -> item -> item -> string
val print4 : string -> item -> item -> item -> item -> string

val print : string -> item list -> string

(* -------------------------------------------------------------------- *)
exception DBError of string

(* -------------------------------------------------------------------- *)
type db
type data = string

val opendb  : string -> db
val closedb : db -> unit
val put     : db -> data -> data -> unit
val get     : db -> data -> data option
val remove  : db -> data -> bool
val all     : db -> (data * data) list
val keys    : db -> data list
val tx      : db -> (db -> 'a) -> 'a

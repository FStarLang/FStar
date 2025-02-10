module FStarC.IMap

open FStarC.Effect

(* mutable map from integer keys *)

type t 'value
val create : int -> t 'value
val clear : t 'value -> unit
val add : t 'value -> int -> 'value -> unit
val of_list : list (int&'value) -> t 'value
val try_find : t 'value -> int -> option 'value
val fold : t 'value -> (int -> 'value -> 'a -> 'a) -> 'a -> 'a
val remove : t 'value -> int -> unit

(* aliases *)
type imap = t
let imap_create n = create n
let imap_clear m = clear m
let imap_add k v = add k v
let imap_of_list l = of_list l
let imap_try_find m k = try_find m k
let imap_fold m f a = fold m f a
let imap_remove m k = remove m k

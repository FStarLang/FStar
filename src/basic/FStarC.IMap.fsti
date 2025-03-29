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
inline_for_extraction type imap = t
inline_for_extraction let imap_create n = create n
inline_for_extraction let imap_clear m = clear m
inline_for_extraction let imap_add k v = add k v
inline_for_extraction let imap_of_list l = of_list l
inline_for_extraction let imap_try_find m k = try_find m k
inline_for_extraction let imap_fold m f a = fold m f a
inline_for_extraction let imap_remove m k = remove m k

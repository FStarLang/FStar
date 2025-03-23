module FStarC.SMap

open FStarC.Effect

(* mutable string map *)

type t 'value
val create : int -> t 'value
val clear : t 'value -> unit
val add : t 'value -> string -> 'value -> unit
val of_list : list (string & 'value) -> t 'value
val try_find : t 'value -> string -> option 'value
val fold : t 'value -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a
val remove : t 'value -> string -> unit
(* The list may contain duplicates. *)
val keys : t 'value -> list string
val copy : t 'value -> t 'value
val size : t 'value -> int
val iter : t 'value -> (string -> 'value -> unit) -> unit

(* Aliases. We use inline_for_extraction so we don't have to define
these in the underlying ML file. *)
inline_for_extraction type smap = t
inline_for_extraction let smap_create u = create u
inline_for_extraction let smap_clear m = clear m
inline_for_extraction let smap_add m k v = add m k v
inline_for_extraction let smap_of_list l = of_list l
inline_for_extraction let smap_try_find m k = try_find m k
inline_for_extraction let smap_fold m f a = fold m f a
inline_for_extraction let smap_remove m k = remove m k
inline_for_extraction let smap_keys m = keys m
inline_for_extraction let smap_copy m = copy m
inline_for_extraction let smap_size m = size m
inline_for_extraction let smap_iter m f = iter m f

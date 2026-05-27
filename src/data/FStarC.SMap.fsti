module FStarC.SMap

open FStarC.Effect

(* mutable string map *)

type t 'value
val create : int -> ML (t 'value)
val clear : t 'value -> ML unit
val add : t 'value -> string -> 'value -> ML unit
val of_list : list (string & 'value) -> ML (t 'value)
val try_find : t 'value -> string -> ML (option 'value)
val fold : t 'value -> (string -> 'value -> 'a -> ML 'a) -> 'a -> ML 'a
val remove : t 'value -> string -> ML unit
(* The list may contain duplicates. *)
val keys : t 'value -> ML (list string)
val copy : t 'value -> ML (t 'value)
val size : t 'value -> ML int
val iter : t 'value -> (string -> 'value -> ML unit) -> ML unit

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

module FStarC.FMap

open FStarC.Effect

(* This is a mutable map, implemented as a reference to a persistent map.
This makes copies essentially free, and the interface behaves exactly the same as
the mutable map. The F is for "fake". *)

val t (v : Type) : Type0

val create : int -> ML (t 'value)
val clear : t 'value -> ML unit
val add : t 'value -> string -> 'value -> ML unit
val of_list : list (string&'value) -> ML (t 'value)
val try_find : t 'value -> string -> ML (option 'value)
val fold : t 'value -> (string -> 'value -> 'a -> 'a) -> 'a -> ML 'a
val remove : t 'value -> string -> ML unit
(* The list may contain duplicates. *)
val keys : t 'value -> ML (list string)
val copy : t 'value -> ML (t 'value)
val size : t 'value -> ML int
val iter : t 'value -> (string -> 'value -> ML unit) -> ML unit

(* Aliases *)
type fmap = t
let fmap_create u = create u
let fmap_clear m = clear m
let fmap_add m k v = add m k v
let fmap_of_list l = of_list l
let fmap_try_find m k = try_find m k
let fmap_fold m f a = fold m f a
let fmap_remove m k = remove m k
let fmap_keys m = keys m
let fmap_copy m = copy m
let fmap_size m = size m
let fmap_iter m f = iter m f

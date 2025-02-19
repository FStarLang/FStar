module FStarC.PSMap

open FStarC.Effect

(* persistent (pure) string map *)

type t 'value
val empty: unit -> t 'value // GH-1161
val add: t 'value -> string -> 'value -> t 'value
val find_default: t 'value -> string -> 'value -> 'value
val try_find: t 'value -> string -> option 'value
val fold: t 'value -> (string -> 'value -> 'a -> 'a) -> 'a -> 'a
val find_map: t 'value -> (string -> 'value -> option 'a) -> option 'a
val modify: t 'value -> string -> (option 'value -> 'value) -> t 'value
val merge: t 'value -> t 'value -> t 'value
val remove: t 'value -> string -> t 'value
val keys : t 'value -> list string

(* aliases *)
type psmap = t
let psmap_empty () = empty ()
let psmap_add m k v = add m k v
let psmap_find_default m k v = find_default m k v
let psmap_try_find m k = try_find m k
let psmap_fold m f a = fold m f a
let psmap_find_map m f = find_map m f
let psmap_modify m k f = modify m k f
let psmap_merge m1 m2= merge m1 m2
let psmap_remove m k = remove m k

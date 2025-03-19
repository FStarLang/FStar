module FStarC.PIMap

open FStarC.Effect

(* persistent (pure) map with integer keys *)

type t 'value
val empty: unit -> t 'value // GH-1161
val add: t 'value -> int -> 'value -> t 'value
val find_default: t 'value -> int -> 'value -> 'value
val try_find: t 'value -> int -> option 'value
val fold: t 'value -> (int -> 'value -> 'a -> 'a) -> 'a -> 'a
val remove: t 'value -> int -> t 'value

type pimap = t
let pimap_empty u = empty u
let pimap_add m k v = add m k v
let pimap_find_default m k = find_default m k
let pimap_try_find m k = try_find m k
let pimap_fold m f a = fold m f a
let pimap_remove m k = remove m k

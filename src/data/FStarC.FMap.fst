module FStarC.FMap

open FStarC
open FStarC.Effect
open FStarC.PSMap

type t x = ref (PSMap.t x)

let create _sz = mk_ref (PSMap.empty ())
let clear m = m := PSMap.empty ()
let add m k v = m := PSMap.add !m k v
let of_list kvs =
  mk_ref (PSMap.of_list kvs)
let try_find m k = PSMap.try_find !m k
let fold m f acc =
  PSMap.fold !m f acc
let remove m k =
  m := PSMap.remove !m k
let keys m = PSMap.keys !m
let copy m = mk_ref !m
let size m = List.length (keys m)
let iter m f = keys m |> List.iter (fun k -> f k (Some?.v (try_find m k)))

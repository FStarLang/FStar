module Steel.IArray

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic

module G = FStar.Ghost
module Set = FStar.Set
module Map = FStar.Map

type u32 = FStar.UInt32.t

type hash_fn_t (k:eqtype) = k -> u32

val iarray (k:eqtype) (v:Type0) (h:hash_fn_t k) : Type0

type repr (k:eqtype) (v:Type0) = Map.t k v

let empty_repr (#k:eqtype) (#v:Type0) (x:v) : repr k v = Map.restrict Set.empty (Map.const x)

val ipts_to (#k:eqtype) (#v:Type0) (#h:hash_fn_t k) (arr:iarray k v h) (m:repr k v) : vprop

val create (#k:eqtype) (#v:Type0) (h:hash_fn_t k) (x:G.erased v) (n:u32)
  : SteelT (iarray k v h)
      emp
      (fun a -> ipts_to a (empty_repr (G.reveal x)))

val index (#k:eqtype) (#v:Type0) (#h:hash_fn_t k) (#m:G.erased (repr k v))
  (a:iarray k v h) (i:k)
  : SteelT (option v)
      (ipts_to a m)
      (fun r ->
       ipts_to a m
         `star`
       pure (Some? r ==> r == Some (Map.sel m i)))

val upd (#k:eqtype) (#v:Type0) (#h:hash_fn_t k) (#m:G.erased (repr k v))
  (a:iarray k v h) (i:k) (x:v)
  : SteelT unit
      (ipts_to a m)
      (fun _ -> ipts_to a (Map.upd m i x))

module PulseCore.BaseHeapSig
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H = PulseCore.Heap
val base_heap : heap_sig u#a
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat
val select_ghost (i:nat) (m:base_heap.sep.core) : GTot (option (H.cell u#a))
val ghost_ctr (b:base_heap.mem) : GTot nat

val interp_ghost_pts_to 
      (i:core_ghost_ref)
      (#meta:bool)
      (#a:Type u#a)
      (#pcm:FStar.PCM.pcm a)
      (v:a)
      (h0:(base_heap u#a).mem)
: Lemma
  (requires interpret (base_heap.ghost_pts_to meta #a #pcm i v) h0)
  (ensures (
    match select_ghost (core_ghost_ref_as_addr i) (base_heap.sep.lens_core.get h0) with
    | None -> False
    | Some c ->
      let H.Ref meta' a' pcm' v' = c in
      meta == reveal meta' /\
      a == a' /\
      pcm == pcm' /\
      compatible pcm v v'))
      
val ghost_pts_to_compatible_equiv 
      (#meta:bool)
      (#a:Type)
      (#pcm:_)
      (x:ghost_ref a pcm)
      (v0:a)
      (v1:a{composable pcm v0 v1})
: Lemma ((base_heap.ghost_pts_to meta x v0 `base_heap.star` base_heap.ghost_pts_to meta x v1) ==
         (base_heap.ghost_pts_to meta x (op pcm v0 v1)))

val ghost_extend
    (meta:erased bool)
    (#ex:inames base_heap)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: ghost_action_except base_heap (ghost_ref a pcm) ex    
      base_heap.emp 
      (fun r -> base_heap.ghost_pts_to meta r x)

val ghost_read
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except base_heap (erased (v:a{compatible p x v /\ p.refine v})) ex
    (base_heap.ghost_pts_to meta r x)
    (fun v -> base_heap.ghost_pts_to meta r (f v))

val ghost_write
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except base_heap unit ex
    (base_heap.ghost_pts_to meta r x)
    (fun _ -> base_heap.ghost_pts_to meta r y)

val ghost_share
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except base_heap unit ex
    (base_heap.ghost_pts_to meta r (v0 `op pcm` v1))
    (fun _ -> base_heap.ghost_pts_to meta r v0 `base_heap.star` base_heap.ghost_pts_to meta r v1)

val ghost_gather
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except base_heap (squash (composable pcm v0 v1)) ex
    (base_heap.ghost_pts_to meta r v0 `base_heap.star` base_heap.ghost_pts_to meta r v1)
    (fun _ -> base_heap.ghost_pts_to meta r (op pcm v0 v1))

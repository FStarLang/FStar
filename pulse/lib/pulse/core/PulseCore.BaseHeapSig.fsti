module PulseCore.BaseHeapSig
open PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H = PulseCore.Heap
val base_heap : heap_sig u#a
val core_ghost_ref_as_addr (_:core_ghost_ref) : GTot nat
val select_ghost (i:nat) (m:(base_heap u#a).sep.core) : GTot (option (H.cell u#a))
val ghost_ctr (b:base_heap.mem) : GTot nat
let free_above_ghost_ctr (m:base_heap.mem)
: prop
= forall addr. addr >= ghost_ctr m ==> select_ghost addr (core_of m) == None

val mem_invariant_interp (ex:inames base_heap) (h0:base_heap.mem) (h1:base_heap.sep.core)
: Lemma (base_heap.interp (base_heap.mem_invariant ex h0) h1 ==>
         free_above_ghost_ctr h0)
val inames_ok_trivial (ex:inames base_heap) (h:base_heap.mem)
: Lemma (inames_ok ex h)

val interp_ghost_pts_to 
      (i:core_ghost_ref)
      (#meta:bool)
      (#a:Type u#a)
      (#pcm:FStar.PCM.pcm a)
      (v:a)
      (h0:(base_heap u#a).sep.core)
: Lemma
  (requires base_heap.interp (base_heap.ghost_pts_to meta #a #pcm i v) h0)
  (ensures (
    match select_ghost (core_ghost_ref_as_addr i) h0 with
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

let heap_cell_evolves (h0 h1:option H.cell)
: prop
= match h0, h1 with
  | None, None -> True
  | None, Some (H.Ref meta _ _ _) -> reveal meta == false
  | Some (H.Ref meta a p v), Some (H.Ref meta' a' p' v') ->
    meta == meta' /\ (reveal meta ==> a==a' /\ p==p' /\ v==v')
  | _, _ -> False

let heaps_preserve_inames (m0 m1:base_heap.mem) =
  ghost_ctr m0 <= ghost_ctr m1 /\
  (forall (addr:nat).
    heap_cell_evolves (select_ghost addr (core_of m0)) (select_ghost addr (core_of m1)))

let preserves_inames 
    (#a:Type u#a)
    (#mg:bool)
    (#pre:base_heap.slprop)
    (#post:a -> GTot (base_heap.slprop))
    (#ex:inames base_heap)
    (action:_action_except (base_heap u#h) a mg ex pre post)
= forall (m0:full_mem base_heap) frame. 
    interpret (pre `base_heap.star` frame `base_heap.star` base_heap.mem_invariant ex m0) m0 /\
    inames_ok ex m0
    ==> ( 
    let x, m1 = action frame m0 in
    heaps_preserve_inames m0 m1
    )

let single_ghost_allocation
        (meta:bool)
        (#a:Type)
        (#pcm:pcm a)
        (x:a{pcm.refine x})
        (r:ghost_ref a pcm)
        (h h1:base_heap.mem)
= (forall (a:nat).
    a <> ghost_ctr h ==>
    select_ghost a (core_of h) == select_ghost a (core_of h1)) /\
  ghost_ctr h1 == ghost_ctr h + 1 /\
  select_ghost (ghost_ctr h) (core_of h1) == Some (H.Ref meta a pcm x) /\
  ghost_ctr h == core_ghost_ref_as_addr r /\
  free_above_ghost_ctr h /\
  free_above_ghost_ctr h1

val ghost_extend
    (meta:erased bool)
    (#ex:inames base_heap)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: act:ghost_action_except base_heap (ghost_ref a pcm) ex    
        base_heap.emp 
        (fun r -> base_heap.ghost_pts_to meta r x) {
            reveal meta == false ==> preserves_inames act
        }


  
val ghost_extend_spec
      (#meta:bool)
      (#ex:inames base_heap)
      #a #pcm (x:a { pcm.refine x })
      (frame:base_heap.slprop)
      (h:full_mem base_heap { 
        inames_ok ex h /\
        interpret (base_heap.emp `base_heap.star`
                   frame `base_heap.star`
                   base_heap.mem_invariant ex h) h })      
: Lemma (
      let (r, h1) = ghost_extend meta #ex #a #pcm x frame h in
      single_ghost_allocation meta #a #pcm x r h h1
)

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
: act:ghost_action_except base_heap (erased (v:a{compatible p x v /\ p.refine v})) ex
        (base_heap.ghost_pts_to meta r x)
        (fun v -> base_heap.ghost_pts_to meta r (f v)) {
            preserves_inames act
        }

val ghost_write
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act:ghost_action_except base_heap unit ex
        (base_heap.ghost_pts_to meta r x)
        (fun _ -> base_heap.ghost_pts_to meta r y) {
            reveal meta == false ==> preserves_inames act
        }

val ghost_share
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act:ghost_action_except base_heap unit ex
    (base_heap.ghost_pts_to meta r (v0 `op pcm` v1))
    (fun _ -> base_heap.ghost_pts_to meta r v0 `base_heap.star` base_heap.ghost_pts_to meta r v1) {
        preserves_inames act
    }


val ghost_gather
    (#ex:inames base_heap)
    (#meta:erased bool)
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act:ghost_action_except base_heap (squash (composable pcm v0 v1)) ex
    (base_heap.ghost_pts_to meta r v0 `base_heap.star` base_heap.ghost_pts_to meta r v1)
    (fun _ -> base_heap.ghost_pts_to meta r (op pcm v0 v1)) {
        preserves_inames act
    }

val extend
    (#ex:inames base_heap)
    (#a:Type u#a)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: act:action_except base_heap (ref a pcm) ex    
        base_heap.emp 
        (fun r -> base_heap.pts_to r x) {
            preserves_inames act
        }

val read
    (#ex:inames base_heap)
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: act:action_except base_heap (v:a{compatible p x v /\ p.refine v}) ex
    (base_heap.pts_to r x)
    (fun v -> base_heap.pts_to r (f v)) {
        preserves_inames act
    }

val write
    (#ex:inames base_heap)
    (#a:Type)
    (#p:pcm a)
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: act:action_except base_heap unit ex
    (base_heap.pts_to r x)
    (fun _ -> base_heap.pts_to r y) {
        preserves_inames act
    }

val share
    (#ex:inames base_heap)
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: act:ghost_action_except base_heap unit ex
    (base_heap.pts_to r (v0 `op pcm` v1))
    (fun _ -> base_heap.pts_to r v0 `base_heap.star` base_heap.pts_to r v1) {
        preserves_inames act
    }

val gather
    (#ex:inames base_heap)
    (#a:Type)
    (#pcm:pcm a)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: act:ghost_action_except base_heap (squash (composable pcm v0 v1)) ex
    (base_heap.pts_to r v0 `base_heap.star` base_heap.pts_to r v1)
    (fun _ -> base_heap.pts_to r (op pcm v0 v1)) {
        preserves_inames act
    }

val pts_to_not_null_action 
      (#ex:inames base_heap)
      (#a:Type u#a)
      (#pcm:pcm a)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: act:ghost_action_except base_heap (squash (not (is_null r))) ex
    (base_heap.pts_to r v)
    (fun _ -> base_heap.pts_to r v) {
        preserves_inames act
    }

val exists_congruence 
        (#a:Type u#a)
        (w:a)
        (p:a -> base_heap.slprop)
: Lemma 
    (requires forall x. is_boxable (p x))
    (ensures is_boxable (exists_ p))
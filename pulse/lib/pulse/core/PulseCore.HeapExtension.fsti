module PulseCore.HeapExtension
open PulseCore.HeapSig

val extend (h:heap_sig u#a) : h2:heap_sig u#(a + 1) { h2.bprop == h.slprop }

val lift_iref (#h:heap_sig u#a) (i:h.iref) : (extend h).iref
// val lift_iname (#h:heap_sig u#a) (i:h.iname) : (extend h).iname
// val lift_inames (#h:heap_sig u#a) (is:inames h) : inames (extend h)
val lower_inames (#h:heap_sig u#a) (is:inames (extend h)) : inames h

// val lift_action
//     (#h:heap_sig u#h)
//     (#a:Type u#a)
//     (#mg:bool)
//     (#ex:inames h)
//     (#pre:h.slprop)
//     (#post:a -> h.slprop)
//     (action:_action_except h a mg ex pre post)
// : _action_except (extend h)
//     a mg (lift_inames ex) 
//     ((extend h).up pre)
//     (fun x -> (extend h).up (post x))

val lift_action_alt
    (#h:heap_sig u#h)
    (#a:Type u#a)
    (#mg:bool)
    (#ex:inames (extend h))
    (#pre:h.slprop)
    (#post:a -> GTot h.slprop)
    (action:_action_except h a mg (lower_inames ex) pre post)
: _action_except (extend h)
    a mg ex 
    ((extend h).up pre)
    (fun x -> (extend h).up (post x))

val dup_inv 
    (#h:heap_sig u#a)
    (e:inames (extend h))
    (i:(extend h).iref)
    (p:(extend h).slprop)
: ghost_action_except (extend h) unit e 
    ((extend h).inv i p) 
    (fun _ -> (extend h).inv i p `(extend h).star` (extend h).inv i p)

val injective_invariant 
        (#h:heap_sig u#a) 
        (i:(extend h).iref)
: GTot bool


let iiref (h:heap_sig) = i:(extend h).iref { injective_invariant i }

val new_invariant
    (#h:heap_sig u#a) 
    (e:inames (extend h))
    (p:boxable (extend h))
: ghost_action_except (extend h) 
    (iiref h)
    e
    p
    (fun i -> (extend h).inv i p)

val with_invariant
    (#h:heap_sig u#a)
    (#a:Type u#aa)
    (#fp:(extend h).slprop)
    (#fp':(a -> (extend h).slprop))
    (#opened_invariants:inames (extend h))
    (#p:(extend h).slprop)
    (#maybe_ghost:bool)
    (i:(extend h).iref{~ (GhostSet.mem i opened_invariants)})
    (f:_action_except (extend h) a maybe_ghost
      (add_iref #(extend h) i opened_invariants) 
      (p `(extend h).star` fp)
      (fun x -> p `(extend h).star` fp' x))
: _action_except (extend h) a maybe_ghost opened_invariants 
      ((extend h).inv i p `(extend h).star` fp)
      (fun x -> (extend h).inv i p `(extend h).star` fp' x)

val distinct_invariants_have_distinct_names
      (#h:heap_sig u#a)
      (e:inames (extend h))
      (p:(extend h).slprop)
      (q:(extend h).slprop { p =!= q })
      (i j: iiref h)
: ghost_action_except (extend h)
    (squash (i =!= j))
    e 
    ((extend h).inv i p `(extend h).star` (extend h).inv j q)
    (fun _ -> (extend h).inv i p `(extend h).star` (extend h).inv j q)

val invariant_name_identifies_invariant
      (#h:heap_sig u#a)
      (e:inames (extend h))
      (p q:(extend h).slprop)
      (i:iiref h)
      (j:iiref h{ i == j } )
: ghost_action_except (extend h)
   (squash (p == q)) e
    ((extend h).inv i p `(extend h).star` (extend h).inv j q)
    (fun _ -> (extend h).inv i p `(extend h).star` (extend h).inv j q)

let fresh_wrt (#h:heap_sig u#h)
              (ctx:list h.iref)
              (i:h.iref)
  = forall i'. List.Tot.memP i' ctx ==> i' =!= i

val fresh_invariant
    (#h:heap_sig u#a) 
    (e:inames (extend h))
    (p:boxable (extend h))
    (ctx:FStar.Ghost.erased (list (extend h).iref))
: ghost_action_except (extend h) 
    (i:iiref h { fresh_wrt ctx i })
    e
    p
    (fun i -> (extend h).inv i p)

val lift_inv (h:heap_sig u#a) (i:h.iref) (p:h.slprop)
: Lemma ((extend h).up (h.inv i p) == (extend h).inv (lift_iref i) ((extend h).up p))

val storable_invariant 
        (#h:heap_sig u#a) 
        (i:(extend h).iref)
: GTot bool

val lift_iref_is_storable (#h:heap_sig u#a) (i:h.iref)
: Lemma (storable_invariant (lift_iref i))

let siref (h:heap_sig) = i:(extend h).iref { storable_invariant i }

val storable_inv (h:heap_sig u#a) (i:siref h) (p:(extend h).slprop { is_storable #(extend h) p })
: Lemma (is_storable ((extend h).inv i p))

open FStar.PCM
open FStar.Ghost

val pts_to (#h:heap_sig u#a) (#a:Type u#(a + 1)) (#pcm:pcm a) (r:ref a pcm) (v:a) : (extend h).slprop
val ghost_pts_to (#h:heap_sig u#a) (#a:Type u#(a + 1)) (#pcm:pcm a) (r:ghost_ref a pcm) (v:a) : (extend h).slprop

val select_refine
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _)
    (r:ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: action_except
    (extend h)
    (v:a{compatible p x v /\ p.refine v}) e
    (pts_to r x)
    (fun v -> pts_to r (f v))

val upd_gen
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _) 
    (r:ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: action_except
    (extend h)
    unit e
    (pts_to r x)
    (fun _ -> pts_to r y)

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except
    (extend h)
    unit e
    (pts_to r (v0 `op pcm` v1))
    (fun _ -> pts_to r v0 `(extend h).star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#h:heap_sig u#h)
  (#a:Type u#(h + 1))
  (#pcm:pcm a)
  (e:inames _)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (composable pcm v0 v1)) e
    (pts_to r v0 `(extend h).star` pts_to r v1)
    (fun _ -> pts_to r (op pcm v0 v1))

val alloc_action
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (x:a{pcm.refine x})
: action_except
    (extend h)
    (ref a pcm) e
    (extend h).emp
    (fun r -> pts_to r x)


val pts_to_not_null_action 
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:erased (ref a pcm))
    (v:Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)

// Ghost operations
val ghost_alloc
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (x:erased a{pcm.refine x})
: ghost_action_except
    (extend h)
    (ghost_ref a pcm)
    e
    (extend h).emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _)
    (r:ghost_ref a p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: ghost_action_except
    (extend h)
    (erased (v:a{compatible p x v /\ p.refine v}))
    e
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#p:pcm a)
    (e:inames _)
    (r:ghost_ref a p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: ghost_action_except
    (extend h)
    unit e
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: ghost_action_except
    (extend h)
    unit e
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `(extend h).star` 
              ghost_pts_to r v1)

val ghost_gather
    (#h:heap_sig u#h)
    (#a:Type u#(h + 1))
    (#pcm:pcm a)
    (e:inames _)
    (r:ghost_ref a pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: ghost_action_except
    (extend h)
    (squash (composable pcm v0 v1)) e
    (ghost_pts_to r v0 `(extend h).star`
     ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))

val exists_congruence
         (#h:heap_sig u#h)
         (#a:Type u#a)
         (p:a -> (extend h).slprop)
: Lemma
    (requires forall x. is_boxable (p x))
    (ensures is_boxable (exists_ p))

val down_star
    (#h:heap_sig u#h)
    (p q:(extend h).slprop)
: Lemma ((extend h).down (p `(extend h).star` q) ==
         (extend h).down p `h.star` (extend h).down q)

val up_star (#h:heap_sig u#a) (p q:h.slprop)
: Lemma ((extend h).up (p `h.star` q) ==
        ((extend h).up p `(extend h).star` (extend h).up q))

val down_exists (#h:heap_sig) #a (p: a -> GTot (extend h).slprop)
: Lemma 
  (ensures (extend h).down (exists_ p) ==
            exists_ #h (fun x -> (extend h).down (p x)))

val down_emp
    (h:heap_sig u#h)
: Lemma ((extend h).down (extend h).emp == h.emp)

val up_emp (h:heap_sig u#a)
: Lemma ((extend h).up h.emp == (extend h).emp)

val up_pure
        (h:heap_sig u#a)
        (p:prop)
: Lemma ((extend h).pure p == (extend h).up (h.pure p))

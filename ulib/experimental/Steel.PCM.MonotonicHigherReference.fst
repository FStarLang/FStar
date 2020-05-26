module Steel.PCM.MonotonicHigherReference
open Steel.PCM
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open Steel.PCM.FractionalPermission
open FStar.Ghost
module Preorder = FStar.Preorder
module Q = Steel.PCM.Preorder
module M = Steel.PCM.Memory
module SB = Steel.PCM.SteelT.Basics
open FStar.Real

noeq
type history (a:Type) (p:Preorder.preorder a) =
  | Witnessed : Q.hist p -> history a p
  | Current : Q.vhist p -> perm -> history a p

let hval #a #p (h:history a p{Current? h}) : Ghost.erased a =
  match h with
  | Current h _ -> Q.curval h

let hperm #a #p (h:history a p{Current? h}) : perm =
  match h with
  | Current _ f -> f

let history_composable #a #p
  : symrel (history a p)
  = fun h0 h1 ->
    match h0, h1 with
    | Witnessed h0, Witnessed h1 ->
      Q.p_composable p h0 h1
    | Witnessed h0, Current h1 f
    | Current h1 f, Witnessed h0 ->
      Q.extends #a #p h1 h0
    | Current h0 f0, Current h1 f1 ->
      h0 == h1 /\
      (sum_perm f0 f1).v <=. 1.0R

let history_compose #a #p (h0:history a p) (h1:history a p{history_composable h0 h1})
  : history a p
  = match h0, h1 with
    | Witnessed h0, Witnessed h1 ->
      Witnessed (Q.p_op p h0 h1)
    | Current h0 f, Witnessed h1
    | Witnessed h1, Current h0 f ->
      Current (Q.p_op p h1 h0) f
    | Current h0 f0, Current _ f1 ->
      Current h0 (sum_perm f0 f1)

let unit_history #a #p : history a p = Witnessed []

let lem_is_unit #a #p (x:history a p)
  : Lemma (history_composable x unit_history /\
           history_compose x unit_history == x)
  = match x with
    | Witnessed h -> ()
    | Current h _ ->
      assert (forall (h:Q.hist p). Q.p_composable p h []);
      assert (forall (h:Q.hist p). Q.p_op p h [] == h);
      assert (forall (h:Q.vhist p). Q.extends #a #p h []);
      assert (h =!= []);
      assert (Q.extends #a #p h [])

let assoc_l #a #p (x y:history a p)
                  (z:history a p{history_composable y z /\
                                 history_composable x (history_compose y z)})
  : Lemma (history_composable x y /\
           history_composable (history_compose x y) z /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  =           ()

#push-options "--query_stats"
let assoc_r #a #p (x y:history a p)
                  (z:history a p{history_composable x y /\
                                 history_composable (history_compose x y) z})
  : Lemma (history_composable y z /\
           history_composable x (history_compose y z) /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  = ()

#push-options "--max_fuel 2 --max_ifuel 1 --z3rlimit_factor 4"
let pcm_history #a #p : pcm (history a p) = {
  p = {
         composable = history_composable;
         op = history_compose;
         one = unit_history
      };
  comm = (fun _ _ -> ());
  assoc = assoc_l;
  assoc_r = assoc_r;
  is_unit = lem_is_unit;
}
#pop-options

let extend_history #a #p (h0:history a p{Current? h0})
                         (v:a{p (hval h0) v})
 : history a p
 = let Current h f = h0 in
   Current (v :: h) f

let extend_history_is_frame_preserving #a #p
                                       (h0:history a p{Current? h0 /\ hperm h0 == full_perm})
                                       (v:a{p (hval h0) v})
  : Lemma (frame_preserving pcm_history h0 (extend_history h0 v))
  = ()

let ref a p = M.ref (history a p) pcm_history

let pts_to_body #a #p (r:ref a p) (f:perm) (v:Ghost.erased a) (h:history a p) =
      M.pts_to r h `star`
      pure (Current? h /\
            hval h == v /\
            hperm h == f)

let pts_to (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:Ghost.erased a) =
    h_exists (pts_to_body r f v)

assume
val intro_pure (#p:slprop) (q:prop { q })
  : SteelT unit p (fun _ -> p `star` pure q)

let alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  = let h = Current [v] full_perm in
    assert (compatible pcm_history h h);
    let x : ref a p = Steel.PCM.Effect.alloc h in
    SB.h_assert (M.pts_to x h);
    intro_pure (Current? h /\
                hval h == Ghost.hide v /\
                hperm h == full_perm);
    SB.h_assert (M.pts_to x h `star`  pure (Current? h /\ hval h == Ghost.hide v /\ hperm h == full_perm));
    SB.intro_h_exists h (pts_to_body x full_perm (Ghost.hide v));
    SB.h_assert (pts_to x full_perm v);
    SB.return x

let read_raw (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#frame:a -> slprop) (#v0:Ghost.erased a)
             (r:ref a p)
  : SteelT (x:a{v0 == Ghost.hide x})
           (pts_to r q v0)
           (fun v -> pts_to r q v0)
  = SB.h_admit _ _

assume
val get_witness (#a:Type) (#p:a -> slprop) (_:unit)
  : SteelT (erased a) (h_exists p) (fun x -> p (Ghost.reveal x))

assume
val h_assoc_r (#p #q #r:slprop) (_:unit)
  : SteelT unit ((p `star` q) `star` r) (fun _ -> p `star` (q `star` r))

let read_refine (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#f:a -> slprop)
                (r:ref a p)
  : SteelT a (h_exists (fun (v:a) -> pts_to r q v `star` f v))
             (fun v -> pts_to r q v `star` f v)
  = let v = get_witness () in
    SB.h_assert (pts_to r q v `star` f (Ghost.reveal v));
    let h : Ghost.erased _ = SB.frame (fun _ -> get_witness #_ #(pts_to_body r q v) ()) _ in
    SB.h_assert (pts_to_body r q v h `star` f (Ghost.reveal v));
    h_assoc_r ();
    let hv = SB.frame (fun _ -> read r h) _ in
    assert (compatible pcm_history h hv);
    assume (Current? h);
    assert (hval h == hval hv);
    SB.h_admit _ _

let write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a{p v x})
  : SteelT unit (pts_to r full_perm v)
                (fun v -> pts_to r full_perm x)
  = let h_old_e = get_witness #_ #(pts_to_body r full_perm v) () in
    SB.h_assert (pts_to_body r full_perm v (Ghost.reveal h_old_e));
    let h_old = SB.frame (fun _ -> read r h_old_e) _ in
    assert (compatible pcm_history h_old_e h_old);
    SB.h_admit _ _

let witnessed = admit()
let witness = admit()
let recall = admit()

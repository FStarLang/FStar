module Steel.MonotonicHigherReference
open FStar.Ghost
open FStar.PCM
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
module Preorder = FStar.Preorder
module Q = Steel.Preorder
module M = Steel.Memory
//module SB = Steel.SteelT.Basics
module Atomic = Steel.Effect.Atomic
open FStar.Real

noeq
type history (a:Type) (p:Preorder.preorder a) =
  | Witnessed : Q.hist p -> history a p
  | Current : Q.vhist p -> perm -> history a p

let hval_tot #a #p (h:history a p{Current? h}) : a =
  match h with
  | Current h _ -> Q.curval h

let hval #a #p (h:history a p{Current? h}) : Ghost.erased a =
  hval_tot h

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
      (sum_perm f0 f1).v <=. one

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
#push-options "--z3rlimit_factor 2"
let assoc_l #a #p (x y:history a p)
                  (z:history a p{history_composable y z /\
                                 history_composable x (history_compose y z)})
  : Lemma (history_composable x y /\
           history_composable (history_compose x y) z /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  = ()


let assoc_r #a #p (x y:history a p)
                  (z:history a p{history_composable x y /\
                                 history_composable (history_compose x y) z})
  : Lemma (history_composable y z /\
           history_composable x (history_compose y z) /\
           history_compose (history_compose x y) z ==
           history_compose x (history_compose y z))
  = ()
#pop-options

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
  refine = (fun _ -> True);
}

let pcm_history_preorder #a #p : Preorder.preorder (history a p) =
  fun h0 h1 ->
    match h0, h1 with
    | Witnessed vh0, Witnessed vh1
    | Current vh0 _, Witnessed vh1
    | Witnessed vh0, Current vh1 _
    | Current vh0 _, Current vh1 _ ->
      vh1 `Q.extends` vh0

#push-options "--z3rlimit_factor 8 --ifuel 1 --fuel 0 --warn_error -271"
let pcm_history_induces_preorder #a #p
  : Lemma (Q.induces_preorder (pcm_history #a #p)
                              (pcm_history_preorder #a #p))
  = let aux (x y:history a p)
            (f:frame_preserving_upd (pcm_history #a #p) x y)
            (v:history a p)
      : Lemma
          (requires compatible (pcm_history #a #p) x v)
          (ensures (pcm_history_preorder #a #p) v (f v))
          [SMTPat ()]
      = let pcm = pcm_history #a #p in
        let v1 = f v in
        match x, v, v1 with
        | Witnessed _, Witnessed _, Witnessed _ ->
          assert (composable pcm x v)
        | Current _ _, Witnessed _, Witnessed _ -> ()
        | Witnessed _, Current _ _, Witnessed _ -> ()
        | Witnessed _, Witnessed _, Current _ _ ->
          assert (composable pcm x v)
        | Current _ _, Witnessed _, Current _ _ -> ()
        | Witnessed _, Current _ _, Current _ _ -> ()
        | Current hx _, Current hv _, Witnessed _
        | Current hx _, Current hv _, Current _ _ ->
          let frame = FStar.IndefiniteDescription.indefinite_description_ghost
            (history a p) (fun frame -> composable pcm x frame /\ op pcm frame x == v) in
          match frame with
          | Current hf _ -> ()
          | Witnessed hf ->
            assert (Q.extends hx hf);
            assert (hx == hv);
            assert (composable pcm x (Witnessed hv))
    in
    ()
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

let history_val #a #p (h:history a p) (v:Ghost.erased a) (f:perm)
  : prop
  = Current? h /\ hval h == v /\ hperm h == f

[@@__reduce__]
let pts_to_body #a #p (r:ref a p) (f:perm) (v:Ghost.erased a) (h:history a p) =
      M.pts_to r h `star`
      pure (history_val h v f)

let pts_to_body_witness_invariant #a #p (r:ref a p) (f:perm) (v:Ghost.erased a)
  : Lemma (is_witness_invariant (pts_to_body r f v))
          [SMTPat (pts_to_body r f v)]
  = let aux (x y : history a p) (m:mem)
       : Lemma (requires interp (pts_to_body r f v x) m
                       /\ interp (pts_to_body r f v y) m)
               (ensures  x == y)
       =
       assert (interp (pts_to_body r f v x) m);
       assert (interp (pts_to_body r f v y) m);
       M.pure_interp (history_val x v f) m;
       M.pure_interp (history_val y v f) m;
       (* They are joinable, so their values match *)
       M.pts_to_join r x y m
    in
    Classical.forall_intro (fun x ->
    Classical.forall_intro (fun y ->
    Classical.forall_intro (fun m ->
    Classical.move_requires (aux x y) m)))



let pts_to (#a:Type) (#p:Preorder.preorder a) (r:ref a p) (f:perm) (v:Ghost.erased a) =
    h_exists (pts_to_body r f v)

let intro_pure #a #p #f
                 (r:ref a p)
                 (v:a)
                 (h:history a p { history_val h v f })
  : SteelT unit
           (M.pts_to r h)
           (fun _ -> pts_to_body r f v h)
  = change_slprop _ _ (fun m ->
      emp_unit (M.pts_to r h);
      pure_star_interp (M.pts_to r h) (history_val h v f) m)

let intro_pure_full #a #p #f
                 (r:ref a p)
                 (v:a)
                 (h:history a p { history_val h v f })
  : SteelT unit
           (M.pts_to r h)
           (fun _ -> pts_to r f v)
  = intro_pure #a #p #f r v h;
    intro_exists h (pts_to_body r f v)


let alloc (#a:Type) (p:Preorder.preorder a) (v:a)
  = let h = Current [v] full_perm in
    assert (compatible pcm_history h h);
    let x : ref a p = Steel.Effect.alloc h in
    intro_pure_full x v h;
    x

let extract_pure #a #uses #p #f
                 (r:ref a p)
                 (v:Ghost.erased a)
                 (h:Ghost.erased (history a p))
  : SteelGhostT (_:unit{history_val h v f})
           uses
           (pts_to_body r f v h)
           (fun _ -> pts_to_body r f v h)
  = change_slprop (pts_to_body r f v h) (M.pts_to r h `star` pure (history_val h v f)) (fun _ -> ());
    elim_pure (history_val h v f);
    change_slprop (M.pts_to r h) (pts_to_body r f v h) (fun m ->
      emp_unit (M.pts_to r h);
      pure_star_interp (M.pts_to r h) (history_val h v f) m
    )

let elim_pure #a #uses #p #f
                 (r:ref a p)
                 (v:Ghost.erased a)
                 (h:Ghost.erased (history a p))
  : SteelGhostT (_:unit{history_val h v f})
           uses
           (pts_to_body r f v h)
           (fun _ ->  M.pts_to r h)
  = let _ = extract_pure r v h in
    drop (pure (history_val h v f))

module ST = Steel.Memory.Tactics

let rewrite_erased #a (p:erased a -> slprop) (x:erased a) (y:a { Ghost.reveal x == y})
  : SteelT unit (p x) (fun _ -> p (Ghost.hide y))
  = change_slprop (p x) (p (Ghost.hide y)) (fun _ -> ())

let rewrite_reveal_hide #a (x:a) (p:a -> slprop) ()
  : SteelT unit (p (Ghost.reveal (Ghost.hide x))) (fun _ -> p x)
  = change_slprop (p (Ghost.reveal (Ghost.hide x))) (p x) (fun _ -> ())

let pts_to_is_witness_invariant (#a:Type) (#p:Preorder.preorder a)
    (r:ref a p) (q:perm)
  : Lemma (is_witness_invariant (pts_to r q))
          [SMTPat (is_witness_invariant (pts_to r q))]
  = let aux (x y : erased a) (m:mem)
       : Lemma (requires interp (pts_to r q x) m
                       /\ interp (pts_to r q y) m)
               (ensures  x == y)
       =
       assert (interp (h_exists (pts_to_body r q x)) m);
       assert (interp (h_exists (pts_to_body r q y)) m);
       let h1 : erased (history a p) = id_elim_exists (pts_to_body r q x) m in
       let h2 : erased (history a p) = id_elim_exists (pts_to_body r q y) m in
       assert (interp (pts_to_body r q x h1) m);
       assert (interp (pts_to_body r q y h2) m);
       M.pure_interp (history_val h1 x q) m;
       M.pure_interp (history_val h2 y q) m;
       (* They are joinable, so their values match *)
       M.pts_to_join r h1 h2 m
    in
    Classical.forall_intro (fun x ->
    Classical.forall_intro (fun y ->
    Classical.forall_intro (fun m ->
    Classical.move_requires (aux x y) m)))

let read_refine (#a:Type) (#q:perm) (#p:Preorder.preorder a) (#f:a -> slprop)
                (r:ref a p)
  : SteelT a (h_exists (fun (v:a) -> pts_to r q v `star` f v))
             (fun v -> pts_to r q v `star` f v)
  = let v = witness_h_exists #_ #_ #(fun (v:a) -> pts_to r q v `star` f v) (
        pts_to_is_witness_invariant r q;
        star_is_witinv_left (fun (v:a) -> pts_to r q v) f
    ) in
    change_slprop (pts_to r q (Ghost.hide (Ghost.reveal v)) `star` f v) (h_exists (pts_to_body r q v) `star` f v) (fun _ -> ());

    let h = witness_h_exists #_ #_ #(pts_to_body r q v) () in

    let _ = elim_pure #_ #_ #_ #q r v h in

    let hv = read #_ #_ r h in

    change_slprop (M.pts_to r h) (pts_to_body r q v h) (fun m ->
      emp_unit (M.pts_to r h);
      pure_star_interp (M.pts_to r h) (history_val h v q) m);

    intro_exists_erased h (pts_to_body r q v);
    rewrite_erased (fun v -> (pts_to r q v `star` f v)) v (hval_tot hv);
    let v = hval_tot hv in

    change_slprop
      (pts_to r q (hval_tot hv) `star` f (Ghost.reveal (Ghost.hide (hval_tot hv))))
      (pts_to r q v `star` f v)
      (fun _ -> ());
    return v


let write (#a:Type) (#p:Preorder.preorder a) (#v:erased a)
          (r:ref a p) (x:a{p v x})
  : SteelT unit (pts_to r full_perm v)
              (fun v -> pts_to r full_perm x)
  = let h_old_e = witness_h_exists #_ #_ #(pts_to_body r full_perm v) () in
    let _ = elim_pure #_ #_ #_ #full_perm r v h_old_e in

    let h_old = read r h_old_e in
    let h: history a p = extend_history h_old x in
    write r h_old_e h;

    intro_pure_full #_ #_ #full_perm r x h

let lift_fact #a #p (f:property a)
  : property (history a p)
  = fun history ->
      match history with
      | Witnessed h -> Cons? h /\ f (Cons?.hd h)
      | Current h _ -> f (hval history)

let lift_fact_is_stable #a #p (f:property a{FStar.Preorder.stable f p})
  : Lemma (FStar.Preorder.stable #(history a p)
                                 (lift_fact f)
                                 (Steel.Preorder.preorder_of_pcm pcm_history))
  = assert (FStar.Preorder.stable #(history a p) (lift_fact f) pcm_history_preorder);
    pcm_history_induces_preorder #a #p;
    Q.stability #(history a p) (lift_fact f) pcm_history_preorder pcm_history

let witnessed #a #p r fact =
  M.witnessed r (lift_fact fact)

let get_squash (#p:prop) (_:unit{p}) : squash p = ()

let witness_thunk (#a:Type) (#pcm:FStar.PCM.pcm a)
                  (r:M.ref a pcm)
                  (fact:M.stable_property pcm)
                  (v:Ghost.erased a)
                  (_:fact_valid_compat fact v)
                  (_:unit)
  : SteelT unit (M.pts_to r v)
                (fun _ -> M.pts_to r v `star` pure (M.witnessed r fact))
  = Steel.Effect.witness r fact v ()


let witness (#a:Type) (#q:perm) (#p:Preorder.preorder a) (r:ref a p)
            (fact:stable_property p)
            (v:Ghost.erased a)
            (_:squash (fact v))
  : SteelT unit (pts_to r q v)
                (fun _ -> pts_to r q v `star` pure (witnessed r fact))
  = let h = witness_h_exists #_ #_ #(pts_to_body r q v) () in
    let _ = elim_pure #_ #_ #_ #q r v h in

    assert (forall h'. compatible pcm_history h h' ==> lift_fact fact h');
    lift_fact_is_stable #a #p fact;

    witness_thunk r (lift_fact fact) h () _;

    change_slprop (M.pts_to r h) (pts_to_body r q v h) (fun m ->
      emp_unit (M.pts_to r h);
      pure_star_interp (M.pts_to r h) (history_val h v q) m);

    intro_exists_erased h (pts_to_body r q v);
    change_slprop (pts_to r q v) (pts_to r q v) (fun _ -> ())


let recall (#a:Type u#1) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:ref a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to r q v `star` pure (fact v))
  = let h = witness_h_exists #_ #_ #(pts_to_body r q v) () in
    let _ = elim_pure #_ #_ #_ #q r v h in

    let h1 = Steel.Effect.recall r h in

    change_slprop (M.pts_to r h) (pts_to_body r q v h) (fun m ->
      emp_unit (M.pts_to r h);
      pure_star_interp (M.pts_to r h) (history_val h v q) m);

    intro_exists_erased h (pts_to_body r q v);

    change_slprop (pts_to r q v `star` pure (lift_fact fact h1))
      (pts_to r q v `star` pure (fact v)) (fun _ -> ())

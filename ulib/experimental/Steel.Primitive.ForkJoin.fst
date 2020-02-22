module Steel.Primitive.ForkJoin
open Steel.Effect
open Steel.Memory
module L = Steel.SpinLock
open Steel.Permissions
open FStar.Ghost
open Steel.Reference

assume
val intro_or_l (p q:hprop)
  : SteelT unit p (fun _ -> h_or p q)

assume
val intro_or_r (p q:hprop)
  : SteelT unit q (fun _ -> h_or p q)

assume
val pure (p:prop) : hprop

assume
val interp_pure (p:prop)
  : Lemma (p ==> (forall m. interp (pure p) m))

assume
val interp_pure_2 (p:prop)
  : Lemma (~p ==> (forall m. ~(interp (pure p) m)))

assume
val intro_wand_hyp (p q r:hprop)
  : Steel.Effect.Steel unit r (fun _ -> p `wand` q)
    (requires (fun _ -> (forall m. interp (p `star` r) m ==> interp q m)))
    (ensures (fun _ _ _ -> True))

assume
val steel_admit (#a:Type) (#p:a -> hprop) (_:unit) : SteelT a emp p

assume
val intro_wand_trivial (p:prop{~p}) (q:hprop)
  : SteelT unit emp (fun _ -> pure p `wand` q)

// let intro_wand_trivial (p:prop{~p}) (q:hprop)
//     SteelT unit emp (fun _ -> pure p `wand` q)
//   = //interp_pure_2 p;
//     //assert (forall m. interp (pure p `star` emp) m ==> interp q m);
//     steel_admit (); return ()
//     intro_wand_hyp (pure p) emp q

let intro_wand_have (p q:hprop) (_:unit)
  : SteelT unit q (fun _ -> p `wand` q)
  = intro_wand_hyp p q q

assume
val elim_wand (p q:hprop)
  : SteelT unit (p `star` (p `wand` q)) (fun _ -> q)

assume
val return (#a:Type) (#p:a -> hprop) (x:a)
  : SteelT a (p x) p

assume
val intro_h_exists (#a:Type) (x:a) (p:(a -> hprop))
  : SteelT unit (p x) (fun _ -> h_exists p)

// let lock_inv (r:ref bool) (p:hprop) : hprop = (h_or (pts_to r full false) (pts_to r full true `star` p))


let frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          ($f:unit -> SteelT a pre post)
          (frame:hprop)
  : SteelT a
    (pre `star` frame)
    (fun x -> post x `star` frame)
  = steel_frame f frame (fun _ -> True)

assume
val h_assert (p:hprop)
  : SteelT unit p (fun _ -> p)

assume
val h_intro_emp_l (p:hprop)
  : SteelT unit p (fun _ -> emp `star` p)


assume
val h_admit (#a:_) (p:hprop) (q:a -> hprop)
  : SteelT a p q

assume
val h_commute (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> q `star` p)

assume
val h_affine (p q:hprop)
  : SteelT unit (p `star` q) (fun _ -> p)


assume
val read_refine (#a:_) (#perm:_) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r perm v `star` q v))
             (fun v -> pts_to r perm v `star` q v)


assume
val par (#preL:pre_t) (#postL:post_t unit)
        ($f:unit -> SteelT unit preL postL)
        (#preR:pre_t) (#postR:post_t unit)
        ($g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun _ -> postL () `star` postR ())

assume
val h_elim_emp_l (p:hprop)
  : SteelT unit (emp `star` p) (fun _ -> p)

let maybe_p (p:hprop) (v:bool) = pure (v==true) `wand` p

let lock_inv_pred (r:ref bool) (p:hprop) (v:bool) : hprop =
  pts_to r full v `star` maybe_p p v

let lock_inv (r:ref bool) (p:hprop)
  : hprop
  = h_exists (lock_inv_pred r p)

noeq
type thread (p:hprop) = {
  r:ref bool;
  l:L.lock (lock_inv r p)
}

let new_thread (p:hprop)
  : SteelT (thread p) emp (fun _ -> emp)
  = intro_wand_trivial (false == true) p;
    h_assert (pure (false == true) `wand` p);
    h_intro_emp_l (pure (false == true) `wand` p);
    let r = frame #(ref bool) #emp #(fun r -> pts_to r full false)
                  (fun () -> alloc false)
                  (pure (false == true) `wand` p) in
    intro_h_exists false (lock_inv_pred r p);
    let l  = L.new_lock (lock_inv r p) in
    let t  =  { r = r ; l = l } in
    return t

let finish (#p:hprop) (t:thread p) (v:bool)
  : SteelT unit (pts_to t.r full v `star` p) (fun _ -> emp)
  = frame (fun _ -> write t.r true) p;
    h_assert (pts_to t.r full true `star` p);
    h_commute (pts_to t.r full true) p;
    frame (intro_wand_have (pure (true==true)) p) (pts_to t.r full true);
    h_commute (pure (true==true) `wand` p) (pts_to t.r full true);
    intro_h_exists true (lock_inv_pred t.r p);
    L.release t.l

let acquire (#p:hprop) (t:thread p)
  : SteelT bool emp (fun b -> pts_to t.r full b)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_affine (pts_to t.r full b) (maybe_p p b);
    return b

let spawn (#p #q:hprop)
          ($f: (unit -> SteelT unit p (fun _ -> q)))
          (t:thread q)
          (_:unit)
  : SteelT unit p (fun _ -> emp)
  = h_intro_emp_l p;
    let b  = frame (fun () -> acquire t) p in
    h_commute (pts_to t.r full b) p;
    let _ = frame f (pts_to t.r full b) in
    h_commute q (pts_to t.r full b);
    finish t b

let fork (#a:Type) (#p #q #r #s:hprop)
      (f: (unit -> SteelT unit p (fun _ -> q)))
      (g: (thread q -> unit -> SteelT unit r (fun _ -> s)))
  : SteelT unit (p `star` r) (fun _ -> s)
  = h_intro_emp_l (p `star` r);
    let t : thread q = frame (fun _ -> new_thread q) (p `star` r) in
    h_assert (emp `star` (p `star` r));
    h_elim_emp_l (p `star` r);
    par (spawn f t) (g t);
    h_elim_emp_l s


let rec join (#p:hprop) (t:thread p)
  : SteelT unit emp (fun _ -> p)
  = L.acquire t.l;
    let b = read_refine (maybe_p p) t.r in
    h_assert (pts_to t.r full b `star` maybe_p p b);
    h_admit _ _
    // if b
    // then (h_assert (pts_to t.r full true `star` maybe_p p true);
    //       elim_wand (pure (true==true)) p)
    // else (intro_h_exists false (lock_inv_pred t.r p); L.release t.l; join' t)

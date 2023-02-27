(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.HigherReference
open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open FStar.PCM
open Steel.PCMFrac
open FStar.Real
module RP = Steel.PCMReference

#set-options "--ide_id_info_off"

module Mem = Steel.Memory

let ref a = Mem.ref (fractional a) pcm_frac
let null #a = Mem.null #(fractional a) #pcm_frac
let is_null #a r = Mem.is_null #(fractional a) #pcm_frac r
let perm_ok p : prop = (p.v <=. one == true) /\ True
let pts_to_raw_sl (#a:Type) (r:ref a) (p:perm) (v:erased a) : slprop =
  Mem.pts_to r (Some (Ghost.reveal v, p))
let pts_to_raw (#a:Type) (r:ref a) (p:perm) (v:erased a) : vprop =
  to_vprop (Mem.pts_to r (Some (Ghost.reveal v, p)))
[@@__reduce__]
let pts_to' (#a:Type u#1) (r:ref a) (p:perm) (v:erased a) : vprop = pts_to_raw r p v `star` pure (perm_ok p)
let pts_to_sl #a r p v  = hp_of (pts_to' r p v)

let abcd_acbd (a b c d:slprop)
  : Lemma (Mem.(((a `star` b) `star` (c `star` d)) `equiv`
           ((a `star` c) `star` (b `star` d))))
  = let open Steel.Memory in
    calc (equiv) {
    ((a `star` b) `star` (c `star` d));
      (equiv) { star_associative a b (c `star` d) }
    ((a `star` (b `star` (c `star` d))));
      (equiv) { star_associative b c d;
                star_congruence a (b `star` (c `star` d))
                                a ((b `star` c) `star` d) }
    (a `star` ((b `star` c) `star` d));
      (equiv) { star_commutative  b c;
                star_congruence (b `star` c) d (c `star` b) d;
                star_congruence a ((b `star` c) `star` d)
                                a ((c `star` b) `star` d) }
    (a `star` ((c `star` b) `star` d));
      (equiv) { star_associative c b d;
                star_congruence a ((c `star` b) `star` d)
                                a (c `star` (b `star` d)) }
    (a `star` (c `star` (b `star` d)));
      (equiv) { star_associative a c (b `star` d) }
    ((a `star` c) `star` (b `star` d));
   }

let pts_to_ref_injective
      (#a: Type u#1)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1:a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to_sl r p0 v0 `Mem.star` pts_to_sl r p1 v1) m)
      (ensures v0 == v1)
    = let open Steel.Memory in
      abcd_acbd (hp_of (pts_to_raw r p0 v0))
                (pure (perm_ok p0))
                (hp_of (pts_to_raw r p1 v1))
                (pure (perm_ok p1));
      Mem.affine_star (hp_of (pts_to_raw r p0 v0) `star` hp_of (pts_to_raw r p1 v1))
                      (pure (perm_ok p0) `star` pure (perm_ok p1)) m;
      Mem.pts_to_compatible r (Some (Ghost.reveal v0, p0))
                              (Some (Ghost.reveal v1, p1))
                              m

let pts_to_not_null (#a:Type u#1)
                    (r:ref a)
                    (p:perm)
                    (v:a)
                    (m:mem)
  : Lemma (requires interp (pts_to_sl r p v) m)
          (ensures r =!= null)
  = Mem.affine_star (hp_of (pts_to_raw r p v)) (Mem.pure (perm_ok p)) m;
    Mem.pts_to_not_null r (Some (Ghost.reveal v, p)) m

let pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to_sl r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (pts_to_sl r p x) m /\ interp (pts_to_sl r p y) m))
            (ensures  (x == y))
    =
    Mem.pts_to_join r (Some (Ghost.reveal x, p)) (Some (Ghost.reveal y, p)) m
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let higher_ref_pts_to_injective_eq #a #opened #p0 #p1 #v0 #v1 r =
  extract_info_raw (pts_to r p0 v0 `star` pts_to r p1 v1) (v0 == v1)
    (fun m -> pts_to_ref_injective r p0 p1 v0 v1 m);
  rewrite_slprop (pts_to r p1 v1) (pts_to r p1 v0) (fun _ -> ())

let pts_to_framon (#a:Type) (r:ref a) (p:perm) : Lemma (is_frame_monotonic (pts_to_sl r p)) =
  pts_to_witinv r p

let intro_pts_to (p:perm) #a #uses (#v:erased a) (r:ref a)
  : SteelGhost unit uses
                (pts_to_raw r p v)
                (fun _ -> pts_to r p v)
                (requires fun _ -> perm_ok p)
                (ensures fun _ _ _ -> True)
  = intro_pure (perm_ok p);
    rewrite_slprop (pts_to' r p v) (pts_to r p v) (fun _ -> ())

let alloc #a x =
  let v = Some (x, full_perm) in
  assert (FStar.PCM.composable pcm_frac v None);
  assert (compatible pcm_frac v v);
  let r = RP.alloc v in
  rewrite_slprop (RP.pts_to r v) (pts_to r full_perm x)
    (fun m ->
      emp_unit (hp_of (pts_to_raw r full_perm x));
      pure_star_interp (hp_of (pts_to_raw r full_perm x)) (perm_ok full_perm) m
    );
  extract_info_raw (pts_to r full_perm x) (~ (is_null r))
    (fun m -> pts_to_not_null r full_perm x m);
   return r

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    rewrite_slprop (pts_to r p v) (RP.pts_to r v1 `star` pure (perm_ok p)) (fun _ -> ());
    elim_pure (perm_ok p);
    let v2 = RP.read r v1 in
    rewrite_slprop (RP.pts_to r v1) (pts_to r p v)
      (fun m ->
        emp_unit (hp_of (pts_to_raw r p v));
        pure_star_interp (hp_of (pts_to_raw r p v)) (perm_ok p) m);
    assert (compatible pcm_frac v1 v2);
    let Some (x, _) = v2 in
    rewrite_slprop (pts_to r p v) (pts_to r p x) (fun _ -> ());
    return x

let atomic_read (#opened:_) (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    rewrite_slprop (pts_to r p v) (RP.pts_to r v1 `star` pure (perm_ok p)) (fun _ -> ());
    elim_pure (perm_ok p);

    let v2 = RP.atomic_read r v1 in
    rewrite_slprop (RP.pts_to r v1) (pts_to r p v)
      (fun m ->
        emp_unit (hp_of (pts_to_raw r p v));
        pure_star_interp (hp_of (pts_to_raw r p v)) (perm_ok p) m);
    assert (compatible pcm_frac v1 v2);
    let Some (x, _) = v2 in
    rewrite_slprop (pts_to r p v) (pts_to r p x) (fun _ -> ());
    return x

let read_refine (#a:Type) (#p:perm) (q:a -> vprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
                (fun v -> pts_to r p v `star` q v)
  = let vs:erased a = witness_exists () in

    rewrite_slprop (pts_to r p (Ghost.hide (Ghost.reveal vs))) (pts_to r p vs) (fun _ -> ());

    let v = read r in

    rewrite_slprop (q vs) (q v) (fun _ -> ());
    return v

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    rewrite_slprop (pts_to r full_perm v) (RP.pts_to r v_old `star` pure (perm_ok full_perm)) (fun _ -> ());

    elim_pure (perm_ok full_perm);

    RP.write r v_old v_new;
    rewrite_slprop (RP.pts_to r v_new) (pts_to r full_perm x)
        (fun m -> emp_unit (hp_of (pts_to_raw r full_perm x));
          pure_star_interp (hp_of (pts_to_raw r full_perm x)) (perm_ok full_perm) m)

let atomic_write #opened #a #v r x
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    rewrite_slprop (pts_to r full_perm v) (RP.pts_to r v_old `star` pure (perm_ok full_perm)) (fun _ -> ());

    elim_pure (perm_ok full_perm);

    RP.atomic_write r v_old v_new;
    rewrite_slprop (RP.pts_to r v_new) (pts_to r full_perm x)
        (fun m -> emp_unit (hp_of (pts_to_raw r full_perm x));
          pure_star_interp (hp_of (pts_to_raw r full_perm x)) (perm_ok full_perm) m)

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    rewrite_slprop
      (pts_to r full_perm v)
      (RP.pts_to r v_old `star` pure (perm_ok full_perm))
      (fun _ -> ());
    elim_pure (perm_ok full_perm);
    RP.free r v_old;
    drop (RP.pts_to r (Mkpcm'?.one (Mkpcm?.p pcm_frac)))

let share_atomic_raw #a #uses (#p:perm) (r:ref a{perm_ok p}) (v0:erased a)
  : SteelGhostT unit uses
                (pts_to_raw r p v0)
                (fun _ -> pts_to_raw r (half_perm p) v0 `star` pts_to_raw r (half_perm p) v0)
  = rewrite_slprop
      (pts_to_raw r p v0)
      (RP.pts_to r _)
      (fun _ -> ());
    RP.split r (Some (Ghost.reveal v0, p)) (Some (Ghost.reveal v0, half_perm p)) (Some (Ghost.reveal v0, half_perm p));
    rewrite_slprop
      (RP.pts_to r _)
      (pts_to_raw r (half_perm p) v0)
      (fun _ -> ());
    rewrite_slprop
      (RP.pts_to r _)
      (pts_to_raw r (half_perm p) v0)
      (fun _ -> ())

let share (#a:Type) #uses (#p:perm) (#v:erased a) (r:ref a)
  : SteelGhostT unit uses
               (pts_to r p v)
               (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    rewrite_slprop
      (pts_to r p v)
      (pts_to' r p v)
      (fun _ -> ());
    elim_pure (perm_ok p);
    share_atomic_raw r v;
    intro_pts_to (half_perm p) r;
    intro_pts_to (half_perm p) r

let gather_atomic_raw (#a:Type) (#uses:_) (#p0 #p1:perm) (r:ref a) (v0:erased a) (v1:erased a)
  : SteelGhostT (_:unit{v0==v1 /\ perm_ok (sum_perm p0 p1)}) uses
                 (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                 (fun _ -> pts_to_raw r (sum_perm p0 p1) v0)
  = 
    rewrite_slprop
      (pts_to_raw r p0 v0)
      (RP.pts_to r (Ghost.reveal (Some (Ghost.reveal v0, p0))))
      (fun _ -> ());
    rewrite_slprop
      (pts_to_raw r p1 v1)
      (RP.pts_to r (Ghost.reveal (Some (Ghost.reveal v1, p1))))
      (fun _ -> ());
    let _ = RP.gather r (Some (Ghost.reveal v0, p0)) (Some (Ghost.reveal v1, p1)) in
    rewrite_slprop
      (RP.pts_to r _)
      (pts_to_raw r (sum_perm p0 p1) v0)
      (fun _ -> ())

let gather (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  = let v0_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v0, p0)) in
    let v1_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v1, p1)) in
    rewrite_slprop
      (pts_to r p0 v0)
      (pts_to_raw r p0 v0 `star` pure (perm_ok p0))
      (fun _ -> ());
    rewrite_slprop
      (pts_to r p1 v1)
      (pts_to_raw r p1 v1 `star` pure (perm_ok p1))
      (fun _ -> ());
    elim_pure (perm_ok p0);
    elim_pure (perm_ok p1);
    let _ = gather_atomic_raw r v0 v1 in
    intro_pts_to (sum_perm p0 p1) r

let cas_provides #t (r:ref t) (v:Ghost.erased t) (v_new:t) (b:bool) =
    if b then pts_to_sl r full_perm v_new else pts_to_sl r full_perm v

let equiv_ext_right (p q r:slprop)
  : Lemma
      (requires q `Mem.equiv` r)
      (ensures Mem.((p `star` q) `equiv` (p `star` r)))
  = let open Steel.Memory in
    calc (equiv) {
      p `star` q;
         (equiv) { star_commutative p q }
      q `star` p;
         (equiv) { equiv_extensional_on_star q r p }
      r `star` p;
         (equiv) { star_commutative p r }
      p `star` r;
    }

let cas_action_helper (p q r s:slprop) (m:mem)
  : Lemma
      (requires interp Mem.(p `star` q `star` r `star` s) m)
      (ensures interp Mem.(p `star` q `star` s) m)
  = let open Steel.Memory in
    calc (equiv) {
      r `star` s;
         (equiv) { star_commutative r s }
      s `star` r;
    };
    calc (equiv) {
      p `star` q `star` r `star` s;
         (equiv) { Mem.star_associative (p `star` q) r s }
      (p `star` q) `star` (r `star` s);
         (equiv) { equiv_ext_right (p `star` q)
                     (r `star` s)
                     (s `star` r) }
      (p `star` q) `star` (s `star` r);
         (equiv) { star_associative (p `star` q) s r }
      (p `star` q `star` s) `star` r;
    };
    assert (interp ((p `star` q `star` s) `star` r) m);
    affine_star (p `star` q `star` s) r m

let cas_action (#t:Type) (eq: (x:t -> y:t -> b:bool{b <==> (x == y)}))
               (#uses:inames)
               (r:ref t)
               (v:Ghost.erased t)
               (v_old:t)
               (v_new:t)
               (fr:slprop)
   : MstTot
        (b:bool{b <==> (Ghost.reveal v == v_old)})
        uses
        (pts_to_sl r full_perm v)
        (cas_provides r v v_new)
        fr
        (fun _ -> True)
        (fun _ _ _ -> True)
   = let m0 : full_mem = NMSTTotal.get () in
     let fv = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
     let fv' = Some (v_new, full_perm) in
     assert (interp Mem.(pts_to_sl r full_perm v `star` fr `star` locks_invariant uses m0) m0);
     assert (interp Mem.(pts_to r fv `star` pure (perm_ok full_perm) `star` fr `star` locks_invariant uses m0) m0);
     cas_action_helper (Mem.pts_to r fv)
       (Mem.pure (perm_ok full_perm))
       fr
       (locks_invariant uses m0)
       m0;
     assert (interp Mem.((pts_to r fv `star` pure (perm_ok full_perm)) `star` locks_invariant uses m0) m0);
     let fv_actual = Mem.frame (Mem.pure (perm_ok full_perm)) (sel_action uses r fv) fr in
     assert (compatible pcm_frac fv fv_actual);
     let Some (v', p) = fv_actual in
     assert (v == Ghost.hide v');
     assert (p == full_perm);
     let b =
       if eq v' v_old
       then (Mem.frame (Mem.pure (perm_ok full_perm)) (upd_action uses r fv fv') fr; true)
       else false
     in
     b

(*** GHOST REFERENCES ***)

let ghost_ref a = erased (ref a)

[@@__reduce__]
let ghost_pts_to_sl #a (r:ghost_ref a) (p:perm) (x:a) = pts_to_sl (reveal r) p x

let reveal_ghost_ref _ = ()

let reveal_ghost_pts_to_sl _ _ _ = ()

let ghost_pts_to_witinv (#a:Type) (r:ghost_ref a) (p:perm) : Lemma (is_witness_invariant (ghost_pts_to_sl r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (ghost_pts_to_sl r p x) m /\ interp (ghost_pts_to_sl r p y) m))
            (ensures  (x == y))
    =
    Mem.pts_to_join (Ghost.reveal r) (Some (Ghost.reveal x, p)) (Some (Ghost.reveal y, p)) m
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let ghost_alloc_aux (#a:Type) (#u:_) (x:a)
  : SteelGhostT (ref a) u
                 emp
                 (fun r -> pts_to r full_perm (Ghost.hide x))
  = let v : fractional a = Some (x, full_perm) in
    assert (FStar.PCM.composable pcm_frac v None);
    assert (compatible pcm_frac v v);
    rewrite_slprop emp (to_vprop Mem.emp) (fun _ -> reveal_emp());
    let r : ref a = as_atomic_action_ghost (Steel.Memory.alloc_action u v) in
    rewrite_slprop (RP.pts_to r v) (pts_to r full_perm x)
      (fun m -> emp_unit (hp_of (pts_to_raw r full_perm x));
             pure_star_interp (hp_of (pts_to_raw r full_perm x)) (perm_ok full_perm) m);
    r

let ghost_alloc x =
  let r = ghost_alloc_aux (reveal x) in
  hide r

let ghost_free #a #u #v r =
  let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    rewrite_slprop
      (pts_to r full_perm v)
      (RP.pts_to r v_old `star` pure (perm_ok full_perm))
      (fun _ -> ());
    elim_pure (perm_ok full_perm);
    as_atomic_action_ghost (free_action u r v_old);
    drop (RP.pts_to r (Mkpcm'?.one (Mkpcm?.p pcm_frac)))

let ghost_share r = share (reveal r)
let ghost_gather r = gather (reveal r)

let ghost_pts_to_injective_eq #_ #_ #p0 #p1 r v0 v1 =
  higher_ref_pts_to_injective_eq #_ #_ #p0 #p1 #v0 #v1 (reveal r)

let ghost_read #a #u #p #v r
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    rewrite_slprop (pts_to r p v) (RP.pts_to r v1 `star` pure (perm_ok p)) (fun _ -> ());
    elim_pure (perm_ok p);
    let v2 = as_atomic_action_ghost (sel_action u r v1) in
    rewrite_slprop (RP.pts_to r v1) (pts_to r p v)
      (fun m ->
        emp_unit (hp_of (pts_to_raw r p v));
        pure_star_interp (hp_of (pts_to_raw r p v)) (perm_ok p) m);
    assert (compatible pcm_frac v1 v2);
    let Some (x, _) = v2 in
    rewrite_slprop (pts_to r p v) (pts_to r p x) (fun _ -> ());
    x

let ghost_write_aux (#a:Type) (#u:_) (#v:erased a) (r:ref a) (x:a)
  : SteelGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (Ghost.hide x))
  = let v_old : erased (fractional a) = Ghost.hide (Some (reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    rewrite_slprop (pts_to r full_perm v)
                  (RP.pts_to r v_old `star` pure (perm_ok full_perm))
                  (fun _ -> ());
    elim_pure (perm_ok full_perm);
    as_atomic_action_ghost (Mem.upd_action u r v_old v_new);
    rewrite_slprop (RP.pts_to r v_new)
                  (pts_to r full_perm (hide x))
                  (fun m -> emp_unit (hp_of (pts_to_raw r full_perm (hide x)));
                         pure_star_interp (hp_of (pts_to_raw r full_perm (hide x))) (perm_ok full_perm) m)

let ghost_write r x =
  ghost_write_aux (reveal r) (reveal x);
  rewrite_slprop
    (pts_to (reveal r) full_perm (hide (reveal x)))
    (ghost_pts_to r full_perm x)
    (fun _ -> ())

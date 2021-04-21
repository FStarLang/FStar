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
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open FStar.Ghost
open FStar.Real
open FStar.PCM
open Steel.FractionalPermission
module Atomic = Steel.Effect.Atomic

let fractional (a:Type u#1) = option (a & perm)
let composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ (sum_perm p0 p1).v <=. one
let compose #a (f0:fractional a) (f1:fractional a{composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let pcm_frac #a : pcm (fractional a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True)
}

module Mem = Steel.Memory

let ref a = Mem.ref (fractional a) pcm_frac
let null #a = Mem.null #(fractional a) #pcm_frac
let is_null #a r = Mem.is_null #(fractional a) #pcm_frac r
let perm_ok p : prop = (p.v <=. one == true) /\ True
let pts_to_raw (#a:Type) (r:ref a) (p:perm) (v:erased a) = Mem.pts_to r (Some (Ghost.reveal v, p))
let pts_to #a r p v = pts_to_raw r p v `star` pure (perm_ok p)

let abcd_acbd (a b c d:slprop)
  : Lemma (((a `star` b) `star` (c `star` d)) `equiv`
           ((a `star` c) `star` (b `star` d)))
  = calc (equiv) {
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
      (v0 v1: erased a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to r p0 v0 `star` pts_to r p1 v1) m)
      (ensures v0 == v1)
    = abcd_acbd (pts_to_raw r p0 v0)
                (pure (perm_ok p0))
                (pts_to_raw r p1 v1)
                (pure (perm_ok p1));
      Mem.affine_star (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                      (pure (perm_ok p0) `star` pure (perm_ok p1)) m;
      Mem.pts_to_compatible r (Some (Ghost.reveal v0, p0))
                              (Some (Ghost.reveal v1, p1))
                              m

let pts_to_not_null (#a:Type u#1)
                    (r:ref a)
                    (p:perm)
                    (v: erased a)
                    (m:mem)
  : Lemma (requires interp (pts_to r p v) m)
          (ensures r =!= null)
  = Mem.affine_star (pts_to_raw r p v) (pure (perm_ok p)) m;
    Mem.pts_to_not_null r (Some (Ghost.reveal v, p)) m

let pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (pts_to r p x) m /\ interp (pts_to r p y) m))
            (ensures  (x == y))
    =
    Mem.pts_to_join r (Some (Ghost.reveal x, p)) (Some (Ghost.reveal y, p)) m
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let higher_ref_pts_to_injective_eq #a #opened #p0 #p1 #v0 #v1 r =
  Atomic.extract_info (pts_to r p0 v0 `star` pts_to r p1 v1) (v0 == v1)
    (fun m -> pts_to_ref_injective r p0 p1 v0 v1 m);
  change_slprop (pts_to r p1 v1) (pts_to r p1 v0) (fun _ -> ())

let pts_to_framon (#a:Type) (r:ref a) (p:perm) : Lemma (is_frame_monotonic (pts_to r p)) =
  pts_to_witinv r p

let intro_perm_ok #uses (p:perm{perm_ok p}) (q:slprop)
  : SteelGhostT unit uses
                q
                (fun _ -> q `star` pure (perm_ok p))
  = change_slprop q (q `star` pure (perm_ok p))
    (fun m -> emp_unit q; pure_star_interp q (perm_ok p) m)

let elim_perm_ok #uses (p:perm)
  : SteelGhostT (q:perm{perm_ok q /\ q == p}) uses
                (pure (perm_ok p))
                (fun _ -> emp)
  = let _ = Atomic.elim_pure (perm_ok p) in
    p

let intro_pts_to (p:perm{perm_ok p}) #a #uses (#v:erased a) (r:ref a) (_:unit)
  : SteelGhostT unit uses
                (pts_to_raw r p v)
                (fun _ -> pts_to r p v)
  = intro_perm_ok p _

let alloc #a x =
  let v = Some (x, full_perm) in
  assert (FStar.PCM.composable pcm_frac v None);
  assert (compatible pcm_frac v v);
  let r = Steel.Effect.alloc v in
  change_slprop (Steel.Memory.pts_to r v) (pts_to r full_perm (hide x))
    (fun m -> emp_unit (pts_to_raw r full_perm x); pure_star_interp (pts_to_raw r full_perm x) (perm_ok full_perm) m);
  steela_return r

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    change_slprop (pts_to r p v) (Mem.pts_to r v1 `star` pure (perm_ok p)) (fun _ -> ());
    let _ = elim_perm_ok p in
    let v2 = Steel.Effect.read r v1 in
    change_slprop (Steel.Memory.pts_to r v1) (pts_to r p v)
        (fun m -> emp_unit (pts_to_raw r p v); pure_star_interp (pts_to_raw r p v) (perm_ok p) m);
    assert (compatible pcm_frac v1 v2);
    let Some (x, _) = v2 in
    change_slprop (pts_to r p v) (pts_to r p x) (fun _ -> ());
    steela_return x

let read_refine (#a:Type) (#p:perm) (q:a -> slprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
                (fun v -> pts_to r p v `star` q v)
  = let vs:erased a = Atomic.witness_h_exists #_ #_ #(fun (v:a) -> pts_to r p v `star` q v) (
        pts_to_witinv r p;
        star_is_witinv_left (fun (v:a) -> pts_to r p v) q
    ) in

    change_slprop (pts_to r p (Ghost.hide (Ghost.reveal vs)) `star` q vs) (pts_to r p vs `star` q vs) (fun _ -> ());

    let v = read #a #p #vs r in

    change_slprop (pts_to r p v `star` q vs) (pts_to r p v `star` q v) (fun _ -> ());
    steela_return v

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    change_slprop (pts_to r full_perm v) (Mem.pts_to r v_old `star` pure (perm_ok full_perm)) (fun _ -> ());

    let _ = elim_perm_ok full_perm in
    Steel.Effect.write r v_old v_new;
    change_slprop (Mem.pts_to r v_new) (pts_to r full_perm x)
        (fun m -> emp_unit (pts_to_raw r full_perm x); pure_star_interp (pts_to_raw r full_perm x) (perm_ok full_perm) m)

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    change_slprop
      (pts_to r full_perm v)
      (Mem.pts_to r v_old `star` pure (perm_ok full_perm))
      (fun _ -> ());
    let _ = elim_perm_ok full_perm in
    Steel.Effect.free r v_old;
    drop (Mem.pts_to r (Mkpcm'?.one (Mkpcm?.p pcm_frac)))

(* move these to Mem *)
#push-options "--z3rlimit 20 --retry 2"
let mem_share_atomic_raw (#a:Type) (#uses:_) (#p:perm{perm_ok p}) (r:ref a)
                         (v0:erased a)
  : action_except unit uses (pts_to_raw r p v0)
                            (fun _ -> pts_to_raw r (half_perm p) v0 `star` pts_to_raw r (half_perm p) v0)
  = let v = Ghost.hide (Some (Ghost.reveal v0, half_perm p)) in
    Mem.split_action uses r v v
#pop-options

let share_atomic_raw #a #uses (#p:perm) (r:ref a{perm_ok p}) (v0:erased a)
  : SteelGhostT unit uses
                (pts_to_raw r p v0)
                (fun _ -> pts_to_raw r (half_perm p) v0 `star` pts_to_raw r (half_perm p) v0)
  = as_atomic_action_ghost (mem_share_atomic_raw r v0)

let share (#a:Type) #uses (#p:perm) (#v:erased a) (r:ref a)
  : SteelGhostT unit uses
               (pts_to r p v)
               (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    change_slprop
      (pts_to r p v)
      (pts_to_raw r p v `star` pure (perm_ok p))
      (fun _ -> ());
    let _ = Atomic.elim_pure (perm_ok p) in
    share_atomic_raw #_ #_ #p r v;
    intro_pts_to (half_perm p) r ();
    intro_pts_to (half_perm p) r ()

let mem_gather_atomic_raw (#a:Type) (#uses:_) (#p0 #p1:perm) (r:ref a) (v0:erased a) (v1:erased a)
  : action_except (_:unit{v0==v1 /\ perm_ok (sum_perm p0 p1)}) uses
                  (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                  (fun _ -> pts_to_raw r (sum_perm p0 p1) v0)
  = let v0 = Ghost.hide (Some (Ghost.reveal v0, p0)) in
    let v1 = Ghost.hide (Some (Ghost.reveal v1, p1)) in
    Mem.gather_action uses r v0 v1

let gather_atomic_raw (#a:Type) (#uses:_) (#p0 #p1:perm) (r:ref a) (v0:erased a) (v1:erased a)
  : SteelGhostT  (_:unit{v0==v1 /\ perm_ok (sum_perm p0 p1)}) uses
                 (pts_to_raw r p0 v0 `star` pts_to_raw r p1 v1)
                 (fun _ -> pts_to_raw r (sum_perm p0 p1) v0)
  = as_atomic_action_ghost (mem_gather_atomic_raw r v0 v1)

let gather (#a:Type) (#uses:_) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  = let v0_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v0, p0)) in
    let v1_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v1, p1)) in
    change_slprop
      (pts_to r p0 v0)
      (pts_to_raw r p0 v0 `star` pure (perm_ok p0))
      (fun _ -> ());
    change_slprop
      (pts_to r p1 v1)
      (pts_to_raw r p1 v1 `star` pure (perm_ok p1))
      (fun _ -> ());
    let _ = Atomic.elim_pure (perm_ok p0) in
    let _ = Atomic.elim_pure (perm_ok p1) in
    let _ = gather_atomic_raw #_ #_ #p0 #p1 r v0 v1 in
    intro_pts_to (sum_perm p0 p1) r ()

let cas_provides #t (r:ref t) (v:Ghost.erased t) (v_new:t) (b:bool) =
    if b then pts_to r full_perm v_new else pts_to r full_perm v

let equiv_ext_right (p q r:slprop)
  : Lemma
      (requires q `equiv` r)
      (ensures (p `star` q) `equiv` (p `star` r))
  = calc (equiv) {
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
      (requires interp (p `star` q `star` r `star` s) m)
      (ensures interp (p `star` q `star` s) m)
  = calc (equiv) {
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
    Mem.affine_star (p `star` q `star` s) r m

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
        (pts_to r full_perm v)
        (cas_provides r v v_new)
        fr
        (fun _ -> True)
        (fun _ _ _ -> True)
   = let m0 : full_mem = NMSTTotal.get () in
     let fv = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
     let fv' = Some (v_new, full_perm) in
     assert (interp (pts_to r full_perm v `star` fr `star` locks_invariant uses m0) m0);
     assert (interp (Mem.pts_to r fv `star` pure (perm_ok full_perm) `star` fr `star` locks_invariant uses m0) m0);
     cas_action_helper (Mem.pts_to r fv)
       (pure (perm_ok full_perm))
       fr
       (locks_invariant uses m0)
       m0;
     assert (interp ((Mem.pts_to r fv `star` pure (perm_ok full_perm)) `star` locks_invariant uses m0) m0);
     let fv_actual = Mem.frame (pure (perm_ok full_perm)) (sel_action uses r fv) fr in
     assert (compatible pcm_frac fv fv_actual);
     let Some (v', p) = fv_actual in
     assert (v == Ghost.hide v');
     assert (p == full_perm);
     let b =
       if eq v' v_old
       then (Mem.frame (pure (perm_ok full_perm)) (upd_action uses r fv fv') fr; true)
       else false
     in
     b

(*** GHOST REFERENCES ***)

let ghost_ref a = erased (ref a)

[@@__reduce__]
let ghost_pts_to #a (r:ghost_ref a) (p:perm) (x:erased a) = pts_to (reveal r) p x

let ghost_alloc_aux (#a:Type) (#u:_) (x:a)
  : SteelGhostT (ref a) u
                 emp
                 (fun r -> pts_to r full_perm (Ghost.hide x))
  = let v : fractional a = Some (x, full_perm) in
    assert (FStar.PCM.composable pcm_frac v None);
    assert (compatible pcm_frac v v);
    let r : ref a = as_atomic_action_ghost #_ #_ (Steel.Memory.alloc_action u v) in
    change_slprop (Steel.Memory.pts_to r v) (pts_to r full_perm x)
      (fun m -> emp_unit (pts_to_raw r full_perm x);
             pure_star_interp (pts_to_raw r full_perm x) (perm_ok full_perm) m);
    r

let ghost_alloc #a #u x =
  let r = ghost_alloc_aux #a #u (reveal x) in
  rewrite_context ();
  hide r

let ghost_share #a #u #p #x r = share (reveal r); rewrite_context ()
let ghost_gather #a #u #p0 #p1 #x0 #x1 r =
  gather #_ #_ #p0 #p1 #x0 #x1 (reveal r); rewrite_context ()

let ghost_pts_to_injective_eq #a #u #p #q r v0 v1 =
  higher_ref_pts_to_injective_eq (reveal r)

let ghost_write_aux (#a:Type) (#u:_) (#v:erased a) (r:ref a) (x:a)
  : SteelGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (Ghost.hide x))
  = let v_old : erased (fractional a) = Ghost.hide (Some (reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    change_slprop (pts_to r full_perm v)
                  (Mem.pts_to r v_old `star` pure (perm_ok full_perm))
                  (fun _ -> ());
    let _ = elim_perm_ok full_perm in
    as_atomic_action_ghost #_ #_ (Mem.upd_action u r v_old v_new);
    change_slprop (Mem.pts_to r v_new)
                  (pts_to r full_perm (hide x))
                  (fun m -> emp_unit (pts_to_raw r full_perm (hide x));
                         pure_star_interp (pts_to_raw r full_perm (hide x)) (perm_ok full_perm) m)

let ghost_write #a #u #v r x =
  ghost_write_aux (reveal r) (reveal x);
  rewrite_context ()

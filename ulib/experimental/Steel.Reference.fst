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

module Steel.Reference
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open FStar.Ghost
module H = Steel.HigherReference
module U = FStar.Universe
module A = Steel.Effect.Atomic

let ref a = H.ref (U.raise_t a)

let null #a = H.null #(U.raise_t a)
let is_null #a r = H.is_null #(U.raise_t a) r

let pts_to r p v = H.pts_to r p (hide (U.raise_val (reveal v)))

val raise_val_inj (#a:Type) (x y:a) : Lemma
  (requires U.raise_val x == U.raise_val y)
  (ensures x == y)

let raise_val_inj x y =
  U.downgrade_val_raise_val x;
  U.downgrade_val_raise_val y

let pts_to_ref_injective
      (#a: Type u#0)
      (r: ref a)
      (p0 p1:perm)
      (v0 v1: erased a)
      (m:mem)
    : Lemma
      (requires
        interp (pts_to r p0 v0 `star` pts_to r p1 v1) m)
      (ensures v0 == v1)
    = let v0' = hide (U.raise_val (reveal v0)) in
      let v1' = hide (U.raise_val (reveal v1)) in
      H.pts_to_ref_injective r p0 p1 v0' v1' m;
      raise_val_inj (reveal v0) (reveal v1)

let pts_to_not_null (#a:Type u#0)
                    (x:ref a)
                    (p:perm)
                    (v: erased a)
                    (m:mem)
  : Lemma (requires interp (pts_to x p v) m)
          (ensures x =!= null)
  = let v = hide (U.raise_val (reveal v)) in
    H.pts_to_not_null x p v m

let pts_to_witinv (#a:Type) (r:ref a) (p:perm) : Lemma (is_witness_invariant (pts_to r p)) =
  let aux (x y : erased a) (m:mem)
    : Lemma (requires (interp (pts_to r p x) m /\ interp (pts_to r p y) m))
            (ensures  (x == y))
    = H.pts_to_witinv r p;
      raise_val_inj (reveal x) (reveal y)
  in
  Classical.forall_intro_3 (fun x y -> Classical.move_requires (aux x y))

let extract_injective #a #p0 #p1 #v0 #v1 r =
  extract_info (pts_to r p0 v0 `star` pts_to r p1 v1) (v0 == v1)
    (fun m -> pts_to_ref_injective r p0 p1 v0 v1 m);
  change_slprop (pts_to r p1 v1) (pts_to r p1 v0) (fun _ -> ())

let alloc x =
  let r = H.alloc (U.raise_val x) in
  change_slprop (H.pts_to r full_perm (U.raise_val x)) (pts_to r full_perm x) (fun _ -> ());
  r

let read #a #p #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  change_slprop (pts_to r p v) (H.pts_to r p v') (fun _ -> ());
  let x = H.read #_ #p #v' r in
  let v':a = U.downgrade_val x in
  change_slprop (H.pts_to r p (hide x)) (pts_to r p v') (fun _ -> ());
  v'

let read_refine #a #p q r =
  A.lift_h_exists_atomic (fun (v:a) -> pts_to r p v `star` q v);
  A.h_exists_cong_atomic (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v))
                (fun (v:U.raise_t a) -> H.pts_to r p v `star` U.lift_dom q v);
  let x = H.read_refine (U.lift_dom q) r in
  change_slprop
    (H.pts_to r p (hide x) `star` U.lift_dom q x)
    (pts_to r p (U.downgrade_val x) `star` q (U.downgrade_val x)) (fun _ -> ());

  (U.downgrade_val x)

let write #a #v r x =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  change_slprop (pts_to r full_perm v) (H.pts_to r full_perm v') (fun _ -> ());
  let x' = U.raise_val x in
  H.write #_ #v' r x';
  change_slprop (H.pts_to r full_perm (hide x')) (pts_to r full_perm x) (fun _ -> ())

let free #a #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  change_slprop (pts_to r full_perm v) (H.pts_to r full_perm v') (fun _ -> ());
  H.free #_ #v' r

let share_atomic #a #uses #p #v r =
  let v' = Ghost.hide (U.raise_val (Ghost.reveal v)) in
  A.change_slprop (pts_to r p v) (H.pts_to r p v') (fun _ -> ());
  H.share_atomic #_ #_ #p #v' r;
  A.change_slprop (H.pts_to r (half_perm p) v') (pts_to r (half_perm p) v) (fun _ -> ());
  A.change_slprop (H.pts_to r (half_perm p) v') (pts_to r (half_perm p) v) (fun _ -> ())

let hide_raise_reveal (#a:Type) (v0:erased a) (v1:erased a)
  : Lemma (hide (U.raise_val (reveal v0)) == hide (U.raise_val (reveal v1)) <==>
           v0 == v1)
           [SMTPat (hide (U.raise_val (reveal v0)));
            SMTPat (hide (U.raise_val (reveal v1)))]
  = let u0 = hide (U.raise_val (reveal v0)) in
    let u1 = hide (U.raise_val (reveal v1)) in
    assert (U.downgrade_val (U.raise_val (reveal v0)) == U.downgrade_val (U.raise_val (reveal v1)) <==>
            v0 == v1)

let gather_atomic #a #uses #p0 #p1 #v0 #v1 r =
  let v0' = Ghost.hide (U.raise_val (Ghost.reveal v0)) in
  let v1' = Ghost.hide (U.raise_val (Ghost.reveal v1)) in
  A.change_slprop (pts_to r p0 v0) (H.pts_to r p0 v0') (fun _ -> ());
  A.change_slprop (pts_to r p1 v1) (H.pts_to r p1 v1') (fun _ -> ());
  let (u:unit{v0' == v1'}) = H.gather_atomic #_ #_ #p0 #p1 #v0' #v1' r in
  A.change_slprop (H.pts_to r (sum_perm p0 p1) v0') (pts_to r (sum_perm p0 p1) v0) (fun _ -> ());
  u

let raise_equiv (#t:Type) (x y:t)
  : Lemma (U.raise_val x == U.raise_val y <==>
           x == y)
  = assert (U.downgrade_val (U.raise_val x) == x);
    assert (U.downgrade_val (U.raise_val y) == y)


let downgrade_equiv (#t:Type) (x y:U.raise_t t)
  : Lemma (U.downgrade_val x == U.downgrade_val y <==>
           x == y)
  = assert (U.raise_val (U.downgrade_val x) == x);
    assert (U.raise_val (U.downgrade_val y) == y)

let lift_eq (#t:eqtype) (x y:U.raise_t t)
  : b:bool{b <==> x==y}
  = downgrade_equiv x y; U.downgrade_val x = U.downgrade_val y


let cas_action (#t:eqtype)
               (#uses:inames)
               (r:ref t)
               (v:Ghost.erased t)
               (v_old:t)
               (v_new:t)
               (frame:slprop)
   : MstTot (b:bool{b <==> (Ghost.reveal v == v_old)})
             uses
            (pts_to r full_perm v)
            (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
            frame
            (fun _ -> True)
            (fun _ _ _ -> True)
   = let hv =     (Ghost.hide (U.raise_val (Ghost.reveal v))) in
     let b = H.cas_action #(U.raise_t t)
                  (lift_eq #t)
                  #uses
                  r
                  hv
                  (U.raise_val v_old)
                  (U.raise_val v_new)
                  frame
     in
     assert (b <==> (Ghost.reveal hv == U.raise_val v_old));
     assert (b <==> U.raise_val (Ghost.reveal v) == U.raise_val v_old);
     raise_equiv (Ghost.reveal v) v_old;
     b


let cas #t #uses r v v_old v_new = A.as_atomic_action (cas_action #t #uses r v v_old v_new)

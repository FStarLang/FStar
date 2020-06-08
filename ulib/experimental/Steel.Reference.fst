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
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.FractionalPermission
open FStar.Ghost
module H = Steel.HigherReference
module U = FStar.Universe
module A = Steel.Effect.Atomic
module Basics = Steel.SteelT.Basics

let ref a = H.ref (U.raise_t a)

let pts_to r p v = H.pts_to r p (hide (U.raise_val (reveal v)))

let alloc x = H.alloc (U.raise_val x)

let read r =
  let x = H.read r in
  Basics.return (U.downgrade_val x)

let read_refine #a #p q r =
  Basics.h_assert (h_exists (fun (v:a) -> pts_to r p v `star` q v));
  Basics.lift_h_exists (fun (v:a) -> pts_to r p v `star` q v);
  Basics.h_assert (h_exists (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v)));
  Basics.h_exists_cong (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v))
                (fun (v:U.raise_t a) -> H.pts_to r p v `star` U.lift_dom q v);
  Basics.h_assert (h_exists (fun (v:U.raise_t a) -> H.pts_to r p v `star` U.lift_dom q v));
  let x = H.read_refine (U.lift_dom q) r in
  Basics.h_assert (H.pts_to r p x `star` U.lift_dom q x);
  Basics.h_assert (pts_to r p (U.downgrade_val x) `star` q (U.downgrade_val x));
  Basics.return (U.downgrade_val x)

let write r x = H.write r (U.raise_val x)

let free x = H.free x

let share_atomic r = H.share_atomic r

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
  let x = H.gather_atomic r in
  A.return_atomic x

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
               (_:unit)
   : MstTot (b:bool{b <==> (Ghost.reveal v == v_old)})
             uses
            (pts_to r full_perm v)
            (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
   = let hv =     (Ghost.hide (U.raise_val (Ghost.reveal v))) in
     let b = H.cas_action #(U.raise_t t) 
                  (lift_eq #t)
                  #uses
                  r
                  hv
                  (U.raise_val v_old)
                  (U.raise_val v_new)
                  ()
     in
     assert (b <==> (Ghost.reveal hv == U.raise_val v_old));
     assert (b <==> U.raise_val (Ghost.reveal v) == U.raise_val v_old);
     raise_equiv (Ghost.reveal v) v_old;
     b


let cas #t #uses r v v_old v_new = A.as_atomic_action (cas_action #t #uses r v v_old v_new)

let raise_ref r p v = Basics.return r

let lower_ref r p v = Basics.return r

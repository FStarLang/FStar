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

module E = Steel.Effect
module AT = Steel.Effect.Atomic
module M = Steel.Memory
module G = FStar.Ghost
module U = FStar.Universe
module A = Steel.Actions
module R = Steel.HigherReference
module B = Steel.SteelT.Basics
module AB = Steel.SteelAtomic.Basics

#set-options "--print_universes --print_implicits --fuel 0 --ifuel 0"

let alloc (#a:Type0) (x:a)
  : SteelT (ref a) emp (fun r -> pts_to r full x)
  =
  R.alloc #(U.raise_t u#0 u#1 a) (U.raise_val x)

let read (#a:Type0) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)
  =
  let x = R.read r in
  B.return (U.downgrade_val x)

let read_refine (#a:Type0) (#p:perm) (q:a -> hprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  =
  let x = R.read_refine (fun x -> q (U.downgrade_val x)) r in
  B.return (U.downgrade_val x)


let write (#a:Type0) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full v) (fun _ -> pts_to r full x)
  =
  R.write r (U.raise_val x)

let free (#a:Type0) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full v) (fun _ -> emp)
  =
  R.free r

let share (#a:Type0) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p v)
    (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)
  =
  R.share r

let gather (#a:Type0) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a)
  : SteelT unit
    (pts_to r p0 v0 `star` pts_to r p1 v1)
    (fun _ -> pts_to r (sum_perm p0 p1) v0)
  =
  R.gather r

let ghost_read_refine (#a:Type0) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
    (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)
  =
  let x = R.ghost_read_refine r (fun x -> q (U.downgrade_val x)) in
  AB.return_atomic (U.downgrade_val x)

module U = FStar.Universe

let cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_perm v)
    (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
  = SteelAtomic?.reflect (fun _ ->
      let m0 = mst_get () in
      //preorder_lifting_lemma t;
      let act = A.cas u#1 uses r v v_old v_new in
      let (| x, m1 |) = act m0 in
      atomic_preserves_frame_and_preorder act m0;
      mst_put m1;
      x)

////////////////////////////////////////////////////////////////////////////////

let alloc_monotonic_ref (#a:Type0) (p:Preorder.preorder a) (v:a)
  : SteelT (ref_pre a p) emp (fun r -> pts_to_pre r full v)
  =
  R.alloc_monotonic_ref (A.raise_preorder u#1 p) (U.raise_val v)


let read_monotonic_ref
  (#a:Type0)
  (#q:perm)
  (#p:Preorder.preorder a)
  (#frame:a -> hprop)
  (r:ref_pre a p)
  : SteelT a (h_exists (fun (v:a) ->
                pts_to_pre r q v `star` frame v))
             (fun v -> pts_to_pre r q v `star` frame v)
  =
  let x = R.read_monotonic_ref r in
  B.return (U.downgrade_val x)

let write_monotonic_ref
  (#a:Type0)
  (#p:Preorder.preorder a)
  (#v:erased a)
  (r:ref_pre a p)
  (x:a{p v x})
  : SteelT unit
    (pts_to_pre r full v)
    (fun v -> pts_to_pre r full x)
  =
  R.write_monotonic_ref r (U.raise_val x)

let pure (p:prop) : hprop =
  R.pure p

let witnessed
  (#a:Type0)
  (#p:Preorder.preorder a)
  (r:ref_pre a p)
  (fact:property a) : prop
  =
  R.witnessed r (fun x -> fact (U.downgrade_val x))

let witness
  (#a:Type0)
  (#q:perm)
  (#p:Preorder.preorder a)
  (r:ref_pre a p)
  (fact:stable_property p)
  (v:(Ghost.erased a))
  (pf:squash (fact v))
  : SteelT unit
    (pts_to_pre r q v)
    (fun _ -> pts_to_pre r q v `star` pure (witnessed r fact))
  =
  R.witness
    r
    _
    _
    pf

let recall (#a:Type u#0) (#q:perm) (#p:Preorder.preorder a) (#fact:property a)
           (r:ref_pre a p) (v:(Ghost.erased a))
  : SteelT unit (pts_to_pre r q v `star` pure (witnessed r fact))
                (fun _ -> pts_to_pre r q v `star` pure (fact v))
  =
  R.recall r _

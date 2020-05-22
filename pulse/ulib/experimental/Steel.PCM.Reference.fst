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

module Steel.PCM.Reference
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open Steel.PCM.FractionalPermission
open FStar.Ghost
module H = Steel.PCM.HigherReference
module U = FStar.Universe
module Basics = Steel.PCM.SteelT.Basics

let ref a = H.ref (U.raise_t a)

let pts_to r p v = H.pts_to r p (hide (U.raise_val (reveal v)))

let alloc x = H.alloc (U.raise_val x)


assume
val sl_admit (#a:_) (#p:_) (q:a -> slprop)
  : SteelT a p q


assume
val sl_admit_atomic (#a:_) (#uses:_) (#o:_) (#p:_) (q:a -> slprop)
  : SteelAtomic a uses o p q

let read r =
  let x = H.read r in
  Basics.return (U.downgrade_val x)

let lift_q #a (q:a -> slprop) : U.raise_t a -> slprop = fun v -> q (U.downgrade_val v)

// let h_exists #a (p:a -> slprop) =
//   h_forall #slprop (fun (q:slprop) ->
//   h_forall (fun (x:a) -> p x `wand` q) `wand` q)

// val elim_h_exists (#a:_) (p:a -> slprop) (q:slprop)
//   : SteelT unit (h_exists p)
//                 (fun _ -> h_forall (fun (x:a) -> p x `wand` q) `wand` q)


assume
val elim_h_exists (#a:_) (p:a -> slprop) (q:slprop { forall m (x:a). interp (p x) m ==> interp q m} )
  : SteelT unit (h_exists p)
                (fun _ -> q)

let lift_h_exists (#a:_) (p:a -> slprop)
  : SteelT unit (h_exists p)
                (fun _ -> h_exists #(U.raise_t a) (lift_q p))
  = sl_admit _

let h_exists_cong (#a:_) (p:a -> slprop) (q:a -> slprop {forall x. equiv (p x) (q x) })
  : SteelT unit (h_exists p)
                (fun _ -> h_exists q)
  = sl_admit _

let read_refine #a #p q r =
  Basics.h_assert (h_exists (fun (v:a) -> pts_to r p v `star` q v));
  lift_h_exists (fun (v:a) -> pts_to r p v `star` q v);
  Basics.h_assert (h_exists (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v)));
  h_exists_cong (fun (v:U.raise_t a) -> pts_to r p (U.downgrade_val v) `star` q (U.downgrade_val v))
                (fun (v:U.raise_t a) -> H.pts_to r p v `star` lift_q q v);
  Basics.h_assert (h_exists (fun (v:U.raise_t a) -> H.pts_to r p v `star` lift_q q v));
  let x = H.read_refine (lift_q q) r in
  Basics.h_assert (H.pts_to r p x `star` lift_q q x);
  Basics.h_assert (pts_to r p (U.downgrade_val x) `star` q (U.downgrade_val x));
  Basics.return (U.downgrade_val x)

let write r x = H.write r (U.raise_val x)

let free x = H.free x

let share r = H.share r

let gather r = H.gather r

let ghost_read_refine r q = sl_admit_atomic _

let cas r v v_old v_new = sl_admit_atomic _

let raise_ref r p v = Basics.return r

let lower_ref r p v = Basics.return r

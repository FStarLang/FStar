(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStar.Universe.PCM
(* Lift a PCM to a higher universe, including its frame-preserving updates *)
open FStar.PCM
open FStar.Universe
open FStar.Classical.Sugar

let raise (#a:Type) (p:pcm a)
  : pcm (raise_t u#a u#b a)
  = {
      p = {
             composable = (fun x y -> p.p.composable (downgrade_val x) (downgrade_val y));
             op = (fun x y -> raise_val (p.p.op (downgrade_val x) (downgrade_val y)));
             one = raise_val p.p.one;
          };
      comm = (fun x y -> p.comm (downgrade_val x) (downgrade_val y));
      assoc = (fun x y z -> p.assoc (downgrade_val x) (downgrade_val y) (downgrade_val z));
      assoc_r = (fun x y z -> p.assoc_r (downgrade_val x) (downgrade_val y) (downgrade_val z));
      is_unit = (fun x -> p.is_unit (downgrade_val x));
      refine = (fun x -> p.refine (downgrade_val x));
    }

let raise_frame_preserving_upd (#a:Type u#a) (#p:pcm a) (#x #y:a) (f:frame_preserving_upd p x y)
  : frame_preserving_upd (raise u#a u#b p) (raise_val u#a u#b x) (raise_val u#a u#b y)
  = fun v ->
      let u = f (downgrade_val v) in
      let v_new = raise_val u#a u#b u in
      assert (forall frame. composable p y frame ==> composable (raise u#a u#b p) (raise_val u#a u#b y) (raise_val u#a u#b frame));
      assert (forall frame. composable (raise u#a u#b p) (raise_val u#a u#b x) frame ==> composable p x (downgrade_val frame));
      v_new

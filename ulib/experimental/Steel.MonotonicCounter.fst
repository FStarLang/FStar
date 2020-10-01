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

module Steel.MonotonicCounter
open FStar.PCM
open Steel.Preorder
open FStar.Preorder

/// This small module is an experiment that demonstrate how to use [Steel.Preorder] to define
/// a monotonically increasing counter.


(* The PCM corresponding to the monotonically increasing counter is just the maximum element *)
let pre_pcm : pcm' nat = {
  composable=(fun x y -> True);
  op=(fun (x y:nat) -> Math.Lib.max x y);
  one=0
}
let mctr_pcm : pcm nat = {
  p=pre_pcm;
  comm=(fun _ _ -> ());
  assoc=(fun _ _ _ -> ());
  assoc_r=(fun _ _ _ -> ());
  is_unit=(fun _ -> ());
  refine=(fun _ -> True);
}

(** This is a classical preorder for monotonic increase *)
let increasing : preorder nat = fun (x y:nat) -> b2t (x <= y)

(** Indeed, the [increasing] preorder is induced by the PCM *)
let mctr_induces_increases
  : squash (induces_preorder mctr_pcm increasing)
  = ()

(** Small test: two values compatible for the PCM preserve a stable fact for the preorder *)
let test (x z:nat) (f:(nat -> prop){stable f increasing})
  : Lemma
    (requires (compatible mctr_pcm x z /\ f x))
    (ensures f z)
  = assert (increasing x z)

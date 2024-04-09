(*
   Copyright 2024 Microsoft Research

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

module PulseCore.NondeterministicMonotonicStateMonad
open FStar.Preorder
friend PulseCore.MonotonicStateMonad
module M = PulseCore.MonotonicStateMonad

#push-options "--print_universes"

let tape = nat -> bool
let ctr = nat

let nmst' (#s:Type u#s)
          (rel:FStar.Preorder.preorder s)
          (a:Type u#a)
          (pre:s -> prop)
          (post:s -> a -> s -> prop)
  = s0:s { pre s0 }
    -> tape
    -> ctr
    -> Dv (
        res:(a & s & ctr) {
            post s0 res._1 res._2 /\
            rel s0 res._2
        }
    )

let nmst #s rel a pre post =
    unit -> Dv (nmst' #s rel a pre post)

let lift #s #rel #a #pre #post (f:M.mst #s rel a pre post)
: nmst #s rel a pre post
= fun () s t c -> let x, s1 = f s in (x, s1, c)

let return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: nmst rel a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)
= fun () s0 t c -> (x, s0, c)

let bind f g =
    fun () s0 t c ->
        let x, s1, c = f () s0 t c in
        g x () s1 t c

let weaken f = fun () s t c -> f () s t c

let flip _ = fun () s t c -> (t c, s, c + 1)

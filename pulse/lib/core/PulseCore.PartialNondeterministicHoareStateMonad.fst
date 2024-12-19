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

module PulseCore.PartialNondeterministicHoareStateMonad

module NST = PulseCore.NondeterministicHoareStateMonad
type tape = nat -> bool
type ctr = nat

type pnst' (#s:Type u#s)
           (a:Type u#a)
           (pre:req_t s)
           (post:ens_t s a) =
  s0:s { pre s0 } ->
  tape ->
  ctr ->
  Dv (res:(a & s & ctr) {
    post s0 res._1 res._2
  })
let pnst #s a pre post = unit -> Dv (pnst' #s a pre post)

let repr #s #a #pre #post f = fun s0 t c -> f () s0 t c
let lift #s #a #pre #post f =
  fun () s0 t c -> let x, s1, c1 = NST.repr f s0 t c in x, s1, c1

let return #s #a x =
  fun () s0 t c -> x, s0, c

let bind #s #a #b #req_f #ens_f #req_g #ens_g f g =
  fun () s0 t c ->
  let x, s1, c = f () s0 t c in
  g x () s1 t c

let weaken #s #a #req_f #ens_f #req_g #ens_g f =
  fun () s0 t c -> f () s0 t c

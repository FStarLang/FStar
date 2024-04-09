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
open PulseCore.MonotonicStateMonad
module M = PulseCore.MonotonicStateMonad

val nmst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
: Type u#0

val lift #s #rel #a #pre #post (f:M.mst #s rel a pre post)
: nmst #s rel a pre post

val return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: nmst rel a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:nmst rel a req_f ens_f)
      (g:(x:a -> Dv (nmst rel b (req_g x) (ens_g x))))
: nmst rel b
  (fun s0 ->
    req_f s0 /\
    (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 ->
    req_f s0 /\
    (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    
val weaken
      (#s:Type u#s)
      (#rel:preorder s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:nmst rel a req_f ens_f)
: Pure 
  (nmst rel a req_g ens_g)
  (requires
    (forall s. req_g s ==> req_f s) /\
    (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
  (ensures fun _ -> True)

val flip (#s:Type u#s) (#rel:preorder s) (_:unit)
  : nmst rel bool (fun _ -> True) (fun s0 x s1 -> s0 == s1)
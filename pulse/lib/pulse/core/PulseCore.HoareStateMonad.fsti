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

module PulseCore.HoareStateMonad

let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

let st
    (#s:Type u#s)
    (a:Type u#a)
    (pre:req_t s)
    (post:ens_t s a)
: Type u#(max a s)
= s0:s { pre s0 }
    -> (
        res:(a & s) {
            post s0 res._1 res._2
        }
    )

val return (#s:Type u#s)
           (#a:Type u#a)
           (x:a)
: st #s a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      ($f:st #s a req_f ens_f)
      ($g:(x:a -> st #s b (req_g x) (ens_g x)))
: st b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    
val weaken
      (#s:Type u#s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      ($f:st #s a req_f ens_f)
    : Pure (st #s a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

val get (#s:Type u#s) (_:unit)
  : st s (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == s0)

val put (#s:Type u#s) (v:s)
  : st unit (fun s0 -> True) (fun s0 x s1 -> v == s1)
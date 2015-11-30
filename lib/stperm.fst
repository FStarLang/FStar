(*--build-config
  options: --admit_fsi FStar.Set;
  other-files: set.fsi heap.fst;
  --*)
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.ST
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.Set
open FStar.Heap

// this intentionally does not preclude h' extending h with fresh refs
opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

kind STPre = STPre_h heap
kind STPost (a:Type) = STPost_h heap a
kind STWP (a:Type) = STWP_h heap a
new_effect STATE = STATE_h heap
effect State (a:Type) (wp:STWP a) =
       STATE a wp wp
effect ST (a:Type) (pre:STPre) (post: (heap -> STPost a)) =
       STATE a
             (fun (p:STPost a) (h:heap) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
             (fun (p:STPost a) (h:heap) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:heap) -> wp (fun a -> p a h)

(* signatures WITH permissions *)
assume val alloc: #a:Type -> init:a -> ST (ref a)
                                         (fun h -> True)
                                         (fun h0 r h1 -> not(contains h0 r) /\ contains h1 r /\ h1==upd h0 r init)

assume val read: #a:Type -> r:ref a -> ST a
                                         (requires (fun h -> contains h r))
                                         (ensures (fun h0 x h1 -> h0==h1 /\ x==sel h0 r))

assume val write: #a:Type -> r:ref a -> v:a -> ST unit
                                                 (requires (fun h -> contains h r))
                                                 (ensures (fun h0 x h1 -> h1==upd h0 r v))

assume val op_Colon_Equals: #a:Type -> r:ref a -> v:a -> ST unit
                                                 (requires (fun h -> contains h r))
                                                 (ensures (fun h0 x h1 -> h1==upd h0 r v))

assume val free: #a:Type -> r:ref a -> ST unit
         (requires (fun h -> contains h r))
         (ensures (fun h0 x h1 -> modifies !{r} h0 h1 /\ not(contains h1 r)))

assume val get: unit -> State heap (fun 'post h -> 'post h h)

assume val forget_ST: #a:Type -> #b:(a -> Type)
  -> #req:(a -> heap -> Type)
  -> #ens:(x:a -> heap -> b x -> heap -> Type)
  -> =f:(x:a -> ST (b x) (req x) (ens x))
  -> Pure (x:a -> Div (b x)
                 (requires (forall h. req x h))
                 (ensures (fun (y:b x) -> exists h0 h1. ens x h0 y h1)))
          (requires (forall (x:a) (y:b x) h h'.
                        (req x h /\ ens x h y h' ==> modifies !{} h h')))
          (ensures (fun _ -> True))

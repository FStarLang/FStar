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
type ref (a:Type) = Heap.ref a

// this intentionally does not preclude h' extending h with fresh refs
type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

let st_pre = st_pre_h heap
let st_post a = st_post_h heap a
let st_wp a = st_wp_h heap a
new_effect STATE = STATE_h heap
unfold let lift_div_state (a:Type) (wp:pure_wp a) (p:st_post a) (h:heap) = wp (fun a -> p a h)
sub_effect DIV ~> STATE = lift_div_state

effect State (a:Type) (wp:st_wp a) =
       STATE a wp
effect ST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)

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
  -> $f:(x:a -> ST (b x) (req x) (ens x))
  -> Pure (x:a -> Div (b x)
                 (requires (forall h. req x h))
                 (ensures (fun (y:b x) -> exists h0 h1. ens x h0 y h1)))
          (requires (forall (x:a) (y:b x) h h'.
                        (req x h /\ ens x h y h' ==> modifies !{} h h')))
          (ensures (fun _ -> True))

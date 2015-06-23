(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:set.fsi heap.fst map.fsi list.fst
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
module HyperHeap
open Map
open Heap
type rid = list int
type t = Map.t rid heap
new_effect STATE = STATE_h t

private type rref (id:rid) (a:Type) = Prims.ref a
val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref id r = r

private val ref_as_rref : #a:Type -> i:rid -> r:ref a -> Tot (rref i a)
let ref_as_rref i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj i r = ()

effect ST (a:Type) (pre:t -> Type) (post:t -> a -> t -> Type) =
       STATE a (fun 'p m0 -> pre m0 /\ (forall x m1. post m0 x m1 ==> 'p x m1))
               (fun 'p m0 ->  (forall x m1. pre m0 /\ post m0 x m1 ==> 'p x m1))

val includes : rid -> rid -> Tot bool
let rec includes (r1:rid) (r2:rid) =
 if r1=r2 then true
 else if List.length r2 > List.length r1
 then includes r1 (Cons.tl r2)
 else false

let extends r1 r0 = is_Cons r1 && Cons.tl r1 = r0

let test0 = assert (includes [1;0] [2;1;0])
let test1 (r1:rid) (r2:rid{includes r1 r2}) = assert (includes r1 (0::r2))
let test2 (r1:rid) (r2:rid{extends r1 r2})  = assert (includes r2 r1)

type fresh_region (i:rid) (m0:t) (m1:t) =
 (forall j. includes i j ==> not (Map.contains m0 j))
 /\ Map.contains m1 i

assume val new_region: r0:rid -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
                        /\ m1=Map.upd m0 r1 Heap.emp))

type Let (#a:Type) (x:a) (body:(a -> Type)) = body x

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> Map.contains m i))
    (ensures (fun m0 x m1 ->
                    Let (Map.sel m0 i) (fun region_i ->
                    not (Heap.contains region_i (as_ref x))
                    /\ m1=Map.upd m0 i (Heap.upd region_i (as_ref x) init))))

assume val op_ColonEquals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _u m1 -> m1= Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)))

assume val op_Bang:#a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m1=m0 /\ x=Heap.sel (Map.sel m0 i) (as_ref r)))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

opaque type modifies (s:Set.set rid) (m0:t) (m1:t) =
  (forall (id:rid).{:pattern (Map.contains m0 id)}
     Map.contains m0 id
      ==> (Map.contains m1 id
        /\ (forall (id':rid). {:pattern Set.mem id' s} Set.mem id' s /\ not (includes id' id))
            ==> Map.sel m1 id = Map.sel m0 id))

type contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

type fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))

kind STPost (a:Type) = a -> t -> Type
kind STWP (a:Type) = STPost a -> t -> Type

sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:t) -> wp (fun a -> p a h)

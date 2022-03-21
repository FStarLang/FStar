(*
   Copyright 2008-2018 Microsoft Research

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
module NatHeap

open FStar.Preorder

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

(* NB: (a:Type0 & a) instead of dtuple2 is better notation *)

module F = FStar.FunctionalExtensionality

let heap = h:(nat * (F.restricted_t nat (fun _ -> (option (dtuple2 Type0 (fun a -> a))))))
		       {(forall (n:nat) . n < fst h ==> (exists v . snd h n == Some v)) /\ 
			(forall (n:nat) . n >= fst h ==> snd h n == None)}


(* Consistency of heaps. aka, no strong updates *)

let consistent (h0:heap) (h1:heap) : GTot Type0 =
  forall n x y . (snd h0 n == Some x /\ snd h1 n == Some y)  ==> dfst x == dfst y


(* References. *)

let ref (a:Type) = nat

//type aref =
//  | Ref : a:Type -> r:ref a -> aref

(* Containment predicate on heaps. *)

let contains (#a:Type) (h:heap) (r:ref a) : GTot Type0 =
  exists x . snd h r == Some (| a , x |)

//NB: Some? (snd h r), would avoid the existential, but would not capture the type equality

//NB: match snd h r with | Some (| b, _ |) -> a == b | _ -> False
//    this style would avoid the existential

//NB: Although, it appears that the existential variable actually seems to help in this case
//    would be good to understand why (at some point)

(* Select. *)

let sel #a h r =
  match snd h r with
  | Some (| _ , x |) -> x


(* Generating a fresh reference for the given heap. *)

let alloc_ref h0 a x = 
  (fst h0 , (fst h0 + 1 , F.on_dom nat (fun r -> if r = fst h0 then Some (| a , x |)
					     else snd h0 r)))


(* Update. *)

let upd #a h0 r x = 
  (fst h0 , F.on_dom nat (fun r' -> if r = r' then Some (| a , x |)
                                else snd h0 r'))


let emp = Mktuple2 0 (F.on_dom nat (fun (r:nat) -> None))


let concat h0 h1 = 
  (max (fst h0) (fst h1) , F.on_dom nat (fun r -> match snd h0 r with
                                             | None -> snd h1 r
  				             | Some v -> 
  				               (match snd h1 r with
  					        | None -> Some v
  					        | Some v' -> Some v')))


(* Lemmas about the consistency of heaps. *)

let consistent_refl h = ()

let emp_consistent h = ()

let upd_consistent h a r x = ()

let alloc_ref_consistent h a x = ()

let contains_sel h a r = ()

let contains_upd h a b r x r' = ()           

let contains_emp a r = ()

let sel_upd1 h a r x = ()

let sel_upd2 h a b r x r' = ()

let upd_sel h a r = 
  assert (FStar.FunctionalExtensionality.feq (snd (upd h r (sel h r))) (snd h))

let contains_concat1 h0 h1 a r = 
  match snd h0 r with
  | Some v -> 
      (match snd h1 r with
       | None -> ()
       | Some v' -> assert (dfst v == dfst v'))

let contains_concat2 h0 h1 a r = ()

let sel_concat1 h0 h1 a r = 
  match snd h0 r with
  | Some v -> 
      match snd h1 r with
      | None -> ()
      | Some v' -> assert (dfst v == dfst v')

let sel_concat2 h0 h1 a r = ()


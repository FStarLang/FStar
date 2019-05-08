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
(*  A very rough sketch of how we can use regions and observational purity ...
*)
module PromoteAndDemote
open FStar.HyperStack
open FStar.Ghost

val swap : int*int -> Tot (int*int)
let swap (x, y) = (y, x)
(*
 promote (let r = new_region in 
   let x = ralloc_pair 0 1 in 
   let q = promote (let p : located (int * int) = demote swap x r in p) : Tot (located (int * int)) in
   //  drop r; if you drop r here, then the deref at the next line fails
   let ret = lfst q + lsnd q in 
   drop r; ret) : Tot int

Take 2: (useless)
   promote (let q = demote swap (#locate (0, 1))  in
	    lfst q + lsnd q)

take 3: equivalent (provably?) to take 2, and so much nicer
   let x, y = swap (0,1) in x + y

*)

(*abstract *)let located t = stackref t

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
//Note: eventually, we want to package up r:rid inside the monad
//STL: signifies that the stack of regions doesn't change

assume val reify : #a:Type0 -> #wp:st_wp a -> $f:(unit -> STATE a wp) -> Tot (m0:mem -> PURE (a * mem) (fun (post:(a*mem) -> Type0) ->  wp (fun (y:a) m1 -> post (y, m1)) m0))

//Questions: located is a shallow? i.e., it's just an abstract type constructor
//           we might want it to be deep, meaning that it could be some type function that operates on the type structure
//           but, it's not clear how to make that type function work in an open world
assume val demote: f:('a -> Tot 'b) -> Tot (x:located 'a -> STL (located 'b)
					       (requires (fun m -> HS.contains m x))
					       (ensures (fun m0 y m1 -> HS.frameOf y = HS.frameOf x 
								   /\ modifies (Set.singleton (HS.frameOf x)) m0 m1
								   /\ HS.sel m1 y = f (HS.sel m0 x)
								   /\ HS.modifies_ref (HS.frameOf x) Set.empty m0 m1
								   /\ HH.fresh_rref y.ref m0.h m1.h)))

//Question: Is there a variant of demote that includes an extrinsic spec for the demoted function in terms of its reification
//E.g., something like this:
#set-options "--print_universes"

(* assume val demote': #a:Type0 -> #b:Type0 -> f:(a -> Tot b) -> Tot (g:(x:located a -> STL (located b) *)
(* 					       (requires (fun m -> HS.contains m x)) *)
(* 					       (ensures (fun m0 y m1 -> HS.frameOf y = HS.frameOf x  *)
(* 								   /\ modifies (Set.singleton (HS.frameOf x)) m0 m1 *)
(* 								   /\ HS.sel m1 y = f (HS.sel m0 x) *)
(* 								   /\ HS.modifies_ref (HS.frameOf x) Set.empty m0 m1 *)
(* 								   /\ HH.fresh_rref y.ref m0.h m1.h))){ *)
(* 								   forall (x:located a) (m0:mem).   *)
(* 								     HS.contains m0 x  *)
(* 								     ==> (let y, m1 = reify (fun () -> g x) m0 in  //this will not type check, because of some bizarre universe error ... need to investigate *)
(* 								         (sel m0 x) = sel m1 y)}) *)



//st_wp a = st_post a -> st_pre
//	  = (a -> mem -> Type) -> mem -> Type
//PURE : a:Type -> pure_wp a -> Comp
//     where pure_wp a = pure_post  a -> pure_pre
//		     = (a -> Type) -> Type
//TODO: this is needlessly specific for Type0, some universe inference glitch
//Also, in general, reify 

assume val eq_l : mem -> mem -> located 'a -> located 'a -> Type0

effect StTot (a:Type) = STATE a (fun post m0 -> forall (x:a) (m1:mem). post x m1)
val reify_tot : #a:Type0 -> $f:(unit -> StTot a) -> Tot (m0:mem -> Tot (a * mem)) 
let reify_tot #a f = reify f

assume val promote: #a:Type0
		  -> f:(unit -> StTot a)//(located a))
		  -> Pure a
		         (requires (forall m0 m1. 
				      let x0, m0' = reify f m0 in
      				      let x1, m1' = reify f m1 in
				      eq_l m0' m1' x0 x1 //the contents of x0 in m0' matches the contents of x1 in m1'
				      /\ modifies (Set.singleton (HS.frameOf x0)) m0 m0'
     				      /\ modifies (Set.singleton (HS.frameOf x1)) m1 m1'
		      		      /\ HS.modifies_ref (HS.frameOf x0) Set.empty m0 m0'
      		      		      /\ HS.modifies_ref (HS.frameOf x1) Set.empty m1 m1'))
			 (ensures (fun (x:a) -> forall (m0:mem). let l, m1 = reify f m0 in x = sel m1 l))
			 

(* Eventually, we should expect this to check: 

   promote (fun () -> 
   let x = ralloc_pair (get_region()) 0 1 in
   demote' swap x : STL (located (int * int)) (requires (fun m -> HS.contains m x)) (ensures (fun ... ))) : Tot (int * int)

*)

(* To support this, we'd compile swap like so:

   let swap l = 
     let x = lpair_get_fst l in
     let y = lpair_get_snd l in
     lalloc_pair (region_of l) y x


  But, how would we compile:

     let swap_deep ((x, y), (a, b)) = ((b, a), (y, x)) ??

  cf. the discussion about deep vs. shallow located things
*)

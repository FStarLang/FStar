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
module Curve.Point

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Math.Lib
open Math.Field
open Math.Curve
open Curve.Parameters
open Curve.Bigint
open Curve.Bignum
open FStar.UInt64

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module HS = FStar.HyperStack

let w: u32 -> Tot int = U32.v
let vv: u128 -> Tot int = U128.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let heap = HS.mem

type point = | Point: x:bigint -> y:bigint -> z:bigint -> point

val get_x: point -> Tot bigint
let get_x p = Point.x p
val get_y: point -> Tot bigint
let get_y p = Point.y p
val get_z: point -> Tot bigint
let get_z p = Point.z p

// Separation between the references of all three coordinates
abstract type separateCoordinates (p:point) = 
  disjoint (get_x p) (get_y p) /\ disjoint (get_x p) (get_z p) /\ disjoint (get_y p) (get_z p)

// Point "live" in memory 'h'
abstract type live (h:heap) (p:point) = 
  live h (get_x p) /\ live h (get_y p) /\ live h (get_z p) /\ separateCoordinates p

// Wellformedness of points : all its coordinates are properly normalized big integers
abstract type wellFormed (h:heap) (p:point) =
  norm h (get_x p) /\ norm h (get_y p) /\ norm h (get_z p) /\ separateCoordinates p

val to_apoint: h:heap -> p:point{live h p} -> GTot Math.Curve.affine_point
let to_apoint h p = 
  Affine.p (to_affine (Projective (Proj (valueOf h (get_x p)) (valueOf h (get_y p)) (valueOf h (get_z p)))))

// Proper point located on the curve
type onCurve (h:heap) (p:point) =
  wellFormed h p /\ curvePoint (to_apoint h p)

(* val refs: p:point -> GTot (Set.set abuffer) *)
let refs p : GTot (FStar.TSet.set abuffer) = (only (get_x p) ++ only (get_y p) ++ only (get_z p))

(* val erefs: p:point -> Tot (FStar.Ghost.erased (FStar.TSet.set FStar.Heap.aref)) *)
let erefs p = hide (refs p)

let op_Plus_Plus_Plus a b = FStar.TSet.union a b

// Two distincts points from a memory point of view
type distinct (a:point) (b:point) =
  disjoint (get_x a) (get_x b) /\ disjoint (get_x a) (get_y b) /\ disjoint (get_x a) (get_z b)
  /\ disjoint (get_y a) (get_x b) /\ disjoint (get_y a) (get_y b) /\ disjoint (get_y a) (get_z b)
  /\ disjoint (get_z a) (get_x b) /\ disjoint (get_z a) (get_y b) /\ disjoint (get_z a) (get_z b)

assume val set_intersect_lemma: #a:Type -> x:FStar.TSet.set a -> y:FStar.TSet.set a -> Lemma
  (FStar.TSet.intersect x y = FStar.TSet.intersect y x)

val make: bigint -> bigint -> bigint -> Tot point
let make x y z = Point x y z

// Map curve points to curve points, any other to the point at infinity
val pointOf: h:heap -> p:point{onCurve h p} -> GTot Math.Curve.celem
let pointOf h p = to_apoint h p

abstract type partialSwap (h0:heap) (h1:heap) (is_swap:u64) (ctr:nat{ctr<=norm_length})
  (a:bigint) (b:bigint{disjoint a b}) =
  norm h0 a /\ norm h0 b /\ norm h1 a /\ norm h1 b 
  /\ (forall (i:nat). {:pattern (get h1 a i) \/ (get h1 b i)} (i >= ctr /\ i < norm_length) ==>
      ((v is_swap = 0 ==> (v (get h1 a i) = v (get h0 a i) 
		         /\ v (get h1 b i) = v (get h0 b i)))
       /\ (v is_swap = pow2 platform_size - 1 ==> (v (get h1 a i) = v (get h0 b i) 
						       /\ v (get h1 b i) = v (get h0 a i)))))

val swap_conditional_aux': a:bigint -> b:bigint{disjoint a b} ->  
  is_swap:u64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  ctr:u32{w ctr<=norm_length} -> STL unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1
      /\ norm h0 a /\ norm h0 b /\ norm h1 a /\ norm h1 b
      (* /\ EqSub h0 a 0 h1 a 0 ctr /\ EqSub h0 b 0 h1 b 0 ctr *)
      /\ partialSwap h0 h1 is_swap (w ctr) a b))
let rec swap_conditional_aux' a b swap ctr =
  admit(); // TODO
  let h0 = HST.get() in
  if U32.eq nlength ctr then ()
  else begin
    admitP (True /\ w ctr < norm_length); 
    let ai = index a ctr in 
    let bi = index b ctr in 
    let y = ai ^^ bi in 
    let x = swap &^ y in
    let ai' =  x ^^ ai in
    let bi' = x ^^ bi in
    // Definition of the bitwise operations
    admitP (v swap = 0 ==> (v ai' = v ai /\ v bi' = v bi));
    admitP (v swap = pow2 platform_size - 1 ==> (v ai' = v bi /\ v bi' = v ai)); 
    upd a ctr ai'; 
    let h2 = HST.get() in
    upd b ctr bi'; 
    let h3 = HST.get() in 
    (* upd_lemma h0 h2 a ctr ai';  *)
    (* no_upd_lemma h0 h2 b (only a);  *)
    (* upd_lemma h2 h3 b ctr bi';   *)
    (* no_upd_lemma h2 h3 a (only b);  *)
    swap_conditional_aux' a b swap (ctr+|1ul); 
    let h1 = HST.get() in
    admitP (forall (i:nat). (i >= w ctr + 1 /\ i < norm_length) ==> 
      ((v swap = 0 ==> (v (get h1 a i) = v (get h0 a i) 
	         /\ v (get h1 b i) = v (get h0 b i)))
       /\ (v swap = pow2 platform_size - 1 ==> (v (get h1 a i) = v (get h0 b i) 
					       /\ v (get h1 b i) = v (get h0 a i)))));
    admitP (forall (i:nat). {:pattern (get h1 a i) \/ (get h1 b i)} 0+i = i); 
    cut (forall (i:nat). {:pattern (get h1 a i)} i < w ctr ==> v (get h1 a i) = v (get h3 a i)); 
    cut (forall (i:nat). {:pattern (get h1 b i)} i < w ctr ==> v (get h1 b i) = v (get h3 b i));
    ()
 end
#reset-options

val swap_conditional_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint{disjoint a b} ->
  is_swap:u64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} -> 
  Lemma
    (requires (partialSwap h0 h1 is_swap 0 a b))
    (ensures (norm h0 a /\ norm h1 a /\ norm h0 b /\ norm h1 b 
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = pow2 platform_size - 1 ==> 
  	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) )) []
let rec swap_conditional_aux_lemma h0 h1 a b swap =
  admit(); // OK
  if (v swap = 0) then (
    eval_eq_lemma h0 h1 a a norm_length; 
    eval_eq_lemma h0 h1 b b norm_length )
  else (eval_eq_lemma h0 h1 a b norm_length; eval_eq_lemma h0 h1 b a norm_length)

#reset-options

val swap_conditional_aux: a:bigint -> b:bigint{disjoint a b} ->
  is_swap:u64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} -> 
  ctr:nat{ctr<=norm_length} -> STL unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 _ h1 -> modifies_2 a b h0 h1
      /\ norm h0 a /\ norm h0 b /\ norm h1 a /\ norm h1 b
      /\ (v is_swap = 0 ==> ((valueOf h1 a = valueOf h0 a) /\ (valueOf h1 b = valueOf h0 b)))
      /\ (v is_swap = pow2 platform_size - 1 ==> 
  	  ((valueOf h1 a = valueOf h0 b) /\ (valueOf h1 b = valueOf h0 a))) ))
let rec swap_conditional_aux a b swap ctr =
  let h0 = HST.get() in
  swap_conditional_aux' a b swap 0ul; 
  let h1 = HST.get() in 
  swap_conditional_aux_lemma h0 h1 a b swap  

#reset-options

(* val norm_lemma: h0:heap -> h1:heap -> b:bigint{norm h0 b} -> mods:FStar.TSet.set aref -> *)
(*   Lemma (requires (modifies mods h0 h1 /\ not(FStar.TSet.mem (Ref (getRef b)) mods))) *)
(* 	(ensures (norm h1 b /\ valueOf h1 b = valueOf h0 b)) *)
(* let norm_lemma h0 h1 b mods = *)
(*   admit(); // OK *)
(*   Eval.eval_eq_lemma h0 h1 b b norm_length *)

(* open FStar.Ghost *)

(* val enorm_lemma: h0:heap -> h1:heap -> b:bigint{norm h0 b} -> mods:erased (FStar.TSet.set aref) -> *)
(*   Lemma (requires (modifies (reveal mods) h0 h1 /\ not(FStar.TSet.mem (Ref (getRef b)) (reveal mods)))) *)
(* 	(ensures (norm h1 b /\ valueOf h1 b = valueOf h0 b)) *)
(* let enorm_lemma h0 h1 b mods = *)
(*   admit(); // OK *)
(*   Eval.eval_eq_lemma h0 h1 b b norm_length *)

(* #reset-options *)

val swap_is_on_curve: h0:heap -> h3:heap -> a:point -> b:point{distinct a b} -> 
  is_swap:u64{v is_swap = pow2 platform_size - 1 \/ v is_swap = 0} -> Lemma
    (requires (wellFormed h0 a /\ wellFormed h0 b /\ wellFormed h3 a /\ wellFormed h3 b
	      /\ (v is_swap = 0 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x a) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z a)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x b)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z b)))
	 /\ (v is_swap = pow2 platform_size - 1 ==> 
	   (valueOf h3 (get_x a) = valueOf h0 (get_x b) 
	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y b)
	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z b)
	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x a)
	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y a)
	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z a))) ))
  (ensures ((onCurve h0 a /\ onCurve h0 b) ==> (onCurve h3 a /\ onCurve h3 b)))
let swap_is_on_curve h0 h3 a b is_swap = 
  admit(); // OK
  ()

#reset-options
val swap_conditional_lemma: h0:heap -> h1:heap -> h2:heap -> h3:heap -> a:point -> b:point{distinct a b} -> is_swap:u64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  Lemma (requires (onCurve h0 a /\ onCurve h0 b /\ modifies_2 (get_x a) (get_x b) h0 h1
           /\ modifies_2 (get_y a) (get_y b) h1 h2
	   /\ modifies_2 (get_z a) (get_z b) h2 h3
	   /\ norm h1 (get_x a) /\ norm h1 (get_x b) /\ norm h1 (get_y a) /\ norm h1 (get_y b)
	   /\ norm h2 (get_y a) /\ norm h2 (get_y b) /\ norm h2 (get_z a) /\ norm h2 (get_z b)
	   /\ norm h3 (get_z a) /\ norm h3 (get_z b) 
	   /\ (v is_swap = 0 ==> 
	   	   (valueOf h1 (get_x a) = valueOf h0 (get_x a) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y a) 
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z a) 
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x b)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z b)))
	   /\ (v is_swap = pow2 platform_size - 1 ==>
	           (valueOf h1 (get_x a) = valueOf h0 (get_x b) 
		   /\ valueOf h2 (get_y a) = valueOf h1 (get_y b)
		   /\ valueOf h3 (get_z a) = valueOf h2 (get_z b)
		   /\ valueOf h1 (get_x b) = valueOf h0 (get_x a)
		   /\ valueOf h2 (get_y b) = valueOf h1 (get_y a)
		   /\ valueOf h3 (get_z b) = valueOf h2 (get_z a)))
	))
	(ensures (onCurve h0 a /\ onCurve h0 b /\ onCurve h3 a /\ onCurve h3 b
	  (* /\ modifies (refs a +++ refs b) h0 h1  *)
	  /\ (v is_swap = 0 ==> 
	    ((pointOf h3 a) == (pointOf h0 a) /\ (pointOf h3 b) == (pointOf h0 b)))
	  /\ (v is_swap = pow2 platform_size - 1 ==> 
  	    ((pointOf h3 a) == (pointOf h0 b) /\ (pointOf h3 b) == (pointOf h0 a))) 
	)) []
let swap_conditional_lemma h0 h1 h2 h3 a b is_swap = 
  admit(); // TODO
  (* let set01 = !{getRef (get_x a), getRef (get_x b)} in *)
  (* let set02 = !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)} in *)
  (* let set12 = !{getRef (get_y a), getRef (get_y b)} in *)
  (* let set13 = !{getRef (get_y a), getRef (get_y b), getRef (get_z a), getRef (get_z b)} in *)
  (* let set23 = !{getRef (get_z a), getRef (get_z b)} in *)
  (* let set03 = !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b), getRef (get_z a), getRef (get_z b)} in *)
  (* cut (modifies set03 h0 h3);  *)
  (* FStar.TSet.lemma_equal_intro set03 (refs a +++ refs b); *)
  (* cut (modifies set02 h0 h2); *)
  (* cut (modifies set13 h1 h3); *)
  (* cut (not(FStar.TSet.mem (Ref (getRef (get_x a))) set13) *)
  (*      /\ not(FStar.TSet.mem (Ref (getRef (get_x b))) set13));  *)
  (* cut (not(FStar.TSet.mem (Ref (getRef (get_z a))) set02) *)
  (*      /\ not(FStar.TSet.mem (Ref (getRef (get_z b))) set02));  *)
  (* norm_lemma h1 h3 (get_x a) set13; *)
  (* norm_lemma h1 h3 (get_x b) set13;  *)
  (* norm_lemma h0 h1 (get_y a) set01; *)
  (* norm_lemma h0 h1 (get_y b) set01;  *)
  (* norm_lemma h2 h3 (get_y a) set23; *)
  (* norm_lemma h2 h3 (get_y b) set23;  *)
  (* norm_lemma h0 h2 (get_z a) set02; *)
  (* norm_lemma h0 h2 (get_z b) set02;  *)
  (* cut(v is_swap = 0 ==>  *)
  (* 	   (valueOf h3 (get_x a) = valueOf h0 (get_x a)  *)
  (* 	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y a) *)
  (* 	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z a) *)
  (* 	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x b) *)
  (* 	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y b) *)
  (* 	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z b))); *)
  (* cut(v is_swap = pow2 platform_size - 1 ==>  *)
  (* 	   (valueOf h3 (get_x a) = valueOf h0 (get_x b)  *)
  (* 	   /\ valueOf h3 (get_y a) = valueOf h0 (get_y b) *)
  (* 	   /\ valueOf h3 (get_z a) = valueOf h0 (get_z b) *)
  (* 	   /\ valueOf h3 (get_x b) = valueOf h0 (get_x a) *)
  (* 	   /\ valueOf h3 (get_y b) = valueOf h0 (get_y a) *)
  (* 	   /\ valueOf h3 (get_z b) = valueOf h0 (get_z a)));	  *)
  swap_is_on_curve h0 h3 a b is_swap;
  ()

#reset-options

val swap_conditional: 
  a:point -> b:point{distinct a b} -> 
  is_swap:u64{v is_swap = pow2 platform_size -1 \/ v is_swap = 0} ->
  ST unit
    (requires (fun h -> onCurve h a /\ onCurve h b))
    (ensures (fun h0 _ h1 -> (onCurve h0 a /\ onCurve h0 b) /\ (onCurve h1 a /\ onCurve h1 b)
      (* /\ modifies (refs a +++ refs b) h0 h1  *)
      /\ (v is_swap = 0 ==> 
	  ((pointOf h1 a) == (pointOf h0 a) /\ (pointOf h1 b) == (pointOf h0 b)))
      /\ (v is_swap = pow2 platform_size - 1 ==> 
  	  ((pointOf h1 a) == (pointOf h0 b) /\ (pointOf h1 b) == (pointOf h0 a))) ))
let swap_conditional a b is_swap =
  admit(); // TODO
  let h0 = HST.get() in
  swap_conditional_aux (get_x a) (get_x b) is_swap 0;
  let h1 = HST.get() in
  (* norm_lemma h0 h1 (get_y a) !{getRef (get_x a), getRef (get_x b)}; *)
  (* norm_lemma h0 h1 (get_y b) !{getRef (get_x a), getRef (get_x b)}; *)
  swap_conditional_aux (get_y a) (get_y b) is_swap 0;
  let h2 = HST.get() in
  (* let mods = (hide !{getRef (get_x a), getRef (get_x b), getRef (get_y a), getRef (get_y b)}) in *)
  (* cut(modifies (reveal mods) h0 h2);  *)
  (* cut(not(FStar.TSet.mem (Ref (getRef (get_z b))) (reveal mods)) /\ not(FStar.TSet.mem (Ref (getRef (get_z a))) (reveal mods)));  *)
  (* enorm_lemma h0 h2 (get_z a) mods; *)
  (* enorm_lemma h0 h2 (get_z b) mods; *)
  swap_conditional_aux (get_z a) (get_z b) is_swap 0;
  let h3 = HST.get() in
  swap_conditional_lemma h0 h1 h2 h3 a b is_swap

#reset-options

(* val bignum_live_lemma: h0:heap -> h1:heap -> b:bigint{live h0 b} -> mods:FStar.TSet.set aref -> *)
(*   Lemma (requires (modifies mods h0 h1 /\ not(FStar.TSet.mem (Ref (getRef b)) mods))) *)
(* 	(ensures (Bignum.live h1 b)) *)
(* let bignum_live_lemma h0 h1 b mods = () *)

#reset-options

(* val norm_lemma_2: h0:heap -> h1:heap -> a:bigint -> b:bigint -> Lemma  *)
(*   (requires (eqSub h0 a 0 h1 b 0 norm_length /\ norm h0 a)) *)
(*   (ensures (norm h1 b)) *)
(* let norm_lemma_2 h0 h1 a b =  *)
(*   admit(); // OK *)
(*   cut(forall (i:nat). {:pattern (get h1 b i)} 0+i = i);  *)
(*   cut (forall (i:nat). i < norm_length ==> v (get h1 b i) = v (get h0 a i)) *)

val copy:
  a:point -> b:point{distinct a b} -> 
  ST unit
    (requires (fun h -> live h a /\ onCurve h b))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (onCurve h1 a) /\ (onCurve h0 b) /\ (onCurve h1 b)
      /\ (pointOf h1 a = pointOf h0 b) /\ (pointOf h1 b = pointOf h0 b)
      (* /\ (modifies (refs a) h0 h1)  *)
      ))
let copy a b =
  admit(); // TODO
  let h0 = HST.get() in
  blit (get_x b) 0ul (get_x a) 0ul nlength; 
  let h1 = HST.get() in 
  (* norm_lemma h0 h1 (get_x b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_y b) (!{getRef (get_x a)});  *)
  (* norm_lemma h0 h1 (get_z b) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_y a) (!{getRef (get_x a)});  *)
  (* bignum_live_lemma h0 h1 (get_z a) (!{getRef (get_x a)});  *)
  blit (get_y b) 0ul (get_y a) 0ul nlength;
  let h2 = HST.get() in
  (* norm_lemma h1 h2 (get_x b) (!{getRef (get_y a)});  *)
  (* norm_lemma h1 h2 (get_y b) (!{getRef (get_y a)}); *)
  (* norm_lemma h1 h2 (get_z b) (!{getRef (get_y a)});  *)
  (* norm_lemma_2 h0 h1 (get_x b) (get_x a);  *)
  (* norm_lemma h1 h2 (get_x a) (!{getRef (get_y a)});  *)
  (* bignum_live_lemma h1 h2 (get_z a) (!{getRef (get_y a)}); *)
  blit (get_z b) 0ul (get_z a) 0ul nlength;
  let h3 = HST.get() in
  (* norm_lemma h2 h3 (get_x b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_y b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_z b) (!{getRef (get_z a)}); *)
  (* norm_lemma h2 h3 (get_x a) (!{getRef (get_z a)}); *)
  (* norm_lemma_2 h1 h2 (get_y b) (get_y a);  *)
  (* norm_lemma h2 h3 (get_y a) (!{getRef (get_z a)});  *)
  (* norm_lemma_2 h2 h3 (get_z b) (get_z a) *)
  ()
  
val swap:
  a:point -> b:point{distinct a b} ->
  ST unit
    (requires (fun h -> onCurve h a /\ live h b))
    (ensures (fun h0 _ h1 -> onCurve h0 a /\ live h0 b /\ onCurve h1 b /\ live h1 a 
      /\ (pointOf h0 a) == (pointOf h1 b)
      (* /\ modifies (FStar.TSet.union (refs a) (refs b)) h0 h1)) *)
      ))
let swap a b = 
  copy b a

val on_curve_lemma: h0:heap -> h1:heap -> a:point -> mods:Ghost.erased (TSet.set abuffer) -> Lemma
  (requires (onCurve h0 a 
    (* /\ modifies (reveal mods) h0 h1  *)
    /\ TSet.intersect (reveal mods) (refs a) = !{}))
  (ensures (onCurve h0 a /\ onCurve h1 a /\ pointOf h1 a = pointOf h0 a))
let on_curve_lemma h0 h1 a mods = 
  admit(); // OK
  (* cut(True /\ FStar.TSet.mem (Ref (getRef (get_x a))) (refs a)); *)
  (* cut(True /\ FStar.TSet.mem (Ref (getRef (get_y a))) (refs a)); *)
  (* cut(True /\ FStar.TSet.mem (Ref (getRef (get_z a))) (refs a)); *)
  (* norm_lemma h0 h1 (get_x a) (reveal mods); *)
  (* norm_lemma h0 h1 (get_y a) (reveal mods); *)
  (* norm_lemma h0 h1 (get_z a) (reveal mods);  *)
  eval_eq_lemma h0 h1 (get_x a) (get_x a) norm_length;
  eval_eq_lemma h0 h1 (get_y a) (get_y a) norm_length;
  eval_eq_lemma h0 h1 (get_z a) (get_z a) norm_length

(* val live_lemma: h0:heap -> h1:heap -> a:point -> mods:erased (FStar.TSet.set aref) -> Lemma *)
(*   (requires (live h0 a /\ modifies (reveal mods) h0 h1 /\ FStar.TSet.intersect (reveal mods) (refs a) = !{})) *)
(*   (ensures (live h1 a)) [] *)
(* let live_lemma h0 h1 a mods =  *)
(*   admit(); // OK *)
(*   cut(True /\ FStar.TSet.mem (Ref (getRef (get_x a))) (refs a)); *)
(*   cut(True /\ FStar.TSet.mem (Ref (getRef (get_y a))) (refs a)); *)
(*   cut(True /\ FStar.TSet.mem (Ref (getRef (get_z a))) (refs a)) *)

#reset-options

val distinct_lemma: a:point -> b:point{distinct a b} -> Lemma (requires (True)) (ensures (FStar.TSet.intersect (refs a) (refs b) = !{})) []
let distinct_lemma a b = 
  FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs a) (refs b)) !{}

#reset-options

val distinct_commutative: a:point -> b:point -> Lemma 
  (requires (True)) (ensures (distinct a b <==> distinct b a)) [SMTPat (distinct a b)]
let distinct_commutative a b = 
  admit(); // OK
  ()

val swap_both:
  a:point -> b:point{distinct a b} -> c:point{distinct c a /\ distinct c b} ->
  d:point{distinct d a /\ distinct d b /\ distinct d c} ->
  ST unit
    (requires (fun h -> onCurve h a /\ onCurve h b /\ live h c /\ live h d))
    (ensures (fun h0 _ h1 -> onCurve h0 a /\ onCurve h0 b /\ live h0 c /\ live h0 d 
      /\ onCurve h1 c /\ onCurve h1 d /\ live h1 a /\ live h1 b 
      /\ (pointOf h0 a) == (pointOf h1 c) /\ (pointOf h0 b) == (pointOf h1 d)
      (* /\ modifies ((refs a) +++ (refs b) +++ (refs c) +++ (refs d)) h0 h1)) *)
    ))
let swap_both a b c d =
  admit(); // OK
  let h0 = HST.get() in
  copy c a; 
  (* let h1 = HST.get() in *)
  (* let set01 = erefs c in  *)
  (* distinct_lemma c b;  *)
  (* distinct_lemma c d;  *)
  (* on_curve_lemma h0 h1 b set01;  *)
  (* live_lemma h0 h1 d set01;  *)
  copy d b;
  (* let h2 = HST.get() in *)
  (* distinct_lemma d c;  *)
  (* distinct_lemma d a; *)
  (* distinct_lemma d b; *)
  (* on_curve_lemma h1 h2 c (erefs d); *)
  (* live_lemma h1 h2 a (erefs d); *)
  (* live_lemma h1 h2 b (erefs d) *)
  ()
  
val copy2: p':point -> q':point{distinct p' q'} -> p:point{distinct p p' /\ distinct p q'} -> 
  q:point{distinct q p' /\ distinct q q'} -> STL unit 
    (requires (fun h -> live h p' /\ live h q' /\ onCurve h p /\ onCurve h q ))
    (ensures (fun h0 _ h1 -> onCurve h1 p' /\ onCurve h1 q' /\ onCurve h1 p /\ onCurve h1 q 
      /\ onCurve h0 p /\ onCurve h0 q
      (* /\ (modifies (FStar.TSet.union (refs p') (refs q')) h0 h1) *)
      /\ (pointOf h1 p' == pointOf h0 p)
      /\ (pointOf h1 q' == pointOf h0 q) ))
let copy2 p' q' p q =
  admit(); // OK
  let h0 = HST.get() in
  copy p' p; 
  let h1 = HST.get() in
  (* let set01 = (erefs p') in  *)
  (* distinct_lemma p' q;  *)
  (* distinct_lemma p' q';  *)
  (* on_curve_lemma h0 h1 q set01;  *)
  (* live_lemma h0 h1 q' set01;   *)
  copy q' q; 
  let h2 = HST.get() in
  (* distinct_lemma q' p';  *)
  (* distinct_lemma q' p; *)
  (* distinct_lemma q' q;  *)
  (* on_curve_lemma h1 h2 p' (erefs q');  *)
  (* on_curve_lemma h1 h2 p (erefs q');  *)
  (* on_curve_lemma h1 h2 q (erefs q') *)
  ()

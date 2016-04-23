module Curve.AddAndDouble

open FStar.Ghost
open FStar.Heap
open SInt.UInt64
open Bignum.Parameters
open SInt
open SBuffer
open Bignum.Bigint
open Bignum.Core
open Curve.Point


(*
val equation_1: felem -> felem -> GTot felem
let equation_1 x2 z2 = (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2))
val equation_2: felem -> felem -> GTot felem
let equation_2 x2 z2 = ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2))))
val equation_3: felem -> felem -> felem -> felem -> GTot felem
let equation_3 x2 z2 x3 z3 = ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
val equation_4: felem -> felem -> felem -> felem -> felem -> GTot felem
let equation_4 x2 z2 x3 z3 x1 = (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
*)

val double_and_add': two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point ->
  ST unit
    (requires (fun h ->
      (live h two_p) /\ (live h two_p_plus_q)
      /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
    ))
    (ensures (fun h0 _ h1 ->
      (live h0 two_p) /\ (live h0 two_p_plus_q)
      /\ (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
      /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q)
      /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q)
       /\ (modifies_buf (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       /\ (Bignum.Bigint.live h1 (get_x q) /\ Bignum.Bigint.live h1 (get_x p) /\ Bignum.Bigint.live h1 (get_z p) 
	 /\ Bignum.Bigint.live h1 (get_x p_plus_q) 
	 /\ Bignum.Bigint.live h1 (get_z p_plus_q) /\ Bignum.Bigint.live h1 (get_x two_p) 
	 /\ Bignum.Bigint.live h1 (get_z two_p) /\ Bignum.Bigint.live h1 (get_x two_p_plus_q) 
	 /\ Bignum.Bigint.live h1 (get_z two_p_plus_q))
(*
      /\ (
	  let x1 = valueOf h1 (get_x q) in 
	  let x2 = valueOf h1 (get_x p) in let z2 = valueOf h1 (get_z p) in
	  let x3 = valueOf h1 (get_x p_plus_q) in let z3 = valueOf h1 (get_z p_plus_q) in
	  (valueOf h1 (get_x two_p) = equation_1 x2 z2	 
//	       (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2))
	   /\ valueOf h1 (get_z two_p) = equation_2 x2 z2
//	       ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2))))
	   /\ valueOf h1 (get_x two_p_plus_q) = equation_3 x2 z2 x3 z3
//	       ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
	   /\ valueOf h1 (get_z two_p_plus_q) = equation_4 x2 z2 x3 z3 x1 
//	       (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
	))
	*)
    ))    
      
let double_and_add' two_p two_p_plus_q p p_plus_q q =
  admit();
  let h0 = ST.get() in
//  let qmqp = get_x q in
  let qmqp = q.x in
//  let x = get_x p in let z = get_z p in 
  let x = p.x in let z = p.z in 
//  let x2 = get_x two_p in let z2 = get_z two_p in
//  let xprime = get_x p_plus_q in let zprime = get_z p_plus_q in
  let x2 = two_p.x in let z2 = two_p.z in
  let xprime = p_plus_q.x in let zprime = p_plus_q.z in
  let origx = create #64 zero norm_length in
  let origxprime = create #64 zero norm_length in
  let zzz = create #64 zero (2*norm_length-1) in
  let xx = create #64 zero (2*norm_length-1) in
  let zz = create #64 zero (2*norm_length-1) in
  let xxprime = create #64 zero (2*norm_length-1) in
  let zzprime = create #64 zero (2*norm_length-1) in
  let xxxprime = create #64 zero (2*norm_length-1) in
  let zzzprime = create #64 zero (2*norm_length-1) in  
  blit x 0 origx 0 norm_length;
  fsum x z;
  fdifference z origx; 
  blit xprime 0 origxprime 0 norm_length;
  fsum xprime zprime;
  fdifference zprime origxprime;
  fmul xxprime xprime z;
  fmul zzprime x zprime;  
  blit xxprime 0 origxprime 0 norm_length;
  fsum xxprime zzprime;
  fdifference zzprime origxprime;
  fsquare xxxprime xxprime;
  fsquare zzzprime zzprime;
  fmul zzprime zzzprime qmqp;
//  blit xxxprime 0 (get_x two_p_plus_q) 0 norm_length;
//  blit zzprime 0 (get_z two_p_plus_q) 0 norm_length;
  blit xxxprime 0 (two_p_plus_q.x) 0 norm_length;
  blit zzprime 0 (two_p_plus_q.z) 0 norm_length;
  fsquare xx x;
  fsquare zz z;
  fmul x2 xx zz;
  fdifference zz xx; 
  erase zzz norm_length (norm_length-1) 0;
  fscalar zzz zz #12 (of_int a24');
  fsum zzz xx;
  fmul z2 zz zzz;
  ()

(* Stateful double and add function on concrete points *)
val double_and_add:
  two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point -> 
  ST unit
    (requires (fun h -> 
      (live h two_p) /\ (live h two_p_plus_q)
      /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
      ))
    (ensures (fun h0 _ h1 -> 
      (live h0 two_p) /\ (live h0 two_p_plus_q)
      /\ (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
      /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q)
      /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q)
      /\ (modifies_buf (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
//      /\ ((pointOf h1 two_p) == (Curve.add (pointOf h0 p) (pointOf h0 p)))
//      /\ ((pointOf h1 two_p_plus_q) == (Curve.add (pointOf h0 p) (pointOf h0 p_plus_q)))
    ))
let double_and_add two_p two_p_plus_q p p_plus_q q =
  admit();
  double_and_add' two_p two_p_plus_q p p_plus_q q;
  ()


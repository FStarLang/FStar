module Curve.AddAndDouble

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open Math.Lib
open Math.Field
open Curve.Parameters
open Curve.Bigint
open Curve.Bignum
open Curve.Point

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

let op_Plus_Plus_Plus a b = FStar.Set.union a b

val equation_1: felem -> felem -> GTot felem
let equation_1 x2 z2 = (((x2 ^+ z2) ^^ 2) ^* ((x2 ^- z2) ^^ 2))
val equation_2: felem -> felem -> GTot felem
let equation_2 x2 z2 = ((4 +* x2 ^* z2) ^* (((x2 ^- z2) ^^ 2) ^+ (a24' +* (4 +* x2 ^* z2))))
val equation_3: felem -> felem -> felem -> felem -> GTot felem
let equation_3 x2 z2 x3 z3 = ((((x3 ^- z3) ^* (x2^+z2)) ^+ ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)
val equation_4: felem -> felem -> felem -> felem -> felem -> GTot felem
let equation_4 x2 z2 x3 z3 x1 = (x1 ^* (((x3 ^- z3) ^* (x2^+z2)) ^- ((x3 ^+ z3) ^* (x2 ^- z2))) ^^ 2)

val double_and_add': two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point ->
  STL unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q 
      /\ onCurve h p /\ onCurve h p_plus_q /\ (onCurve h q) ))
    (ensures (fun h0 _ h1 -> live h0 two_p /\ live h0 two_p_plus_q
      /\ onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q
      /\ onCurve h1 two_p /\ onCurve h1 two_p_plus_q
      /\ live h1 p /\ live h1 p_plus_q /\ onCurve h1 q
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       /\ (Buffer.live h1 (get_x q) /\ Buffer.live h1 (get_x p) /\ Buffer.live h1 (get_z p) 
	 /\ Buffer.live h1 (get_x p_plus_q) 
	 /\ Buffer.live h1 (get_z p_plus_q) /\ Buffer.live h1 (get_x two_p) 
	 /\ Buffer.live h1 (get_z two_p) /\ Buffer.live h1 (get_x two_p_plus_q) 
	 /\ Buffer.live h1 (get_z two_p_plus_q))
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
    ))    
      
let double_and_add' two_p two_p_plus_q p p_plus_q q =
//  admit();
  let h0 = HST.get() in
  let qmqp = get_x q in
  let x = get_x p in let z = get_z p in 
  let xprime = get_x p_plus_q in let zprime = get_z p_plus_q in
  let x2 = get_x two_p in let z2 = get_z two_p in
  let origx = create 0uL nlength in
  let origxprime = create 0uL nlength in
  let zzz = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let xx = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let zz = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let xxprime = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let zzprime = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let xxxprime = create 0uL (U32.mul 2ul nlength -| 1ul) in
  let zzzprime = create 0uL (U32.mul 2ul nlength -| 1ul) in  
  blit x 0ul origx 0ul nlength;
  fsum x z;
  fdifference z origx; 
  blit xprime 0ul origxprime 0ul nlength;
  fsum xprime zprime;
  fdifference zprime origxprime;
  fmul xxprime xprime z;
  fmul zzprime x zprime;  
  blit xxprime 0ul origxprime 0ul nlength;
  fsum xxprime zzprime;
  fdifference zzprime origxprime;
  fsquare xxxprime xxprime;
  fsquare zzzprime zzprime;
  fmul zzprime zzzprime qmqp;
  blit xxxprime 0ul (get_x two_p_plus_q) 0ul nlength;
  blit zzprime 0ul (get_z two_p_plus_q) 0ul nlength;
  fsquare xx x;
  fsquare zz z;
  fmul x2 xx zz;
  fdifference zz xx; 
  Curve.Bignum.erase zzz nlength (nlength-|1ul) 0ul;
  fscalar zzz zz a24;
  fsum zzz xx;
  fmul z2 zz zzz

(* Stateful double and add function on concrete points *)
val double_and_add: two_p:point -> two_p_plus_q:point -> p:point -> p_plus_q:point -> q:point -> STL unit
    (requires (fun h -> live h two_p /\ live h two_p_plus_q 
      /\ onCurve h p /\ onCurve h p_plus_q /\ onCurve h q ))
    (ensures (fun h0 _ h1 -> live h0 two_p /\ live h0 two_p_plus_q
      /\ onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q
      /\ onCurve h1 two_p /\ onCurve h1 two_p_plus_q
      /\ live h1 p /\ live h1 p_plus_q /\ onCurve h1 q
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
      /\ (pointOf h1 two_p == Math.Curve.add (pointOf h0 p) (pointOf h0 p))
      /\ (pointOf h1 two_p_plus_q == Math.Curve.add (pointOf h0 p) (pointOf h0 p_plus_q))
    ))
let double_and_add two_p two_p_plus_q p p_plus_q q =
//  admit();
  double_and_add' two_p two_p_plus_q p p_plus_q q


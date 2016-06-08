module Curve.Ladder

open FStar.Ghost
open FStar.Heap
open SInt.UInt8
open SInt.UInt64
open Bignum.Parameters
open IntLib
open SInt
open SBuffer
open Bignum.Bigint
open Bignum.Core
open Curve.Point
open Curve.AddAndDouble

#set-options "--lax"

// q has to be an element of the curve
//type NtimesQ (n:erased nat) (q:celem) (h:heap) (p:point) (p':point) = 
//  OnCurve h p /\ OnCurve h p' /\ pointOf h p == (reveal n +* q) /\ pointOf h p' == ((reveal n+1) +* q)

// Will be specified using the bitwise operators' semantics
val mk_mask:
  x:uint8 -> Tot limb //(y:limb{bitsize (v y) platform_size /\ (x == zero_byte ==> v y = 0) /\ (x = one_byte ==> v y = pow2 platform_size - 1)})
let mk_mask x =
  let y = SInt.Cast.uint8_to_uint64 x in
  zero ^-% y

val small_step_exit: 
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
  p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
  p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
  q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
  n:erased nat -> byte:uint8 -> 
  scalar:erased nat{reveal n = reveal scalar * (pow2 8) + (v byte / (pow2 (8-8)))} -> 
  ST unit
     (requires (fun h -> 
       (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
//       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
       /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q) 
       /\ (modifies_buf (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + byte)
//       /\ (NtimesQ  (formula_0 scalar byte) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))
     
let small_step_exit pp ppq p pq q n byte scalar =
  let h0 = ST.get() in
  copy2 pp ppq p pq;
  let h1 = ST.get() in
  distinct_lemma q p; distinct_lemma q pq; distinct_lemma q pp; distinct_lemma q ppq;
//  let s = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in
//  cut(modifies (reveal s) h0 h1); 
//  admitP(True /\ FStar.Set.intersect (reveal s) (refs q) = !{});
//  on_curve_lemma h0 h1 q (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq);
  cut(onCurve h1 q); 
  ()
//  cut(NtimesQ (hide (reveal scalar * pow2 8 + (v byte / pow2 (8-8)))) (pointOf h0 q) h0 p pq); 
//  helper_lemma_1 scalar byte

abstract val nth_bit: byt:uint8 -> idx:nat{idx < 8} -> Tot (b:uint8{SInt.UInt8.logand (SInt.UInt8.shift_right byt (7-idx)) (SInt.UInt8.one) = b /\ (b == SInt.UInt8.zero \/ b = SInt.UInt8.one) } )
let nth_bit byte idx =
  let bit = SInt.UInt8.logand (SInt.UInt8.shift_right byte (7-idx)) (SInt.UInt8.one) in
//  and_one_lemma (SInt.UInt8.shift_right byte (7-idx));
  bit

(*
abstract val gdouble_and_add_lemma_1: q:Curve.celem -> n:erased nat -> m:erased nat -> 
  Lemma (requires (True)) 
	(ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) )) []
let gdouble_and_add_lemma_1 q n m = 
  Curve.smul_lemma q (reveal n) (reveal m)

val double_and_add_lemma_1: q:Curve.celem -> n:erased nat -> m:erased nat -> 
  Lemma (requires (True)) 
	(ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) ))
let double_and_add_lemma_1 q n m =
  coerce
    (requires (True))
    (ensures ((Curve.add (reveal n +* q) (reveal m +* q)) == ((reveal n + reveal m) +* q) ))
    (fun _ -> gdouble_and_add_lemma_1 q n m)
*)

val small_step_core_lemma_1: h0:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> Lemma
  (requires (modifies_buf (refs p +++ refs pq) h0 h1 /\ onCurve h0 q /\ live h0 pp /\ live h0 ppq))
  (ensures (live h1 pp /\ live h1 ppq /\ onCurve h1 q)) 
let small_step_core_lemma_1 h0 h1 pp ppq p pq q =
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs pp)) !{};  
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs ppq)) !{}; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs p +++ refs pq) (refs q)) !{}; 
  live_lemma h0 h1 pp (hide (refs p +++ refs pq)); 
  live_lemma h0 h1 ppq (hide ((refs p +++ refs pq)));
  on_curve_lemma h0 h1 q (hide (refs p +++ refs pq))

val small_step_core_lemma_2: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> Lemma
  (requires (modifies_buf (refs p +++ refs pq) h0 h /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h h2 /\ modifies_buf (refs pp +++ refs ppq) h2 h1))
  (ensures (modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1))
let small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q = 
  ()

(*
val small_step_core_lemma_3: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->    n:erased nat -> ctr:nat{ctr<8} -> byt:uint8 -> scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> Lemma
  (requires (
    let bit = (nth_bit byt ctr) in
    onCurve h0 p /\ onCurve h0 pq /\ onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q
    /\ onCurve h p /\ onCurve h pq /\ onCurve h2 pp /\ onCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) 
    ))
  (ensures (onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq
  )) []
let gsmall_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar =
  admit()
  let q0 = pointOf h0 q in
  let bit = nth_bit byt ctr in
  if (bit = zero_byte) then (
      Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 p) (pointOf h0 p);
      Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 p) (pointOf h0 pq)
      );
  if (bit = one_byte) then (
      Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 pq) (pointOf h0 pq);
      Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 pq) (pointOf h0 p)
      );
  cut (bit == zero_byte ==> 
      ((pointOf h1 pp) == (Curve.add (pointOf h0 p) (pointOf h0 p))
      /\ (pointOf h1 ppq) == (Curve.add (pointOf h0 p) (pointOf h0 pq))));
  cut (bit == one_byte ==> 
      ((pointOf h1 pp) == (Curve.add (pointOf h0 pq) (pointOf h0 p))
      /\ (pointOf h1 ppq) == (Curve.add (pointOf h0 pq) (pointOf h0 pq)))); 
  Curve.add_equality (pointOf h0 p) (pointOf h0 p) (smul (reveal n) q0) (smul (reveal n) q0); 
  Curve.add_equality (pointOf h0 p) (pointOf h0 pq) (smul (reveal n) q0) (smul (reveal n+1) q0);
  Curve.add_equality (pointOf h0 pq) (pointOf h0 pq) (smul (reveal n+1) q0) (smul (reveal n+1) q0);
  Curve.add_equality (pointOf h0 pq) (pointOf h0 p) (smul (reveal n+1) q0) (smul (reveal n) q0); 
  cut (bit == zero_byte ==> 
      ((pointOf h1 pp) == (Curve.add (smul (reveal n) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) == (Curve.add (smul (reveal n) q0) (smul (reveal n+1) q0)))); 
  cut (bit = one_byte ==> 
      ((pointOf h1 pp) == (Curve.add (smul (reveal n+1) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) == (Curve.add (smul (reveal n+1) q0) (smul (reveal n+1) q0)))); 
  double_and_add_lemma_1 q0 n n;
  double_and_add_lemma_1 q0 n (hide (reveal n+1));
  double_and_add_lemma_1 q0 (hide (reveal n+1)) n;
  double_and_add_lemma_1 q0 (hide (reveal n+1)) (hide (reveal n+1)); 
  lemma_8 (reveal n);
  cut (bit == zero_byte \/ bit == one_byte); 
  cut (bit == zero_byte ==> NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (bit == one_byte ==> NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (NtimesQ (hide (2*(reveal n)+v bit)) q0 h1 pp ppq);
  cut (True /\ nth_bit byt ctr = bit);
  cut (True /\ reveal (formula_1 n (nth_bit byt ctr)) = (2*reveal n+v bit));
  cut (NtimesQ (formula_1 n (nth_bit byt ctr)) q0 h1 pp ppq)

val small_step_core_lemma_3: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->    n:erased nat -> ctr:nat{ctr<8} -> byt:uint8 -> scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> Lemma
  (requires (
    let bit = (nth_bit byt ctr) in
    onCurve h0 p /\ onCurve h0 pq /\ onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q
    /\ onCurve h p /\ onCurve h pq /\ onCurve h2 pp /\ onCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) ))
  (ensures (onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq))
let small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar =
  coerce 
  (requires (
    let bit = (nth_bit byt ctr) in
    onCurve h0 p /\ onCurve h0 pq /\ onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q
    /\ onCurve h p /\ onCurve h pq /\ onCurve h2 pp /\ onCurve h2 ppq
    /\ (NtimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) )
    /\ ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)))
    /\ (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))) ))
  (ensures (onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q 
    /\ NtimesQ (formula_1 n (nth_bit byt ctr)) (pointOf h0 q) h1 pp ppq))
  (fun _ -> gsmall_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar)
*)

val small_step_core: 
   two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
   p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
   n:erased nat -> ctr:nat{ctr<8} -> byt:uint8 -> 
   scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v byt / (pow2 (8-ctr)))} -> 
   ST unit
     (requires (fun h -> 
       (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
//       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
       /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q) 
       /\ (modifies_buf (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + byte)
//       /\ (NtimesQ  (formula_2 (reveal n) (nth_bit byt ctr)) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))
let small_step_core pp ppq p pq q n ctr b scalar =
  admit();
  let h0 = ST.get() in
  distinct_commutative p pq;
  let bit = nth_bit b ctr in
  let mask = mk_mask bit in
  cut (v mask = IntLib.pow2 platform_size - 1 \/ v mask = 0); 
  swap_conditional p pq mask; 
  let h = ST.get() in
  small_step_core_lemma_1 h0 h pp ppq p pq q;
  double_and_add pp ppq p pq q; 
  let h2 = ST.get() in
  swap_conditional pp ppq mask; 
//  lemma_5 scalar b ctr;
  let h1 = ST.get() in
  cut ((live h2 p) /\ (live h2 pq) /\ (onCurve h2 q) /\ onCurve h1 pp /\ onCurve h1 ppq); 
//  let set2 = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in
//  let set21 = (erefs pp +*+ erefs ppq) in
//  assert(modifies_buf (reveal set21) h2 h1); 
  small_step_core_lemma_1 h2 h1 p pq pp ppq q; 
  small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q; 
//  cut ( bit == zero_byte ==> ((pointOf h p) == (pointOf h0 p) /\ (pointOf h pq) == (pointOf h0 pq)) );
//  cut ( bit == one_byte ==> ((pointOf h pq) == (pointOf h0 p) /\ (pointOf h p) == (pointOf h0 pq)) );
//  cut ( ((pointOf h2 pp) == (Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) == (Curve.add (pointOf h p) (pointOf h pq))) );
//  cut (bit == zero_byte ==> ((pointOf h1 pp) == (pointOf h2 pp) /\ (pointOf h1 ppq) == (pointOf h2 ppq)));
//  cut (bit == one_byte ==> ((pointOf h1 pp) == (pointOf h2 ppq) /\ (pointOf h1 ppq) == (pointOf h2 pp))); 
//  cut (NtimesQ n (pointOf h0 q) h0 p pq); 
//  small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr b scalar
  ()

val small_step_lemma_1 : h0:heap -> h1:heap -> h2:heap ->
   pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> 
   Lemma
     (requires (onCurve h0 q /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2))
     (ensures (onCurve h0 q /\ onCurve h1 q /\ onCurve h2 q
//	       /\ pointOf h2 q == pointOf h0 q /\ pointOf h1 q == pointOf h0 q
	       )) 
let small_step_lemma_1 h0 h1 h2 pp ppq p pq q =
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  on_curve_lemma h0 h2 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq));
  on_curve_lemma h0 h1 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step_lemma_2 : h0:heap -> h1:heap -> h2:heap -> h3:heap ->
   pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> 
   Lemma
     (requires (onCurve h0 q /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
       /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2
       /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h2 h3))
     (ensures (onCurve h3 q /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3)) 
let small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q =
  FStar.Set.lemma_equal_intro (FStar.Set.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  cut (modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3);
  on_curve_lemma h0 h3 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step :
   two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
   p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
   n:erased nat -> ctr:nat{ctr<=8} -> b:uint8 -> 
   scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (v b / (pow2 (8-ctr)))} -> 
   ST unit
     (requires (fun h -> 
       (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
//       /\ (NtimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
       /\ (live h1 two_p) /\ (live h1 two_p_plus_q) /\ (onCurve h1 p) /\ (onCurve h1 p_plus_q) /\ (onCurve h1 q) 
       /\ (modifies_buf (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1)
       // Formula_0 replaces (scalar * pow2 8 + b)
//       /\ (NtimesQ  (formula_0 scalar b) (pointOf h0 q) h1 p p_plus_q)
     ))
let rec small_step pp ppq p pq q n ctr b scalar =
  match 8 - ctr with
  | 0 -> 
//    lemma_9 ctr;
//    helper_lemma_1 n b; 
      ()
  | _ -> 
    let h0 = ST.get() in
//    lemma_0 ctr 8;
    small_step_core pp ppq p pq q n ctr b scalar; 
    let h1 = ST.get() in
    let bit = nth_bit b ctr in 
//    cut (NtimesQ (formula_1 n bit) (pointOf h0 q) h1 pp ppq); 
//    lemma_10 scalar ctr b;
    // Replaces a missing definition of the euclidian division 
    assume (2*reveal n+v bit = reveal scalar * (pow2 (ctr+1)) + (v b / pow2 (8 - (ctr+1))));    
    cut (ctr+1 <= 8 /\ True); 
    cut (onCurve h1 pp /\ onCurve h1 ppq /\ live h1 p /\ live h1 pq); 
    swap_both pp ppq p pq; 
    let h2 = ST.get() in 
//    assert (Curve.Equal (pointOf h2 p) (pointOf h1 pp) /\ Curve.Equal (pointOf h2 pq) (pointOf h1 ppq)); 
    small_step_lemma_1 h0 h1 h2 pp ppq p pq q;
//    formula_lemma n bit; 
//    assert(NtimesQ (eformula_2 n bit) (pointOf h2 q) h2 p pq); 
    let hidden = hide 0 in
    small_step pp ppq p pq q hidden (*(eformula_2 n bit)*) (ctr+1) b scalar; 
    let h3 = ST.get() in
    small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q;
    ()

// TODO
assume val formula_4: h:heap -> n:bytes{serialized h n} -> ctr:nat{ctr<=bytes_length} -> Tot (z:erased nat{reveal z = (valueOfBytes h n / pow2 ((bytes_length-ctr)*8))})

let distinct2 (n:bytes) (p:point) = (not(FStar.Set.mem (Buff n) (refs p)))

val serialized_lemma: h0:heap -> h1:heap -> n:bytes{serialized h0 n} -> mods:FStar.Set.set abuffer{FStar.Set.intersect mods (only n) = !{}} -> Lemma
  (requires (modifies_buf mods h0 h1))
  (ensures (serialized h1 n /\ valueOfBytes h1 n = valueOfBytes h0 n))
let serialized_lemma h0 h1 n mods =
  FStar.Set.lemma_equal_intro (only n) (FStar.Set.singleton (Buff n)); 
  cut (True /\ FStar.Set.mem (Buff n) (only n)); 
  cut( not(FStar.Set.mem (Buff n) mods) /\ True); 
  eq_lemma h0 h1 n mods; 
  assert(forall (i:nat). {:pattern (getValue h1 n i)} i < bytes_length ==> v (getValue h1 n i) = v (getValue h1 n i));  
  eval_eq_lemma h0 h1 n n bytes_length

val big_step_lemma_1: h0:heap -> h1:heap ->
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
  p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
  pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
  q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> ctr:nat{ctr<=bytes_length-1} -> b:uint8 ->
  Lemma
    (requires (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q) /\ serialized h0 n
//      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ onCurve h1 p /\ onCurve h1 pq /\ onCurve h1 q /\ live h1 pp /\ live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
//      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
    ))
    (ensures (
      (live h1 pp) /\ (live h1 ppq) /\ (onCurve h1 p) /\ (onCurve h1 pq) /\ (onCurve h1 q) /\ serialized h1 n
//      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
    )) 
let big_step_lemma_1 h0 h1 n pp ppq p pq q ctr b =
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (only n)) empty; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (refs q)) empty; 
  serialized_lemma h0 h1 n mods; 
  on_curve_lemma h0 h1 q (hide mods);
//  admitP(reveal (formula_4 h0 n (ctr+1)) = reveal (formula_0 (formula_4 h0 n ctr) b) /\ True)
  ()

val big_step_lemma_2: h0:heap -> h1:heap -> h2:heap ->
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
  p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
  pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
  q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->  ctr:nat{ctr<=bytes_length-1} -> b:uint8 -> Lemma
    (requires (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q) /\ serialized h0 n
//      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1
      /\ onCurve h1 p /\ onCurve h1 pq /\ onCurve h1 q /\ live h1 pp /\ live h1 ppq
      /\ b = getValue h0 n (bytes_length-1-ctr)
//      /\ NtimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
      /\ (live h1 pp) /\ (live h1 ppq) /\ (onCurve h1 p) /\ (onCurve h1 pq) /\ (onCurve h1 q)
      /\ (onCurve h2 p) /\ (onCurve h2 pq) /\ serialized h1 n
      /\ (modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2)
//      /\ (NtimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
//      /\ (NtimesQ (hide (valueOfBytes h1 n)) (pointOf h1 q) h2 p pq)
    ))
    (ensures (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q)
      /\ (onCurve h2 p) /\ (onCurve h2 pq) /\ serialized h0 n
      /\ (modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h2)
//      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
//      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h2 p pq)
    )) 
let big_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr byte = 
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (only n)) empty; 
  FStar.Set.lemma_equal_intro (FStar.Set.intersect mods (refs q)) empty; 
  serialized_lemma h0 h1 n mods; 
  on_curve_lemma h0 h1 q (hide mods)

val big_step:
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
  p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
  pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
  q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->  ctr:nat{ctr<=bytes_length} ->
  ST unit
    (requires (fun h -> 
      (live h pp) /\ (live h ppq) /\ (onCurve h p) /\ (onCurve h pq) /\ (onCurve h q) /\ serialized h n
//      /\ (NtimesQ (formula_4 h n ctr) (pointOf h q) h p pq)
    ))
    (ensures (fun h0 _ h1 ->
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q)
      /\ (onCurve h1 p) /\ (onCurve h1 pq) /\ serialized h0 n
      /\ (modifies_buf (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1)
//      /\ (NtimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
//      /\ (NtimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h1 p pq)
    ))
    
let rec big_step n pp ppq p pq q ctr = 
  let h0 = ST.get() in
  match bytes_length - ctr with
  | 0 -> 
    // Trivial
    assume (reveal (formula_4 h0 n bytes_length) = valueOfBytes h0 n);
    ()
  | _ -> 
    assume(bytes_length-1-ctr>=0 /\ bytes_length-ctr-1>=0);
    let byte = index n (bytes_length-1-ctr) in 
    let m = formula_4 h0 n ctr in
    // Replaces missing euclidian definitions in F*
    assume(reveal m = reveal m * pow2 0 + (v byte / pow2 (8-0)) /\ True); 
    small_step pp ppq p pq q m 0 byte m; 
    let h1 = ST.get() in 
    big_step_lemma_1 h0 h1 n pp ppq p pq q ctr byte;
    big_step n pp ppq p pq q (ctr+1); 
    let h2 = ST.get() in 
    big_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr byte;
    ()

val montgomery_ladder:
  res:point -> n:bytes{distinct2 n res} -> q:point{distinct2 n q /\ distinct res q} ->
  ST unit
    (requires (fun h -> 
      (live h res) /\ (serialized h n) /\ (onCurve h q)
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 res) /\ (serialized h0 n) /\ (onCurve h0 q) /\ (onCurve h1 res) 
      /\ (modifies_buf (refs res) h0 h1) 
//      /\ (pointOf h1 res = (valueOfBytes h0 n +* (pointOf h0 q)))
      ))
let montgomery_ladder res n q =
  // Build 'storage' empty but 'live' points
  let two_p_x = create #64 zero norm_length in
  let two_p_y = create #64 zero norm_length in
  let two_p_z = create #64 zero norm_length in
//  let two_p =  make two_p_x two_p_y two_p_z in
  let two_p =  {x = two_p_x; y = two_p_y; z = two_p_z} in
  cut(distinct two_p q); 
  let two_p_plus_q_x = create #64 zero norm_length in
  let two_p_plus_q_y = create #64 zero norm_length in
  let two_p_plus_q_z = create #64 zero norm_length in
//  let two_p_plus_q = make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z in
  let two_p_plus_q = {x = two_p_plus_q_x; y =  two_p_plus_q_y; z =  two_p_plus_q_z} in
  cut(distinct two_p_plus_q two_p /\ distinct two_p_plus_q q); 
  // Copy of the 'q' point
  let p_x = create #64 zero norm_length in
//  blit (get_x q) 0 p_x 0 norm_length;
  blit (q.x) 0 p_x 0 norm_length;
  let p_y = create #64 zero norm_length in
//  blit (get_y q) 0 p_y 0 norm_length;
  blit (q.y) 0 p_y 0 norm_length;
  let p_z = create #64 zero norm_length in
  blit (q.z) 0 p_z 0 norm_length;
//  blit (get_z q) 0 p_z 0 norm_length;
//  let p = make p_x p_y p_z in
  let p = {x = p_x; y = p_y; z = p_z} in
  // Point at infinity
  let inf_x = create #64 zero norm_length in
  upd inf_x 0 SInt.UInt64.one;
  let inf_y = create #64 zero norm_length in
  let inf_z = create #64 zero norm_length in
//  let inf = make inf_x inf_y inf_z in
  let inf = {x = inf_x; y = inf_y; z = inf_z} in
  // Perform scalar multiplication by the content of 'n'
  big_step n two_p two_p_plus_q inf p q 0;
  // Copy result to output
  copy res two_p;
  ()


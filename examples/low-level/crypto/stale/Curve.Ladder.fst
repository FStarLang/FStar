module Curve.Ladder

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.Buffer
open FStar.UInt64
open Math.Lib
(* open Math.Field *)
open Math.Curve
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

val op_Plus_Star: nat -> celem -> GTot celem
let op_Plus_Star (n:nat) (x:celem) = smul n x
let op_Plus_Plus_Plus a b = FStar.TSet.union a b

assume val op_Plus_Star_Plus: #a:Type -> x:erased (FStar.TSet.set a) -> y:erased (FStar.TSet.set a) ->
  Tot (z:erased (FStar.TSet.set a){reveal z = (reveal x +++ reveal y)})

// q has to be an element of the curve
type nTimesQ (n:erased nat) (q:celem) (h:heap) (p:point) (p':point) =
  onCurve h p /\ onCurve h p' /\ pointOf h p = (reveal n +* q) /\ pointOf h p' = ((reveal n+1) +* q)

val formula_0: scalar:erased nat -> byte:u8 -> GTot (erased nat)
let formula_0 scalar byte = 
  hide (reveal scalar * pow2 8 + U8.v byte)

val formula_1: n:FStar.Ghost.erased nat -> b:u8 -> GTot (z:erased nat{reveal z = 2*FStar.Ghost.reveal n+U8.v b})
let formula_1 n b = 
  hide (2*Ghost.reveal n+U8.v b)

assume val formula_2: n:nat -> b:u8 -> Tot (z:FStar.Ghost.erased nat{FStar.Ghost.reveal z = 2*n+U8.v b})

assume val eformula_2: n:erased nat -> b:u8 -> Tot (z:FStar.Ghost.erased nat{FStar.Ghost.reveal z = 2*reveal n+U8.v b})

// Will be specified using the bitwise operators' semantics
val mk_mask: x:u8 -> Tot (y:u64{v y < pow2 platform_size /\ (x = 0uy ==> v y = 0) /\ (x = 1uy ==> v y = pow2 platform_size - 1)})
let mk_mask x =
  admit(); // OK
  let y = Int.Cast.uint8_to_uint64 x in
  U64.sub_mod 0uL y

val small_step_exit: 
  two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
  p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
  p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
  q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
  n:erased nat -> byte:u8 -> 
  scalar:erased nat{reveal n = reveal scalar * (pow2 8) + (U8.v byte / (pow2 (8-8)))} -> 
  ST unit
     (requires (fun h -> 
       (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
       /\ (nTimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
       /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q) 
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       /\ (nTimesQ  (formula_0 scalar byte) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))     
let small_step_exit pp ppq p pq q n byte scalar =
  admit(); // OK
  let h0 = HST.get() in
  Curve.Point.copy2 pp ppq p pq;
  (* let h1 = HST.get() in *)
  (* distinct_lemma q p; distinct_lemma q pq; distinct_lemma q pp; distinct_lemma q ppq; *)
  (* let s = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in *)
  (* cut(modifies (reveal s) h0 h1); *)
  (* admitP(True /\ FStar.TSet.intersect (reveal s) (refs q) = !{}); *)
  (* on_curve_lemma h0 h1 q (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq); *)
  (* cut(onCurve h1 q);  *)
  (* cut(nTimesQ (hide (reveal scalar * pow2 8 + (U8.v byte / pow2 (8-8)))) (pointOf h0 q) h0 p pq);  *)
  ()
  (* helper_lemma_1 scalar byte *)

#reset-options

val nth_bit: byt:u8 -> idx:u32{w idx < 8} -> Tot (b:u8{U8.logand (U8.shift_right byt (7ul-|idx)) (1uy) = b /\ (b = 0uy \/ b = 1uy) })
let nth_bit byte idx =
  let bit = U8.logand (U8.shift_right byte (7ul-|idx)) (1uy) in
  (* and_one_lemma (U8.shift_right byte (7-idx)); *)
  bit

val double_and_add_lemma_1: q:Math.Curve.celem -> n:erased nat -> m:erased nat -> 
  Lemma (requires (True)) 
	(ensures ((Math.Curve.add (reveal n +* q) (reveal m +* q)) = ((reveal n + reveal m) +* q) )) []
let double_and_add_lemma_1 q n m = 
  Math.Curve.smul_lemma q (reveal n) (reveal m)


val small_step_core_lemma_1: h0:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> Lemma
  (requires ((* modifies (refs p +++ refs pq) h0 h1 /\  *)onCurve h0 q /\ live h0 pp /\ live h0 ppq))
  (ensures (live h1 pp /\ live h1 ppq /\ onCurve h1 q)) []
let small_step_core_lemma_1 h0 h1 pp ppq p pq q =
  admit(); // OK
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs p +++ refs pq) (refs pp)) !{};   *)
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs p +++ refs pq) (refs ppq)) !{};  *)
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs p +++ refs pq) (refs q)) !{};  *)
  (* live_lemma h0 h1 pp (hide (refs p +++ refs pq));  *)
  (* live_lemma h0 h1 ppq (hide ((refs p +++ refs pq))); *)
  (* on_curve_lemma h0 h1 q (hide (refs p +++ refs pq)) *)
  ()

(* val small_step_core_lemma_2: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> Lemma *)
(*   (requires ( *)
(*     modifies (refs p +++ refs pq) h0 h  *)
(*     /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h h2  *)
(*     /\ modifies (refs pp +++ refs ppq) h2 h1 *)
(*     )) *)
(*   (ensures (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1)) *)
(* let small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q = () *)

#reset-options

val small_step_core_lemma_3: h0:heap -> h:heap -> h2:heap -> h1:heap -> pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->    n:erased nat -> ctr:nat{ctr<8} -> byt:u8 -> scalar:erased nat{reveal n = reveal scalar * (pow2 ctr) + (U8.v byt / (pow2 (8-ctr)))} ->  Lemma
  (requires (
    let bit = (nth_bit byt (U32.uint_to_t ctr)) in
    onCurve h0 p /\ onCurve h0 pq /\ onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q
    /\ onCurve h p /\ onCurve h pq /\ onCurve h2 pp /\ onCurve h2 ppq
    /\ (nTimesQ n (pointOf h0 q) h0 p pq)
    /\ ( bit = 0uy ==> ((pointOf h p) = (pointOf h0 p) /\ (pointOf h pq) = (pointOf h0 pq)) )
    /\ ( bit = 1uy ==> ((pointOf h pq) = (pointOf h0 p) /\ (pointOf h p) = (pointOf h0 pq)) )
    /\ ( (pointOf h2 pp) = (Math.Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) = (Math.Curve.add (pointOf h p) (pointOf h pq)))
    /\ (bit = 0uy ==> ((pointOf h1 pp) = (pointOf h2 pp) /\ (pointOf h1 ppq) = (pointOf h2 ppq)))
    /\ (bit = 1uy ==> ((pointOf h1 pp) = (pointOf h2 ppq) /\ (pointOf h1 ppq) = (pointOf h2 pp))) ))
  (ensures (onCurve h1 pp /\ onCurve h1 ppq /\ onCurve h0 q 
    /\ nTimesQ (formula_1 n (nth_bit byt (U32.uint_to_t ctr))) (pointOf h0 q) h1 pp ppq))
let gsmall_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr byt scalar =
  admit(); // OK
  let q0 = pointOf h0 q in
  let bit = nth_bit byt ctr in
  if (bit = 0uy) then (
      Math.Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 p) (pointOf h0 p);
      Math.Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 p) (pointOf h0 pq)
      );
  if (bit = 1uy) then (
      Math.Curve.add_equality (pointOf h p) (pointOf h p) (pointOf h0 pq) (pointOf h0 pq);
      Math.Curve.add_equality (pointOf h p) (pointOf h pq) (pointOf h0 pq) (pointOf h0 p)
      );
  cut (bit = 0uy ==> 
      ((pointOf h1 pp) = (Math.Curve.add (pointOf h0 p) (pointOf h0 p))
      /\ (pointOf h1 ppq) = (Math.Curve.add (pointOf h0 p) (pointOf h0 pq))));
  cut (bit = 1uy ==> 
      ((pointOf h1 pp) = (Math.Curve.add (pointOf h0 pq) (pointOf h0 p))
      /\ (pointOf h1 ppq) = (Math.Curve.add (pointOf h0 pq) (pointOf h0 pq)))); 
  Math.Curve.add_equality (pointOf h0 p) (pointOf h0 p) (smul (reveal n) q0) (smul (reveal n) q0); 
  Math.Curve.add_equality (pointOf h0 p) (pointOf h0 pq) (smul (reveal n) q0) (smul (reveal n+1) q0);
  Math.Curve.add_equality (pointOf h0 pq) (pointOf h0 pq) (smul (reveal n+1) q0) (smul (reveal n+1) q0);
  Math.Curve.add_equality (pointOf h0 pq) (pointOf h0 p) (smul (reveal n+1) q0) (smul (reveal n) q0); 
  cut (bit = 0uy ==> 
      ((pointOf h1 pp) = (Math.Curve.add (smul (reveal n) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) = (Math.Curve.add (smul (reveal n) q0) (smul (reveal n+1) q0)))); 
  cut (bit = 1uy ==> 
      ((pointOf h1 pp) = (Math.Curve.add (smul (reveal n+1) q0) (smul (reveal n) q0))
      /\ (pointOf h1 ppq) = (Math.Curve.add (smul (reveal n+1) q0) (smul (reveal n+1) q0)))); 
  double_and_add_lemma_1 q0 n n;
  double_and_add_lemma_1 q0 n (hide (reveal n+1));
  double_and_add_lemma_1 q0 (hide (reveal n+1)) n;
  double_and_add_lemma_1 q0 (hide (reveal n+1)) (hide (reveal n+1)); 
  (* lemma_8 (reveal n); *)
  cut (bit = 0uy \/ bit = 1uy); 
  cut (bit = 0uy ==> nTimesQ (hide (2*(reveal n)+U8.v bit)) q0 h1 pp ppq);
  cut (bit = 1uy ==> nTimesQ (hide (2*(reveal n)+U8.v bit)) q0 h1 pp ppq);
  cut (nTimesQ (hide (2*(reveal n)+U8.v bit)) q0 h1 pp ppq);
  cut (True /\ nth_bit byt ctr = bit);
  cut (True /\ reveal (formula_1 n (nth_bit byt ctr)) = (2*reveal n+U8.v bit));
  cut (nTimesQ (formula_1 n (nth_bit byt ctr)) q0 h1 pp ppq)

val small_step_core: 
   two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
   p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
   n:erased nat -> ctr:u32{w ctr<8} -> byt:u8 -> scalar:erased nat{reveal n = reveal scalar * (pow2 (w ctr)) + (U8.v byt / (pow2 (8-w ctr)))} -> 
   ST unit
     (requires (fun h -> 
       (live h two_p) /\ (live h two_p_plus_q) /\ (onCurve h p) /\ (onCurve h p_plus_q) /\ (onCurve h q)
       /\ (nTimesQ n (pointOf h q) h p p_plus_q) 
     ))
     (ensures (fun h0 _ h1 ->
       (onCurve h0 p) /\ (onCurve h0 p_plus_q) /\ (onCurve h0 q)
       /\ (onCurve h1 two_p) /\ (onCurve h1 two_p_plus_q) /\ (live h1 p) /\ (live h1 p_plus_q) /\ (onCurve h1 q) 
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       // Formula_0 replaces (scalar * pow2 8 + byte)
       /\ (nTimesQ  (formula_2 (reveal n) (nth_bit byt ctr)) (pointOf h0 q) h1 two_p two_p_plus_q)
     ))
let small_step_core pp ppq p pq q n ctr b scalar =
  admit(); // TODO
  let h0 = HST.get() in
  distinct_commutative p pq;
  let bit = nth_bit b ctr in
  let mask = mk_mask bit in
  cut (v mask = pow2 platform_size - 1 \/ v mask = 0); 
  swap_conditional p pq mask; 
  let h = HST.get() in
  small_step_core_lemma_1 h0 h pp ppq p pq q;
  Curve.AddAndDouble.double_and_add pp ppq p pq q; 
  let h2 = HST.get() in
  swap_conditional pp ppq mask; 
  (* lemma_5 scalar b ctr; *)
  let h1 = HST.get() in
  assert ((live h2 p) /\ (live h2 pq) /\ (onCurve h2 q)); 
  assert (onCurve h1 pp /\ onCurve h1 ppq); 
  (* let set2 = (erefs pp +*+ erefs ppq +*+ erefs p +*+ erefs pq) in *)
  (* let set21 = (erefs pp +*+ erefs ppq) in *)
  (* assert(modifies (reveal set21) h2 h1);  *)
  small_step_core_lemma_1 h2 h1 p pq pp ppq q; 
  (* small_step_core_lemma_2 h0 h h2 h1 pp ppq p pq q;  *)
  (* cut ( bit = 0uy ==> ((pointOf h p) = (pointOf h0 p) /\ (pointOf h pq) = (pointOf h0 pq)) ); *)
  (* cut ( bit = 1uy ==> ((pointOf h pq) = (pointOf h0 p) /\ (pointOf h p) = (pointOf h0 pq)) ); *)
  (* cut ( ((pointOf h2 pp) = (Math.Curve.add (pointOf h p) (pointOf h p)) /\ (pointOf h2 ppq) = (Math.Curve.add (pointOf h p) (pointOf h pq))) ); *)
  (* cut (bit = 0uy ==> ((pointOf h1 pp) = (pointOf h2 pp) /\ (pointOf h1 ppq) = (pointOf h2 ppq))); *)
  (* cut (bit = 1uy ==> ((pointOf h1 pp) = (pointOf h2 ppq) /\ (pointOf h1 ppq) = (pointOf h2 pp)));  *)
  (* cut (nTimesQ n (pointOf h0 q) h0 p pq);  *)
  (* small_step_core_lemma_3 h0 h h2 h1 pp ppq p pq q n ctr b scalar *)
  ()


#reset-options

val small_step_lemma_1 : h0:heap -> h1:heap -> h2:heap ->
   pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> 
   Lemma
     (requires (onCurve h0 q 
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1 *)
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2 *)
       ))
     (ensures (onCurve h0 q /\ onCurve h1 q /\ onCurve h2 q
	       /\ pointOf h2 q = pointOf h0 q /\ pointOf h1 q = pointOf h0 q))
let small_step_lemma_1 h0 h1 h2 pp ppq p pq q =
  admit(); // OK
  FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  on_curve_lemma h0 h2 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq));
  on_curve_lemma h0 h1 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step_lemma_2 : h0:heap -> h1:heap -> h2:heap -> h3:heap ->
   pp:point -> ppq:point{distinct pp ppq} -> p:point{distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> 
   Lemma
     (requires (onCurve h0 q 
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1 *)
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2 *)
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h2 h3)) *)
       ))
     (ensures (onCurve h3 q 
       (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3 *)
       ))
let small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q =
  admit(); // OK
  FStar.TSet.lemma_equal_intro (FStar.TSet.intersect (refs pp +++ refs ppq +++ refs p +++ refs pq) (refs q)) !{}; 
  (* cut (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h3); *)
  on_curve_lemma h0 h3 q (hide (refs pp +++ refs ppq +++ refs p +++ refs pq))

val small_step: two_p:point -> two_p_plus_q:point{distinct two_p two_p_plus_q} -> 
   p:point{distinct p two_p /\ distinct p two_p_plus_q} -> 
   p_plus_q:point{distinct p_plus_q two_p /\ distinct p_plus_q two_p_plus_q /\ distinct p_plus_q p} -> 
   q:point{distinct q two_p /\ distinct q two_p_plus_q /\ distinct q p /\ distinct q p_plus_q} -> 
   n:erased nat -> ctr:u32{w ctr<=8} -> b:u8 -> 
   scalar:erased nat{reveal n = reveal scalar * (pow2 (w ctr)) + (U8.v b / (pow2 (8-w ctr)))} -> STL unit
     (requires (fun h -> live h two_p /\ live h two_p_plus_q /\ onCurve h p /\ onCurve h p_plus_q 
       /\ onCurve h q /\ nTimesQ n (pointOf h q) h p p_plus_q ))
     (ensures (fun h0 _ h1 -> onCurve h0 p /\ onCurve h0 p_plus_q /\ onCurve h0 q
       /\ (live h1 two_p) /\ (live h1 two_p_plus_q) /\ (onCurve h1 p) /\ (onCurve h1 p_plus_q) /\ (onCurve h1 q) 
       (* /\ (modifies (refs two_p +++ refs two_p_plus_q +++ refs p +++ refs p_plus_q) h0 h1) *)
       // Formula_0 replaces (scalar * pow2 8 + b)
       /\ (nTimesQ  (formula_0 scalar b) (pointOf h0 q) h1 p p_plus_q)
     ))
let rec small_step pp ppq p pq q n ctr b scalar =
  admit(); // OK
  if U32.eq 8ul ctr then begin
    (* lemma_9 ctr; *)
    (* helper_lemma_1 n b;  *)
    ()
  end
  else begin
    let h0 = HST.get() in
    (* lemma_0 ctr 8; *)
    small_step_core pp ppq p pq q n ctr b scalar; 
    let h1 = HST.get() in
    let bit = nth_bit b ctr in 
    cut (nTimesQ (formula_1 n bit) (pointOf h0 q) h1 pp ppq); 
    (* lemma_10 scalar ctr b; *)
    // Replaces a missing definition of the euclidean division 
    admitP (True /\ 2*reveal n+U8.v bit = reveal scalar * (pow2 (w ctr+1)) + (U8.v b / pow2 (8 - (w ctr+1))));    
    cut (w ctr+1 <= 8 /\ True); 
    assert (onCurve h1 pp /\ onCurve h1 ppq /\ live h1 p /\ live h1 pq); 
    swap_both pp ppq p pq; 
    let h2 = HST.get() in 
    assert (Math.Curve.equal (pointOf h2 p) (pointOf h1 pp) /\ Math.Curve.equal (pointOf h2 pq) (pointOf h1 ppq)); 
    small_step_lemma_1 h0 h1 h2 pp ppq p pq q;
    (* formula_lemma n bit;  *)
    assert(nTimesQ (eformula_2 n bit) (pointOf h2 q) h2 p pq); 
    small_step pp ppq p pq q (eformula_2 n bit) (ctr+|1ul) b scalar; 
    let h3 = HST.get() in
    small_step_lemma_2 h0 h1 h2 h3 pp ppq p pq q
  end
  
assume  val formula_4: h:heap -> n:bytes -> ctr:nat{ctr<=bytes_length} -> Tot (z:erased nat{reveal z = (valueOfBytes h n / pow2 ((bytes_length-ctr)*8))})

#reset-options

type distinct2 (n:bytes) (p:point) = (* b2t(not(FStar.TSet.mem (Ref (getRef n)) (refs p))) *) True

#reset-options

(* val serialized_lemma: h0:heap -> h1:heap -> n:bytes -> mods:FStar.TSet.set aref{FStar.TSet.intersect mods !{getRef n} = !{}} -> Lemma *)
(*   (requires (modifies mods h0 h1)) *)
(*   (ensures (valueOfBytes h1 n = valueOfBytes h0 n)) *)
(* let serialized_lemma h0 h1 n mods = *)
(*   admit(); // OK *)
(*   FStar.TSet.lemma_equal_intro !{getRef n} (FStar.TSet.singleton (Ref (getRef n)));  *)
(*   cut (True /\ FStar.TSet.mem (Ref (getRef n)) !{getRef n});  *)
(*   cut( not(FStar.TSet.mem (Ref (getRef n)) mods) /\ True);  *)
(*   no_upd_lemma h0 h1 n mods;  *)
(*   assert(forall (i:nat). {:pattern (get h1 n i)} i < bytes_length ==> v (get h1 n i) = v (get h1 n i));   *)
(*   Eval.eval_eq_lemma h0 h1 n n bytes_length *)
  
(* #reset-options *)

val big_step_lemma_1: h0:heap -> h1:heap ->
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
   p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} -> ctr:nat{ctr<=bytes_length-1} -> b:u8 ->
  Lemma
    (requires (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q)
      /\ (nTimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1 *)
      /\ onCurve h1 p /\ onCurve h1 pq /\ onCurve h1 q /\ live h1 pp /\ live h1 ppq
      /\ b = get h0 n (bytes_length-1-ctr)
      /\ nTimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
    ))
    (ensures (
      (live h1 pp) /\ (live h1 ppq) /\ (onCurve h1 p) /\ (onCurve h1 pq) /\ (onCurve h1 q)
      /\ (nTimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
    ))
let gbig_step_lemma_1 h0 h1 n pp ppq p pq q ctr b =
  admit(); // TODO
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect mods !{getRef n}) !{};  *)
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect mods (refs q)) !{};  *)
  (* serialized_lemma h0 h1 n mods;  *)
  on_curve_lemma h0 h1 q (hide mods);
  admitP(reveal (formula_4 h0 n (ctr+1)) = reveal (formula_0 (formula_4 h0 n ctr) b) /\ True)

val big_step_lemma_2: h0:heap -> h1:heap -> h2:heap ->
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
   p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->  ctr:nat{ctr<=bytes_length-1} -> b:u8 -> Lemma
    (requires (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q)
      /\ (nTimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      (* /\ modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1 *)
      /\ onCurve h1 p /\ onCurve h1 pq /\ onCurve h1 q /\ live h1 pp /\ live h1 ppq
      /\ b = get h0 n (bytes_length-1-ctr)
      /\ nTimesQ (formula_0 (formula_4 h0 n ctr) b) (pointOf h0 q) h1 p pq
      /\ (live h1 pp) /\ (live h1 ppq) /\ (onCurve h1 p) /\ (onCurve h1 pq) /\ (onCurve h1 q)
      /\ (onCurve h2 p) /\ (onCurve h2 pq)
      (* /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h1 h2) *)
      /\ (nTimesQ (formula_4 h1 n (ctr+1)) (pointOf h1 q) h1 p pq)
      /\ (nTimesQ (hide (valueOfBytes h1 n)) (pointOf h1 q) h2 p pq)
    ))
    (ensures (
      (live h0 pp) /\ (live h0 ppq) /\ (onCurve h0 p) /\ (onCurve h0 pq) /\ (onCurve h0 q)
      /\ (onCurve h2 p) /\ (onCurve h2 pq)
      (* /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h2) *)
      /\ (nTimesQ (formula_4 h0 n ctr) (pointOf h0 q) h0 p pq)
      /\ (nTimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h2 p pq)
    )) []
let big_step_lemma_2 h0 h1 h2 n pp ppq p pq q ctr byte = 
  admit(); // TODO
  let mods = (refs pp +++ refs ppq +++ refs p +++ refs pq) in
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect mods !{getRef n}) !{};  *)
  (* FStar.TSet.lemma_equal_intro (FStar.TSet.intersect mods (refs q)) !{};  *)
  (* serialized_lemma h0 h1 n mods;  *)
  on_curve_lemma h0 h1 q (hide mods)
    
#reset-options

val big_step:
  n:bytes -> pp:point{distinct2 n pp} -> ppq:point{distinct2 n ppq /\ distinct pp ppq} -> 
   p:point{distinct2 n p /\ distinct p pp /\ distinct p ppq} -> 
   pq:point{distinct2 n pq /\ distinct pq pp /\ distinct pq ppq /\ distinct pq p} -> 
   q:point{distinct2 n q /\ distinct q pp /\ distinct q ppq /\ distinct q p /\ distinct q pq} ->  
   ctr:u32{w ctr<=bytes_length} -> STL unit
    (requires (fun h -> live h pp /\ live h ppq /\ onCurve h p /\ onCurve h pq /\ onCurve h q
      /\ nTimesQ (formula_4 h n (w ctr)) (pointOf h q) h p pq ))
    (ensures (fun h0 _ h1 -> live h0 pp /\ live h0 ppq /\ onCurve h0 p /\ onCurve h0 pq /\ onCurve h0 q
      /\ onCurve h1 p /\ onCurve h1 pq
      (* /\ (modifies (refs pp +++ refs ppq +++ refs p +++ refs pq) h0 h1) *)
      /\ nTimesQ (formula_4 h0 n (w ctr)) (pointOf h0 q) h0 p pq
      /\ nTimesQ (hide (valueOfBytes h0 n)) (pointOf h0 q) h1 p pq  ))    
let rec big_step n pp ppq p pq q ctr = 
  admit(); // OK modulo
  let h0 = HST.get() in
  if U32.eq blength ctr then assume(reveal (formula_4 h0 n bytes_length) = valueOfBytes h0 n)
  else begin
    assume(bytes_length-1-w ctr>=0 /\ bytes_length-w ctr-1>=0);
    let byte = index n (blength-|1ul-|ctr) in 
    let m = formula_4 h0 n (w ctr) in
    // Replaces missing euclidean definitions in F*
    admitP(reveal m = reveal m * pow2 0 + (U8.v byte / pow2 (8-0)) /\ True); 
    small_step pp ppq p pq q m 0ul byte m; 
    let h1 = HST.get() in 
    (* big_step_lemma_1 h0 h1 n pp ppq p pq q ctr byte; *)
    big_step n pp ppq p pq q (ctr+|1ul); 
    let h2 = HST.get() in 
    big_step_lemma_2 h0 h1 h2 n pp ppq p pq q (w ctr) byte
  end
  
val montgomery_ladder:
  res:point -> n:bytes{distinct2 n res} -> q:point{distinct2 n q /\ distinct res q} ->
  ST unit
    (requires (fun h -> live h res /\ onCurve h q ))
    (ensures (fun h0 _ h1 -> live h0 res /\ onCurve h0 q /\ onCurve h1 res
      (* /\ (modifies (refs res) h0 h1)  *)
      /\ (pointOf h1 res = (valueOfBytes h0 n +* (pointOf h0 q)))  ))
let montgomery_ladder res n q =
  admit(); // TODO
  // Build 'storage' empty but 'live' points
  let two_p_x = create 0uL (nlength+|1ul) in
  let two_p_y = create 0uL nlength in
  let two_p_z = create 0uL (nlength+|1ul) in
  let two_p =  make two_p_x two_p_y two_p_z in
  cut(distinct two_p q); 
  let two_p_plus_q_x = create 0uL (nlength+|1ul) in
  let two_p_plus_q_y = create 0uL nlength in
  let two_p_plus_q_z = create 0uL (nlength+|1ul) in
  let two_p_plus_q = make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z in
  cut(distinct two_p_plus_q two_p /\ distinct two_p_plus_q q); 
  // Copy of the 'q' point
  let p_x = create 0uL nlength in
  blit (get_x q) 0ul p_x 0ul nlength;
  let p_y = create 0uL nlength in
  blit (get_y q) 0ul p_y 0ul nlength;
  let p_z = create 0uL nlength in
  blit (get_z q) 0ul p_z 0ul nlength;
  let p = make p_x p_y p_z in
  // Point at infinity
  let inf_x = create 0uL (nlength+|1ul) in
  upd inf_x 0ul 1uL;
  let inf_y = create 0uL nlength in
  let inf_z = create 0uL (nlength+|1ul) in
  let inf = make inf_x inf_y inf_z in
  // Perform scalar multiplication by the content of 'n'
  big_step n two_p two_p_plus_q inf p q 0ul;
  // Copy result to output
  copy res two_p

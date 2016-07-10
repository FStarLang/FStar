module Curve.Modulo

(* 64/128 bits *)

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt128
open FStar.Buffer
open Math.Lib
open Math.Field
open Curve.Parameters
open Curve.Bigint

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module HS = FStar.HyperStack

let w: u32 -> Tot int = U32.v
let vv: u64 -> Tot int = U64.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let heap = HS.mem

let op_Bar_Amp x y = U128.logand x y
let op_Bar_Greater_Greater x y = U128.shift_right x y
let op_Bar_Less_Less x y = U128.shift_left x y
let op_Bar_Plus x y = U128.add x y
let op_Bar_Star x y = U128.mul x y

// Because the details from parameters.fst are not imported although needed for proofs here
(* assume Templ_lemma: forall (i:nat). {:pattern (templ i)} templ i = 51 *)
(* assume Platform_size_lemma: platform_size = 64 *)
(* assume PrimeValue: reveal prime = (pow2 255 - 19) *)
(* assume NormLengthValue: norm_length = 5 *)
(* assume Ndiff: ndiff = 53 *)
(* assume Ndiff': ndiff' = 51 *)

assume val prime_modulo_lemma: unit -> Lemma (pow2 255 % (reveal prime) = 19)

assume val modulo_lemma: a:nat -> b:pos -> 
  Lemma
    (requires (a < b))
    (ensures (a % b = a))
    [SMTPat (a % b)]

val pow2_4_lemma: unit -> 
  Lemma
    (requires (True))
    (ensures (pow2 4 = 16))
    [SMTPat (pow2 4)]
let pow2_4_lemma () = 
  admit(); // OK
  ()

val pow2_5_lemma: unit -> 
  Lemma
    (requires (True))
    (ensures (pow2 5 = 32))
    [SMTPat (pow2 5)]
let pow2_5_lemma () = 
  admit(); // OK
  ()

let satisfies_modulo_constraints h b = // TODO
  length b >= 2*norm_length-1
  && maxValue_wide h b (length b) * 20 < pow2 (platform_wide - 1)

type satisfiesModuloConstraints (h:heap) (b:bigint_wide) = live h b /\ satisfies_modulo_constraints h b

val times_19: x:u128{19 * v x < pow2 platform_wide} -> Tot (y:u128{v y = 19 * v x})
let times_19 x =
  let y = x |<< 4ul in
  let z = x |<< 1ul in
  x |+ y |+ z

abstract type reducible (h:heap) (b:bigint_wide) (ctr:nat) =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (getValue h b (i+norm_length))}
      (i >= ctr /\ i < norm_length-1) ==> v (getValue h b i) + 19 * v (getValue h b (i+norm_length)) < pow2 platform_wide)

abstract type reducible' (h:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length-1}) =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (getValue h b (i+norm_length))}
      i <= ctr ==> v (getValue h b i) + 19 * v (getValue h b (i+norm_length)) < pow2 platform_wide)

abstract type times19 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
       (i >= ctr /\ i < norm_length - 1) ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * (v (getValue h0 b (i+norm_length))))

abstract type times19' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length - 1}) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
       i <= ctr ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * (v (getValue h0 b (i+norm_length))))

abstract type untouched (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
      ((i < ctr \/ i >= norm_length-1) /\ i < 2*norm_length-1) ==> v (getValue h0 b i) = v (getValue h1 b i))

abstract type untouched' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) = 
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==> 
      v (getValue h0 b i) = v (getValue h1 b i))

#reset-options

(* val helper_lemma_00: ctr:nat{ctr >= 2} -> Lemma *)
(*   (requires (True)) *)
(*   (ensures (bitweight templ (ctr+norm_length-2) = bitweight templ (ctr-2) + bitweight templ *)

(* val lemma_helper_0: ctr:nat{ctr >= 2} -> Lemma *)
(*   (requires (True)) *)
(*   (ensures (pow2 (bitweight templ (ctr+norm_length-2)) = pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length))) *)
(* let lemma_helper_0 ctr =  *)
(*   bitweight_definition templ (ctr+norm_length *)

val lemma_helper_00: ctr:nat{ctr>=2} -> Lemma (ctr-1+norm_length = ctr+norm_length-1 
					   /\ ctr+norm_length-1 = (ctr-1) + norm_length
					   /\ (ctr+norm_length-1)-1=ctr+norm_length-2)
let lemma_helper_00 ctr = ()					   

val lemma_helper_01: ctr:nat{ctr>=2} -> Lemma 
  (bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 51)
let lemma_helper_01 ctr = bitweight_def templ (ctr+norm_length-2)

val lemma_helper_02: a:nat -> b:nat -> Lemma (bitweight templ (a+b) = bitweight templ a + bitweight templ b)
let rec lemma_helper_02 a b = match a with | 0 -> () | _ -> lemma_helper_02 (a-1) b

val lemma_helper_03: ctr:nat{ctr>=2} -> Lemma (pow2 51 * pow2 (bitweight templ (ctr-2)) = pow2 (bitweight templ (ctr-1)))
let lemma_helper_03 ctr = 
  bitweight_def templ 1;
  lemma_helper_02 1 (ctr-2); 
  Math.Lemmas.pow2_exp_1 51 (bitweight templ (ctr-2))

val lemma_helper_04: ctr:nat{ctr>=2} -> Lemma
  (requires (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * pow2 (bitweight templ (ctr+norm_length-2))))
  (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let lemma_helper_04 ctr =
  admit(); // OK
  lemma_helper_02 (ctr-2) norm_length;
  Math.Lemmas.pow2_exp_1 (bitweight templ (ctr-2)) (bitweight templ norm_length); 
  Math.Axioms.paren_mul_right (pow2 51) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
  lemma_helper_03 ctr

val pow2_bitweight_lemma_1: ctr:pos -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let rec pow2_bitweight_lemma_1 ctr =
  admit(); // OK
  match ctr with
  | 1 -> ()
  | _ -> 
    lemma_helper_00 ctr;
    pow2_bitweight_lemma_1 (ctr-1);
    lemma_helper_01 ctr;
    bitweight_def templ (ctr+norm_length-2);
    Math.Lemmas.pow2_exp_1 51 (bitweight templ (ctr+norm_length-2)); 
    lemma_helper_04 ctr

#reset-options

val bitweight_norm_length_lemma: unit ->
  Lemma (requires (True))
	(ensures (bitweight templ norm_length = 255))
	[SMTPat (bitweight templ norm_length)]
let bitweight_norm_length_lemma () = 
  admit(); // OK
  bitweight_def templ (norm_length-1);
  bitweight_def templ (norm_length-2);
  bitweight_def templ (norm_length-3);
  bitweight_def templ (norm_length-4);
  bitweight_def templ (norm_length-5)
  
#reset-options

val lemma_helper_10: h0:heap -> b:bigint_wide{live h0 b (* /\ length b >= 2*norm_length-1 *)} -> ctr:pos{length b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma
  ( ctr+norm_length = norm_length+ctr 
    /\ (norm_length+1+ctr)-1 = norm_length + ctr 
    /\ norm_length+ctr = (ctr+1)+norm_length-1 
    /\ eval_wide h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (ctr+norm_length))
let lemma_helper_10 h0 b ctr = 
  admit(); // OK
  eval_wide_def h0 b (norm_length+1+ctr)

val lemma_helper_12: a:int -> b:int -> c:int -> Lemma (a * b * c = b * (a * c))
let lemma_helper_12 a b c = ()

val lemma_helper_11: h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b /\ (* length b >= 2 * norm_length - 1 /\ *) length b = length b} -> ctr:pos{length b >= ctr + norm_length + 1 /\ctr < norm_length-1} -> prime:pos -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))} (i < length b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i))
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
      /\ eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime
      /\ eval_wide h0 b (norm_length+ctr) - eval_wide h0 b (ctr+1) = eval_wide h1 b (norm_length+ctr) - eval_wide h1 b (ctr+1)
      /\ eval_wide h0 b ctr = eval_wide h1 b ctr))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % (prime) = eval_wide h1 b (norm_length+ctr) % (prime)))
let lemma_helper_11 h0 h1 b ctr prime = 
  admit(); // OK
  eval_wide_def h0 b (norm_length+1+ctr);
  Math.Axioms.distributivity_add_right (pow2 (bitweight templ ctr)) (v (getValue h0 b ctr)) (19 * v (getValue h0 b (norm_length+ctr)));
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime); 
  lemma_helper_12 19 (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  cut (True /\ 19 * v (getValue h0 b (ctr+norm_length)) = v (getValue h1 b ctr) - v (getValue h0 b ctr));
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * (v (getValue h1 b ctr) - v (getValue h0 b ctr)) + eval_wide h0 b (norm_length+ctr)) % prime); 
  Math.Axioms.distributivity_sub_right (pow2 (bitweight templ ctr)) (v (getValue h1 b ctr)) (v (getValue h0 b ctr));
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (getValue h1 b ctr) - pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval_wide h0 b (norm_length+ctr)) % prime); 
  eval_wide_def h0 b (ctr+1);
  eval_wide_def h1 b (ctr+1);
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (getValue h1 b ctr) - pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval_wide h1 b (norm_length+ctr) - eval_wide h1 b (ctr+1) + eval_wide h0 b (ctr+1)) % prime);
  ()

val freduce_degree_lemma_2:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ length b >= 2 * norm_length - 1 *) /\ length b = length b} -> ctr:pos{length b >= ctr + norm_length + 1 /\ ctr < norm_length-1} -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < length b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % (reveal prime) = eval_wide h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma_2 h0 h1 b ctr = 
  admit(); // OK
  let prime = reveal prime in
  eval_wide_def h0 b (norm_length+1+ctr); 
  (* cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); *)
  (* cut (True /\ eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (getValue h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length));  *)
  lemma_helper_10 h0 b ctr;
  pow2_bitweight_lemma_1 (ctr+1); 
  lemma_helper_02 norm_length ctr;
  bitweight_norm_length_lemma (); 
  Math.Lemmas.pow2_exp_1 255 (bitweight templ ctr);
  (* cut(True /\ pow2 (bitweight templ (norm_length+ctr)) = pow2 255 * pow2 (bitweight templ ctr));  *)
  Math.Axioms.paren_mul_left (pow2 255) (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  Math.Axioms.paren_mul_right (pow2 255) (pow2 (bitweight templ ctr)) (v (getValue h0 b (norm_length+ctr))); 
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) = (pow2 255 * pow2 (bitweight templ ctr)) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr));
  (* ModuloLemmas.helper_lemma_5 (pow2 255) (pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr))) (eval_wide h0 b (norm_length+ctr)) prime;  *)
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = ((pow2 255 % prime) * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime); 
  prime_modulo_lemma (); 
  cut (True /\ eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (getValue h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime); 
  (* eval_eq_lemma h0 h1 b b ctr;  *)
  eval_wide_def h0 b (ctr+1);
  eval_wide_def h1 b (ctr+1);
  (* cut (True /\ eval_wide h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (getValue h0 b ctr) + eval_wide h0 b ctr); *)
  (* cut (True /\ eval_wide h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (getValue h0 b ctr) + 19 * v (getValue h0 b (norm_length+ctr))) + eval_wide h0 b ctr);  *)
  Math.Axioms.distributivity_add_right (pow2 (bitweight templ ctr)) (v (getValue h0 b ctr)) (19 * v (getValue h0 b (norm_length+ctr))); 
  (* eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr); *)
  lemma_helper_11 h0 h1 b ctr prime

#reset-options

val freduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ length b >= 2 * norm_length - 1 *) /\ length b = length b} -> ctr:nat{length b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (getValue h1 b i))}
	(i < length b /\ i <> ctr) ==> v (getValue h1 b i) = v (getValue h0 b i)) 
      /\ v (getValue h1 b ctr) = v (getValue h0 b ctr) + 19 * v (getValue h0 b (ctr+norm_length))
    ))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % (reveal prime) = eval_wide h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma h0 h1 b ctr =
  admit(); // OK
  let prime = reveal prime in
  if ctr = 0 then (
    eval_wide_def h0 b (norm_length+1);
    assert(eval_wide h0 b (norm_length+1) = pow2 (bitweight templ norm_length) * v (getValue h0 b norm_length) + eval_wide h0 b norm_length); 
    assert(eval_wide h0 b (norm_length+1) = pow2 255 * v (getValue h0 b norm_length) + eval_wide h0 b norm_length);
    (* ModuloLemmas.helper_lemma_5 (pow2 255) (v (getValue h0 b norm_length)) (eval_wide h0 b norm_length) prime; *)
    assert(eval_wide h0 b (norm_length+1) % prime = ((pow2 255 % prime) * v (getValue h0 b norm_length) + eval_wide h0 b norm_length) % prime); 
    prime_modulo_lemma ();
    assert(eval_wide h0 b (norm_length+1) % prime = (19 * v (getValue h0 b norm_length) + eval_wide h0 b norm_length) % prime);
    cut(eval_wide h0 b 1 = v (getValue h0 b 0) /\ eval_wide h1 b 1 = v (getValue h0 b 0) + 19 * v (getValue h0 b norm_length)); 
    (* eval_partial_eq_lemma h0 h1 b b 1 norm_length; *)
    cut(True /\ eval_wide h1 b norm_length - eval_wide h1 b 1 = eval_wide h0 b norm_length - eval_wide h0 b 1)
  ) else (
    freduce_degree_lemma_2 h0 h1 b ctr
  )

val freduce_degree': b:bigint_wide -> ctr:u32{w ctr < norm_length - 1} -> STL unit 
    (requires (fun h -> reducible' h b (w ctr))) 
    (ensures (fun h0 _ h1 -> untouched' h0 h1 b (w ctr) /\ times19' h0 h1 b (w ctr)
      /\ eval_wide h1 b (norm_length) % reveal prime = eval_wide h0 b (norm_length+1+w ctr) % reveal prime
      /\ modifies_1 b h0 h1))
let rec freduce_degree' b ctr' =
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq ctr' 0ul then begin
    let b5ctr = index b (nlength) in 
    let bctr = index b 0ul in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr |+ b5ctr in 
    upd b 0ul bctr;
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b 0ul bctr; *)
    freduce_degree_lemma h0 h1 b 0;
    cut (True /\ eval_wide h0 b (norm_length+1+0) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime);
    cut (True /\ eval_wide h0 b (norm_length+1) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime)
  end
  else begin
    let ctr = ctr' in
    let b5ctr = index b (ctr +| nlength) in 
    let bctr = index b ctr in
    let b5ctr = times_19 b5ctr in
    let bctr = bctr |+ b5ctr in 
    upd b ctr bctr;
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b ctr bctr; *)
    freduce_degree_lemma h0 h1 b (w ctr); 
    cut (True /\ eval_wide h0 b (norm_length+1+w ctr) % reveal prime = eval_wide h1 b (norm_length+w ctr) % reveal prime);
    cut(reducible' h1 b (w ctr-1)); 
    freduce_degree' b (ctr-|1ul); 
    let h2 = HST.get() in 
    cut (forall (i:nat). {:pattern (v (getValue h1 b i))} (i > w ctr /\ i < 2*norm_length-1) ==>
	   v (getValue h1 b i) = v (getValue h0 b i)); 
    cut(untouched' h0 h2 b (w ctr));
    cut (times19' h0 h2 b (w ctr)) 
  end

val aux_lemma_4: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ satisfies_modulo_constraints h b))
  (ensures (reducible' h b (norm_length-2)))
let aux_lemma_4 h b = 
  let max = maxValue_wide h b (length b) in
  cut (forall (i:nat). {:pattern (v (getValue h b i))} i < length b ==> v (getValue h b i) <= max); 
  Math.Lemmas.pow2_increases_1 platform_wide (platform_wide-1)

val aux_lemma_5: h0:heap -> h1:heap -> b:bigint_wide -> Lemma
  (requires (live h0 b /\ satisfies_modulo_constraints h0 b /\ times19' h0 h1 b (norm_length-2)
      /\ untouched' h0 h1 b (norm_length-2)))
  (ensures (live h0 b /\ satisfies_modulo_constraints h0 b /\ times19' h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (getValue h1 b i) < pow2 (platform_wide-1))))
let aux_lemma_5 h0 h1 b = 
  admit(); // OK
  let max = maxValue_wide h0 b (length b) in
  cut (forall (i:nat). {:pattern (v (getValue h0 b i))} i < length b ==> v (getValue h0 b i) <= max);
  cut (forall (i:nat). i < norm_length-1 ==> v (getValue h1 b i) = v (getValue h0 b i) + 19 * v (getValue h0 b (i+norm_length)) )

#reset-options

val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> live h b /\ satisfies_modulo_constraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfies_modulo_constraints h0 b
    /\ length b >= 2*norm_length - 1
    /\ length b = length b /\ modifies_1 b h0 h1 /\ length b >= norm_length+1
    /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i <= norm_length ==> 
	v (getValue h1 b i) < pow2 (platform_wide - 1))
    /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
  let h0 = HST.get() in
  aux_lemma_4 h0 b; 
  freduce_degree' b (nlength-|2ul); 
  let h1 = HST.get() in
  aux_lemma_5 h0 h1 b

#reset-options

val pow2_bitweight_lemma: ctr:nat -> 
  Lemma
    (requires (True))
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
let pow2_bitweight_lemma ctr =
  bitweight_def templ ctr;
  Math.Lemmas.pow2_exp_1 (bitweight templ ctr) (templ ctr)

#reset-options

val eval_carry_lemma: ha:heap -> a:bigint_wide{live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint_wide{live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> Lemma
    (requires (
      v (getValue hb b ctr) = v (getValue ha a ctr) % pow2 (templ ctr)
      /\ v (getValue hb b (ctr+1)) = v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (getValue hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (getValue hb b i) = v (getValue ha a i))
    ))
    (ensures (eval_wide hb b (norm_length+1) = eval_wide ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr =
  admit(); // OK
  (* eval_eq_lemma ha hb a b ctr; *)
  assert(eval_wide ha a ctr = eval_wide hb b ctr);
  eval_wide_def ha a (ctr+2);
  eval_wide_def ha a (ctr+1);
  eval_wide_def hb b (ctr+2);
  eval_wide_def hb b (ctr+1);
  (* ModuloLemmas.helper_lemma_0 ctr; ModuloLemmas.helper_lemma_1 ctr; *)
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (getValue hb b (ctr+1)) + eval_wide hb b (ctr+1)); 
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (getValue hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (getValue hb b ctr) + eval_wide hb b ctr));  
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (getValue ha a (ctr+1)) + v (getValue ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr)); 
  Math.Axioms.distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (getValue ha a (ctr+1))) (v (getValue ha a ctr) / pow2 (templ ctr));
  cut(True /\ eval_wide hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (getValue ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr)); 
  pow2_bitweight_lemma ctr; 
  cut(True /\ eval_wide hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (getValue ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (getValue ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr));  
  (* ModuloLemmas.helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (getValue ha a ctr)) (eval_wide hb b ctr);  *)
  cut(True /\ eval_wide hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (getValue ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (getValue ha a ctr) + eval_wide hb b ctr));  
  cut(True /\ eval_wide hb b (ctr+2) = eval_wide ha a (ctr+2)); 
  (* eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1); *)
  (* ModuloLemmas.helper_lemma_3 (eval_wide ha a (norm_length+1)) (eval_wide hb b (norm_length+1)) (eval_wide ha a (ctr+2)) (eval_wide hb b (ctr+2)) *)
 ()

val auxiliary_lemma_1: bip1:u128 -> c:u128 -> Lemma
    (requires (v bip1 < pow2 (platform_wide  - 1) /\ v c < pow2 (platform_wide - 51)))
    (ensures (v bip1 + v c < pow2 platform_wide))
let gauxiliary_lemma_1 bip1 c =
  (* ModuloLemmas.helper_lemma_4 (v bip1) (v c) 51 platform_wide *)
  ()

#reset-options

val mod_lemma_1: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a))
let mod_lemma_1 a b = ()

#reset-options

// The encoding needs to depend on the bitwise encoding
val mod2_51: a:u128 -> Tot (b:u128{v b = v a % pow2 51})
let mod2_51 a = 
  let mask = (U128.of_string "1") |<< 51ul in
  cut (v mask = pow2 51 % pow2 platform_wide /\ pow2 51 >= 1); 
  Math.Lemmas.pow2_increases_1 platform_wide 51; 
  mod_lemma_1 (pow2 51) (pow2 platform_wide);
  let mask = U128.sub mask (U128.of_string "1") in
  let res = a |& mask in
  (* log_and_wide_lemma_3 a mask 51; *)
  res

abstract type carriable (h:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h b i))}
      (i > ctr /\ i <= norm_length) ==> v (getValue h b i) < pow2 (platform_wide - 1))

abstract type carried (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} i < ctr ==> v (getValue h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (getValue h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (getValue h1 b norm_length) < pow2 77)

abstract type carried' (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i >= ctr /\ i < norm_length) ==> v (getValue h1 b i) < pow2 (templ ctr))
  /\ v (getValue h1 b norm_length) < pow2 77

abstract type untouched_2 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= norm_length+1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (getValue h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (getValue h0 b i) = v (getValue h1 b i))

val carry:
  b:bigint_wide -> ctr:u32{w ctr <= norm_length} -> STL unit
    (requires (fun h -> carriable h b (w ctr) /\ carried h b (w ctr)))
    (ensures (fun h0 _ h1 -> carried h1 b norm_length /\ untouched_2 h0 h1 b (w ctr)
      /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1)
      /\ modifies_1 b h0 h1))
let rec carry b i =
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq i nlength then ()
  else begin
    let bi = index b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ (w i))); 
    upd b i ri; 
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b i ri;  *)
    let c = (bi |>> 51ul) in
    // In the spec of >>
    admitP(True /\ v c < pow2 (platform_wide - 51)); 
    let bip1 = index b (i+|1ul) in
    assert(v bip1 = v (getValue h1 b (w i+1))); 
    assert(v bip1 < pow2 (platform_wide - 1)); 
    (* auxiliary_lemma_1 bip1 c;  *)
    let z = bip1 |+ c in
    upd b (i+|1ul) z;
    let h2 = HST.get() in
    (* upd_lemma h1 h2 b (i+|1ul) z;  *)
    eval_carry_lemma h0 b h2 b (w i); 
    cut (forall (j:nat). (j > w i+1 /\ j <= norm_length) ==> v (getValue h2 b j) < pow2 (platform_wide - 1));
    carry b (i+|1ul)
  end
  
#reset-options

val carry_top_to_0: b:bigint_wide -> STL unit
    (requires (fun h -> carried h b norm_length /\ length b >= norm_length+1
      /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 (platform_wide-1)))
    (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carried' h1 b 1
      /\ eval_wide h1 b norm_length % (reveal prime) = eval_wide h0 b (norm_length+1) % (reveal prime)
      /\ v (getValue h1 b 0) = v (getValue h0 b 0) + 19 * v (getValue h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (getValue h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (getValue h1 b i) = v (getValue h0 b i)) ))
let carry_top_to_0 b =
  admit(); // OK
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in 
  let btop_19 = times_19 btop in  
  upd b 0ul (b0 |+ btop_19); 
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0

#reset-options

abstract type carriable2 (h:heap) (b:bigint_wide) (ctr:nat{ctr<=norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} i < ctr ==> v (getValue h b i) < pow2 51)
  /\ (forall (i:nat). {:pattern (v (getValue h b i))} (i > ctr /\ i < norm_length) ==> v (getValue h b i) < pow2 51)
  /\ (ctr < norm_length ==> v (getValue h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (getValue h b norm_length) < 2)
  /\ v (getValue h b ctr) < pow2 51 + pow2 32
  /\ (v (getValue h b ctr) >= pow2 51 ==> (
      forall (i:nat). {:pattern (v (getValue h b i))} (i < ctr /\ i > 0) ==> v (getValue h b i) < pow2 32))
  /\ ((ctr = norm_length /\ v (getValue h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (getValue h b i))} (i > 0 /\ i < norm_length) ==> v (getValue h b i) < pow2 32))

val helper_lemma_20: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 32))
  (ensures (v a + v b < pow2 52 /\ v a + v b / pow2 51 < 2 /\ (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 32) ))
let helper_lemma_20 a b = admit() // TODO: enrich % properties

val helper_lemma_21: a:u128 -> Lemma (requires (v a < pow2 51 + pow2 32))
				    (ensures (v a < pow2 52 /\ v a / pow2 51 < 2))
let helper_lemma_21 a = 
  admit(); // OK
  Math.Lemmas.pow2_double_sum 51; pow2_increases_lemma 51 32

val carry2: b:bigint_wide -> ctr:u32{w ctr <= norm_length} -> STL unit
  (requires (fun h -> carriable2 h b (w ctr)))
  (ensures (fun h0 _ h1 -> carriable2 h0 b (w ctr) /\ carriable2 h1 b norm_length
    /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1)
    /\ modifies_1 b h0 h1))
let rec carry2 b i = 
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq i nlength then ()
  else begin
    let bi = index b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ (w i))); 
    upd b i ri; 
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b i ri;  *)
    let bip1 = index b (i+|1ul) in
    let c = (bi |>> 51ul) in 
    helper_lemma_21 bi;
    helper_lemma_20 bip1 c; 
    (* // In the spec of >> *)
    (* admitP(True /\ v c < pow2 (platform_wide - 51));  *)
    (* assert(v bip1 = v (getValue h1 b (i+1)));  *)
    pow2_increases_lemma (platform_wide-1) 51;
    (* assert(v bip1 < pow2 (platform_wide - 1));  *)
    (* auxiliary_lemma_1 bip1 c;  *)
    let z = bip1 |+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51); 
    cut (v z >= pow2 51 ==> v c = 1); 
    cut (v c > 0 ==> v (getValue h0 b (w i)) / (pow2 51) > 0 ==> v (getValue h0 b (w i)) >= pow2 51); 
    cut (v z >= pow2 51 ==> v (getValue h1 b (w i)) < pow2 32); 
    upd b (i+|1ul) z;
    let h2 = HST.get() in
    (* upd_lemma h1 h2 b (i+|1ul) z;  *)
    cut (v z >= pow2 51 ==> v c = 1 /\ True); 
    eval_carry_lemma h0 b h2 b (w i);
    carry2 b (i+|1ul)
  end
  
val helper_lemma_30: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 37))
  (ensures (v a + v b < pow2 52 /\ v a + v b / pow2 51 < 2
	    /\ (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 37) ))
let helper_lemma_30 a b = admit() // TODO: enrich % properties

val helper_lemma_32: a:u128 -> Lemma (requires (v a < pow2 52))
				   (ensures (v a / pow2 51 = 1 ==> v a >= pow2 51))
let helper_lemma_32 a =
  Math.Lemmas.pow2_double_sum 51

val helper_lemma_33: a:u128 -> b:u128 -> Lemma (requires (v a < pow2 51 /\ v b < 2 /\ 
  (v b = 1 ==> v a < pow2 32)))
  (ensures (v a + v b < pow2 51))
let helper_lemma_33 a b = pow2_increases_lemma 51 33; Math.Lemmas.pow2_double_sum 26

val last_carry: b:bigint_wide -> STL unit
  (requires (fun h -> carriable2 h b norm_length))
  (ensures (fun h0 _ h1 -> carriable2 h0 b norm_length /\ norm_wide h1 b
    /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (norm_length+1) % reveal prime
    /\ modifies_1 b h0 h1))
let last_carry b =
  admit(); // OK
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in
  cut (v b0 < pow2 51 /\ v btop < 2); 
  pow2_5_lemma ();
  cut (19 * v btop < pow2 5 /\ True);
  pow2_increases_lemma 51 5;
  Math.Lemmas.pow2_double_sum 51;
  pow2_increases_lemma platform_wide 52;
  pow2_increases_lemma platform_wide 51;
  cut (v b0 + 19 * v btop < pow2 52 /\ True); 
  let btop_19 = times_19 btop in  
  let bi = (b0 |+ btop_19) in
  (* upd_wide b 0 (b0 |+ btop_19);  *)
  upd b 0ul bi;
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0; 
  upd b nlength (U128.of_string "0");
  let h2 = HST.get() in
  (* eval_eq_lemma h1 h2 b b norm_length;  *)
  cut (eval_wide h2 b (norm_length+1) = eval_wide h1 b norm_length /\ True); 
  (* let bi = index b 0 in  *)
  let ri = mod2_51 bi in
  upd b 0ul ri; 
  let h3 = HST.get() in
  let c = (bi |>> 51ul) in 
  Math.Lemmas.pow2_exp_1 32 5;
  cut (v bi < pow2 51 + 19 /\ True); 
  cut (v bi >= pow2 51 ==> v (getValue h3 b 1) < pow2 32); 
  helper_lemma_30 b0 btop_19; 
  helper_lemma_32 bi;
  let bip1 = index b 1ul in 
  cut (v bi >= pow2 51 ==> v bip1 < pow2 32); 
  cut (v c = 1 ==> v bip1 < pow2 32); 
  cut (v c = (v b0 + v btop_19) / pow2 51 /\ v bip1 < pow2 51); 
  helper_lemma_33 bip1 c; 
  let z = bip1 |+ c in 
  upd b 1ul z;
  let h4 = HST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (True /\ v (getValue h4 b 1) < pow2 51);
  cut (norm_wide h4 b)

#reset-options

val lemma_helper_40: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ length b >= norm_length + 1 /\ v (getValue h b norm_length) < pow2 77
	    /\ v (getValue h b 0) < pow2 51))
  (ensures (live h b /\ length b >= norm_length + 1 
    /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 (platform_wide - 1)
    /\ v (getValue h b 0) + 19 * v (getValue h b norm_length) < pow2 83))
let lemma_helper_40 h b = 
  pow2_5_lemma ();
  Math.Lemmas.pow2_exp_1 5 77;
  pow2_increases_lemma 82 51;
  pow2_increases_lemma (platform_wide-1) 83;
  Math.Lemmas.pow2_double_sum 82

val lemma_helper_41: a:u128 -> Lemma (requires (v a < pow2 83))
				    (ensures (v a / pow2 51 < pow2 32))
let lemma_helper_41 a = 
  admit(); // TODO
  ()

val lemma_helper_42: a:u128 -> b:u128 -> Lemma (requires (v a < pow2 51 /\ v b < pow2 32))
					      (ensures (v a + v b < pow2 52 
						       /\ v a + v b < pow2 platform_wide))
let lemma_helper_42 a b = pow2_increases_lemma platform_wide 52; pow2_increases_lemma 51 32

val freduce_coefficients: b:bigint_wide -> ST unit
  (requires (fun h -> carriable h b 0))
  (ensures (fun h0 _ h1 -> carriable h0 b 0 /\ norm_wide h1 b
    /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b norm_length % reveal prime))
let freduce_coefficients b =
  admit(); // TODO
  let h = HST.get() in
  upd b nlength (U128.of_string "0");
  let h' = HST.get() in
  (* eval_eq_lemma h h' b b norm_length; *)
  eval_wide_def h' b (norm_length+1);
  cut (True /\ eval_wide h' b (norm_length+1) = eval_wide h b norm_length);
  carry b 0ul;
  let h = HST.get() in
  lemma_helper_40 h b;
  carry_top_to_0 b;
  let h1 = HST.get() in
  upd b nlength (U128.of_string "0");
  let h2 = HST.get() in
  (* eval_eq_lemma h1 h2 b b norm_length; *)
  eval_wide_def h2 b (norm_length+1);
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let r0 = mod2_51 b0 in
  let c0 = b0 |>> 51ul in
  lemma_helper_41 b0; 
  lemma_helper_42 b1 c0;
  let h = HST.get() in
  upd b 0ul r0; 
  upd b 1ul (b1 |+ c0); 
  let h' = HST.get() in
  eval_carry_lemma h b h' b 0; 
  carry2 b 1ul; 
  last_carry b
  
#reset-options

val addition_lemma: a:u64 -> m:nat -> b:u64 -> n:nat -> 
  Lemma (requires (vv a < pow2 m /\ vv b < pow2 n))
	(ensures (vv a + vv b <  pow2 (max m n + 1)))
let addition_lemma a m b n = (* add_lemma m (v a) n (v b) *) ()

val aux_lemma_1: unit -> Lemma (requires (True)) (ensures (pow2 52 - 2 >= pow2 51 /\ pow2 52 - 38 >= pow2 51))
let aux_lemma_1 () =
  cut (pow2 6 = 64 /\ pow2 2 = 4);
  Math.Lemmas.pow2_increases_1 51 6; Math.Lemmas.pow2_increases_1 51 2;
  Math.Lemmas.pow2_double_sum 51

#reset-options

val add_big_zero_core: b:bigint -> ST unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ live h1 b /\ length b = length b
			 /\ filled h1 b
			 /\ vv (getValue h1 b 0) = vv (getValue h0 b 0) + (pow2 52 - 38)
			 /\ vv (getValue h1 b 1) = vv (getValue h0 b 1) + (pow2 52 - 2)
			 /\ vv (getValue h1 b 2) = vv (getValue h0 b 2) + (pow2 52 - 2)
			 /\ vv (getValue h1 b 3) = vv (getValue h0 b 3) + (pow2 52 - 2)
			 /\ vv (getValue h1 b 4) = vv (getValue h0 b 4) + (pow2 52 - 2)
			 /\ modifies_1 b h0 h1))
let add_big_zero_core b =
  let h0 = HST.get() in
  let two52m38 = 0xfffffffffffdauL in // pow2 52 - 38
  let two52m2 =  0xffffffffffffeuL in // pow2 52 - 2
  admitP(vv two52m38 = pow2 52 - 38 /\ vv two52m2 = pow2 52 - 2); 
  let b0 = index b 0ul in 
  cut(True /\ vv b0 = vv (getValue h0 b 0)); 
  cut(forall (i:nat). {:pattern (vv (getValue h0 b i))} i < norm_length ==> (vv (getValue h0 b i)) < pow2 (templ i)); 
  cut(forall (i:nat). i < norm_length ==> vv (getValue h0 b i) < pow2 (templ i)); 
  cut (vv b0 < pow2 51 /\ vv two52m38 < pow2 52); 
  addition_lemma b0 51 two52m38 52;
  Math.Lemmas.pow2_increases_1 platform_size 53; 
  upd b 0ul (U64.add b0 two52m38); 
  let h1 = HST.get() in
  (* upd_lemma h0 h1 b 0ul (U64.add b0 two52m38);  *)
  let b1 = index b 1ul in
  cut (vv b1 = vv (getValue h0 b 1) /\ vv b1 < pow2 51 /\ vv two52m2 < pow2 52); 
  addition_lemma b1 51 two52m2 52;
  Math.Lemmas.pow2_increases_1 platform_size 53; 
  upd b 1ul (U64.add b1 two52m2);   
  let h2 = HST.get() in
  (* upd_lemma h1 h2 b 1ul (U64.add b1 two52m2);  *)
  let b2 = index b 2ul in
  cut (vv b2 = vv (getValue h1 b 2) /\ vv (getValue h1 b 2) = vv (getValue h0 b 2) /\ vv b2 < pow2 51);
  addition_lemma b2 51 two52m2 52;
  Math.Lemmas.pow2_increases_1 platform_size 53; 
  upd b 2ul (U64.add b2 two52m2); 
  let h3 = HST.get() in
  (* upd_lemma h2 h3 b 2ul (U64.add b2 two52m2);  *)
  let b3 = index b 3ul in
  cut (vv b3 = vv (getValue h2 b 3) /\ vv (getValue h2 b 3) = vv (getValue h1 b 3) /\ vv (getValue h1 b 3) = vv (getValue h0 b 3) /\ vv b3 < pow2 51);
  addition_lemma b3 51 two52m2 52;
  Math.Lemmas.pow2_increases_1 platform_size 53; 
  upd b 3ul (U64.add b3 two52m2);   
  let h4 = HST.get() in
  (* upd_lemma h3 h4 b 3ul (U64.add b3 two52m2);  *)
  let b4 = index b 4ul in
  cut (vv b4 = vv (getValue h3 b 4) /\ vv (getValue h3 b 4) = vv (getValue h2 b 4) /\ vv (getValue h2 b 4) = vv (getValue h1 b 4) /\ vv (getValue h1 b 4) = vv (getValue h0 b 4) /\ vv b4 < pow2 51);
  addition_lemma b4 51 two52m2 52;
  Math.Lemmas.pow2_increases_1 platform_size 53; 
  upd b 4ul (U64.add b4 two52m2);
  let h5 = HST.get() in 
  (* upd_lemma h4 h5 b 4ul (U64.add b4 two52m2); *)
  cut (vv (getValue h5 b 0) = vv (getValue h0 b 0) + (pow2 52 - 38) /\ True); 
  cut (vv (getValue h5 b 1) = vv (getValue h0 b 1) + (pow2 52 - 2) /\ True); 
  cut (vv (getValue h5 b 2) = vv (getValue h0 b 2) + (pow2 52 - 2) /\ True); 
  cut (vv (getValue h5 b 3) = vv (getValue h0 b 3) + (pow2 52 - 2) /\ True); 
  cut (vv (getValue h5 b 4) = vv (getValue h0 b 4) + (pow2 52 - 2) /\ True); 
  (* cut (forall (i:nat). {:pattern (v (getValue h5 b i))} i < 5 ==> v (getValue h5 b i) < pow2 ndiff);  *)
  aux_lemma_1 (); 
  (* cut (forall (i:nat). {:pattern (v (getValue h5 b i))} i < 5 ==> v (getValue h5 b i) >= pow2 ndiff');  *)
  cut (norm_length = 5 /\ True); 
  cut(filled h5 b)
  
#reset-options

val aux_lemma_2: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) =
	 pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 256 - 38)
let aux_lemma_2 a b c d e =
  let v = pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) in
  cut (True /\ v = pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 204 * pow2 52 - pow2 204 * 2 + pow2 153 * pow2 52 - pow2 153 * 2 + pow2 102 * pow2 52 - pow2 102 * 2 + pow2 51 * pow2 52 - pow2 51 * 2 + pow2 52 - 38); 
  cut (True /\ pow2 1 = 2); 
  Math.Lemmas.pow2_exp_1 204 52; Math.Lemmas.pow2_exp_1 204 2; 
  Math.Lemmas.pow2_exp_1 153 52; Math.Lemmas.pow2_exp_1 153 2; 
  Math.Lemmas.pow2_exp_1 102 52; Math.Lemmas.pow2_exp_1 102 2; 
  Math.Lemmas.pow2_exp_1 51 52; Math.Lemmas.pow2_exp_1 51 2

#reset-options

// Missing modulo spec, TODO: add to axioms
assume val modulo_lemma_2: a:int -> b:pos -> Lemma ( (a + 2 * b) % b = a % b)

val aux_lemma_3: a:int -> Lemma (requires (True)) (ensures ((a + pow2 256 - 38) % reveal prime = a % reveal prime)) []
let aux_lemma_3 a =
  Math.Lemmas.pow2_double_mult 255;
  cut (True /\ 2 * reveal prime = pow2 256 - 38);
  modulo_lemma_2 a (reveal prime)

#reset-options

val add_big_zero_lemma: h0:heap -> h1:heap -> b:bigint -> 
  Lemma (requires (norm h0 b /\ live h1 b /\ length b = length b 
		  /\ filled h1 b
		  /\ vv (getValue h1 b 0) = vv (getValue h0 b 0) + (pow2 52 - 38)
		  /\ vv (getValue h1 b 1) = vv (getValue h0 b 1) + (pow2 52 - 2)
		  /\ vv (getValue h1 b 2) = vv (getValue h0 b 2) + (pow2 52 - 2)
		  /\ vv (getValue h1 b 3) = vv (getValue h0 b 3) + (pow2 52 - 2)
		  /\ vv (getValue h1 b 4) = vv (getValue h0 b 4) + (pow2 52 - 2) ))
	(ensures (norm h0 b /\ live h1 b /\ length b = length b
		 /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime)) []
let add_big_zero_lemma h0 h1 b =
  cut (bitweight templ 0 = 0 /\ bitweight templ 1 = 51 /\ bitweight templ 2 = 102 /\ bitweight templ 3 = 153 /\ bitweight templ 4 = 204); 
  cut (True /\ eval h1 b norm_length = pow2 204 * (vv (getValue h0 b 4) + pow2 52 - 2) + eval h1 b 4); 
  cut (True /\ eval h1 b 4 = pow2 153 * (vv (getValue h0 b 3) + pow2 52 - 2) + eval h1 b 3); 
  cut (True /\ eval h1 b 3 = pow2 102 * (vv (getValue h0 b 2) + pow2 52 - 2) + eval h1 b 2); 
  cut (True /\ eval h1 b 2 = pow2 51 * (vv (getValue h0 b 1) + pow2 52 - 2) + eval h1 b 1); 
  cut (True /\ eval h1 b 1 = (vv (getValue h0 b 0) + pow2 52 - 38)); 
  cut (eval h1 b norm_length = 
	    pow2 204 * (vv (getValue h0 b 4) + pow2 52 - 2) 
	    + pow2 153 * (vv (getValue h0 b 3) + pow2 52 - 2) 
	    + pow2 102 * (vv (getValue h0 b 2) + pow2 52 - 2) 
	    + pow2 51 * (vv (getValue h0 b 1) + pow2 52 - 2) 
	    + (vv (getValue h0 b 0) + pow2 52 - 38) /\ True); 
  cut (True /\ eval h0 b norm_length = pow2 204 * vv (getValue h0 b 4)  + eval h0 b 4); 
  cut (True /\ eval h0 b 4 = pow2 153 * vv (getValue h0 b 3)  + eval h0 b 3); 
  cut (True /\ eval h0 b 3 = pow2 102 * vv (getValue h0 b 2) + eval h0 b 2); 
  cut (True /\ eval h0 b 2 = pow2 51 * vv (getValue h0 b 1) + eval h0 b 1); 
  cut (True /\ eval h0 b 1 = vv (getValue h0 b 0) ); 
  cut (True /\ eval h0 b norm_length = pow2 204 * vv (getValue h0 b 4) + pow2 153 * vv (getValue h0 b 3)  
			       + pow2 102 * vv (getValue h0 b 2) + pow2 51 * vv (getValue h0 b 1) 
			       + vv (getValue h0 b 0)); 
  aux_lemma_2 (vv (getValue h0 b 4)) (vv (getValue h0 b 3)) (vv (getValue h0 b 2)) (vv (getValue h0 b 1)) (vv (getValue h0 b 0));
  let a = pow2 204 * vv (getValue h0 b 4) + pow2 153 * vv (getValue h0 b 3)  
			       + pow2 102 * vv (getValue h0 b 2) + pow2 51 * vv (getValue h0 b 1) 
			       + vv (getValue h0 b 0) in
  aux_lemma_3 a			       

#reset-options

let add_big_zero b =
  let h0 = HST.get() in
  add_big_zero_core b;
  let h1 = HST.get() in
  add_big_zero_lemma h0 h1 b

#reset-options

(* Not verified *)
let normalize (b:bigint) =
  admit();
  let two51m1 = 0x7ffffffffffffuL in // pow2 51 - 1
  let two51m19 = 0x7ffffffffffeduL in // pow2 51 - 19
  let b4 = (index b 4ul) in
  let b3 = (index b 3ul) in
  let b2 = (index b 2ul) in
  let b1 = (index b 1ul) in
  let b0 = (index b 0ul) in  
  let mask = U64.eq_mask b4 two51m1 in
  let mask = U64.logand mask (U64.eq_mask b3 two51m1) in
  let mask = U64.logand mask (U64.eq_mask b2 two51m1) in
  let mask = U64.logand mask (U64.eq_mask b1 two51m1) in
  let mask = U64.logand mask (U64.gte_mask b0 two51m19) in
  let sub_mask = U64.logand mask two51m1 in
  let sub_mask2 = U64.logand mask two51m19 in
  // Conditionally substract 2^255 - 19 
  let b4 = index b 4ul in
  upd b 4ul (U64.sub b4 sub_mask);
  let b3 = index b 3ul in
  upd b 3ul (U64.sub b3 sub_mask);
  let b2 = index b 2ul in
  upd b 2ul (U64.sub b2 sub_mask);
  let b1 = index b 1ul in
  upd b 1ul (U64.sub b1 sub_mask);
  let b0 = index b 0ul in
  upd b 0ul (U64.sub b0 sub_mask2)

val sum_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (norm h0 a /\ norm h0 b /\ live h1 cpy /\ length cpy >= 2*norm_length-1
		/\ (forall (i:nat). i < norm_length ==> v (getValue h1 cpy i) = vv (getValue h0 a i) 
							  + vv (getValue h0 b i))
		/\ (forall (i:nat). (i >= norm_length /\ i < length cpy) ==> 
		    v (getValue h1 cpy i) = 0)))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let sum_satisfies_constraints h0 h1 cpy a b =
  admit();
  let max = maxValue_wide h1 cpy (length cpy) in
  cut (forall (i:nat). {:pattern (vv (getValue h0 b i))} i < norm_length ==> vv (getValue h0 b i) < pow2 51);
  cut (forall (i:nat). {:pattern (vv (getValue h0 a i))} i < norm_length ==> (vv (getValue h0 a i)) < pow2 51);
  admitP (forall (i:nat). i < norm_length ==> (vv (getValue h0 a i) < pow2 51 /\ vv (getValue h0 b i) < pow2 51));
  Math.Lemmas.pow2_double_sum 51;
  cut (forall (i:nat). i < length cpy ==> v (getValue h1 cpy i) < pow2 52);
  cut (True /\ maxValue_wide h1 cpy (length cpy)  < pow2 52);
  cut (20 < pow2 5 /\ pow2 52 * 20 <= pow2 52 * pow2 5);
  Math.Lemmas.pow2_exp_1 52 5;
  Math.Lemmas.pow2_increases_1 (platform_wide - 1) 57

val mul_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (norm h0 a /\ norm h0 b /\ live h1 cpy /\ length cpy >= 2*norm_length-1
      /\ maxValue_wide h1 cpy (length cpy) <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let mul_satisfies_constraints h0 h1 cpy a b =
  admit();
  let max = maxValue_wide h1 cpy (length cpy) in
  cut (forall (i:nat). {:pattern (vv (getValue h0 b i))} i < norm_length ==> (vv (getValue h0 b i)) < pow2 51);
  cut (forall (i:nat). {:pattern (vv (getValue h0 a i))} i < norm_length ==> (vv (getValue h0 a i)) < pow2 51);
  admitP (forall (i:nat). i < norm_length ==> (vv (getValue h0 a i) < pow2 51 /\ vv (getValue h0 b i) < pow2 51));
  cut (maxValueNorm h0 a < pow2 51 /\ maxValueNorm h0 b < pow2 51);
  Math.Lemmas.pow2_exp_1 51 51;
  cut (maxValue_wide h1 cpy (length cpy) <= 5 * pow2 102 /\ 5 < pow2 3);
  Math.Lemmas.pow2_exp_1 102 3;
  cut (True /\ max <= pow2 105);
  cut (20 < pow2 5 /\ pow2 102 * 20 <= pow2 102 * pow2 5);
  Math.Lemmas.pow2_exp_1 102 5;
  Math.Lemmas.pow2_increases_1 (platform_wide - 1) 107

val difference_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (filled h0 a /\ norm h0 b /\ live h1 cpy 
      /\ length cpy >= 2*norm_length-1
      /\ (forall (i:nat). i < norm_length ==> v (getValue h1 cpy i) = vv (getValue h0 a i) - vv (getValue h0 b i))
      /\ (forall (i:nat). (i >= norm_length /\ i < length cpy) ==> v (getValue h1 cpy i) = 0) ))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let difference_satisfies_constraints h0 h1 cpy a b =
  admit();
  cut (forall (i:nat). {:pattern (vv (getValue h0 b i))} i < norm_length ==> (vv (getValue h0 b i)) < pow2 51);
  cut (forall (i:nat). {:pattern (vv (getValue h0 a i))} i < norm_length ==> vv (getValue h0 a i) < pow2 53);
  admitP (forall (i:nat). i < norm_length ==> (vv (getValue h0 a i) < pow2 53 /\ vv (getValue h0 b i) < pow2 51));
  Math.Lemmas.pow2_increases_1 53 51;
  cut (forall (i:nat). i < length cpy ==> v (getValue h1 cpy i) < pow2 53);
  cut (True /\ maxValue_wide h1 cpy (length cpy) < pow2 53);
  cut (20 < pow2 5 /\ pow2 53 * 20 <= pow2 53 * pow2 5);
  Math.Lemmas.pow2_exp_1 53 5;
  Math.Lemmas.pow2_increases_1 (platform_wide - 1) 58

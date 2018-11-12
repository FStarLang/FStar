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

#set-options "--z3rlimit 30"

let w: u32 -> Tot int = U32.v
let vv: u64 -> Tot int = U64.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let heap = HS.mem

let op_Bar_Amp = U128.logand
let op_Bar_Greater_Greater = U128.shift_right
let op_Bar_Less_Less = U128.shift_left
let op_Bar_Plus = U128.add
let op_Bar_Star = U128.mul

// Because the details from parameters.fst are not imported although needed for proofs here
(* assume Templ_lemma: forall (i:nat). {:pattern (templ i)} templ i = 51 *)
(* assume Platform_size_lemma: platform_size = 64 *)
(* assume PrimeValue: reveal prime = (pow2 255 - 19) *)
(* assume NormLengthValue: norm_length = 5 *)
(* assume Ndiff: ndiff = 53 *)
(* assume Ndiff': ndiff' = 51 *)

val prime_modulo_lemma: unit -> Lemma (pow2 255 % (reveal prime) = 19)
let prime_modulo_lemma () = assert_norm (pow2 255 % (reveal prime) = 19)

val modulo_lemma: a:nat -> b:pos -> Lemma
  (requires (a < b))
  (ensures (a % b = a))
  [SMTPat (a % b)]
let modulo_lemma a b = () //Math.Lemmas.modulo_lemma a b

val pow2_4_lemma: unit -> Lemma
  (requires True)
  (ensures (pow2 4 = 16))
  [SMTPat (pow2 4)]
let pow2_4_lemma () =
  assert_norm (pow2 4 = 16)

val pow2_5_lemma: unit -> Lemma
  (requires True)
  (ensures (pow2 5 = 32))
  [SMTPat (pow2 5)]
let pow2_5_lemma () =
  assert_norm (pow2 5 = 32)

let satisfies_modulo_constraints h (b:bigint_wide{live h b}) = // TODO
  length b >= 2*norm_length-1
  && maxValue_wide h b (length b) * 20 < pow2 (platform_wide - 1)

type satisfiesModuloConstraints (h:heap) (b:bigint_wide) =
  live h b /\ satisfies_modulo_constraints h b

val times_19: x:u128{19 * v x < pow2 platform_wide} -> Tot (y:u128{v y = 19 * v x})
let times_19 x =
  let y = x |<< 4ul in
  let z = x |<< 1ul in
  x |+ y |+ z

abstract type reducible (h:heap) (b:bigint_wide) (ctr:nat) =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (get h b (i+norm_length))}
      (i >= ctr /\ i < norm_length-1) ==> v (get h b i) + 19 * v (get h b (i+norm_length)) < pow2 platform_wide)

abstract type reducible' (h:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length-1}) =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (get h b (i+norm_length))}
      i <= ctr ==> v (get h b i) + 19 * v (get h b (i+norm_length)) < pow2 platform_wide)

abstract type times19 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (get h1 b i)}
       (i >= ctr /\ i < norm_length - 1) ==> v (get h1 b i) = v (get h0 b i) + 19 * (v (get h0 b (i+norm_length))))

abstract type times19' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat{ctr < norm_length - 1}) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (get h1 b i)}
       i <= ctr ==> v (get h1 b i) = v (get h0 b i) + 19 * (v (get h0 b (i+norm_length))))

abstract type untouched (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length-1) /\ i < 2*norm_length-1) ==> v (get h0 b i) = v (get h1 b i))

abstract type untouched' (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) = 
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==> 
      v (get h0 b i) = v (get h1 b i))


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
let rec lemma_helper_02 a b =
  match a with
  | 0 -> ()
  | _ -> lemma_helper_02 (a-1) b

val lemma_helper_03: ctr:nat{ctr>=2} -> Lemma (pow2 51 * pow2 (bitweight templ (ctr-2)) = pow2 (bitweight templ (ctr-1)))
let lemma_helper_03 ctr = 
  bitweight_def templ 1;
  lemma_helper_02 1 (ctr-2); 
  Math.Lemmas.pow2_plus 51 (bitweight templ (ctr-2))

val lemma_helper_04: ctr:nat{ctr>=2} -> Lemma
  (requires (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * pow2 (bitweight templ (ctr+norm_length-2))))
  (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let lemma_helper_04 ctr =
//admit(); // OK
  lemma_helper_02 (ctr-2) norm_length;
  Math.Lemmas.pow2_plus (bitweight templ (ctr-2)) (bitweight templ norm_length); 
  Math.Lemmas.paren_mul_right (pow2 51) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
  lemma_helper_03 ctr

val pow2_bitweight_lemma_1: ctr:pos -> Lemma
  (pow2 (bitweight templ (ctr+norm_length-1)) =
   pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length))
let rec pow2_bitweight_lemma_1 ctr =
//admit(); // OK
  match ctr with
  | 1 -> ()
  | _ -> 
    lemma_helper_00 ctr;
    pow2_bitweight_lemma_1 (ctr-1);
    lemma_helper_01 ctr;
    bitweight_def templ (ctr+norm_length-2);
    Math.Lemmas.pow2_plus 51 (bitweight templ (ctr+norm_length-2)); 
    lemma_helper_04 ctr

val bitweight_norm_length_lemma: unit ->
  Lemma (requires True)
	(ensures (bitweight templ norm_length = 255))
	[SMTPat (bitweight templ norm_length)]
let bitweight_norm_length_lemma () = 
  assert_norm (bitweight templ norm_length = 255)

val lemma_helper_10: h0:heap -> b:bigint_wide{live h0 b (* /\ length b >= 2*norm_length-1 *)} -> ctr:pos{length b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma
  ( ctr+norm_length = norm_length+ctr 
    /\ (norm_length+1+ctr)-1 = norm_length + ctr 
    /\ norm_length+ctr = (ctr+1)+norm_length-1 
    /\ eval_wide h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (ctr+norm_length))
let lemma_helper_10 h0 b ctr = 
//admit(); // OK
  eval_wide_def h0 b (norm_length+1+ctr)

val lemma_helper_11: h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b /\ (* length b >= 2 * norm_length - 1 /\ *) length b = length b} -> ctr:pos{length b >= ctr + norm_length + 1 /\ctr < norm_length-1} -> prime:pos -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (get h1 b i))} (i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i))
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 19 * v (get h0 b (ctr+norm_length))
      /\ eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime
      /\ eval_wide h0 b (norm_length+ctr) - eval_wide h0 b (ctr+1) = eval_wide h1 b (norm_length+ctr) - eval_wide h1 b (ctr+1)
      /\ eval_wide h0 b ctr = eval_wide h1 b ctr))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % prime = eval_wide h1 b (norm_length+ctr) % prime))
let lemma_helper_11 h0 h1 b ctr prime = 
//admit(); // OK
  eval_wide_def h0 b (norm_length+1+ctr);
  Math.Lemmas.distributivity_add_right (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (19 * v (get h0 b (norm_length+ctr)));
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime);
  Math.Lemmas.paren_mul_right 19 (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr)));
  cut (19 * v (get h0 b (ctr+norm_length)) = v (get h1 b ctr) - v (get h0 b ctr));
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * (v (get h1 b ctr) - v (get h0 b ctr)) + eval_wide h0 b (norm_length+ctr)) % prime);
  Math.Lemmas.distributivity_sub_right (pow2 (bitweight templ ctr)) (v (get h1 b ctr)) (v (get h0 b ctr));
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (get h1 b ctr) - pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval_wide h0 b (norm_length+ctr)) % prime);
  eval_wide_def h0 b (ctr+1);
  eval_wide_def h1 b (ctr+1);
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = (pow2 (bitweight templ ctr) * v (get h1 b ctr) - pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval_wide h1 b (norm_length+ctr) - eval_wide h1 b (ctr+1) + eval_wide h0 b (ctr+1)) % prime)

val freduce_degree_lemma_2:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ length b >= 2 * norm_length - 1 *) /\ length b = length b} -> ctr:pos{length b >= ctr + norm_length + 1 /\ ctr < norm_length-1} -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 19 * v (get h0 b (ctr+norm_length))
    ))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % (reveal prime) = eval_wide h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma_2 h0 h1 b ctr = 
  admit(); // OK?
  let prime = reveal prime in
  eval_wide_def h0 b (norm_length+1+ctr); 
  (* cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); *)
  (* cut (eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length));  *)
  lemma_helper_10 h0 b ctr;
  pow2_bitweight_lemma_1 (ctr+1); 
  lemma_helper_02 norm_length ctr;
  bitweight_norm_length_lemma (); 
  Math.Lemmas.pow2_plus 255 (bitweight templ ctr);
  (* cut(pow2 (bitweight templ (norm_length+ctr)) = pow2 255 * pow2 (bitweight templ ctr));  *)
  Math.Lemmas.paren_mul_left (pow2 255) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr)));
  Math.Lemmas.paren_mul_right (pow2 255) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr)));
  cut (eval_wide h0 b (norm_length+1+ctr) = (pow2 255 * pow2 (bitweight templ ctr)) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr));
  (* ModuloLemmas.helper_lemma_5 (pow2 255) (pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) (eval_wide h0 b (norm_length+ctr)) prime;  *)
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = ((pow2 255 % prime) * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime);
  prime_modulo_lemma (); 
  cut (eval_wide h0 b (norm_length+1+ctr) % prime = (19 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval_wide h0 b (norm_length+ctr)) % prime);
  (* eval_eq_lemma h0 h1 b b ctr;  *)
  eval_wide_def h0 b (ctr+1);
  eval_wide_def h1 b (ctr+1);
  (* cut (eval_wide h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval_wide h0 b ctr); *)
  (* cut (eval_wide h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (get h0 b ctr) + 19 * v (get h0 b (norm_length+ctr))) + eval_wide h0 b ctr);  *)
  Math.Lemmas.distributivity_add_right (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (19 * v (get h0 b (norm_length+ctr)));
  (* eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr); *)
  lemma_helper_11 h0 h1 b ctr prime


val freduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint_wide{live h1 b /\ live h0 b (* /\ length b >= 2 * norm_length - 1 *) /\ length b = length b} -> ctr:nat{length b >= ctr+norm_length+1 /\ ctr < norm_length-1} -> Lemma
    (requires (
      (forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 19 * v (get h0 b (ctr+norm_length))
    ))
    (ensures (eval_wide h0 b (norm_length+1+ctr) % (reveal prime) = eval_wide h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma h0 h1 b ctr =
  admit(); // OK?
  let prime = reveal prime in
  if ctr = 0 then (
    eval_wide_def h0 b (norm_length+1);
    assert(eval_wide h0 b (norm_length+1) = pow2 (bitweight templ norm_length) * v (get h0 b norm_length) + eval_wide h0 b norm_length); 
    assert(eval_wide h0 b (norm_length+1) = pow2 255 * v (get h0 b norm_length) + eval_wide h0 b norm_length);
    (* ModuloLemmas.helper_lemma_5 (pow2 255) (v (get h0 b norm_length)) (eval_wide h0 b norm_length) prime; *)
    assert(eval_wide h0 b (norm_length+1) % prime = ((pow2 255 % prime) * v (get h0 b norm_length) + eval_wide h0 b norm_length) % prime); 
    prime_modulo_lemma ();
    assert(eval_wide h0 b (norm_length+1) % prime = (19 * v (get h0 b norm_length) + eval_wide h0 b norm_length) % prime);
    cut(eval_wide h0 b 1 = v (get h0 b 0) /\ eval_wide h1 b 1 = v (get h0 b 0) + 19 * v (get h0 b norm_length)); 
    (* eval_partial_eq_lemma h0 h1 b b 1 norm_length; *)
    cut(eval_wide h1 b norm_length - eval_wide h1 b 1 = eval_wide h0 b norm_length - eval_wide h0 b 1)
  ) else
    freduce_degree_lemma_2 h0 h1 b ctr


val freduce_degree': b:bigint_wide -> ctr:u32{w ctr < norm_length - 1} -> Stack unit
    (requires (fun h -> reducible' h b (w ctr))) 
    (ensures (fun h0 _ h1 -> untouched' h0 h1 b (w ctr) /\ times19' h0 h1 b (w ctr)
      /\ eval_wide h1 b (norm_length) % reveal prime = eval_wide h0 b (norm_length+1+w ctr) % reveal prime
      /\ modifies_1 b h0 h1))
let rec freduce_degree' b ctr' =
  admit(); // OK?
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
    cut (eval_wide h0 b (norm_length+1+0) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime);
    cut (eval_wide h0 b (norm_length+1) % reveal prime = eval_wide h1 b (norm_length+0) % reveal prime)
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
    cut (eval_wide h0 b (norm_length+1+w ctr) % reveal prime = eval_wide h1 b (norm_length+w ctr) % reveal prime);
    cut(reducible' h1 b (w ctr-1)); 
    freduce_degree' b (ctr-|1ul); 
    let h2 = HST.get() in 
    cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > w ctr /\ i < 2*norm_length-1) ==>
	   v (get h1 b i) = v (get h0 b i)); 
    cut(untouched' h0 h2 b (w ctr));
    cut (times19' h0 h2 b (w ctr)) 
  end

val aux_lemma_4: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ satisfies_modulo_constraints h b))
  (ensures (reducible' h b (norm_length-2)))
let aux_lemma_4 h b = 
  let max = maxValue_wide h b (length b) in
  maxValue_wide_lemma h b;
  Math.Lemmas.pow2_lt_compat platform_wide (platform_wide-1)

val aux_lemma_5: h0:heap -> h1:heap -> b:bigint_wide -> Lemma
  (requires (live h0 b /\ satisfies_modulo_constraints h0 b /\ times19' h0 h1 b (norm_length-2)
      /\ untouched' h0 h1 b (norm_length-2)))
  (ensures (live h0 b /\ satisfies_modulo_constraints h0 b /\ times19' h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (get h1 b i) < pow2 (platform_wide-1))))
let aux_lemma_5 h0 h1 b = 
  let max = maxValue_wide h0 b (length b) in
  maxValue_wide_lemma h0 b;
  cut (forall (i:nat). i < norm_length-1 ==> v (get h1 b i) = v (get h0 b i) + 19 * v (get h0 b (i+norm_length)) )


val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> live h b /\ satisfies_modulo_constraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfies_modulo_constraints h0 b
    /\ length b >= 2*norm_length - 1
    /\ length b = length b /\ modifies_1 b h0 h1 /\ length b >= norm_length+1
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> 
	v (get h1 b i) < pow2 (platform_wide - 1))
    /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
  let h0 = HST.get() in
  aux_lemma_4 h0 b; 
  freduce_degree' b (nlength-|2ul); 
  let h1 = HST.get() in
  aux_lemma_5 h0 h1 b


val pow2_bitweight_lemma: ctr:nat -> Lemma
  (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr))
let pow2_bitweight_lemma ctr =
  bitweight_def templ ctr;
  Math.Lemmas.pow2_plus (bitweight templ ctr) (templ ctr)

#set-options "--z3rlimit 60"

(* TODO: Move to Curve.Bigint *)
val eval_wide_eq_lemma: ha:heap -> hb:heap -> a:bigint_wide{live ha a} -> b:bigint_wide{live hb b} ->
  len:nat{ (len <= length a) /\ (len <= length b) } -> Lemma
    (requires ( (forall (i:nat). i < len ==> v (get ha a i) = v (get hb b i)) ))
    (ensures ( eval_wide ha a len = eval_wide hb b len ))
let rec eval_wide_eq_lemma ha hb a b len =
  match len with
  | 0 -> ()
  | _ -> eval_wide_eq_lemma ha hb a b (len-1)

val eval_wide_partial_eq_lemma: ha:heap -> hb:heap -> a:bigint_wide{live ha a} -> b:bigint_wide{live hb b} ->
  ctr:nat -> len:nat{ ctr <= len /\ len <= length a /\ len <= length b} -> Lemma
    (requires (live ha a /\ live hb b
      /\ (forall (i:nat). i < len-ctr ==> get ha a (ctr+i) = get hb b (ctr+i)) ))
    (ensures ( eval_wide ha a len - eval_wide ha a ctr = eval_wide hb b len - eval_wide hb b ctr ))
let rec eval_wide_partial_eq_lemma ha hb a b ctr len =
  if len = ctr then ()
  else
    begin
      eval_wide_def ha a len;
      eval_wide_def hb b len;
      eval_wide_partial_eq_lemma ha hb a b ctr (len-1)
    end

#set-options "--z3rlimit 30"


val eval_carry_lemma: ha:heap -> a:bigint_wide{live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint_wide{live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> Lemma
    (requires (
      v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i))
    ))
    (ensures (eval_wide hb b (norm_length+1) = eval_wide ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr =
  admit(); // OK?
  eval_wide_eq_lemma ha hb a b ctr;
  assert(eval_wide ha a ctr = eval_wide hb b ctr);
  eval_wide_def ha a (ctr+2);
  eval_wide_def ha a (ctr+1);
  eval_wide_def hb b (ctr+2);
  eval_wide_def hb b (ctr+1);
  (* ModuloLemmas.helper_lemma_0 ctr; ModuloLemmas.helper_lemma_1 ctr; *)
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + eval_wide hb b (ctr+1)); 
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (get hb b ctr) + eval_wide hb b ctr));  
  assert(eval_wide hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr)); 
  Math.Lemmas.distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (get ha a (ctr+1))) (v (get ha a ctr) / pow2 (templ ctr));
  cut(eval_wide hb b (ctr+2) =
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr)); 
  pow2_bitweight_lemma ctr; 
  cut(eval_wide hb b (ctr+2) =
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval_wide hb b ctr));  
  (* ModuloLemmas.helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (get ha a ctr)) (eval_wide hb b ctr);  *)
  cut(eval_wide hb b (ctr+2) =
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (get ha a ctr) + eval_wide hb b ctr));  
  cut(eval_wide hb b (ctr+2) = eval_wide ha a (ctr+2));
  eval_wide_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1)
  (* ModuloLemmas.helper_lemma_3 (eval_wide ha a (norm_length+1)) (eval_wide hb b (norm_length+1)) (eval_wide ha a (ctr+2)) (eval_wide hb b (ctr+2)) *)


val auxiliary_lemma_1: bip1:u128 -> c:u128 -> Lemma
    (requires (v bip1 < pow2 (platform_wide - 1) /\ v c < pow2 (platform_wide - 51)))
    (ensures  (v bip1 + v c < pow2 platform_wide))
let auxiliary_lemma_1 bip1 c =
  assert_norm (platform_wide - 51 < platform_wide - 1);
  Math.Lemmas.pow2_lt_compat (platform_wide - 1) (platform_wide - 51);
  Math.Lemmas.pow2_double_sum (platform_wide - 1)


// The encoding needs to depend on the bitwise encoding
val mod2_51: a:u128 -> Tot (b:u128{v b = v a % pow2 51})
let mod2_51 a =
  admit ();
  assert_norm (51 < pow2 32);
  let mask = (U128.of_string "1") |<< 51ul in
  cut (v mask = pow2 51 % pow2 platform_wide /\ pow2 51 >= 1);
  Math.Lemmas.pow2_lt_compat platform_wide 51; 
  Math.Lemmas.modulo_lemma (pow2 51) (pow2 platform_wide);
  let mask = U128.sub mask (U128.of_string "1") in
  let res = a |& mask in
  (* log_and_wide_lemma_3 a mask 51; *)
  res

abstract type carriable (h:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))}
      (i > ctr /\ i <= norm_length) ==> v (get h b i) < pow2 (platform_wide - 1))

abstract type carried (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (get h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h1 b norm_length) < pow2 77)

abstract type carried' (h1:heap) (b:bigint_wide) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= ctr /\ i < norm_length) ==> v (get h1 b i) < pow2 (templ ctr))
  /\ v (get h1 b norm_length) < pow2 77

abstract type untouched_2 (h0:heap) (h1:heap) (b:bigint_wide) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= norm_length+1 /\ length b = length b
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (get h0 b i) = v (get h1 b i))

val carry:
  b:bigint_wide -> ctr:u32{w ctr <= norm_length} -> Stack unit
    (requires (fun h -> carriable h b (w ctr) /\ carried h b (w ctr)))
    (ensures (fun h0 _ h1 -> carried h1 b norm_length /\ untouched_2 h0 h1 b (w ctr)
      /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1)
      /\ modifies_1 b h0 h1))
let rec carry b i =
  //admit(); // OK
  let h0 = HST.get() in
  if U32.eq i nlength then ()
  else begin
    let bi = index b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ (w i))); 
    b.(i) <- ri;
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b i ri;  *)
    assert (forall (j:nat). {:pattern (v (get h1 b (w i)))}
      (j > w i /\ j <= norm_length) ==> v (get h1 b j) == v (get h0 b j));
    assert (carriable h1 b (w i));
    assert_norm (51 < pow2 32);
    let c = (bi |>> 51ul) in
    // In the spec of >>
    admitP(v c < pow2 (platform_wide - 51));
    let bip1 = index b (i+|1ul) in
    assert(v bip1 = v (get h1 b (w i+1)));
    assert(v bip1 < pow2 (platform_wide - 1));
    auxiliary_lemma_1 bip1 c;
    let z = bip1 |+ c in
    upd b (i+|1ul) z;
    let h2 = HST.get() in
    (* upd_lemma h1 h2 b (i+|1ul) z;  *)
    eval_carry_lemma h0 b h2 b (w i); 
    cut (forall (j:nat). (j > w i+1 /\ j <= norm_length) ==> v (get h2 b j) < pow2 (platform_wide - 1));
    carry b (i+|1ul)
  end


val carry_top_to_0: b:bigint_wide -> Stack unit
    (requires (fun h -> carried h b norm_length /\ length b >= norm_length+1
      /\ v (get h b 0) + 19 * v (get h b norm_length) < pow2 (platform_wide-1)))
    (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carried' h1 b 1
      /\ eval_wide h1 b norm_length % (reveal prime) = eval_wide h0 b (norm_length+1) % (reveal prime)
      /\ v (get h1 b 0) = v (get h0 b 0) + 19 * v (get h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (get h1 b i) = v (get h0 b i)) ))
let carry_top_to_0 b =
//  admit(); // OK
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in 
  let btop_19 = times_19 btop in  
  upd b 0ul (b0 |+ btop_19); 
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0


abstract type carriable2 (h:heap) (b:bigint_wide) (ctr:nat{ctr<=norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < ctr ==> v (get h b i) < pow2 51)
  /\ (forall (i:nat). {:pattern (v (get h b i))} (i > ctr /\ i < norm_length) ==> v (get h b i) < pow2 51)
  /\ (ctr < norm_length ==> v (get h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h b norm_length) < 2)
  /\ v (get h b ctr) < pow2 51 + pow2 32
  /\ (v (get h b ctr) >= pow2 51 ==> (
      forall (i:nat). {:pattern (v (get h b i))} (i < ctr /\ i > 0) ==> v (get h b i) < pow2 32))
  /\ ((ctr = norm_length /\ v (get h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (get h b i))} (i > 0 /\ i < norm_length) ==> v (get h b i) < pow2 32))

val helper_lemma_20: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 32))
  (ensures (v a + v b < pow2 52 /\ (v a + v b) / pow2 51 < 2 /\
    (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 32) ))
let helper_lemma_20 a b =
  Math.Lemmas.pow2_plus 51 32;
  Math.Lemmas.pow2_lt_compat 51 32;
  Math.Lemmas.pow2_minus 52 51;
  assert_norm (52 - 51 = 1);
  assert_norm (pow2 1 = 2)

val helper_lemma_21: a:u128 -> Lemma
  (requires (v a < pow2 51 + pow2 32))
  (ensures (v a < pow2 52 /\ v a / pow2 51 < 2))
let helper_lemma_21 a = 
  Math.Lemmas.pow2_double_sum 51;
  Math.Lemmas.pow2_le_compat 51 32

val carry2: b:bigint_wide -> ctr:u32{w ctr <= norm_length} -> Stack unit
  (requires (fun h -> carriable2 h b (w ctr)))
  (ensures (fun h0 _ h1 -> carriable2 h0 b (w ctr) /\ carriable2 h1 b norm_length
    /\ eval_wide h1 b (norm_length+1) = eval_wide h0 b (norm_length+1)
    /\ modifies_1 b h0 h1))
let rec carry2 b i = 
  //admit(); // OK
  let h0 = HST.get() in
  if U32.eq i nlength then ()
  else begin
    let bi = index b i in
    let ri = mod2_51 bi in
    assert(v ri < pow2 (templ (w i))); 
    b.(i) <- ri;
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b i ri;  *)
    assert (forall (j:nat). {:pattern (v (get h1 b j))}
      (0 < j /\ j <> w i /\ j <= norm_length) ==> v (get h1 b j) == v (get h0 b j));
    let bip1 = index b (i+|1ul) in
    assert_norm (51 < pow2 32);
    let c = (bi |>> 51ul) in
    admitP(v c < pow2 (platform_wide - 51));
    assert (v bip1 = v (get h1 b (w i+1)));
    Math.Lemmas.pow2_lt_compat (platform_wide-1) 51;
    assert (v bip1 < pow2 (platform_wide - 1));
    helper_lemma_21 bi;
    helper_lemma_20 bip1 c; 
    (* // In the spec of >> *)
    auxiliary_lemma_1 bip1 c;
    let z = bip1 |+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51); 
    cut (v z >= pow2 51 ==> v c = 1); 
    cut (v c > 0 ==> v (get h0 b (w i)) / (pow2 51) > 0 ==> v (get h0 b (w i)) >= pow2 51); 
    cut (v z >= pow2 51 ==> v (get h1 b (w i)) < pow2 32); 
    b.(i+|1ul) <- z;
    let h2 = HST.get() in
    (* upd_lemma h1 h2 b (i+|1ul) z;  *)
    cut (v z >= pow2 51 ==> v c = 1);
    eval_carry_lemma h0 b h2 b (w i);
    carry2 b (i+|1ul)
  end


val helper_lemma_30: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 37))
  (ensures (v a + v b < pow2 52 /\ (v a + v b) / pow2 51 < 2
	    /\ (v a + v b >= pow2 51 ==> (v a + v b) % pow2 51 < pow2 37) ))
let helper_lemma_30 a b =
  Math.Lemmas.pow2_plus 51 37;
  Math.Lemmas.pow2_lt_compat 51 37;
  Math.Lemmas.pow2_minus 52 51;
  assert_norm (52 - 51 = 1);
  assert_norm (pow2 1 = 2)

val helper_lemma_32: a:u128 -> Lemma
  (requires (v a < pow2 52))
  (ensures  (v a / pow2 51 = 1 ==> v a >= pow2 51))
let helper_lemma_32 a =
  Math.Lemmas.pow2_double_sum 51

val helper_lemma_33: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < 2 /\ (v b = 1 ==> v a < pow2 32)))
  (ensures (v a + v b < pow2 51))
let helper_lemma_33 a b =
  Math.Lemmas.pow2_lt_compat 51 33;
  Math.Lemmas.pow2_double_sum 26

val last_carry: b:bigint_wide -> Stack unit
  (requires (fun h -> carriable2 h b norm_length))
  (ensures (fun h0 _ h1 -> carriable2 h0 b norm_length /\ norm_wide h1 b
    /\ eval_wide h1 b norm_length % reveal prime ==
      eval_wide h0 b (norm_length+1) % reveal prime
    /\ modifies_1 b h0 h1))
let last_carry b =
  admit(); // OK?
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in
  assert (v b0 == v (get h0 b 0));
  assert (v btop == v (get h0 b norm_length));
  cut (v b0 < pow2 51 /\ v btop < 2);
  pow2_5_lemma ();
  cut (19 * v btop < pow2 5);
  Math.Lemmas.pow2_lt_compat 51 5;
  Math.Lemmas.pow2_double_sum 51;
  Math.Lemmas.pow2_lt_compat platform_wide 52;
  Math.Lemmas.pow2_lt_compat platform_wide 51;
  cut (v b0 + 19 * v btop < pow2 52);
  let btop_19 = times_19 btop in  
  let bi = (b0 |+ btop_19) in
  (* upd_wide b 0 (b0 |+ btop_19);  *)
  b.(0ul) <- bi;
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0; 
  b.(nlength) <- U128.of_string "0";
  let h2 = HST.get() in
  eval_wide_eq_lemma h1 h2 b b norm_length;
  //cut (eval_wide h2 b (norm_length+1) = eval_wide h1 b norm_length);
  (* let bi = index b 0 in  *)
  let ri = mod2_51 bi in
  b.(0ul) <- ri;
  let h3 = HST.get() in
  let c = (bi |>> 51ul) in 
  Math.Lemmas.pow2_plus 32 5;
  cut (v bi < pow2 51 + 19);
  cut (v bi >= pow2 51 ==> v (get h3 b 1) < pow2 32); 
  helper_lemma_30 b0 btop_19; 
  helper_lemma_32 bi;
  let bip1 = index b 1ul in 
  cut (v bi >= pow2 51 ==> v bip1 < pow2 32); 
  cut (v c = 1 ==> v bip1 < pow2 32); 
  cut (v c = (v b0 + v btop_19) / pow2 51 /\ v bip1 < pow2 51); 
  helper_lemma_33 bip1 c; 
  let z = bip1 |+ c in 
  b.(1ul) <- z;
  let h4 = HST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (v (get h4 b 1) < pow2 51);
  cut (norm_wide h4 b)


val lemma_helper_40: h:heap -> b:bigint_wide -> Lemma
  (requires (live h b /\ length b >= norm_length + 1 /\ v (get h b norm_length) < pow2 77
	    /\ v (get h b 0) < pow2 51))
  (ensures (live h b /\ length b >= norm_length + 1 
    /\ v (get h b 0) + 19 * v (get h b norm_length) < pow2 (platform_wide - 1)
    /\ v (get h b 0) + 19 * v (get h b norm_length) < pow2 83))
let lemma_helper_40 h b = 
  pow2_5_lemma ();
  Math.Lemmas.pow2_plus 5 77;
  Math.Lemmas.pow2_lt_compat 82 51;
  Math.Lemmas.pow2_lt_compat (platform_wide-1) 83;
  Math.Lemmas.pow2_double_sum 82

val lemma_helper_41: a:u128 -> Lemma
  (requires (v a < pow2 83))
  (ensures  (v a / pow2 51 < pow2 32))
let lemma_helper_41 a =
  assert_norm ((pow2 83 - 1) / pow2 51 < pow2 32);
  admit () // TODO

val lemma_helper_42: a:u128 -> b:u128 -> Lemma
  (requires (v a < pow2 51 /\ v b < pow2 32))
  (ensures (v a + v b < pow2 52 /\ v a + v b < pow2 platform_wide))
let lemma_helper_42 a b =
  Math.Lemmas.pow2_lt_compat platform_wide 52;
  Math.Lemmas.pow2_lt_compat 51 32

val freduce_coefficients: b:bigint_wide -> ST unit
  (requires (fun h -> carriable h b 0))
  (ensures (fun h0 _ h1 -> carriable h0 b 0 /\ norm_wide h1 b
    /\ eval_wide h1 b norm_length % reveal prime = eval_wide h0 b norm_length % reveal prime))
let freduce_coefficients b =
  admit(); // TODO
  let h = HST.get() in
  b.(nlength) <- (U128.of_string "0");
  let h' = HST.get() in
  eval_wide_eq_lemma h h' b b norm_length;
  eval_wide_def h' b (norm_length+1);
  //cut (eval_wide h' b (norm_length+1) = eval_wide h b norm_length);
  carry b 0ul;
  let h = HST.get() in
  lemma_helper_40 h b;
  carry_top_to_0 b;
  let h1 = HST.get() in
  b.(nlength) <- U128.of_string "0";
  let h2 = HST.get() in
  eval_wide_eq_lemma h1 h2 b b norm_length;
  eval_wide_def h2 b (norm_length+1);
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let r0 = mod2_51 b0 in
  let c0 = b0 |>> 51ul in
  lemma_helper_41 b0; 
  lemma_helper_42 b1 c0;
  let h = HST.get() in
  b.(0ul) <- r0;
  b.(1ul) <- (b1 |+ c0);
  let h' = HST.get() in
  eval_carry_lemma h b h' b 0; 
  carry2 b 1ul; 
  last_carry b


val addition_lemma: a:u64 -> m:nat -> b:u64 -> n:nat -> Lemma
  (requires (vv a < pow2 m /\ vv b < pow2 n))
  (ensures  (vv a + vv b <  pow2 (max m n + 1)))
let addition_lemma a m b n =
  if max m n = m then
    begin
    Math.Lemmas.pow2_le_compat m n;
    Math.Lemmas.pow2_double_mult m
    end
  else
    begin
    Math.Lemmas.pow2_le_compat n m;
    Math.Lemmas.pow2_double_mult n
    end

val aux_lemma_1: unit -> Lemma (pow2 52 - 2 >= pow2 51 /\ pow2 52 - 38 >= pow2 51)
let aux_lemma_1 () =
  assert_norm (pow2 52 - 2 >= pow2 51 && pow2 52 - 38 >= pow2 51)


val add_big_zero_core: b:bigint -> ST unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ live h1 b /\ length b = length b
			 /\ filled h1 b
			 /\ vv (get h1 b 0) = vv (get h0 b 0) + (pow2 52 - 38)
			 /\ vv (get h1 b 1) = vv (get h0 b 1) + (pow2 52 - 2)
			 /\ vv (get h1 b 2) = vv (get h0 b 2) + (pow2 52 - 2)
			 /\ vv (get h1 b 3) = vv (get h0 b 3) + (pow2 52 - 2)
			 /\ vv (get h1 b 4) = vv (get h0 b 4) + (pow2 52 - 2)
			 /\ modifies_1 b h0 h1))
let add_big_zero_core b =
  admit (); // OK?
  let h0 = HST.get() in
  let two52m38 = 0xfffffffffffdauL in // pow2 52 - 38
  let two52m2 = 0xffffffffffffeuL in // pow2 52 - 2
  admitP(vv two52m38 = pow2 52 - 38 /\ vv two52m2 = pow2 52 - 2);
  let b0 = index b 0ul in 
  cut(vv b0 = vv (get h0 b 0));
  cut(forall (i:nat). {:pattern (vv (get h0 b i))} i < norm_length ==> (vv (get h0 b i)) < pow2 (templ i)); 
  cut(forall (i:nat). i < norm_length ==> vv (get h0 b i) < pow2 (templ i)); 
  cut (vv b0 < pow2 51 /\ vv two52m38 < pow2 52); 
  addition_lemma b0 51 two52m38 52;
  Math.Lemmas.pow2_lt_compat platform_size 53; 
  b.(0ul) <- (U64.add b0 two52m38);
  let h1 = HST.get() in
  (* upd_lemma h0 h1 b 0ul (U64.add b0 two52m38);  *)
  let b1 = index b 1ul in
  cut (vv b1 = vv (get h0 b 1) /\ vv b1 < pow2 51 /\ vv two52m2 < pow2 52); 
  addition_lemma b1 51 two52m2 52;
  Math.Lemmas.pow2_lt_compat platform_size 53; 
  b.(1ul) <- (U64.add b1 two52m2);
  let h2 = HST.get() in
  (* upd_lemma h1 h2 b 1ul (U64.add b1 two52m2);  *)
  let b2 = index b 2ul in
  cut (vv b2 = vv (get h1 b 2) /\ vv (get h1 b 2) = vv (get h0 b 2) /\ vv b2 < pow2 51);
  addition_lemma b2 51 two52m2 52;
  Math.Lemmas.pow2_lt_compat platform_size 53; 
  b.(2ul) <- (U64.add b2 two52m2);
  let h3 = HST.get() in
  (* upd_lemma h2 h3 b 2ul (U64.add b2 two52m2);  *)
  let b3 = index b 3ul in
  cut (vv b3 = vv (get h2 b 3) /\ vv (get h2 b 3) = vv (get h1 b 3) /\ vv (get h1 b 3) = vv (get h0 b 3) /\ vv b3 < pow2 51);
  addition_lemma b3 51 two52m2 52;
  Math.Lemmas.pow2_lt_compat platform_size 53; 
  b.(3ul) <- (U64.add b3 two52m2);
  let h4 = HST.get() in
  (* upd_lemma h3 h4 b 3ul (U64.add b3 two52m2);  *)
  let b4 = index b 4ul in
  cut (vv b4 = vv (get h3 b 4) /\ vv (get h3 b 4) = vv (get h2 b 4) /\ vv (get h2 b 4) = vv (get h1 b 4) /\ vv (get h1 b 4) = vv (get h0 b 4) /\ vv b4 < pow2 51);
  addition_lemma b4 51 two52m2 52;
  Math.Lemmas.pow2_lt_compat platform_size 53; 
  b.(4ul) <- (U64.add b4 two52m2);
  let h5 = HST.get() in 
  (* upd_lemma h4 h5 b 4ul (U64.add b4 two52m2); *)
  cut (vv (get h5 b 0) = vv (get h0 b 0) + (pow2 52 - 38));
  cut (vv (get h5 b 1) = vv (get h0 b 1) + (pow2 52 - 2));
  cut (vv (get h5 b 2) = vv (get h0 b 2) + (pow2 52 - 2));
  cut (vv (get h5 b 3) = vv (get h0 b 3) + (pow2 52 - 2));
  cut (vv (get h5 b 4) = vv (get h0 b 4) + (pow2 52 - 2));
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) < pow2 ndiff);  *)
  aux_lemma_1 (); 
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) >= pow2 ndiff');  *)
  cut (norm_length = 5);
  cut (filled h5 b)


val aux_lemma_2: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (pow2 204 * (a + (pow2 52 - 2)) 
       + pow2 153 * (b + (pow2 52 - 2)) 
       + pow2 102 * (c + (pow2 52 - 2))
       + pow2 51  * (d + (pow2 52 - 2)) + 
	 pow2 0   * (e + (pow2 52 - 38)) ==
	 pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 256 - 38)
let aux_lemma_2 a b c d e =
  assert_norm (pow2 204 * (a + (pow2 52 - 2)) 
       + pow2 153 * (b + (pow2 52 - 2)) 
       + pow2 102 * (c + (pow2 52 - 2))
       + pow2 51  * (d + (pow2 52 - 2)) + 
	 pow2 0   * (e + (pow2 52 - 38)) ==
	 (pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e) + pow2 256 - 38)

val aux_lemma_3: a:int -> Lemma ((a + pow2 256 - 38) % reveal prime = a % reveal prime)
let aux_lemma_3 a =
  assert_norm ((a + pow2 256 - 38) % reveal prime = a % reveal prime)

val add_big_zero_lemma_aux: a:int -> a':int -> b:int -> b':int -> c:int -> c':int -> d:int -> d':int -> e:int -> e':int -> Lemma
  (requires (a == a' + b /\
	     b == b' + c /\
	     c == c' + d /\
	     d == d' + e /\
	     e == e'))
  (ensures (a == a' + b' + c' + d' + e'))
let add_big_zero_lemma_aux a a' b b' c c' d d' e e' = ()


val add_big_zero_lemma: h0:heap -> h1:heap -> b:bigint -> Lemma 
  (requires (norm h0 b /\ live h1 b /\ filled h1 b /\ 
	     vv (get h1 b 0) = vv (get h0 b 0) + (pow2 52 - 38) /\
	     vv (get h1 b 1) = vv (get h0 b 1) + (pow2 52 - 2) /\
	     vv (get h1 b 2) = vv (get h0 b 2) + (pow2 52 - 2) /\
	     vv (get h1 b 3) = vv (get h0 b 3) + (pow2 52 - 2) /\
	     vv (get h1 b 4) = vv (get h0 b 4) + (pow2 52 - 2) ))
  (ensures (norm h0 b /\ live h1 b /\
	    eval h1 b norm_length % reveal prime == 
	    eval h0 b norm_length % reveal prime))
let add_big_zero_lemma h0 h1 b =
  assert_norm (bitweight templ 0 == 0);
  assert_norm (bitweight templ 1 == 51);
  assert_norm (bitweight templ 2 == 102);
  assert_norm (bitweight templ 3 == 153);
  assert_norm (bitweight templ 4 == 204);
  eval_def h1 b norm_length;
  eval_def h1 b 4;
  eval_def h1 b 3;
  eval_def h1 b 2;
  eval_def h1 b 1;
  eval_def h1 b 0;
  assert (eval h1 b 1 == pow2 0 * (vv (get h0 b 0) + pow2 52 - 38));
  add_big_zero_lemma_aux
    (eval h1 b 5) (pow2 204 * (vv (get h0 b 4) + (pow2 52 - 2)))
    (eval h1 b 4) (pow2 153 * (vv (get h0 b 3) + (pow2 52 - 2)))
    (eval h1 b 3) (pow2 102 * (vv (get h0 b 2) + (pow2 52 - 2)))
    (eval h1 b 2) (pow2 51  * (vv (get h0 b 1) + (pow2 52 - 2)))
    (eval h1 b 1) (pow2 0   * (vv (get h0 b 0) + (pow2 52 - 38)));
  cut (eval h1 b norm_length ==
        pow2 204 * (vv (get h0 b 4) + (pow2 52 - 2))
      + pow2 153 * (vv (get h0 b 3) + (pow2 52 - 2)) 
      + pow2 102 * (vv (get h0 b 2) + (pow2 52 - 2)) 
      + pow2 51  * (vv (get h0 b 1) + (pow2 52 - 2))
      + pow2 0   * (vv (get h0 b 0) + (pow2 52 - 38)));
  eval_def h0 b norm_length;
  eval_def h0 b 4;
  eval_def h0 b 3;
  eval_def h0 b 2;
  eval_def h0 b 1;
  eval_def h0 b 0;
  assert (eval h0 b 1 == pow2 0 * (vv (get h0 b 0)));
  add_big_zero_lemma_aux
    (eval h0 b 5) (pow2 204 * vv (get h0 b 4))
    (eval h0 b 4) (pow2 153 * vv (get h0 b 3))
    (eval h0 b 3) (pow2 102 * vv (get h0 b 2))
    (eval h0 b 2) (pow2 51  * vv (get h0 b 1))
    (eval h0 b 1) (pow2 0   * vv (get h0 b 0));
  let a = pow2 204 * vv (get h0 b 4)
        + pow2 153 * vv (get h0 b 3)
        + pow2 102 * vv (get h0 b 2)
	+ pow2 51  * vv (get h0 b 1)
	+ pow2 0   * vv (get h0 b 0) in
  cut (eval h0 b norm_length == a);
  aux_lemma_2 (vv (get h0 b 4))
	     (vv (get h0 b 3))
	     (vv (get h0 b 2))
	     (vv (get h0 b 1))
	     (vv (get h0 b 0));
  cut (eval h1 b norm_length == a + pow2 256 - 38);
  aux_lemma_3 a


let add_big_zero b =
  let h0 = HST.get() in
  add_big_zero_core b;
  let h1 = HST.get() in
  add_big_zero_lemma h0 h1 b

(* Not verified *)
let normalize (b:bigint) =
  admit();
  let two51m1 = 0x7ffffffffffffuL in // pow2 51 - 1
  let two51m19 = 0x7ffffffffffeduL in // pow2 51 - 19
  let b4 = b.(4ul) in
  let b3 = b.(3ul) in
  let b2 = b.(2ul) in
  let b1 = b.(1ul) in
  let b0 = b.(0ul) in  
  let mask = U64.eq_mask b4 two51m1 in
  let mask = U64.logand mask (U64.eq_mask b3 two51m1) in
  let mask = U64.logand mask (U64.eq_mask b2 two51m1) in
  let mask = U64.logand mask (U64.eq_mask b1 two51m1) in
  let mask = U64.logand mask (U64.gte_mask b0 two51m19) in
  let sub_mask = U64.logand mask two51m1 in
  let sub_mask2 = U64.logand mask two51m19 in
  // Conditionally substract 2^255 - 19 
  b.(4ul) <- U64.sub b.(4ul) sub_mask;
  b.(3ul) <- U64.sub b.(3ul) sub_mask;
  b.(2ul) <- U64.sub b.(2ul) sub_mask;
  b.(1ul) <- U64.sub b.(1ul) sub_mask;
  b.(0ul) <- U64.sub b.(0ul) sub_mask2

val sum_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (norm h0 a /\ norm h0 b /\ live h1 cpy /\ length cpy >= 2*norm_length-1
	/\ (forall (i:nat).{:pattern (get h1 cpy i)} 
	    i < norm_length ==> v (get h1 cpy i) = vv (get h0 a i) + vv (get h0 b i))
        /\ (forall (i:nat).{:pattern (get h1 cpy i)} 
	    (i >= norm_length /\ i < length cpy) ==> v (get h1 cpy i) = 0)))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let sum_satisfies_constraints h0 h1 cpy a b =
  maxValue_bound_lemma_aux h0 a norm_length (pow2 51);
  maxValue_bound_lemma_aux h0 b norm_length (pow2 51);
  cut (maxValueNorm h0 a <= pow2 51);
  cut (maxValueNorm h0 b <= pow2 51);
  assert_norm (pow2 51 + pow2 51 == pow2 52);
  maxValue_wide_bound_lemma h1 cpy (pow2 52);
  assert_norm (pow2 52 * 20 < pow2 (platform_wide - 1))

private val le_trans: a:int -> b:int -> c:int -> d:int -> e:int -> Lemma 
  (requires a <= b /\ b <= c /\ c <= d /\ d * 20 < e)
  (ensures  a * 20 < e)
let le_trans a b c d e = ()

val mul_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (norm h0 a /\ norm h0 b /\ live h1 cpy /\ length cpy >= 2*norm_length-1
      /\ maxValue_wide h1 cpy (length cpy) <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let mul_satisfies_constraints h0 h1 cpy a b =
  //admit();
  maxValue_bound_lemma_aux h0 a norm_length (pow2 51);
  maxValue_bound_lemma_aux h0 b norm_length (pow2 51);
  cut (maxValueNorm h0 a <= pow2 51);
  cut (maxValueNorm h0 b <= pow2 51);
  cut (norm_length * maxValueNorm h0 a * maxValueNorm h0 b <= 5 * pow2 51 * pow2 51);
  assert_norm (5 * pow2 51 * pow2 51 <= pow2 105);
  assert_norm (pow2 105 * 20 < pow2 (platform_wide - 1));
  le_trans (maxValue_wide h1 cpy (length cpy)) 
	   (norm_length * maxValueNorm h0 a * maxValueNorm h0 b)
	   (5 * pow2 51 * pow2 51)
	   (pow2 105)
	   (pow2 (platform_wide - 1))
	   
val difference_satisfies_constraints: h0:heap -> h1:heap -> cpy:bigint_wide -> a:bigint -> b:bigint ->
  Lemma 
    (requires (filled h0 a /\ norm h0 b /\ live h1 cpy 
      /\ length cpy >= 2*norm_length-1
      /\ (forall (i:nat).{:pattern (get h1 cpy i)}
	  i < norm_length ==> v (get h1 cpy i) = vv (get h0 a i) - vv (get h0 b i))
      /\ (forall (i:nat).{:pattern (get h1 cpy i)}
	  (i >= norm_length /\ i < length cpy) ==> v (get h1 cpy i) = 0) ))
    (ensures (live h1 cpy /\ satisfies_modulo_constraints h1 cpy))
let difference_satisfies_constraints h0 h1 cpy a b =
  //admit();
  assert_norm (pow2 51 < pow2 53);
  maxValue_bound_lemma_aux h0 a norm_length (pow2 53);
  maxValue_bound_lemma_aux h0 b norm_length (pow2 51);
  cut (maxValueNorm h0 a <= pow2 53);
  cut (maxValueNorm h0 b <= pow2 51);
  maxValue_wide_bound_lemma h1 cpy (pow2 53);
  assert_norm (pow2 53 * 20 < pow2 (platform_wide - 1))

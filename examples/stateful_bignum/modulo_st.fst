module Modulo

open Heap
open ST
open Bigint
open Eval
open Shift
open Carry

(* The modulo pass goes as follows :
   1 - shift the modulus by several cells so that its length is 1 less than a
   2 - shift it by bits until it is bigger than the big int
   3 - then subtract the modulus shifted by 1 bit less and iterate step 2
   4 - when a < cell shifted modulus, iterate step 1 with a smaller shift
Probably required for size : 
  - Before each of steps 1, a carry
  - Align the sign of the modulus on the sign of a
 *)

(* Expected specification for the modulo operation *)
assume val modulo:
  a:bigint -> b:bigint -> 
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h b)
		/\ (Bigint63.t a = Bigint63.t b)
     ))
     (ensures (fun h0 r h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (getLength h1 a = getLength h0 b)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a) % eval h0 b (getLength h0 b))
     ))

let rec modulo_bit a modulus shift =
  (* Shift the modulus by "shift" bits *)
  let s = shift_over_by_bits modulus shift in
  (* If smaller than a iterate *)
  if Compare.compare2 a s > 0 then 
    modulo_bit a modulus (shift+1)
  else (
    (* Else if shift > 0 subtract modulus shifted by shift - 1 *)    
    if shift > 0 then (
      Substraction.substraction_with_lemma a (shift_over_by_bits modulus (shift-1)) (get_length a);
      modulo_bit a modulus 0
    )
    else 
      (* Else return, a smaller than the modulus shifted by this number of cells *)
      ()
  ) 

let rec modulo_cell a modulus offset =
  match offset with
  | 0 ->
     (* Align modulus on the sign of a *)
     let modulus = 
       if get a (get_length a - 1) >= 0 && get modulus (get_length modulus - 1) >= 0 then
	 modulus
       else Neg.neg modulus in
     (* Shift it bits by bits and subtract when required *)
     modulo_bit a modulus 0;
     (* a smaller than modulus, do final carry *)
     carry a;
     normalized_carry a
  | _ ->
     (* Align modulus on the sign of a *)
     let modulus = 
       if get a (get_length a - 1) >= 0 && get modulus (get_length modulus - 1) >= 0 then
	 modulus
       else Neg.neg modulus in
     (* Shift by offset cells *)
     let m = shift modulus offset in
     (* Shift and subtract bit by bit *)
     modulo_bit a m 0;
     (* Carry *)
     carry a;
     normalized_carry a;
     (* Iterate *)
     modulo_cell a modulus offset

(* A signed version of the modulo *)
let signed_modulo a modulus =
  (* Assume that the top cell of the modulus is not empty *)
  (* Assume that the modulus is positive *)
  normalized_carry a;
  normalized_carry modulus;
  let lmod = get_length modulus in
  let la = get_length a in
  if la < lmod then 
    (* Since we assume top cell of modulus not empty, |a| < |modulus| so return a *)
    Bigint.copy a
  else 
    let sign = Compare.compare2 a zero_bigint in
    let a = if sign = -1 then Neg.neg a else a in
    let b = Bigint.mk_zero_bigint (la + 1) (Bigint63.t a) in
    Array.blit (Bigint63.data a) 0 (Bigint63.data b) 0 la;
    modulo_cell b modulus (la - lmod);
    let c = Array.create lmod zero_tint in
    Array.blit (Bigint63.data b) 0 c 0 lmod;
    Bigint63.data b := !c;
    if sign = -1 then Neg.neg b else b

(* An unsigned version of the modulo *)
let unsigned_modulo a modulus =
  let b = signed_modulo a modulus in
  if Compare.compare b zero_bigint = -1 then (
    Addition.addition_with_lemma b modulus (get_length b);
    b)
  else b

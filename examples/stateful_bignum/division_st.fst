module Division

(* Implementation of the Algorithm D of Knuth : division of positive big integers *)
(* Work in progress :
   This implementation is not intended to be constant time, although we hope to be 
   hiding some information using masking in the implementations using the algorithm *)

open IntLib
open Heap
open ST
open Bigint

(* Computation of qh, step D3 of Knuth algorithm D *)
val test_qh : nat -> nat -> nat -> nat -> nat -> nat -> nat -> Tot nat
let rec test_qh qh v1 v2 uj ujp1 ujp2 radix =
  if v2*qh > (uj*radix + ujp1 - qh*v1)*radix + ujp2 then
    test_qh (qh-1) v1 v2 uj ujp1 ujp2 radix
  else qh

(* Returns the 2-complement of the bigint in input (inplace) *)
val two_complement:
  bigint -> nat -> nat ->
  ST unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec two_complement u idx len =
  match len with
  | 0 -> ()
  | _ ->
     let i = len - 1 in
     let ui = get u (idx+i) in
     (* let ci = IntLib.xor_op ui (pow2 (Bigint.Bigint63.t u 0) - 1) in *)
     let ci = ui + (pow2 (Bigint.Bigint63.t u i)) in
     Bigint.updateBigint u (idx+i) (Bigint.mk_tint u (erase 0) ci);
     two_complement u idx i

val is_negative :
  bigint -> nat ->
  ST bool
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec is_negative b len =
  match len with
  | 0 -> false
  | _ -> 
     let i = len - 1 in
     let bi = get b i in
     if bi > 0 then false
     else if bi < 0 then true
     else is_negative b i

(* Main loop of the division algorithm, steps D3 to D7 *)
val iterate :
  nat -> bigint -> bigint -> bigint -> nat -> nat -> nat ->
  ST unit
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec iterate j u v q m_n n radix =
  (* Used template and sub array *)
  let t = Bigint63.t u in

  let u = Carry.carry u in
  let v = Carry.carry v in
  Carry.normalized_carry u;
  Carry.normalized_carry v;
  let u = Bigint63 (Array.sub (Bigint.Bigint63.data u) 0 (m_n+1)) t in
  let v = Bigint63 (Array.sub (Bigint.Bigint63.data v) 0 n) t in

  let sub_u = Bigint63 (Array.sub (Bigint63.data u) (m_n-n-j) (n+1)) t in
  
  (* Compute ^q *)
  let uj = get sub_u n in
  let ujp1 = get sub_u (n-1) in
  let ujp2 = get sub_u (n-2) in
  let v1 = get v (n-1) in
  let v2 = get v (n-2) in
  let qh =
    if uj = v1 then radix - 1 
    else div (uj*radix + ujp1) v1 in
  let qh = test_qh qh v1 v2 uj ujp1 ujp2 radix in
  
  (* Multiply and subtract *)
  let borrow = ref false in

  let qhv = Bigint.mk_zero_bigint n t in
  ScalarMultiplication.scalar_multiplication_with_lemma qhv v radix qh n;
  Substraction.substraction_tr (erase (Array.to_seq (Bigint63.data u))) u (m_n-n-j) qhv 0 n 0;
  
  let sub_u = Bigint63 (Array.sub (Bigint63.data u) (m_n-n-j) (n+1)) t in

  let sub_u = Carry.carry sub_u in
  Carry.normalized_carry sub_u;
  
  if is_negative sub_u (get_length sub_u) then (
    borrow := true;
    (* two_complement u (m_n-n-j) (n+1)
    two_complement sub_u 0 (get_length sub_u);
    Array.blit (Bigint.Bigint63.data sub_u) 0 (Bigint.Bigint63.data u) (m_n-n-j) *)
    Bigint.updateBigint u (m_n-j) (Bigint.mk_tint u (erase 0) (get u (m_n-j) + (pow2 (t 0))))
  );
  
  (* Test remainder *)
  Bigint.updateBigint q j (Bigint.mk_tint q (erase 0) qh);
  
  if !borrow then (
    Bigint.updateBigint q j (Bigint.mk_tint q (erase 0) (Bigint.get q j - 1));
    Addition.addition_tr (erase (Array.to_seq (Bigint63.data u))) u (m_n-n-j+1) v 0 n 0;
    (* Get rid of the carry *)
    let u = Carry.carry u in
    let u = Bigint63 (Array.sub (Bigint63.data u) 0 (m_n+1)) t in
    Bigint.updateBigint u n (Bigint.mk_tint u (erase 0) (get u (m_n-j) - 1))
  );
  let j = j+1 in
  if j <= m_n - n then iterate j u v q m_n n radix
  else ()

val get_real_length :
  bigint -> nat ->
  ST nat
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec get_real_length a len = 
  if Bigint.get a (len-1) = 0 then get_real_length a (len-1)
  else len

val flip_aux :
  bigint -> bigint -> nat ->
  ST bigint
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let rec flip_aux q' q len =
  match len with
  | 0 -> q'
  | _ -> 
     let i = len - 1 in
     Bigint.updateBigint q' i (Array.index (Bigint.Bigint63.data q) (get_length q - 1 - i));
     flip_aux q' q i

val flip : 
  bigint -> 
  ST bigint
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let flip q =
  let q' = Bigint.mk_zero_bigint (get_length q) (Bigint63.t q) in
  flip_aux q' q (get_length q)

(* Assume a and b are all positive *)
(* Assume a and b have been normalized and have the same constant template *)
val division :
  bigint -> bigint ->
  ST bigint
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let division a b =
  (* Knuth's algorithm is explained in big endian *)
  (* Need be careful about the indexing (bigint is little endian) *)

  (* Template and radix for the division *)
  let t = Bigint63.t a in
  let radix = pow2 (t 0) in
  
  (* Format integers and compute concrete sizes (first non zero word) *)
  (* Real lengths must be non zero *)
  let a = Carry.carry a in
  let b = Carry.carry b in
  Carry.normalized_carry a;
  Carry.normalized_carry b;

  let neg_div = is_negative a (get_length a) in
  let a = if neg_div then Neg.neg a else a in
  
  (* a and b normalized, compute their concrete length *)
  let n = get_real_length b (get_length b) in
  let m_n = get_real_length a (get_length a) in

  (* If a smaller than b return immediately *)
  if m_n < n then (Bigint.mk_zero_bigint 1 t)
  else (    
    (* q will store the quotient *)
    let q = Bigint.mk_zero_bigint (m_n - n + 1) t in

    (* Normalization phase *)
    let d = div radix (Bigint.get b (n-1)+1) in
    let u = Bigint.mk_zero_bigint m_n t in
    let v = Bigint.mk_zero_bigint n t in

    (* Compute the normalized forms *)
    ScalarMultiplication.scalar_multiplication_with_lemma u a (t 0) d m_n;
    ScalarMultiplication.scalar_multiplication_with_lemma v b (t 0) d n;

    
    (* Initialize j *)
    let j = 0 in
    
    iterate j u v q m_n n radix;
    
    let q = flip q in
    
    if neg_div then Neg.neg q else q
  )
  
val modulo : 
  bigint -> bigint -> 
  ST bigint
    (requires (fun h -> True))
    (ensures (fun h0 _ h1 -> True))
let modulo a b =
  let len_a = get_length a in
  let len_b = get_length b in
  let len_r = len_b in
  let t = Bigint.Bigint63.t a in
  let q = division a b in
  let len_q = get_length q in
  let r = Bigint.copy a in
  let qb = Bigint.mk_zero_bigint (len_b + len_q - 1) t in
  Multiplication.multiplication2 qb b q;
  let qb = Carry.carry qb in
  let qb = Bigint.Bigint63 (Array.sub (Bigint.Bigint63.data qb) 0 (len_b+len_q-1)) t in
  Substraction.substraction_with_lemma r qb (len_b+len_q-1);
  let r = Carry.carry r in
  Carry.normalized_carry r;
  if is_negative r (get_length r) then (
    Addition.addition_with_lemma r b len_b;
    let r = Carry.carry r in
    Carry.normalized_carry r;
    Bigint.Bigint63 (Array.sub (Bigint.Bigint63.data r) 0 len_r) t
  ) else (
    Bigint.Bigint63 (Array.sub (Bigint.Bigint63.data r) 0 len_r) t
  )

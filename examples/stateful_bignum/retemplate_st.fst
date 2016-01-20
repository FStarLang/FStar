(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Retemplate --z3timeout 3000 --max_fuel 15 --max_ifuel 15 --initial_fuel 5 --initial_ifuel 5;
    variables:LIB=../../lib;
    other-files:$LIB/FStar.Classical.fst $LIB/FStar.FunctionalExtensionality.fst $LIB/FStar.Set.fsi $LIB/FStar.Heap.fst $LIB/FStar.ST.fst $LIB/FStar.All.fst $LIB/seq.fsi $LIB/FStar.SeqProperties.fst $LIB/FStar.Array.fst $LIB/FStar.Ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst eval_st.fst
  --*)

module Retemplate 

open IntLib
open FStar.Heap
open FStar.ST
open Eval
open Bigint
open Limb

assume val modulo_identity_lemma :
  a:int -> n:nat{ Bitsize a n } -> m:nat ->
  Lemma
    (requires (m >= n))
    (ensures (signed_modulo a (pow2 m) = a))

assume val modulo_of_multiple_lemma :
  a:int -> b:pos ->
  Lemma 
    (requires (True))
    (ensures ( (a*b) % b = 0 /\ (b*a) % b = 0 /\ signed_modulo (a*b) b = 0 /\ signed_modulo (b*a) b = 0))

#reset-options

assume val add_with_different_bit_domains :
  a:int -> n:nat{ Bitsize a n } -> b:int -> m:nat{ Bitsize b m } ->
  Lemma
    (requires (signed_modulo a (pow2 m) = 0))
    (ensures (Bitsize (a + b) n))

#reset-options
#set-options "--z3timeout 5"

(* TODO : not verified *)
(* Takes a value, a size and a bitweight and fill the array with that value *)
val fill_array : 
  b:bigint -> 
  ghost_b:bigint -> 
  v:int -> 
  tsize:pos{ tsize < ocaml63 /\ Bitsize v tsize } -> 
  bw:nat -> 
  len:nat -> 
  ST unit
     (requires (fun h -> 
       (inHeap h b)
       /\ (inHeap h ghost_b)
       /\ (getData ghost_b <> getData b)
       /\ (getLength h ghost_b = getLength h b)
       /\ (Normalized h b)
       /\ (Normalized h ghost_b)
       /\ (getLength h b > 0)
       /\ (len <= getLength h b)
       /\ (Bitsize (eval h ghost_b (getLength h ghost_b)) bw)
       /\ (bitweight (getTemplate b) (getLength h b) >= bw + tsize)
       /\ (bitweight (getTemplate b) len = 0 ==> eval h b (getLength h b) = eval h ghost_b (getLength h ghost_b))
       /\ (bitweight (getTemplate b) len > 0 ==> eval h b (getLength h b) = eval h ghost_b (getLength h ghost_b) + signed_modulo (pow2 bw * v) (pow2 (bitweight (getTemplate b) len)))
       /\ (getTemplate b = getTemplate ghost_b)
     ))
    (ensures (fun h0 u h1 ->
      (inHeap h0 b)
      /\ (inHeap h1 b)
      /\ (inHeap h0 ghost_b)
      /\ (getData ghost_b <> getData b)
      /\ (getLength h1 b = getLength h0 ghost_b)
      /\ (getLength h1 b = getLength h0 b)
      /\ (len <= getLength h0 b)
      /\ (getLength h0 b > 0)
      /\ (Normalized h0 ghost_b)
      /\ (Normalized h1 b)
      /\ (modifies !{getData b} h0 h1)
      /\ (Bitsize (eval h0 ghost_b (getLength h0 ghost_b)) bw)
      /\ (bitweight (getTemplate b) (getLength h0 b) >= bw + tsize)
      /\ (eval h1 b (getLength h1 b) = eval h0 ghost_b (getLength h0 ghost_b) + pow2 bw * v)
      /\ (Bitsize (eval h1 b (getLength h1 b)) (bw+tsize))
      /\ (getTemplate b = getTemplate ghost_b)
     ))
     
let rec fill_array b ghost_b v tsize bw len =
  match (get_length b - len) with
  | 0 -> 
     (
       let tb = getTemplate b in
       let h0 = ST.get() in
       modulo_of_multiple_lemma v (pow2 bw);
       size_of_mul_by_pow2_lemma tsize v bw;
       add_with_different_bit_domains
	 (pow2 bw * v) (bw+tsize)
	 (eval h0 ghost_b (getLength h0 ghost_b)) bw;
       cut (True /\ bitweight tb len > 0);
       modulo_identity_lemma (pow2 bw * v) (bw+tsize) (bitweight tb (getLength h0 b));
       cut (True /\ eval h0 b (getLength h0 b) = eval h0 ghost_b (getLength h0 ghost_b) + pow2 bw * v)
     )
  | _ ->
     let h0 = (ST.get()) in

     let tb = getTemplate b in

     (* Compute the bitweight and size of the cell to fit part of v in *)
     let bw2 = bitweight tb len in
     let tsize2 = tb len in
     (
       cut ( b2t (tsize2 < ocaml63) )
     );
       
     (* If v and the current cell overlap, then fill it *)
     if bw + tsize > bw2 && bw2 + tsize2 > bw then (
       
       (* Previous cell value *)
       let blen = get b len in
       
       (* Compute new value *)
       let v2 = 
	 if bw < bw2 then div_non_eucl v (pow2 (bw2 - bw))
         else (
	   let m = signed_modulo v (pow2 (bw2 + tsize2 - bw)) in
	   cut( True /\ Bitsize m (bw2 + tsize2 - bw));
	   Limb.shift_left (bw2 + tsize2 - bw) m (bw - bw2)
	 ) in
       
       (* Make it fit the new cell size *)
       let v3 = signed_modulo v2 (pow2 tsize2) in
       (* Add it to the existing content *)
       (* NB : in terms of bits, it should not overlap the existing value
	  ie v2 + b[len] == v2 xor b[len] *)
       let size_b_len = getSize h0 b len in
       let v2 = Limb.add tsize2 v3 size_b_len blen in
       
       (* TODO : PROOF *)
       admitP (True /\ signed_modulo v3 (pow2 size_b_len) = 0);
       add_with_different_bit_domains v3 tsize2 blen size_b_len;

       cut ( Bitsize v2 tsize2 /\ tsize2 < ocaml63 );
              
       let t2 = mk_tint b ((tsize2)) v2 in

       updateBigint b len t2;

       let h1 = ST.get() in

       cut (True /\ inHeap h1 b);
       cut (True /\ inHeap h1 ghost_b);
       cut (True /\ getData ghost_b <> getData b);
       cut (True /\ getLength h1 ghost_b = getLength h1 b);
       cut (True /\ Normalized h1 b);
       cut (True /\ Normalized h1 ghost_b);
       cut (True /\ getLength h1 b > 0);
       cut (True /\ len+1 <= getLength h1 b);

       eval_eq_lemma h0 h1 ghost_b ghost_b (getLength h1 ghost_b);

       cut (True /\ Bitsize (eval h1 ghost_b (getLength h1 ghost_b)) bw);
       cut (True /\ bitweight tb (getLength h1 b) >= bw + tsize);

       (* TODO : PROOF *) 
       admitP (True /\ eval h1 b (getLength h1 b) = eval h1 ghost_b (getLength h1 ghost_b) + signed_modulo (pow2 bw * v) (pow2 (bitweight tb (len+1))));

       cut (modifies !{getData b} h0 h1);

       fill_array b ghost_b v tsize bw (len+1);
       
       let h2 = ST.get() in
       
       cut (True /\ inHeap h0 b);
       cut (True /\ inHeap h2 b);
       cut (True /\ inHeap h0 ghost_b);
       cut (True /\ getData ghost_b <> getData b);
       cut (True /\ getLength h2 b = getLength h0 ghost_b);
       cut (True /\ getLength h2 b = getLength h0 b);
       cut (True /\ len <= getLength h0 b);
       cut (True /\ getLength h0 b > 0);
       
       cut (True /\ Normalized h0 ghost_b);
       cut (True /\ Normalized h2 b);
       
       cut (True /\ modifies !{getData b} h0 h2);
       cut (True /\ Bitsize (eval h0 ghost_b (getLength h0 ghost_b)) bw);
       
       cut (True /\ bitweight (getTemplate b) (getLength h0 b) >= bw + tsize);

       eval_eq_lemma h1 h2 ghost_b ghost_b (getLength h0 ghost_b);
       cut (True /\ eval h2 b (getLength h2 b) = eval h0 ghost_b (getLength h0 ghost_b) + pow2 bw * v);
       
       cut (True /\ Bitsize (eval h2 b (getLength h2 b)) (bw+tsize));
       cut (True /\ getTemplate b = getTemplate ghost_b);

       ()
	 
     )
     else (
       
       let h1 = ST.get() in
       cut (True /\ inHeap h1 b);
       cut (True /\ inHeap h1 ghost_b);
       cut (True /\ getData ghost_b <> getData b);
       cut (True /\ getLength h1 ghost_b = getLength h1 b);
       cut (True /\ Normalized h1 b);
       cut (True /\ Normalized h1 ghost_b);
       cut (True /\ getLength h1 b > 0);
       cut (True /\ len+1 <= getLength h1 b);
       cut (True /\ Bitsize (eval h1 ghost_b (getLength h1 ghost_b)) bw);
       cut (True /\ bitweight tb (getLength h1 b) >= bw + tsize);
       cut (True /\ bitweight tb (len+1) > 0);
       (* TODO : PROOF *) 
       admitP (True /\ eval h1 b (getLength h1 b) = eval h1 ghost_b (getLength h1 ghost_b) + signed_modulo (pow2 bw * v) (pow2 (bitweight tb (len+1))));
       cut (True /\ tb = getTemplate ghost_b);
       cut (modifies !{getData b} h0 h1);
       
       fill_array b ghost_b v tsize bw (len+1)
     )

#reset-options

(* Verified *)
opaque val compute_size_aux : 
  t:template -> 
  n:nat -> 
  tn:nat{tn = bitweight t n} -> 
  wa:nat{ tn < wa } ->
  Tot (size:pos{ bitweight t size >= wa /\ bitweight t (size-1) < wa })
      (decreases (wa - tn))
let rec compute_size_aux t n tn wa =
  (* Compute bitweight t (n+1) *)
  let bwnp1 = tn + t n in
  (* Test if against the total bitweight of a, if smaller iterate *)
  if bwnp1 >= wa then n+1
  else compute_size_aux t (n+1) bwnp1 wa

#reset-options

(* Compute the required size for the new template *)
(* Verified *)
opaque val compute_size : 
  a:bigint -> t:template ->
  ST pos
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 n h1 ->
	       (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{} h0 h1)
	       /\ (bitweight t n >= bitweight (getTemplate a) (getLength h0 a))
	       /\ (n > 0)
	       /\ (bitweight t (n-1) < bitweight (getTemplate a) (getLength h0 a))
     ))
let compute_size a t =
  let n = 0 in
  let tn = 0 in
  let weight_a = bitweight (getTemplate a) (get_length a) in
  compute_size_aux t n tn weight_a

#reset-options

(* Auxiliary function to retemplate *)
(* TODO : verify *)
opaque val retemplate_aux : 
  a:bigint -> ta:template{ ta = getTemplate a } -> b:bigint -> 
  tb:template{ tb = getTemplate b } -> len:nat ->
  ST unit
     (requires (fun h -> 
       (inHeap h a)
       /\ (Normalized h a)
       /\ (inHeap h b)
       /\ (Normalized h b)
       /\ (getData a <> getData b)
       /\ (len <= getLength h a)
       /\ (getLength h b > 0)
       /\ (eval h b (getLength h b) = eval h a len)
       /\ (bitweight (getTemplate b) (getLength h b) >= bitweight (getTemplate a) (getLength h a))
     ))
     (ensures (fun h0 u h1 -> 
       (inHeap h0 a)
       /\ (inHeap h0 b)
       /\ (inHeap h1 b)
       /\ (getData a <> getData b)
       /\ (Normalized h0 a)
       /\ (Normalized h0 b)
       /\ (Normalized h1 b)
       /\ (modifies !{getData b} h0 h1)
       /\ (len <= getLength h0 a)
       /\ (getLength h0 b > 0)
       /\ (getLength h0 b = getLength h1 b)
       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
       /\ (bitweight (getTemplate b) (getLength h0 b) >= bitweight (getTemplate a) (getLength h0 a))
     ))
     
let rec retemplate_aux a ta b tb len =
  match get_length a - len with
  | 0 -> ()
  | _ ->
     let h0 = (ST.get()) in

     (* Current cell value and size *)
     let v = get a len in
     let tsize = ta len in

     (
       order_n_bits v (getSize h0 a len) tsize;
       cut ( Bitsize v tsize );     
       cut (True /\ tsize < ocaml63 )
     );
     let bw = bitweight ta len in

     let ghost_b = Bigint.copy b in

     let h1 = (ST.get()) in

     (
       eval_eq_lemma h1 h1 b ghost_b (getLength h1 ghost_b);
       cut (True /\ eval h1 b (getLength h1 b) = eval h1 ghost_b (getLength h1 b) );
       cut (True /\ getData b <> getData ghost_b)
     );
     
     cut (True /\ inHeap h1 b);
     cut (True /\ inHeap h1 ghost_b);
     cut (True /\ getData ghost_b <> getData b);
     cut (True /\ getLength h1 ghost_b = getLength h1 b);
     cut (True /\ Normalized h1 b);
     cut (True /\ Normalized h1 ghost_b);
     cut (True /\ getLength h1 b > 0);

     (* TODO : prove, comes from the "compute_size" function and from the 
	fact that eval h b (getLength h b) = eval h a len *)
     admitP (True /\ Bitsize (eval h1 ghost_b (getLength h1 ghost_b)) bw);
     admitP (True /\ bitweight (getTemplate b) (getLength h1 b) >= bw + tsize);
     cut (True /\ bitweight (getTemplate b) 0 = 0);
     cut (True /\ eval h1 b (getLength h1 b) = eval h1 ghost_b (getLength h1 ghost_b));
     cut (True /\ getTemplate b = getTemplate ghost_b);

     (* Fill new bigint with the current cell of a *)
     fill_array b ghost_b v tsize bw 0;

     (
       let h2 = ST.get() in
       cut (modifies !{getData b} h0 h2 /\ inHeap h2 a);
       cut (True /\ Normalized h2 a);
       cut (True /\ inHeap h2 b);
       cut (True /\ Normalized h2 b);
       cut (True /\ len+1 <= getLength h2 a);
       cut (True /\ getLength h2 b > 0);
       cut (getTemplate a = ta /\ getTemplate b = tb);
       cut (True /\ getData a <> getData b);
       cut (True /\ eval h2 b (getLength h2 b) = eval h1 ghost_b (getLength h1 ghost_b) + pow2 bw * v);
       eval_eq_lemma h0 h1 b ghost_b (getLength h1 ghost_b);
       cut (True /\ eval h1 ghost_b (getLength h1 ghost_b) = eval h0 a len);
       cut (getLength h2 b = getLength h0 b /\ getLength h2 a = getLength h0 a);
       // TODO : PROOF
       admitP (True /\ eval h2 b (getLength h2 b) = eval h2 a (len+1));
       admitP(True /\ bitweight (getTemplate b) (getLength h2 b) >= bitweight (getTemplate a) (getLength h2 a))
     );
     
     (* Iterate *)
     (* TODO : prove that eval b = eval a len *)
     retemplate_aux a ta b tb (len+1);
     (
       let h3 = ST.get() in
       cut (modifies !{getData b} h0 h3);
       cut (True /\ inHeap h3 a);
       cut (True /\ Normalized h3 a);
       cut (True /\ inHeap h3 b);
       cut (True /\ Normalized h3 b);
       cut (True /\ len+1 <= getLength h3 a);
       cut (True /\ getLength h3 b > 0);
       cut (getTemplate a = ta /\ getTemplate b = tb);
       cut (True /\ getData a <> getData b);
       cut (True /\ eval h1 ghost_b (getLength h1 ghost_b) = eval h0 a len);
       cut (getLength h3 b = getLength h0 b /\ getLength h3 a = getLength h0 a);
       // TODO : PROOF
       admitP (True /\ eval h3 b (getLength h3 b) = eval h0 a (getLength h0 a));
       ()
       )    


#reset-options

(* Retemplating function, returns a fresh big integer with the new template *)
val retemplate:
  a:bigint -> t:template ->
  ST bigint
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{} h0 h1)
	       /\ (getTemplate b = t)
	       /\ (getLength h1 b > 0)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
let retemplate a t =
  (* Initial heap *)
  let h0 = (ST.get()) in
  (* Compute the size of the new array *)
  let new_size = compute_size a t in
  
  (* Create a fresh bigint of the right size *)
  let b = Bigint.mk_zero_bigint new_size t in

  let h = (ST.get()) in
  (
    eval_null h b new_size;
    cut (True /\ eval h b (getLength h b) = eval h a 0)
  );
  
  (* Fill the new bigint *)
  retemplate_aux a (getTemplate a) b t 0;
  
  (
    let h1 = ST.get() in
    
    cut (True /\ inHeap h1 b);
    eval_eq_lemma h0 h a a (getLength h0 a);
    cut (True /\ eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a));
    cut (True /\ getTemplate b = t);
    cut (True /\ getLength h1 b = new_size /\ new_size > 0)
  );
  
  b


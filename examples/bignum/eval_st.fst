// #include "preproc.h"

(* 
  This library file shoul contains types and functions related to big integer 
  representation.
 *)
(* 
  STATUS :  
  Unproven lemmas, see TODOs
 *)

module Eval

open IntLib
open Limb
open ST
open Seq
open Heap
open Array


(* TODO : unify the types and notations for bigint *)
type int64 = int

type intarray = array int

(* Mathematical integer *)
type integer = int
type u8 = int

(* Bounded integer arrays *)
(* TODO : move those to the Limb module *)
(*
type larray (n:nat) = s:seq int{ (forall (i:nat). i< Seq.length s ==> Bitsize (Seq.index s i) n) }
type ularray (n:nat) = s:seq nat{ (forall (i:nat). i < Seq.length s ==> Bitsize (Seq.index s i) n) }
 *)
type larray (n:nat) = a:array int{ (forall (i:nat) (h:heap).
				    (contains h a /\ i < Seq.length (sel h a)) ==> 
				      Bitsize (Seq.index (sel h a) i) n) }


(* Maps the index of the integer data to the theoretic bit size of the cell *)
type template = nat -> Tot nat
type template_const = t:template{ forall (n:nat). t n = t 0 }

(* Template examples : *)
val template_25519 : template
let template_25519 = fun n ->
  if n % 2 = 0 then 26 else 25

val template_bytearray : template
let template_bytearray = fun n -> 8

(* Represents a big integer as an array and a template *)
(* Data is the concrete representation of the bigint *)
(* Template gives information on how to mathematically evaluate it *)
(* Sign is its sign *)
(* Size is a ghost value bounding the size of each element of data to show absence of overflows *)
type bigint = 
  //| Bigint : data:seq integer -> t:template -> size:template -> bigint
  | Bigint64 : data:larray 63{ (forall h. (contains h data) ==> Seq.length (sel h data) > 0) } -> 
	       t:template -> (* TODO : is a 63 bits bound necessary here ? *) 
	       size: ref template{ (forall (n:nat) (h:heap). 
				    (contains h data /\ contains h size /\ n < Seq.length (sel h data)) ==> 
(Bitsize (Seq.index (sel h data) n) (let s = sel h size in s n) /\ (let s = sel h size in s n) <= 63 ) )} ->
	       bigint

type SameFormat (a:bigint) (b:bigint) (ha:heap) (hb:heap) = 
  (contains ha (Bigint64.data a) /\ contains hb (Bigint64.data b) 
   /\ (Bigint64.t a = Bigint64.t b)
   /\ Seq.length (sel ha (Bigint64.data a)) = Seq.length (sel hb (Bigint64.data b) ))


(* Getters *)
val getData : b:bigint -> ST (array int)
			   (requires (fun h -> contains h (Bigint64.data b)))
			   (ensures (fun h0 d h1 -> contains h0 (Bigint64.data b)
						    /\ equal h0 h1
						    /\ Bigint64.data b = d))
let getData b =
  match b with
  //| Bigint data t size -> data
  | Bigint64 data t size -> data

val getTemplate : bigint -> Tot template
let getTemplate b =
  match b with
  //| Bigint data t size -> t
  | Bigint64 data t size -> t

val getSize : b:bigint -> ST template
			   (requires (fun h -> contains h (Bigint64.size b)))
			   (ensures (fun h0 t h1 -> (equal h0 h1)
						    /\ (t = sel h1 (Bigint64.size b))))
let getSize b =
  match b with
  //| Bigint data t size -> size
  | Bigint64 data t size -> 
     let h = ST.get() in
     sel h size

val getLength : b:bigint -> ST nat
			     (requires (fun h -> contains h (Bigint64.data b)))
			     (ensures (fun h0 n h1 -> contains h0 (Bigint64.data b)
						      /\ equal h0 h1
						      /\ Seq.length (sel h1 (Bigint64.data b)) = n))
let getLength b =
  length (getData b)

val get: 
  b:bigint -> 
  n:nat{ (forall (h:heap). contains h (Bigint64.data b) ==> n < Seq.length (sel h (Bigint64.data b))) } -> 
  ST (int)
     (requires (fun h -> contains h (Bigint64.data b) /\ contains h (Bigint64.size b) /\ n < Seq.length (sel h (Bigint64.data b))))
     (ensures (fun h0 x h1 -> (contains h1 (Bigint64.data b))
			      /\ (equal h0 h1)
			      /\ (Seq.index (sel h1 (Bigint64.data b)) n = x)))
let get b n =
  let data = getData b in
  index data n

val maxLimbSize: bigint -> Tot pos
let maxLimbSize b = 
  match b with
    | Bigint64 _ _ _ -> 63

type Normalized (b:bigint) =
  (forall (n:nat) (h:heap). 
   (contains h (Bigint64.data b) /\ contains h (Bigint64.size b) /\n < Seq.length (sel h (Bigint64.data b))) ==> 
     (let s = sel h (Bigint64.size b) in s n <= Bigint64.t b n))

(* Eval computes the mathematical value of the bigint from its content and its template *)
val bitweight : t:template -> n:nat -> Tot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> (t n) + bitweight t (n-1)

val eval_aux : a:seq int -> t:template -> n:nat{ n <= Seq.length a } -> Tot int
let rec eval_aux a t n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight t (n-1)) * Seq.index a (n-1) + eval_aux a t (n-1)
	
val eval : 
  b:bigint -> 
  n:nat(* { n <= getLength b } *) -> 
  ST int
     (requires (fun h -> contains h (Bigint64.data b) /\ n <= Seq.length (sel h (Bigint64.data b))))
     (ensures (fun h0 v h1 -> (contains h0 (Bigint64.data b))
			      /\ (equal h0 h1)))
let eval b len =
  let h0 = ST.get() in
  let data = sel h0 (Bigint64.data b) in
  let template = getTemplate b in
  eval_aux data template len

(* Function returning the size of the integer *)
val size : x:int -> Tot (n:nat{ Bitsize x n })
let size x = 
  if x = 0 then 0
  else if x < 0 then log (-x)
  else log x

type EqualBigint (a:bigint) (b:bigint) (ha:heap) (hb:heap) =
  (contains ha (Bigint64.data a) /\ contains hb (Bigint64.data b) 
   /\ (Eq (sel ha (Bigint64.data a)) (sel hb (Bigint64.data b)))
   /\ (getTemplate a = getTemplate b) )

(* Lemmas *)
val eval_of_zero: 
  a:seq int -> 
  t:template ->
  len:nat{ len <= Seq.length a } ->
  Lemma 
    (requires ((len <= Seq.length a)
	       /\ (forall (i:nat). i < len ==> Seq.index a i = zero)))
    ( ensures ( eval_aux a t len = zero ) )
    [SMTPat (eval_aux a t len)]
let rec eval_of_zero a t len =
  match len with
  | 0 -> ()
  | _ -> 
     cut ( eval_aux a t len = pow2 (bitweight t (len-1)) * Seq.index a (len-1) + eval_aux a t (len-1) /\ True );
     eval_of_zero a t (len-1)
  

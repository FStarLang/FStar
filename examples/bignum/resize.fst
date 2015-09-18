module Resize

open IntLib
open Limb
open Eval
open FStar.Seq
open Axiomatic

val fill_array:
  tmp:bigint{ forall (n:nat). getTemplate tmp n <= maxLimbSize tmp } ->
  v:int ->
  tsize:nat{ Bitsize v tsize } ->
  bw:nat ->
  len:nat{ len <= getLength tmp } ->
  Tot (res:bigint{ (SameFormat tmp res)
		   /\ (eval res (getLength res) = eval tmp (getLength tmp) + (pow2 bw) * v) })
      (decreases (getLength tmp - len))
let rec fill_array tmp v tsize bw len =
  match (getLength tmp - len) with 
  | 0 -> tmp
  | _ -> 
     let bw2 = bitweight (getTemplate tmp) len in
     let tsize2 = getTemplate tmp len in
     (* Case when something has to be done *)
     let tmp =
       if bw + tsize > bw2 && bw2 + tsize2 > bw then 
	 let v2 =
	   if bw < bw2 then div v (pow2 (bw2 - bw))
	   else pow2 (bw - bw2) * v in
	 let v2 = v2 % (pow2 tsize2) in
	 cut ( Bitsize v2 (tsize2) /\ True );
	 let data = getData tmp in
	 let data = upd data len (v2 + index data len) in
	 Bigint64 data (getTemplate tmp) (getTemplate tmp) true
       else tmp in
     fill_array tmp v tsize bw (len+1)			

val realign_aux:
  a:bigint{ Normalized a } ->
  len:nat{ len <= getLength a } ->
  tmp:bigint{ (bitweight (getTemplate tmp) (getLength tmp) >= bitweight (getTemplate a) (getLength a))
	      /\ (eval tmp (getLength tmp) = eval a len) } ->
  Tot (b:bigint{ (SameFormat tmp b)
		 /\ (eval b (getLength b) = eval a (getLength a))})
let rec realign_aux a len tmp =
  match getLength a - len with
  | 0 -> tmp
  | _ ->
     let v = get a len in
     let tsize = getTemplate a len in
     let bw = bitweight (getTemplate a) len in
     let tmp = fill_array tmp v tsize bw 0 in
     realign_aux a (len+1) tmp
  
val computeNewLength : 
  size:nat -> 
  t:template -> 
  tmp:nat{ (bitweight t tmp < size /\ bitweight t tmp + t tmp < size) } -> 
  Tot (n:nat{ (bitweight t n < size) /\ (bitweight t n + t n >= size) })
let rec computeNewLength size t tmp =
  if bitweight t tmp < size && bitweight t (tmp+1) >= size then (tmp+1)
  else computeNewLength size t (tmp+1)

val realign: 
  a:bigint{ Normalized a } -> 
  t:template -> 
  Tot (b:bigint{ (Normalized b)
		 /\ (getTemplate b = t)
		 /\ (eval b (getLength b) = eval a (getLength a)) })
let realign a t =
  let size = bitweight t (getLength a) in
  let tmp = 
    if t 1 >= size then Bigint64 (create 1 zero) t t true
    else (let len = computeNewLength size t 0 in
	  Bigint64 (create len zero) t t true) in
  realign_aux a 0 tmp
  

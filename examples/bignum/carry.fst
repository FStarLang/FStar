(* STATUS : lax type checks but not verified, work in progress *)

module Carry

open Limb
open IntLib
open FStar.Seq
open Axiomatic
open Eval

val carry_over_aux:
  a:bigint{ (forall (n:nat). n < getLength a ==> getSize a n <= maxLimbSize a - 1) } ->
  ctr:nat{ ctr <= getLength a } ->
  tmp:bigint{ (getLength tmp = getLength a + 1) /\ (get tmp (getLength a) = 0) 
	      /\ (forall (n:nat).
		  (n < ctr ==> getSize tmp n <= getTemplate tmp n) 
		  /\ ((n >= ctr /\ n < getLength a) ==> get tmp n = get a n))
	      /\ (eval tmp (getLength tmp) = eval a (getLength a)) } ->
  Tot (res:bigint{ (Normalized res)
		   /\ (SameFormat tmp res)
		   /\ (eval res (getLength res) = eval a (getLength a)) })
let rec carry_over_aux a ctr tmp =
  match (getLength a - ctr) with
  | 0 -> 
     tmp
  | _ ->
     let data = getData tmp in
     let t = getTemplate tmp in
     let size = getSize tmp in
     let over = div (index data ctr) (pow2 (t ctr)) in
     let r = index data ctr % (pow2 (t ctr)) in
     let data = upd data ctr r in
     let data = upd data (ctr+1) (index data (ctr+1) + over) in
     let (size:template) = fun n -> 
       if n = ctr then t ctr
       else if n = ctr + 1 then size n + 1 
       else size n in
     let tmp = Bigint64 data t size true in
     carry_over_aux a (ctr+1) tmp

val carry:
  a:bigint{ (forall (n:nat). n < getLength a ==> getSize a n <= maxLimbSize a - 1) } ->
  Tot (res:bigint{ (Normalized res)
		    /\ (getLength res = getLength a + 1)
		    /\ (getTemplate a = getTemplate res)
		    /\ (eval res (getLength res) = eval a (getLength a)) })
let rec carry a =
  let tmp = extendTo a (getLength a + 1) in
  carry_over_aux a 0 tmp

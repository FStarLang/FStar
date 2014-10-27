
module Stlc
open Prims.PURE

type ty =
  | TyBool  : ty
  | TyArrow : ty -> ty -> ty

type tm =
  | TmVar : nat -> tm
  | TmApp : tm -> tm -> tm
  | TmAbs : nat -> ty -> tm -> tm
  | TmTrue : tm
  | TmFalse : tm
  | TmIf : tm -> tm -> tm -> tm

val is_value : tm -> Tot bool
let is_value t =
  match t with
  | TmAbs _ _ _ -> true
  | TmTrue -> true
  | TmFalse -> true
  | _ -> false

(* Because we only consider call-by-value reduction, we will ever only
   substitute closed values, so this definition of substitution is
   good enough *)
val subst : nat -> tm -> tm -> Tot tm
let rec subst x s t =
  match t with
  | TmVar xprime ->
      if x = xprime then s else t
  | TmAbs xsecond a t1 ->
      TmAbs xsecond a (if x = xsecond then t1 else (subst x s t1))
  | TmApp t1 t2 ->
      TmApp (subst x s t1) (subst x s t2)
  | TmTrue -> 
      TmTrue
  | TmFalse -> 
      TmFalse
  | TmIf t1 t2 t3 -> 
      TmIf (subst x s t1) (subst x s t2) (subst x s t3)





















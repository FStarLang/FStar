module FStarC.Syntax.Visit

open FStarC.Effect
open FStarC.List
open FStarC.Util

open FStarC.Syntax.VisitM
open FStarC.Class.Monad

type id (a:Type) = | I : run:a -> id a

(* We just reuse VisitM with the identity monad to implement this module. *)

instance _ : monad id = {
  return = (fun a -> I a);
  ( let! ) = (fun (I a) f -> f a);
}

let (<<) f g = fun x -> f (g x)

let visit_term pq vt t =
  I?.run (visitM_term pq (I << vt) t)

let visit_term_univs pq vt vu t =
  I?.run (visitM_term_univs pq (I << vt) (I << vu) t)

let visit_sigelt pq vt vu se =
  I?.run (visitM_sigelt pq (I << vt) (I << vu) se)

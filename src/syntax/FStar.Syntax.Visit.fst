module FStar.Syntax.Visit

open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Compiler.Util

open FStar.Syntax.VisitM
open FStar.Class.Monad

type id (a:Type) = | I : run:a -> id a

(* We just reuse VisitM with the identity monad to implement this module. *)

instance _ : monad id = {
  return = (fun a -> I a);
  ( let! ) = (fun (I a) f -> f a);
}

let (<<) f g = fun x -> f (g x)

let visit_term vt t =
  I?.run (visitM_term (I << vt) t)

let visit_term_univs vt vu t =
  I?.run (visitM_term_univs (I << vt) (I << vu) t)

let visit_sigelt vt vu se =
  I?.run (visitM_sigelt (I << vt) (I << vu) se)

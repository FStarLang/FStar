module STLC

open FStar.Reflection.Types
open FStar.Reflection.Data
open FStar.Reflection.Builtins
open FStar.Reflection.Formula

open FStar.Tactics

open DSL.Reflection
open DSL.FStar.TC

type styp =
  | TUnit  : styp
  | TArrow : styp -> styp -> styp

type var = string

type sexpr =
  | Var : n:var -> sexpr
  | Abs : x:var -> t:styp -> e:sexpr -> sexpr
  | App : e1:sexpr -> e2:sexpr -> sexpr

//stlc typing environment
type senv = Map.t var styp
let lookup_senv (en:senv) (x:var) : option styp =
  if Map.contains en x then Some (Map.sel en x)
  else None
let push_senv (en:senv) (x:var) (t:styp) : senv =
  Map.upd en x t

//
//a mapping between the variable names in stlc and
//Tm_names in the elaborated F* Term
//
type mapping = Map.t var bv

//
//a relation that the stlc typechecker maintains when typing
let sg_g_related (sg:senv) (g:env) (m:mapping) : prop =
  forall (x:var). Some? (lookup_senv sg x) ==>
             Some? (lookup_name g (m `Map.sel` x))

let rec elab_st (st:styp) : Tac typ =
  match st with
  | TUnit -> t_unit
  | TArrow t1 t2 ->
    mk_non_dep_arrow (elab_st t1)
                     (mk_tot (elab_st t2))

//return type of the stlc typechecker
type stlc_tc_result (g:env) =
  styp    &                                    //the stlc type
  (e:term &                                    //elaborated term
   t:typ  &                                    //type of the elaborated term
   typing_term g e (mk_tot t, trivial_guard))  //typing derivation

exception Stlc_typing_error

let rec stlc_tc
  (sg:senv)
  (se:sexpr)
  (g:env)
  (m:mapping{sg_g_related sg g m})
  : Tac (stlc_tc_result g)
  = match se with
    | Var x ->
      (match lookup_senv sg x with
       | None -> raise Stlc_typing_error
       | Some st ->
         let e = Map.sel m x in //lookup the mapping for variable n
         let Some t = lookup_name g e in
         let typing = Ty_name g e t in
         st, (| mk_tm_name e, t, typing |))

    | Abs x st se_body ->
      let x_sort = elab_st st in
      //we could easily build a typing for this type in elab_st
      //  but just to illustrate calling into the typechecker
      let tc_x_sort_token =
        fstar_tc_expected_trivial g x_sort (mk_tot t_type) in
      
      let x_bv = fresh_bv x x_sort in
      let x_b = mk_binder x_bv in

      //typecheck the lambda body recursively
      let body_st, (| body_e, body_t, body_typing |) =
        stlc_tc (push_senv sg x st)
                se_body
                (push_binder g x_b)
                (Map.upd m x x_bv) in

      let e = mk_tm_abs x_b body_e in
      let t = mk_tm_arrow x_b (mk_tot body_t) in
      let typing = Ty_abs
        g
        x_b
        body_e
        (mk_tot body_t)
        trivial_guard
        trivial_guard
        (Ty_tc _ _ _ _ tc_x_sort_token)
        body_typing in

      //at this point the guard is:
      //  trivial_guard ++ (close_guard x_b trivial_guard)
      //we could solve it without calling into the typechecker too
      let typing = discharge_guard_typing typing in
      
      TArrow st body_st, (| e, t, typing |)

    | _ -> admit ()

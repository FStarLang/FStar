module Pulse.Checker.Auto.ElimExists
open Pulse.Syntax
open Pulse.Checker.Common
open Pulse.Typing

module T = FStar.Tactics

open Pulse.Checker.Auto.Elims

let should_elim_exists (v:vprop) : T.Tac bool =
  match v with
  | Tm_ExistsSL _ _ _ -> true
  | _ -> false

let mk (#g:env) (#v:vprop) (v_typing:tot_typing g v Tm_VProp)
  : T.Tac (option (t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =

  match v with
  | Tm_ExistsSL u { binder_ppname=nm; binder_ty = t } p ->
    if true then //T.unseal s then
      let x = fresh g in
      let c = Pulse.Typing.comp_elim_exists u t p (nm, x) in
      let tm_typing : st_typing g _ c =
          T_ElimExists g (comp_u c) t p x (magic()) (magic())
      in
      Some (| _, c, tm_typing |)
    else None
  | _ -> None

let elim_exists (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' Tm_VProp &
           continuation_elaborator g ctxt g' ctxt') =

  add_elims should_elim_exists mk ctxt_typing

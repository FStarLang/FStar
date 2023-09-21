module Pulse.Extract.Main
open Pulse.Syntax.Base
open Pulse.Extract.CompilerLib
open Pulse.Syntax.Printer
module T = FStar.Tactics.V2

noeq
type env = { 
  uenv_inner: uenv;
  coreenv: Pulse.Typing.Env.env
}

module RB = Pulse.Readback
module Elab = Pulse.Elaborate.Pure
module E = Pulse.Typing.Env
module LN = Pulse.Syntax.Naming

let name = ppname & nat

let uenv_of_env (g:env) = 
  set_tcenv g.uenv_inner (Pulse.Typing.elab_env g.coreenv)
  
let term_as_mlexpr (g:env) (t:term)
  : T.Tac mlexpr
  = let t = Elab.elab_term t in
    let uenv = uenv_of_env g in
    let mlt, _, _ = term_as_mlexpr uenv t in
    mlt

let term_as_mlty (g:env) (t:term)
  : T.Tac mlty
  = let t = Elab.elab_term t in
    term_as_mlty (uenv_of_env g) t

let extend_env (g:env) (b:binder)
  : T.Tac (env & mlident & mlty & name)
  = let mlty = term_as_mlty g b.binder_ty in
    let x = E.fresh g.coreenv in
    let coreenv = E.push_binding g.coreenv x b.binder_ppname b.binder_ty in
    T.dump (Printf.sprintf "Extending environment with %s : %s\n"
                                      (binder_to_string b)
                                      (term_to_string b.binder_ty));

    let uenv_inner, mlident = extend_bv g.uenv_inner b.binder_ppname x mlty in
    { uenv_inner; coreenv }, mlident, mlty, (b.binder_ppname, x)

exception Extraction_failure of string
let unit_val : term = tm_fstar Pulse.Reflection.Util.unit_tm Range.range_0
let is_erasable (p:st_term) : T.Tac bool = 
  let tag = T.unseal p.effect_tag in
  match tag with
  | Some STT_Ghost -> true
  | _ -> false
    
let rec extract (g:env) (p:st_term)
  : T.Tac (mlexpr & e_tag)
  = let erased_result = mle_unit, e_tag_erasable in
    if is_erasable p
    then erased_result
    else begin
      match p.term with
      | Tm_IntroPure _
      | Tm_ElimExists _
      | Tm_IntroExists _ 
      | Tm_Rewrite _ ->
        erased_result

      | Tm_Abs { b; q; body } -> 
        let g, mlident, mlty, name = extend_env g b in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let res = mle_fun [mlident, mlty] body in
        res, e_tag_pure

      | Tm_Return { term } ->
        term_as_mlexpr g term,
        e_tag_pure

      | Tm_STApp { head; arg } ->
        let head = term_as_mlexpr g head in
        let arg = term_as_mlexpr g arg in
        mle_app head [arg], e_tag_impure
        
      | Tm_Bind { binder; head; body } ->
        if is_erasable head
        then (
          let body = LN.subst_st_term body [LN.NT 0 unit_val] in
          extract g body
        )
        else (
          let head, _ = extract g head in
          let g, mlident, mlty, name = extend_env g binder in
          let body = LN.open_st_term_nv body name in
          let body, _ = extract g body in
          let mllb = mk_mllb mlident ([], mlty) head in 
          let mlletbinding = mk_mlletbinding false [mllb] in
          mle_let mlletbinding body, e_tag_impure
        )
    
      // tot here means non-stateful, head could also be ghost, we should rename it
      | Tm_TotBind { binder; head; body } ->
        let head = term_as_mlexpr g head in
        let g, mlident, mlty, name = extend_env g binder in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let mllb = mk_mllb mlident ([], mlty) head in 
        let mlletbinding = mk_mlletbinding false [mllb] in
        mle_let mlletbinding body, e_tag_impure

      | Tm_ProofHintWithBinders { t } ->
        extract g t
      
    // | Tm_If {
    //     b:term;
    //     then_:st_term;
    //     else_:st_term;
    //     post:option vprop;
    //   }
    // | Tm_Match {
    //     sc:term;
    //     returns_:option vprop;
    //     brs: list branch;
    //   }
    
    // | Tm_While {
    //     invariant:term;
    //     condition:st_term;
    //     condition_var: ppname;
    //     body:st_term;
    //   }
    // | Tm_Par {
    //     pre1:term;
    //     body1:st_term;
    //     post1:term;
    //     pre2:term;
    //     body2:st_term;
    //     post2:term;
    //   }  
    // | Tm_WithLocal {
    //     binder:binder;
    //     initializer:term;
    //     body:st_term;
    //   }
    
    
      | Tm_Admit _
      | _ -> T.raise (Extraction_failure (Printf.sprintf "Cannot extract code with admit: %s\n" (Pulse.Syntax.Printer.st_term_to_string p)))
    end


module RU = Pulse.RuntimeUtils
let extract_pulse (g:uenv) (p:st_term)
  : T.Tac (either (mlexpr  & e_tag & mlty) string)
  = let open T in
    T.dump (Printf.sprintf "About to extract:\n%s\n" (st_term_to_string p));
    try 
      let tm, tag = extract { uenv_inner=g; coreenv=initial_core_env g } p in
      T.dump (Printf.sprintf "Extracted term: %s\n" (mlexpr_to_string tm));
      Inl (tm, tag, mlty_top)
    with
    | Extraction_failure msg -> 
      Inr msg
    | e ->
      Inr (Printf.sprintf "Unexpected extraction error: %s" (RU.print_exn e))
  

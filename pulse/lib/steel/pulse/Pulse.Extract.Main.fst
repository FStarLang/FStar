module Pulse.Extract.Main
open Pulse.Syntax.Base
open Pulse.Extract.CompilerLib
open Pulse.Syntax.Printer
open FStar.List.Tot
module T = FStar.Tactics.V2
exception Extraction_failure of string

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

let rec name_as_mlpath (x:T.name) 
  : T.Tac mlpath 
  = match x with
    | [] -> T.fail "Unexpected empty name"
    | [x] -> [], x
    | x :: xs ->
      let xs, x = name_as_mlpath xs in
      x :: xs, x

module R = FStar.Reflection.V2
let extract_constant (g:env) (c:T.vconst)
  : T.Tac mlconstant
  = let e = T.pack_ln (R.Tv_Const c) in
    let mle, _, _ = CompilerLib.term_as_mlexpr (uenv_of_env g) e in
    match mlconstant_of_mlexpr mle with
    | None -> T.raise (Extraction_failure "Failed to extract constant")
    | Some c -> c

let rec extend_env_pat_core (g:env) (p:pattern)
  : T.Tac (env & list mlpattern & list Pulse.Typing.Env.binding)
  = match p with
    | Pat_Dot_Term _ -> g, [], []
    | Pat_Var pp -> 
      let x = E.fresh g.coreenv in
      let pp = mk_ppname pp FStar.Range.range_0 in
      let coreenv = E.push_binding g.coreenv x pp tm_unknown in
      let uenv_inner, mlident = extend_bv g.uenv_inner pp x mlty_top in
      { uenv_inner; coreenv },
      [ mlp_var mlident ],
      [ (x, tm_unknown) ]

    | Pat_Cons f pats ->
      let g, pats, bindings = 
        T.fold_left
          (fun (g, pats, bindings) (p, _) ->
            let g, pats', bindings' = extend_env_pat_core g p in
            g, pats @ pats', bindings@bindings')
          (g, [], [])
          pats
      in
      g, [mlp_constructor (name_as_mlpath f.fv_name) pats], bindings
    | Pat_Constant c ->
      let c = extract_constant g c in
      g, [mlp_const c], []
let extend_env_pat g p = 
  let g, pats, bs = extend_env_pat_core g p in
  match pats with
  | [p] -> g, p, bs
  | _ -> T.raise (Extraction_failure "Unexpected extraction of pattern")

let unit_val : term = tm_fstar Pulse.Reflection.Util.unit_tm Range.range_0
let is_erasable (p:st_term) : T.Tac bool = 
  let tag = T.unseal p.effect_tag in
  match tag with
  | Some STT_Ghost -> true
  | _ -> false
    
let rec extract (g:env) (p:st_term)
  : T.Tac (mlexpr & e_tag)
  = let erased_result = mle_unit, e_tag_erasable in
    T.dump (Printf.sprintf "Extracting term@%s:\n%s\n" 
              (T.range_to_string p.range)
              (st_term_to_string p));
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
          let body = LN.subst_st_term body [LN.DT 0 unit_val] in
          T.dump (Printf.sprintf "Erasing head of bind %s\nopened body to %s"
                      (st_term_to_string head)
                      (st_term_to_string body));
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
      
      | Tm_If { b; then_; else_ } ->
        let b = term_as_mlexpr g b in
        let then_, _ = extract g then_ in
        let else_, _ = extract g else_ in
        mle_if b then_ (Some else_), e_tag_impure

      | Tm_Match { sc; brs } ->
        let sc = term_as_mlexpr g sc in
        let extract_branch (pat, body) =
          let g, pat, bs = extend_env_pat g pat in
          let body = Pulse.Checker.Match.open_st_term_bs body bs in
          let body, _ = extract g body in
          pat, body
        in
        let brs = T.map extract_branch brs in
        mle_match sc brs, e_tag_impure

    
      | Tm_While { condition; body } ->
        let condition, _ = extract g condition in
        let body, _ = extract g body in
        let condition = mle_fun [("_", mlty_unit)] condition in
        let body = mle_fun [("_", mlty_unit)] body in
        let w = mle_app (mle_name (["Pulse"; "Lib"; "Core"], "while_")) [condition; body] in
        w, e_tag_impure

      | Tm_Par { body1; body2 } ->
        let body1, _ = extract g body1 in
        let body2, _ = extract g body2 in
        let body1 = mle_fun [("_", mlty_unit)] body1 in
        let body2 = mle_fun [("_", mlty_unit)] body2 in
        let p = mle_app (mle_name (["Pulse"; "Lib"; "Core"], "par")) [body1; body2] in
        p, e_tag_impure

      | Tm_WithLocal { binder; initializer; body } ->
        let initializer = term_as_mlexpr g initializer in
        let g, mlident, mlty, name = extend_env g { binder with binder_ty = binder.binder_ty } in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let allocator = mle_app (mle_name (["Pulse"; "Lib"; "Reference"] , "alloc")) [initializer] in
        let mllb = mk_mllb mlident ([], mlty) allocator in
        let mlletbinding = mk_mlletbinding false [mllb] in
        mle_let mlletbinding body, e_tag_impure
    
      | Tm_ProofHintWithBinders { t } -> T.fail "Unexpected constructor: ProofHintWithBinders should have been desugared away"
      | Tm_Admit _ -> T.raise (Extraction_failure (Printf.sprintf "Cannot extract code with admit: %s\n" (Pulse.Syntax.Printer.st_term_to_string p)))
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
  

(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Extract.Main

open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Syntax.Printer
open FStar.List.Tot
open Pulse.Show

module L = FStar.List.Tot
module R = FStar.Reflection
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module RB = Pulse.Readback
module Elab = Pulse.Elaborate.Pure
module E = Pulse.Typing.Env
module LN = Pulse.Syntax.Naming
module RU = Pulse.RuntimeUtils

//
// Not opening this module, it also defines a term type
//
module ECL = Pulse.Extract.CompilerLib

exception Extraction_failure of string

noeq
type env = { 
  uenv_inner: ECL.uenv;
  coreenv: Pulse.Typing.Env.env
}

let name = ppname & nat

let topenv_of_env (g:env) = E.fstar_env g.coreenv
let tcenv_of_env (g:env) = Pulse.Typing.elab_env g.coreenv
let uenv_of_env (g:env) = ECL.set_tcenv g.uenv_inner (tcenv_of_env g)

let debug (g:env) (f: unit -> T.Tac string)
  : T.Tac unit
  = if RU.debug_at_level (E.fstar_env g.coreenv) "pulse_extraction"
    then T.print (f())


let term_as_mlexpr (g:env) (t:term)
  : T.Tac ECL.mlexpr
  = let uenv = uenv_of_env g in
    let t = ECL.normalize_for_extraction uenv t in
    let mlt, _, _ = ECL.term_as_mlexpr uenv t in
    mlt

let term_as_mlty (g:env) (t:term)
  : T.Tac ECL.mlty
  = ECL.term_as_mlty (uenv_of_env g) t

let extend_env (g:env) (b:binder)
  : T.Tac (env & ECL.mlident & ECL.mlty & name)
  = let mlty = term_as_mlty g b.binder_ty in
    let x = E.fresh g.coreenv in
    let coreenv = E.push_binding g.coreenv x b.binder_ppname b.binder_ty in
    debug g (fun _ -> Printf.sprintf "Extending environment with %s : %s\n"
                                      (binder_to_string b)
                                      (term_to_string b.binder_ty));
    let uenv_inner, mlident = ECL.extend_bv g.uenv_inner b.binder_ppname x mlty in
    { uenv_inner; coreenv }, mlident, mlty, (b.binder_ppname, x)

let rec name_as_mlpath (x:T.name) 
  : T.Tac ECL.mlpath 
  = match x with
    | [] -> T.fail "Unexpected empty name"
    | [x] -> [], x
    | x :: xs ->
      let xs, x = name_as_mlpath xs in
      x :: xs, x

module R = FStar.Reflection.V2
let extract_constant (g:env) (c:T.vconst)
  : T.Tac ECL.mlconstant
  = let e = T.pack_ln (R.Tv_Const c) in
    let mle, _, _ = ECL.term_as_mlexpr (uenv_of_env g) e in
    match ECL.mlconstant_of_mlexpr mle with
    | None -> T.raise (Extraction_failure "Failed to extract constant")
    | Some c -> c

let rec extend_env_pat_core (g:env) (p:pattern)
  : T.Tac (env & list ECL.mlpattern & list Pulse.Typing.Env.binding)
  = match p with
    | Pat_Dot_Term _ -> g, [], []
    | Pat_Var pp sort -> 
      let x = E.fresh g.coreenv in
      let pp = mk_ppname pp FStar.Range.range_0 in
      let ty = T.unseal sort in
      let ty = wr ty (T.range_of_term ty) in
      debug g (fun _ -> Printf.sprintf "Pushing pat_var %s : %s\n" (T.unseal pp.name) (term_to_string ty));
      let coreenv = E.push_binding g.coreenv x pp ty in
      let uenv_inner, mlident = ECL.extend_bv g.uenv_inner pp x ECL.mlty_top in
      { uenv_inner; coreenv },
      [ ECL.mlp_var mlident ],
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
      g, [ECL.mlp_constructor (name_as_mlpath f.fv_name) pats], bindings
    | Pat_Constant c ->
      let c = extract_constant g c in
      g, [ECL.mlp_const c], []
let extend_env_pat g p = 
  let g, pats, bs = extend_env_pat_core g p in
  match pats with
  | [p] -> g, p, bs
  | _ -> T.raise (Extraction_failure "Unexpected extraction of pattern")

let unit_val : term = wr Pulse.Reflection.Util.unit_tm Range.range_0
let is_erasable (p:st_term) : T.Tac bool = 
  let tag = T.unseal p.effect_tag in
  match tag with
  | Some STT_Ghost -> true
  | _ -> false
    
let head_and_args (t:term)
  : option (R.term & list R.argv) = Some (R.collect_app_ln t)

let term_eq_string (s:string) (t:R.term) : bool =
  match R.inspect_ln t with
  | R.Tv_Const (R.C_String s') -> s=s'
  | _ -> false

let maybe_unfold_head (g:env) (head:R.term) 
  : T.Tac (option (either st_term R.term))
  = debug g (fun _ -> Printf.sprintf "Maybe unfolding head %s\n" (T.term_to_string head));
    match R.inspect_ln head with
    | R.Tv_FVar f -> (
      let name = R.inspect_fv f in
      match R.lookup_typ (topenv_of_env g) name with
      | None -> None
      | Some se ->
        let attrs = R.sigelt_attrs se in
        let quals = R.sigelt_quals se in
        if List.Tot.existsb (term_eq_string "inline") attrs
        || List.Tot.existsb (function | R.Inline_for_extraction -> true | _ -> false) quals
        then match ECL.sigelt_extension_data se with
             | Some se ->
               debug g (fun _ -> Printf.sprintf "Unfolded head %s\n"  (T.term_to_string head));
               debug g (fun _ -> Printf.sprintf "to %s\n"  (st_term_to_string se));
               Some (Inl se)
             | None -> (
                match T.inspect_sigelt se with
                | T.Sg_Let { isrec=false; lbs = [ { lb_us=[]; lb_def }] } ->
                  Some (Inr lb_def)
                | _ -> None
             )
        else None
    )
    | R.Tv_UInst f _ ->
      //No universe-polymorphic inlining ... yet
      None
    | _ -> None

let rec st_term_abs_take_n_args (n_args:nat) (t:st_term)
  : res:(st_term & nat){snd res <= n_args}
  = if n_args = 0 then t, 0
    else (
      match t.term with 
      | Tm_Abs { body } -> st_term_abs_take_n_args (n_args - 1) body
      | _ -> (t, n_args)
    )

let rec term_abs_take_n_args (n_args:nat) (t:R.term)
  : res:(R.term & nat){snd res <= n_args}
  = if n_args = 0 then t, 0
    else (
      match R.inspect_ln t with 
      | R.Tv_Abs _ body -> term_abs_take_n_args (n_args - 1) body
      | _ -> (t, n_args)
    )

let abs_take_n_args (n_args:nat) (t:either st_term R.term)
  : T.Tac (res:(either st_term R.term & nat){snd res <= n_args}) 
  = match t with
    | Inl t -> 
      let t, n_args = st_term_abs_take_n_args n_args t in
      Inl t, n_args
    | Inr t ->
      let t, n_args = term_abs_take_n_args n_args t in
      Inr t, n_args

let rec unascribe (t:R.term) : T.Tac R.term =
  match R.inspect_ln t with
  | R.Tv_AscribedT e _ _ _ -> unascribe e
  | R.Tv_AscribedC e _ _ _ -> unascribe e
  | _ -> t

let maybe_inline (g:env) (head:term) (arg:term) :T.Tac (option st_term) =
  debug g (fun _ -> Printf.sprintf "Considering inlining %s\n"
                      (term_to_string head));
  match head_and_args head with
  | None -> None
  | Some (head, args) ->
    debug g (fun _ -> Printf.sprintf "head=%s with %d args\n"
                      (T.term_to_string head)
                      (List.length args));
    match maybe_unfold_head g head with
    | None ->
      debug g (fun _ -> Printf.sprintf "No unfolding of %s\n"
                            (T.term_to_string head));
      None

    | Some def ->
      // debug g (fun _ -> Printf.sprintf "Unfolded %s to body %s\n"
      //                       (T.term_to_string head)
      //                       (st_term_to_string body));
      let as_term (a:R.term) =
        wr a Range.range_0 in
      let all_args : list (term & option qualifier) =
        L.map #R.argv
              (fun (t, q) -> 
                let t = as_term t in
                let qual = if R.Q_Implicit? q then Some Implicit else None in
                t, qual)
              args
        @ [arg, None]
      in
      let n_args = L.length all_args in
      let body, remaining_args = abs_take_n_args n_args def in
      let args, rest = L.splitAt (n_args - remaining_args) all_args in
      let _, subst =
          L.fold_right
            (fun arg (i, subst) ->
              i + 1,
              RT.DT i (fst arg)::subst)
            args
            (0, [])
      in
      match body with
      | Inl body -> (
        let applied_body = LN.subst_st_term body subst in
        match rest with
        | [] -> 
          Some applied_body
        | _ ->
          T.fail (Printf.sprintf 
            "Partial or over application of inlined Pulse definition is not yet supported\n\
            %s has %d arguments, but %s were left unapplied"
            (T.term_to_string head)
            (L.length args)
            (String.concat ", " (T.map (fun x -> term_to_string (fst x)) rest))
          )
      )
      | Inr body ->
        let applied_body = unascribe (LN.subst_host_term body subst) in
        let mk_st_app (head:R.term) (arg:term) (arg_qual:option qualifier) =
          let head = wr head (T.range_of_term head) in
          let tm = Tm_STApp { head; arg_qual; arg } in 
          Some { term = tm; range=FStar.Range.range_0; effect_tag=default_effect_hint }
        in
        match rest with
        | [] -> (
          match R.inspect_ln applied_body with
          | R.Tv_App head (arg, aqual) ->
            let arg = wr arg (T.range_of_term arg) in
            let arg_qual = if R.Q_Implicit? aqual then Some Implicit else None in
            mk_st_app head arg arg_qual
          | _ ->
            T.fail 
              (Printf.sprintf "Cannot inline F* definitions of stt terms whose body is not an application; got %s"
                (T.term_to_string applied_body))
        )
        | rest ->
          FStar.List.Tot.lemma_splitAt_snd_length (L.length rest - 1) rest;
          let rest, [last] = L.splitAt (L.length rest - 1) rest in
          let head = 
            L.fold_left 
              (fun head (tm, qual) ->
                R.pack_ln (
                  R.Tv_App head (tm, (if Some? qual then R.Q_Implicit else R.Q_Explicit))
                ))
              applied_body
              rest
          in
          mk_st_app head (fst last) (snd last)

let fresh (g:env) = Pulse.Typing.fresh g.coreenv

let push_binding (g:env) (x:var { ~ (x `Set.mem` E.dom g.coreenv )}) (b:binder) =
  { g with coreenv = E.push_binding g.coreenv x b.binder_ppname b.binder_ty }

let with_open (g:env) (b:binder) (e:st_term) (f:env -> st_term -> T.Tac st_term) : T.Tac st_term =
  let open Pulse.Syntax.Naming in
  let x = fresh g in
  let e = open_st_term' e (tm_var { nm_index = x; nm_ppname = b.binder_ppname }) 0 in
  let e = f (push_binding g x b) e in
  close_st_term' e x 0


let is_internal_binder (b:binder) : T.Tac bool =
  let s = T.unseal b.binder_ppname.name in
  s = "_fret" ||
  s = "_bind_c" ||
  s = "_while_c" ||
  s = "_tbind_c" ||
  s = "_if_br" ||
  s = "_br"

let is_return (e:st_term) : option term =
  match e.term with
  | Tm_Return { term } -> Some term
  | _ -> None

let is_return_bv0 (e:st_term) : bool =
  match is_return e with
  | Some term -> is_bvar term = Some 0
  | _ -> false

//
// let x = (let y = e1 in e2) in e3 ~~> let y = e1 in let x = e2 in e3
//
// The y let binding can be a TotBind, Bind, let mut, let mut array
//
let simplify_nested_let (e:st_term) (b_x:binder) (head:st_term) (e3:st_term)
  : option st_term =

  let mk t : st_term = { range = e.range; effect_tag = default_effect_hint; term = t } in
  let body e2 = mk (Tm_Bind { binder = b_x; head = e2; body = e3 }) in
  match head.term with
  | Tm_TotBind { binder = b_y; head = e1; body = e2 } ->
    Some (mk (Tm_TotBind { binder = b_y; head = e1; body = body e2 }))
  | Tm_Bind { binder = b_y; head = e1; body = e2 } ->
    Some (mk (Tm_Bind { binder = b_y; head = e1; body = body e2 }))
  | Tm_WithLocal { binder = b_y; initializer = e1; body = e2 } ->
    Some (mk (Tm_WithLocal { binder = b_y; initializer = e1; body = body e2 }))
  | Tm_WithLocalArray { binder = b_y; initializer = e1; length; body = e2 } ->
    Some (mk (Tm_WithLocalArray { binder = b_y; initializer = e1; length; body = body e2 }))
  
  | _ -> None

//
// 1. let x = e in x ~~> e
// 2. let x = return e1 in e2 ~~> e2[e1/x]
// 3. The nested let rule above
//
// These apply only when x is an internal binder 
//
let rec simplify_st_term (g:env) (e:st_term) : T.Tac st_term =
  let ret t = { e with term = t } in
  let with_open b e = with_open g b e simplify_st_term in

  match e.term with
  | Tm_Return _
  | Tm_IntroPure _
  | Tm_ElimExists _
  | Tm_IntroExists _
  | Tm_STApp _
  | Tm_Rewrite _
  | Tm_Admit _
  | Tm_ProofHintWithBinders _ -> e

  | Tm_Abs { b; q; ascription; body } ->
    ret (Tm_Abs { b; q; ascription; body = with_open b body })

  | Tm_Bind { binder; head; body } ->
    let is_internal_binder = is_internal_binder binder in
    if is_internal_binder &&
       is_return_bv0 body
    then simplify_st_term g head
    else if is_internal_binder &&
            Some? (is_return head)
    then let Some head = is_return head in
         simplify_st_term g (LN.subst_st_term body [RT.DT 0 head])
    else begin
      match simplify_nested_let e binder head body with
      | Some e -> simplify_st_term g e
      | None ->        
        let head = simplify_st_term g head in
        let body = with_open binder body in
        ret (Tm_Bind { binder; head; body })
    end

  | Tm_TotBind { binder; head; body } ->
    ret (Tm_TotBind { binder; head; body = with_open binder body })

  | Tm_If { b; then_; else_; post } ->
    ret (Tm_If { b; then_ = simplify_st_term g then_; else_ = simplify_st_term g else_; post })

  | Tm_Match { sc; returns_; brs } ->
    ret (Tm_Match { sc; returns_; brs = T.map (simplify_branch g) brs })

  | Tm_While { invariant; condition; condition_var; body } ->
    let condition = simplify_st_term g condition in
    let body = simplify_st_term g body in
    { e with term = Tm_While { invariant; condition; condition_var; body } }
  
  | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
    let body1 = simplify_st_term g body1 in
    let body2 = simplify_st_term g body2 in
    { e with term = Tm_Par { pre1; body1; post1; pre2; body2; post2 } }

  | Tm_WithLocal { binder; initializer; body } ->
    ret (Tm_WithLocal { binder; initializer; body = with_open binder body })
  
  | Tm_WithLocalArray { binder; initializer; length; body } ->
    ret (Tm_WithLocalArray { binder; initializer; length; body = with_open binder body })
    
  | Tm_WithInv {body} ->
    simplify_st_term g body

  | Tm_Unreachable -> e

and simplify_branch (g:env) (b:branch) : T.Tac branch =
  let pat, body = b in
  let g, _, bs = extend_env_pat g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = simplify_st_term g body in
  pat, Pulse.Syntax.Naming.close_st_term_n body (L.map fst bs)

let erase_type_for_extraction (g:env) (t:term) : T.Tac bool =
  RU.must_erase_for_extraction (tcenv_of_env g) t

let rec erase_ghost_subterms (g:env) (p:st_term) : T.Tac st_term =
  let open Pulse.Syntax.Naming in

  let fresh (g:env) = Pulse.Typing.fresh g.coreenv in
  let push_binding g x b =
    { g with coreenv = E.push_binding g.coreenv x b.binder_ppname b.binder_ty } in

  let open_erase_close (g:env) (b:binder) (e:st_term) : T.Tac st_term =
    let x = fresh g in
    let e = open_st_term' e (tm_var { nm_index = x; nm_ppname = b.binder_ppname }) 0 in
    let e = erase_ghost_subterms (push_binding g x b) e in
    close_st_term' e x 0 in

  let unit_tm =
    { p with term = Tm_Return { expected_type=tm_unknown; insert_eq = false; term = unit_val } }
  in
  let ret (t:st_term') = { p with term = t } in
  if is_erasable p
  then unit_tm
  else begin
    match p.term with
    | Tm_IntroPure _
    | Tm_ElimExists _
    | Tm_IntroExists _ 
    | Tm_Rewrite _ -> unit_tm

    | Tm_Abs { b; q; body; ascription } ->
      let body = open_erase_close g b body in
      ret (Tm_Abs { b; q; body; ascription })
    
    | Tm_Return _ -> p

    | Tm_STApp _ -> p

    | Tm_Bind { binder; head; body } ->
      if is_erasable head
      then let body = LN.subst_st_term body [RT.DT 0 unit_val] in
           erase_ghost_subterms g body
      else let head = erase_ghost_subterms g head in
           let body = open_erase_close g binder body in
           ret (Tm_Bind { binder; head; body })

    | Tm_TotBind { binder; head; body } ->
      if erase_type_for_extraction g binder.binder_ty
      then let body = LN.subst_st_term body [RT.DT 0 unit_val] in
           erase_ghost_subterms g body
      else let body = open_erase_close g binder body in
           ret (Tm_TotBind { binder; head; body })

    | Tm_If { b; then_; else_; post } ->
      let then_ = erase_ghost_subterms g then_ in
      let else_ = erase_ghost_subterms g else_ in
      ret (Tm_If { b; then_; else_; post })

    | Tm_Match { sc; brs; returns_ } ->
      let brs = T.map (erase_ghost_subterms_branch g) brs in
      ret (Tm_Match { sc; brs; returns_ })

    | Tm_While { invariant; condition; condition_var; body } ->
      let condition = erase_ghost_subterms g condition in
      let body = erase_ghost_subterms g body in
      ret (Tm_While { invariant; condition; condition_var; body })

    | Tm_Par { pre1; body1; post1; pre2; body2; post2 } ->
      let body1 = erase_ghost_subterms g body1 in
      let body2 = erase_ghost_subterms g body2 in
      ret (Tm_Par { pre1; body1; post1; pre2; body2; post2 })

    | Tm_WithLocal { binder; initializer; body } ->
      let body = open_erase_close g binder body in
      ret (Tm_WithLocal { binder; initializer; body })

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      let body = open_erase_close g binder body in
      ret (Tm_WithLocalArray { binder; initializer; length; body })

    | Tm_Unreachable -> p

    | Tm_Admit _ -> p

    | Tm_ProofHintWithBinders _ ->
      T.fail "erase_ghost_subterms: Unexpected constructor: ProofHintWithBinders should have been desugared away"

    | Tm_WithInv { name; body; returns_inv } ->
      ret (Tm_WithInv { name; body = erase_ghost_subterms g body; returns_inv })
      
  end

and erase_ghost_subterms_branch (g:env) (b:branch) : T.Tac branch =
  let pat, body = b in
  let g, _, bs = extend_env_pat g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = erase_ghost_subterms g body in
  pat, Pulse.Syntax.Naming.close_st_term_n body (L.map fst bs)

let rec extract (g:env) (p:st_term)
  : T.Tac (ECL.mlexpr & ECL.e_tag)
  = let erased_result = ECL.mle_unit, ECL.e_tag_erasable in
    debug g (fun _ -> Printf.sprintf "Extracting term@%s:\n%s\n" 
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
        let mlattrs =
          b.binder_attrs
          |> T.unseal
          |> T.map (term_as_mlexpr g) in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let res = ECL.mle_fun [mlident, mlty, mlattrs] body in
        res, ECL.e_tag_pure

      | Tm_Return { term } ->
        term_as_mlexpr g term,
        ECL.e_tag_pure

      | Tm_STApp { head; arg } -> (
        match maybe_inline g head arg with
        | None ->
          let head = term_as_mlexpr g head in
          let arg = term_as_mlexpr g arg in
          ECL.mle_app head [arg], ECL.e_tag_impure
        | Some t ->
          debug g (fun _ -> Printf.sprintf "Inlined to: %s\n" (st_term_to_string t));
          extract g t
      )

      | Tm_Bind { binder; head; body } ->
        let eh = is_erasable head in
        let et = erase_type_for_extraction g binder.binder_ty in
        //debug g (fun _ ->
        //  Printf.sprintf "Extracting bind %s\neh=%s, et=%s\nBody.tag = %s\n"
        //    (show p) (show eh) (show et) (tag_of_st_term body)
        //);
        // eh: head is erasable, delete it
        // et: the type returned by the head is erasable, and it is a literal
        //     function. Erase it. This happens often with locally-defined ghost
        //     functions.
        if eh || (Tm_Abs? head.term && et)
        then (
          let body = LN.subst_st_term body [RT.DT 0 unit_val] in
          debug g (fun _ -> Printf.sprintf "Erasing head of bind %s\nopened body to %s"
                              (show head)
                              (show body));
          extract g body
        ) else (
          let head, _ = extract g head in
          let g, mlident, mlty, name = extend_env g binder in
          let body = LN.open_st_term_nv body name in
          let body, _ = extract g body in
          let mllb = ECL.mk_mllb mlident ([], mlty) head in 
          let mlletbinding = ECL.mk_mlletbinding false [mllb] in
          ECL.mle_let mlletbinding body, ECL.e_tag_impure
        )
    
      // tot here means non-stateful, head could also be ghost, we should rename it
      | Tm_TotBind { binder; head; body } ->
        let head = term_as_mlexpr g head in
        let g, mlident, mlty, name = extend_env g binder in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let mllb = ECL.mk_mllb mlident ([], mlty) head in 
        let mlletbinding = ECL.mk_mlletbinding false [mllb] in
        ECL.mle_let mlletbinding body, ECL.e_tag_impure
      
      | Tm_If { b; then_; else_ } ->
        let b = term_as_mlexpr g b in
        let then_, _ = extract g then_ in
        let else_, _ = extract g else_ in
        ECL.mle_if b then_ (Some else_), ECL.e_tag_impure

      | Tm_Match { sc; brs } ->
        let sc = term_as_mlexpr g sc in
        let extract_branch (pat0, body) =
          let g, pat, bs = extend_env_pat g pat0 in
          debug g (fun _ -> 
            Printf.sprintf "Extracting branch with pattern %s\n"
                    (Pulse.Syntax.Printer.pattern_to_string pat0)
                    );
          let body = Pulse.Checker.Match.open_st_term_bs body bs in
          let body, _ = extract g body in
          pat, body
        in
        let brs = T.map extract_branch brs in
        ECL.mle_match sc brs, ECL.e_tag_impure

    
      | Tm_While { condition; body } ->
        let condition, _ = extract g condition in
        let body, _ = extract g body in
        let condition = ECL.mle_fun [("_", ECL.mlty_unit, [])] condition in
        let body = ECL.mle_fun [("_", ECL.mlty_unit, [])] body in
        let w = ECL.mle_app (ECL.mle_name (["Pulse"; "Lib"; "Core"], "while_")) [condition; body] in
        w, ECL.e_tag_impure

      | Tm_Par { body1; body2 } ->
        let body1, _ = extract g body1 in
        let body2, _ = extract g body2 in
        let body1 = ECL.mle_fun [("_", ECL.mlty_unit, [])] body1 in
        let body2 = ECL.mle_fun [("_", ECL.mlty_unit, [])] body2 in
        let p = ECL.mle_app (ECL.mle_name (["Pulse"; "Lib"; "Core"], "par")) [body1; body2] in
        p, ECL.e_tag_impure

      | Tm_WithLocal { binder; initializer; body } ->
        let initializer = term_as_mlexpr g initializer in
        let g, mlident, mlty, name = extend_env g { binder with binder_ty = binder.binder_ty } in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        let allocator = ECL.mle_app (ECL.mle_name (["Pulse"; "Lib"; "Reference"] , "alloc")) [initializer] in
        let mllb = ECL.mk_mut_mllb mlident ([], mlty) allocator in
        let mlletbinding = ECL.mk_mlletbinding false [mllb] in
        ECL.mle_let mlletbinding body, ECL.e_tag_impure
      
      | Tm_WithLocalArray { binder; initializer; length; body } ->
        let initializer = term_as_mlexpr g initializer in
        let length = term_as_mlexpr g length in
        let g, mlident, mlty, name = extend_env g { binder with binder_ty = binder.binder_ty } in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract g body in
        //
        // Slice library doesn't have an alloc
        //
        // This is parsed by Pulse2Rust
        //
        let allocator = ECL.mle_app (ECL.mle_name (["Pulse"; "Lib"; "Array"; "Core"] , "alloc")) [initializer; length] in
        let mllb = ECL.mk_mut_mllb mlident ([], mlty) allocator in
        let mlletbinding = ECL.mk_mlletbinding false [mllb] in
        ECL.mle_let mlletbinding body, ECL.e_tag_impure

      | Tm_WithInv { body } ->
        extract g body
    
      | Tm_Unreachable ->
        ECL.mle_app (ECL.mle_name (["Pulse"; "Lib"; "Core"], "unreachable")) [ECL.mle_unit],
        ECL.e_tag_impure

      | Tm_ProofHintWithBinders { t } -> T.fail "Unexpected constructor: ProofHintWithBinders should have been desugared away"
      | Tm_Admit _ ->
        ECL.mle_app (ECL.mle_name ([], "failwith")) [ECL.mle_unit],
        ECL.e_tag_impure
        // T.raise (Extraction_failure (Printf.sprintf "Cannot extract code with admit: %s\n" (Pulse.Syntax.Printer.st_term_to_string p)))
      
    end

let rec map_dv (#a #b:Type) (f:a -> Dv b) (l:list a) : Dv (list b) =
  match l with
  | [] -> []
  | hd::tl -> (f hd)::(map_dv f tl)

let rec generalize (g:env) (t:R.typ) (e:option st_term)
  : T.Tac (env &
           list ECL.mlty_param &
           R.typ &
           o:option st_term { Some? e <==> Some? o}) =

  debug g (fun _ -> Printf.sprintf "Generalizing arrow:\n%s\n" (T.term_to_string t));
  let tv = R.inspect_ln t in
  match tv with
  | R.Tv_Arrow b c ->
    let {sort; ppname} = R.inspect_binder b in
    if R.Tv_Unknown? (R.inspect_ln sort)
    then T.raise (Extraction_failure "Unexpected unknown sort when generalizing")
    else if ECL.is_type g.uenv_inner sort
    then let cview = R.inspect_comp c in
         match cview with
         | R.C_Total t ->
           let x = Pulse.Typing.fresh g.coreenv in
           let xt = R.(pack_ln (Tv_Var (pack_namedv {uniq = x; sort = RT.sort_default; ppname}))) in
           let t = R.subst_term [R.DT 0 xt] t in
           let e, attrs =
             match e with
             | Some {term=Tm_Abs {b; body}} ->
               Some (LN.subst_st_term body [RT.DT 0 (wr xt Range.range_0)]),
               b.binder_attrs
             | _ -> e, binder_attrs_default in
           let mlattrs = attrs |> T.unseal |> T.map (term_as_mlexpr g) in
           let namedv = R.pack_namedv {
            uniq = x;
            sort = FStar.Sealed.seal sort;
            ppname
           } in
           let uenv = ECL.extend_ty g.uenv_inner namedv in
           let coreenv =
             E.push_binding
               g.coreenv
               x
               (mk_ppname ppname FStar.Range.range_0)
               (wr sort FStar.Range.range_0) in
           let g = { g with uenv_inner = uenv; coreenv } in
           let g, tys, t, e = generalize g t e in
           let ty_param = ECL.mk_ty_param (ECL.lookup_ty g.uenv_inner namedv) mlattrs in
           g, ty_param::tys, t, e
         | _ -> T.raise (Extraction_failure "Unexpected effectful arrow")
    else g, [], t, e
  
  | _ -> g, [], t, e

let debug_ = debug

let rec find_map (f: 'a -> option 'b) (l:list 'a) : option 'b =
  match l with
  | [] -> None
  | hd::tl -> let x = f hd in if Some? x then x else find_map f tl

let is_recursive (g:env) (knot_name:R.fv) (selt:R.sigelt)
  : T.Tac (option string)
  = let attrs = RU.get_attributes selt in
    let unpack_string (t:R.term) : option string =
      match R.inspect_ln t with
      | R.Tv_Const (R.C_String s) -> Some s
      | _ -> None
    in
    let pulse_recursive_attr (t:R.term) : option string =
      match R.inspect_ln t with
      | R.Tv_App _ _ -> (
        let hd, args = T.collect_app_ln t in
        if T.is_fvar hd (`%Mktuple2)
        then match args with
             | [_; _; (tag, _); (value, _)] -> (
              match unpack_string tag, unpack_string value with
              | Some "pulse.recursive.knot", Some v -> Some v
              | _ -> None
             )
             | _ -> None
        else None
      )
      | _ -> None
    in
    find_map pulse_recursive_attr attrs

let rec extract_recursive g (p:st_term) (rec_name:R.fv)
  : T.Tac (ECL.mlexpr & ECL.e_tag)
  = match p.term with
    | Tm_Abs { b; q; body } -> (
      match body.term with
      | Tm_Abs _ ->
        let g, mlident, mlty, name = extend_env g b in
        let body = LN.open_st_term_nv body name in
        let body, _ = extract_recursive g body rec_name in
        let attrs =
          b.binder_attrs
          |> T.unseal
          |> T.map (term_as_mlexpr g) in
        let res = ECL.mle_fun [mlident, mlty, attrs] body in
        res, ECL.e_tag_pure
      | _ -> //last binder used for knot; replace it with the recursively bound name
        let body = LN.subst_st_term body [RT.DT 0 (wr R.(pack_ln (Tv_FVar rec_name)) Range.range_0)] in
        let body, tag = extract g body in
        body, tag
    )

    | _ -> T.fail "Unexpected recursive definition of non-function"

let extract_recursive_knot (g:env) (p:st_term)
                           (knot_name:R.fv) (knot_typ:R.term) =
    let g, tys, lb_typ, Some p = generalize g knot_typ (Some p) in
    let mlty = ECL.term_as_mlty g.uenv_inner lb_typ in
    let uenv, _mli, _ml_binding = ECL.extend_fv g.uenv_inner knot_name (tys, mlty) in
    let g = { g with uenv_inner = uenv } in
    let tm, tag = extract_recursive g p knot_name in
    let fv_name = 
      let lids = R.inspect_fv knot_name in
      if Nil? lids
      then T.raise (Extraction_failure "Unexpected empty name");
      FStar.List.Tot.last lids
    in
    debug_ g (fun _ -> Printf.sprintf "Extracted term (%s): %s\n" fv_name (ECL.mlexpr_to_string tm));
    let mllb = ECL.mk_mllb fv_name (tys, mlty) tm in
    Inl [ECL.mlm_let true [mllb]]

let extract_attrs (g:ECL.uenv) (se:R.sigelt) : T.Tac (list ECL.mlexpr) =
  se |> RU.get_attributes
     |> T.map (fun t -> let mlattr, _, _ = ECL.term_as_mlexpr g t in mlattr)

let extract_dv_binder (b:Pulse.Syntax.Base.binder) (q:option Pulse.Syntax.Base.qualifier)
  : T.Tac ECL.binder =
  let q =
    match q with
    | Some Implicit -> Some ECL.implicit_qual
    | _ -> None in
  ECL.mk_binder
    (ECL.rt_term_to_term b.binder_ty)
    (T.unseal b.binder_ppname.name)
    q
    (T.map (fun t -> ECL.rt_term_to_term t) (T.unseal b.binder_attrs))

let rec extract_dv_pattern (p:Pulse.Syntax.Base.pattern) : T.Tac ECL.pattern =
  match p with
  | Pat_Cons fv pats ->
    let fv = ECL.mk_fv fv.fv_name in
    let pats = T.map extract_dv_pattern (List.Tot.map fst pats) in
    ECL.mk_pat_cons fv pats
  | Pat_Constant c -> c |> ECL.mk_const |> ECL.mk_pat_constant
  | Pat_Var ppname sort -> ECL.mk_pat_var (T.unseal ppname) (sort |> T.unseal |> ECL.rt_term_to_term)
  | Pat_Dot_Term t -> ECL.mk_dot_pat (T.map_opt (fun t -> ECL.rt_term_to_term t) t)


// let unit_binder (ppname:string) : Dv binder =
//   mk_binder unit_ty ppname None []

let get_type_of_ref (p: term) : T.Tac ECL.term =
  let fail () = T.fail (Printf.sprintf "expected term (Pulse.Lib.Reference.ref ...), got %s" (term_to_string p)) in
  match R.inspect_ln p with
  | R.Tv_App hd (arg, _) ->
    (* TODO: check that hd is ref *)
    ECL.rt_term_to_term arg
  | _ -> fail ()

let get_type_of_array (p: term) : T.Tac ECL.term =
  let fail () = T.fail (Printf.sprintf "expected term (Pulse.Lib.Array.Core.array ...), got %s" (term_to_string p)) in
  match R.inspect_ln p with
  | R.Tv_App hd (arg, _) ->
    (* TODO: check that hd is array *)
    ECL.rt_term_to_term arg
  | _ -> fail ()

let rec extract_dv (p:st_term) : T.Tac ECL.term =
  if is_erasable p then ECL.mk_return ECL.unit_tm
  else begin
    match p.term with
    | Tm_IntroPure _
    | Tm_ElimExists _
    | Tm_IntroExists _ 
    | Tm_Rewrite _
    | Tm_ProofHintWithBinders _ -> ECL.mk_return ECL.unit_tm

    | Tm_Abs { b; q; body } ->
      let b = extract_dv_binder b q in
      let body = extract_dv body in
      ECL.mk_abs b body

    | Tm_Return { term } -> ECL.mk_return (ECL.rt_term_to_term term)

    | Tm_STApp { head; arg_qual; arg } ->
      let q =
        match arg_qual with
        | Some Implicit -> Some ECL.implicit_arg_qual
        | _ -> None in

      ECL.mk_app (ECL.rt_term_to_term head) q (ECL.rt_term_to_term arg)

    | Tm_Bind { binder; head; body } ->
      let b = extract_dv_binder binder None in
      let e1 = extract_dv head in
      let e2 = extract_dv body in
      //
      // TODO: type is same as the sort in b?
      //
      ECL.mk_let b e1 e2
    
    | Tm_TotBind { binder; head; body } ->
      let b = extract_dv_binder binder None in
      let e1 = ECL.mk_return (ECL.rt_term_to_term head) in
      let e2 = extract_dv body in
      ECL.mk_let b e1 e2
    
    | Tm_If { b; then_; else_ } ->
      let b = ECL.rt_term_to_term b in
      let then_ = extract_dv then_ in
      let else_ = extract_dv else_ in
      ECL.mk_if b then_ else_

    | Tm_Match { sc; brs } ->
      ECL.mk_match (ECL.rt_term_to_term sc) (T.map extract_dv_branch brs)

    | Tm_While { condition; body } ->
      let condition = extract_dv condition in
      let body = extract_dv body in
      let unit_binder ppname = ECL.mk_binder ECL.unit_ty ppname None [] in
      ECL.mk_app
        (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Dv"; "while_"]))
                    None
                    (ECL.mk_abs (unit_binder "while_cond") condition))
        None
        (ECL.mk_abs (unit_binder "while_body") body)

    | Tm_Par { body1; body2 } ->
      let body1 = extract_dv body1 in
      let body2 = extract_dv body2 in
      let unit_binder ppname = ECL.mk_binder ECL.unit_ty ppname None [] in
      ECL.mk_app
        (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Dv"; "par_"]))
                    None
                    (ECL.mk_abs (unit_binder "par_b1") body1))
        None
        (ECL.mk_abs (unit_binder "par_b2") body2)

    | Tm_WithLocal { binder; initializer; body } ->
      let b = extract_dv_binder binder None in
      let body = extract_dv body in
      let allocator = ECL.mk_app (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Reference"; "alloc"]))
        (Some ECL.implicit_arg_qual) (get_type_of_ref binder.binder_ty)) None (ECL.rt_term_to_term initializer) in
      ECL.mk_let b allocator body

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      let b = extract_dv_binder binder None in
      let body = extract_dv body in
      //
      // Slice library doesn't have an alloc
      //
      // This is parsed by Pulse2Rust
      //
      let allocator = ECL.mk_app (ECL.mk_app (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Array"; "Core"; "alloc"]))
        (Some ECL.implicit_arg_qual) (get_type_of_array binder.binder_ty)) None (ECL.rt_term_to_term initializer)) None (ECL.rt_term_to_term length) in
      ECL.mk_let b allocator body

    | Tm_Admit _ ->
      T.print "Admit in dv extraction is currently ignored";
      ECL.mk_return ECL.unit_tm

    | Tm_Unreachable -> ECL.mk_return ECL.unit_tm

    | Tm_WithInv { body } -> extract_dv body

  end

and extract_dv_branch (b:Pulse.Syntax.Base.branch) : T.Tac ECL.branch =
  let pat, body = b in
  ECL.mk_branch (extract_dv_pattern pat) (extract_dv body)

let extract_dv_typ (t:R.typ) : T.Tac ECL.term =
  let bs, c = R.collect_arr_ln_bs t in
  let bs = T.map (fun b ->
    let bview = R.inspect_binder b in
    ECL.mk_binder
      (ECL.rt_term_to_term bview.sort)
      (T.unseal bview.ppname)
      (match bview.qual with
       | R.Q_Implicit -> Some ECL.implicit_qual
       | _ -> None)
      []) bs in
  match (R.inspect_comp c) with
  | R.C_Total t -> begin
    let hd, args = R.collect_app_ln t in
    //
    // TODO: (sanity?) check hd for the effect
    //
    if L.length args = 0
    then T.fail (Printf.sprintf "Unexpected return type in extract_dv_typ: %s" (T.term_to_string t))
    else let ret_typ = args |> L.hd |> fst |> ECL.rt_term_to_term in
         ECL.mk_arrow bs ret_typ
    end
  | _ ->
    T.fail
      (Printf.sprintf "Unexpected arrow comp in extract_dv_typ: %s" (T.term_to_string t))

let extract_pulse_dv (uenv:ECL.uenv) (p:st_term) : T.Tac ECL.term =
  let g = { uenv_inner=uenv; coreenv=ECL.initial_core_env uenv } in
  let p = erase_ghost_subterms g p in
  let p = simplify_st_term g p in

  extract_dv p

let extract_pulse (uenv:ECL.uenv) (selt:R.sigelt) (p:st_term)
  : T.Tac (either ECL.mlmodule string) =
  
  let g = { uenv_inner=uenv; coreenv=ECL.initial_core_env uenv } in
  debug g (fun _ -> Printf.sprintf "About to extract:\n%s\n" (st_term_to_string p));
  let open T in
  try
    let sigelt_view = R.inspect_sigelt selt in
    match sigelt_view with
    | R.Sg_Let is_rec lbs -> (
      if is_rec || List.length lbs <> 1
      then T.raise (Extraction_failure "Extraction of recursive lets is not yet supported")
      else (
        let {lb_fv; lb_typ} = R.inspect_lb (List.Tot.hd lbs) in
        match is_recursive g lb_fv selt with
        | Some _ ->
          extract_recursive_knot g p lb_fv lb_typ
        | _ ->
          let p = erase_ghost_subterms g p in
          let p = simplify_st_term g p in
          let fv_name = R.inspect_fv lb_fv in
          if Nil? fv_name
          then T.raise (Extraction_failure "Unexpected empty name");
          
          let g, tys, lb_typ, Some p = generalize g lb_typ (Some p) in
          let mlty = ECL.term_as_mlty g.uenv_inner lb_typ in
          let tm, tag = extract g p in
          let fv_name = FStar.List.Tot.last fv_name in
          debug_ g (fun _ -> Printf.sprintf "Extracted term (%s): %s\n" fv_name (ECL.mlexpr_to_string tm));
          let attrs = extract_attrs uenv selt in
          let mllb = ECL.mk_mllb_with_attrs fv_name (tys, mlty) tm attrs in
          Inl [ECL.mlm_let_with_attrs false [mllb] attrs]
      )
    )
    | _ -> T.raise (Extraction_failure "Unexpected sigelt")
  with
  | Extraction_failure msg -> 
    Inr msg
  | e ->
    Inr (Printf.sprintf "Unexpected extraction error: %s" (RU.print_exn e))

let extract_pulse_sig (g:ECL.uenv) (selt:R.sigelt) (p:st_term)
  : T.Tac (either (ECL.uenv & ECL.iface) string) =

  let open T in
  try
    let sigelt_view = R.inspect_sigelt selt in
    match sigelt_view with
    | R.Sg_Let is_rec lbs ->
      if is_rec || List.length lbs <> 1
      then T.raise (Extraction_failure "Extraction of iface for recursive lets is not yet supported")
      else
        let {lb_fv; lb_typ} = R.inspect_lb (List.Tot.hd lbs) in
        let g0 = g in
        let g = { uenv_inner=g; coreenv=ECL.initial_core_env g } in
        let g, tys, lb_typ, _ = generalize g lb_typ None in
        debug_ g (fun _ -> Printf.sprintf "Extracting ml typ: %s\n" (T.term_to_string lb_typ));
        let mlty = ECL.term_as_mlty g.uenv_inner lb_typ in
        let g, _, e_bnd = ECL.extend_fv g0 lb_fv (tys, mlty) in
        Inl (g, ECL.iface_of_bindings [lb_fv, e_bnd])
    | _ -> T.raise (Extraction_failure "Unexpected sigelt")    
  with
  | Extraction_failure msg ->  Inr msg
  | e ->
    Inr (Printf.sprintf "Unexpected extraction error (iface): %s" (RU.print_exn e))

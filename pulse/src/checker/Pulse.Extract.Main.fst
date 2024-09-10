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
module E = Pulse.Typing.Env
module LN = Pulse.Syntax.Naming
module RU = Pulse.RuntimeUtils

//
// Not opening this module, it also defines a term type
//
module ECL = Pulse.Extract.CompilerLib

exception Extraction_failure of string

type env = Pulse.Typing.Env.env

let name = ppname & nat

let debug (g:env) (f: unit -> T.Tac string)
  : T.Tac unit
  = if RU.debug_at_level (E.fstar_env g) "pulse_extraction"
    then T.print (f())

let extend_env' (g:env) ppname ty
  : T.Tac (env & nvar)
  = let x = E.fresh g in
    let g = E.push_binding g x ppname ty in
    g, (ppname, x)

let extend_env'_binder (g:env) (b: binder) =
  extend_env' g b.binder_ppname b.binder_ty

module R = FStar.Reflection.V2

let rec extend_env'_pattern g (p:Pulse.Syntax.Base.pattern) :
    T.Tac (env & list Pulse.Typing.Env.binding) =
  match p with
  | Pat_Cons fv pats ->
    let g, bs = extend_env'_patterns g (List.Tot.map fst pats) in
    g, bs
  | Pat_Constant c ->
    g, []
  | Pat_Var ppname sort ->
    let ty = T.unseal sort in
    let g, (_, x) = extend_env' g (mk_ppname ppname Range.range_0) ty in
    g, [x, ty]
  | Pat_Dot_Term t ->
    g, []
and extend_env'_patterns g (ps:list Pulse.Syntax.Base.pattern) :
    T.Tac (env & list Pulse.Typing.Env.binding) =
  match ps with
  | [] -> g, []
  | p::ps ->
    let g, bs = extend_env'_pattern g p in
    let g, bs' = extend_env'_patterns g ps in
    g, bs@bs'

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

let fresh (g:env) = Pulse.Typing.fresh g

let push_binding (g:env) (x:var { ~ (x `Set.mem` E.dom g )}) (b:binder) =
  E.push_binding g x b.binder_ppname b.binder_ty

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
  let g, bs = extend_env'_pattern g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = simplify_st_term g body in
  pat, Pulse.Syntax.Naming.close_st_term_n body (L.map fst bs)

let erase_type_for_extraction (g:env) (t:term) : T.Tac bool =
  RU.must_erase_for_extraction (E.fstar_env g) t

let rec erase_ghost_subterms (g:env) (p:st_term) : T.Tac st_term =
  let open Pulse.Syntax.Naming in

  let fresh (g:env) = Pulse.Typing.fresh g in
  let push_binding g x b =
    E.push_binding g x b.binder_ppname b.binder_ty in

  let open_erase_close (g:env) (b:binder) (e:st_term) : T.Tac st_term =
    let x = fresh g in
    let e = open_st_term' e (tm_var { nm_index = x; nm_ppname = b.binder_ppname }) 0 in
    let e = erase_ghost_subterms (push_binding g x b) e in
    close_st_term' e x 0 in

  let unit_tm =
    { p with term = Tm_Return { expected_type=tm_unknown; insert_eq = false; term = ECL.unit_tm } }
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
      then let body = LN.subst_st_term body [RT.DT 0 ECL.unit_tm] in
           erase_ghost_subterms g body
      else let head = erase_ghost_subterms g head in
           let body = open_erase_close g binder body in
           ret (Tm_Bind { binder; head; body })

    | Tm_TotBind { binder; head; body } ->
      if erase_type_for_extraction g binder.binder_ty
      then let body = LN.subst_st_term body [RT.DT 0 ECL.unit_tm] in
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
  let g, bs = extend_env'_pattern g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = erase_ghost_subterms g body in
  pat, Pulse.Syntax.Naming.close_st_term_n body (L.map fst bs)

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

let rec extract_dv_pattern g (p:Pulse.Syntax.Base.pattern) :
    T.Tac (env & ECL.pattern & list Pulse.Typing.Env.binding) =
  match p with
  | Pat_Cons fv pats ->
    let fv = ECL.mk_fv fv.fv_name in
    let g, pats, bs = extract_dv_patterns g (List.Tot.map fst pats) in
    g, ECL.mk_pat_cons fv pats, bs
  | Pat_Constant c ->
    g, c |> ECL.mk_const |> ECL.mk_pat_constant, []
  | Pat_Var ppname sort ->
    let pp = T.unseal ppname in
    let ty = T.unseal sort in
    let g, (_, x) = extend_env' g (mk_ppname ppname Range.range_0) ty in
    g, ECL.mk_pat_var pp ty, [x, ty]
  | Pat_Dot_Term t ->
    g, ECL.mk_dot_pat t, []
and extract_dv_patterns g (ps:list Pulse.Syntax.Base.pattern) :
    T.Tac (env & list ECL.pattern & list Pulse.Typing.Env.binding) =
  match ps with
  | [] -> g, [], []
  | p::ps ->
    let g, p, bs = extract_dv_pattern g p in
    let g, ps, bs' = extract_dv_patterns g ps in
    g, p::ps, bs@bs'

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

open Pulse.Syntax.Naming
let rec extract_dv g (p:st_term) : T.Tac ECL.term =
  if is_erasable p then ECL.mk_return ECL.unit_tm
  else begin
    match p.term with
    | Tm_IntroPure _
    | Tm_ElimExists _
    | Tm_IntroExists _ 
    | Tm_Rewrite _
    | Tm_ProofHintWithBinders _ -> ECL.mk_return ECL.unit_tm

    | Tm_Abs { b; q; body } ->
      let b' = extract_dv_binder b q in
      let g, x = extend_env'_binder g b in
      let body = extract_dv g (open_st_term_nv body x) in
      ECL.mk_abs b' (close_term body x._2)

    | Tm_Return { term } -> ECL.mk_return (ECL.rt_term_to_term term)

    | Tm_STApp { head; arg_qual; arg } ->
      let q =
        match arg_qual with
        | Some Implicit -> Some ECL.implicit_arg_qual
        | _ -> None in

      ECL.mk_app (ECL.rt_term_to_term head) q (ECL.rt_term_to_term arg)

    | Tm_Bind { binder; head; body } ->
      let b' = extract_dv_binder binder None in
      let e1 = extract_dv g head in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' e1 (close_term body x._2)
    
    | Tm_TotBind { binder; head; body } ->
      let b' = extract_dv_binder binder None in
      let e1 = ECL.mk_return (ECL.rt_term_to_term head) in
      let g, x = extend_env'_binder g binder in
      let e2 = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' e1 (close_term e2 x._2)
    
    | Tm_If { b; then_; else_ } ->
      let b = ECL.rt_term_to_term b in
      let then_ = extract_dv g then_ in
      let else_ = extract_dv g else_ in
      ECL.mk_if b then_ else_

    | Tm_Match { sc; brs } ->
      ECL.mk_match (ECL.rt_term_to_term sc) (T.map (extract_dv_branch g) brs)

    | Tm_While { condition; body } ->
      let condition = extract_dv g condition in
      let body = extract_dv g body in
      let unit_binder ppname = ECL.mk_binder ECL.unit_ty ppname None [] in
      ECL.mk_app
        (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Dv"; "while_"]))
                    None
                    (ECL.mk_abs (unit_binder "while_cond") condition))
        None
        (ECL.mk_abs (unit_binder "while_body") body)

    | Tm_Par { body1; body2 } ->
      let body1 = extract_dv g body1 in
      let body2 = extract_dv g body2 in
      let unit_binder ppname = ECL.mk_binder ECL.unit_ty ppname None [] in
      ECL.mk_app
        (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Dv"; "par"]))
                    None
                    (ECL.mk_abs (unit_binder "par_b1") body1))
        None
        (ECL.mk_abs (unit_binder "par_b2") body2)

    | Tm_WithLocal { binder; initializer; body } ->
      let b' = extract_dv_binder binder None in
      let allocator = ECL.mk_app (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Reference"; "alloc"]))
        (Some ECL.implicit_arg_qual) (get_type_of_ref binder.binder_ty)) None (ECL.rt_term_to_term initializer) in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' allocator (close_term body x._2)

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      let b' = extract_dv_binder binder None in
      //
      // Slice library doesn't have an alloc
      //
      // This is parsed by Pulse2Rust
      //
      let allocator = ECL.mk_app (ECL.mk_app (ECL.mk_app (ECL.mk_fv_tm (ECL.mk_fv ["Pulse"; "Lib"; "Array"; "Core"; "alloc"]))
        (Some ECL.implicit_arg_qual) (get_type_of_array binder.binder_ty)) None (ECL.rt_term_to_term initializer)) None (ECL.rt_term_to_term length) in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' allocator (close_term body x._2)

    | Tm_Admit _ ->
      T.print "Admit in dv extraction is currently ignored";
      ECL.mk_return ECL.unit_tm

    | Tm_Unreachable -> ECL.mk_return ECL.unit_tm

    | Tm_WithInv { body } -> extract_dv g body

  end

and extract_dv_branch g (b:Pulse.Syntax.Base.branch) : T.Tac ECL.branch =
  let pat, body = b in
  let g, pat, bs = extract_dv_pattern g pat in
  ECL.mk_branch pat (RT.close_term_bs bs (extract_dv g (Pulse.Checker.Match.open_st_term_bs body bs)))

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

let extract_pulse_dv (g: env) (p:st_term) : T.Tac ECL.term =
  let p = erase_ghost_subterms g p in
  let p = simplify_st_term g p in
  extract_dv g p

let rec extract_dv_recursive g (p:st_term) (rec_name:R.fv)
  : T.Tac ECL.term
  = match p.term with
    | Tm_Abs { b; q; body } -> (
      match body.term with
      | Tm_Abs _ ->
        let g, x = extend_env'_binder g b in
        let body = open_st_term_nv body x in
        let body = extract_dv_recursive g body rec_name in
        ECL.mk_abs (extract_dv_binder b q) (close_term body x._2)
      | _ -> //last binder used for knot; replace it with the recursively bound name
        let body = LN.subst_st_term body [RT.DT 0 (wr R.(pack_ln (Tv_FVar rec_name)) Range.range_0)] in
        extract_pulse_dv g body
    )

    | _ -> T.fail "Unexpected recursive definition of non-function"

let rec extract_dv_ghost g (p:st_term)
  : T.Tac ECL.term
  = match p.term with
    | Tm_Abs { b; q; body } -> (
        let g, x = extend_env'_binder g b in
        let body = open_st_term_nv body x in
        let body = extract_dv_ghost g body in
        ECL.mk_abs (extract_dv_binder b q) (close_term body x._2)
    )

    | _ -> ECL.unit_tm


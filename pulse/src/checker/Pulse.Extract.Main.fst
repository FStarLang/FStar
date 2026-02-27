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
open Pulse.Reflection.Util

module L = FStar.List.Tot
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module E = Pulse.Typing.Env
module LN = Pulse.Syntax.Naming
module RU = Pulse.RuntimeUtils

//
// Not opening this module, it also defines a term type
//
module ECL = Pulse.Extract.CompilerLib

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
    T.Tac (env & list Pulse.Typing.Env.var_binding) =
  match p with
  | Pat_Cons fv pats ->
    let g, bs = extend_env'_patterns g (List.Tot.map fst pats) in
    g, bs
  | Pat_Constant c ->
    g, []
  | Pat_Var ppname sort ->
    let ty = T.unseal sort in
    let n = mk_ppname ppname Range.range_0 in
    let g, (_, x) = extend_env' g n ty in
    g, [{n; x; ty} <: Pulse.Typing.Env.var_binding]
  | Pat_Dot_Term t ->
    g, []
and extend_env'_patterns g (ps:list Pulse.Syntax.Base.pattern) :
    T.Tac (env & list Pulse.Typing.Env.var_binding) =
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

open Pulse.Typing { fresh }

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
  s = "_br" ||
  s = "__"

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

  let mk t : st_term = {
    range = e.range;
    effect_tag = default_effect_hint;
    term = t;
    source=Sealed.seal false;
    seq_lhs=Sealed.seal false;
  } in
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
  | Tm_ST _
  | Tm_Rewrite _
  | Tm_Admit _
  | Tm_Goto _
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
        if is_return_bv0 body then
          // apply `let x = e in x ~~> e`
          head
        else
          ret (Tm_Bind { binder; head; body })
    end

  | Tm_TotBind { binder; head; body } ->
    ret (Tm_TotBind { binder; head; body = with_open binder body })

  | Tm_If { b; then_; else_; post } ->
    ret (Tm_If { b; then_ = simplify_st_term g then_; else_ = simplify_st_term g else_; post })

  | Tm_Match { sc; returns_; brs } ->
    ret (Tm_Match { sc; returns_; brs = T.map (simplify_branch g) brs })

  | Tm_NuWhile { invariant; loop_requires; meas; condition; body } ->
    let condition = simplify_st_term g condition in
    let body = simplify_st_term g body in
    { e with term = Tm_NuWhile { invariant; loop_requires; meas; condition; body } }

  | Tm_WithLocal { binder; initializer; body } ->
    ret (Tm_WithLocal { binder; initializer; body = with_open binder body })
  
  | Tm_WithLocalArray { binder; initializer; length; body } ->
    ret (Tm_WithLocalArray { binder; initializer; length; body = with_open binder body })
    
  | Tm_PragmaWithOptions { body } ->
    simplify_st_term g body

  | Tm_Unreachable _ -> e

  | Tm_ForwardJumpLabel { lbl; body; post } ->
    let open Pulse.Syntax.Naming in
    let x = fresh g in
    let e = open_st_term' body (tm_var { nm_index = x; nm_ppname = lbl }) 0 in
    let e = simplify_st_term (E.push_goto g x lbl post) e in
    if x `Set.mem` freevars_st e then
      let e = close_st_term' e x 0 in
      ret (Tm_ForwardJumpLabel { lbl; body = e; post })
    else
      e

and simplify_branch (g:env) (b:branch) : T.Tac branch =
  let {pat; e=body; norw} = b in
  let g, bs = extend_env'_pattern g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = simplify_st_term g body in
  let body = Pulse.Syntax.Naming.close_st_term_n body (L.map (fun (b: Pulse.Typing.Env.var_binding) -> b.x) bs) in
  {pat; e=body; norw}

let erase_type_for_extraction (g:env) (t:term) : T.Tac bool =
  RU.must_erase_for_extraction (E.fstar_env g) t

let rec erase_ghost_subterms (g:env) (p:st_term) : T.Tac st_term =
  let open Pulse.Syntax.Naming in

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

    | Tm_ST _ -> p

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

    | Tm_NuWhile { invariant; loop_requires; meas; condition; body } ->
      let condition = erase_ghost_subterms g condition in
      let body = erase_ghost_subterms g body in
      ret (Tm_NuWhile { invariant; loop_requires; meas; condition; body })

    | Tm_WithLocal { binder; initializer; body } ->
      let body = open_erase_close g binder body in
      ret (Tm_WithLocal { binder; initializer; body })

    | Tm_WithLocalArray { binder; initializer; length; body } ->
      let body = open_erase_close g binder body in
      ret (Tm_WithLocalArray { binder; initializer; length; body })

    | Tm_Unreachable _ -> p

    | Tm_Admit _ -> p

    | Tm_ProofHintWithBinders _ ->
      T.fail "erase_ghost_subterms: Unexpected constructor: ProofHintWithBinders should have been desugared away"

    | Tm_PragmaWithOptions { options; body } ->
      ret (Tm_PragmaWithOptions { options; body=erase_ghost_subterms g body })

    | Tm_ForwardJumpLabel { lbl; body; post } ->
      let open Pulse.Syntax.Naming in
      let x = fresh g in
      let e = open_st_term' body (tm_var { nm_index = x; nm_ppname = lbl }) 0 in
      let e = erase_ghost_subterms (E.push_goto g x lbl post) e in
      let e = close_st_term' e x 0 in
      ret (Tm_ForwardJumpLabel { lbl; body = e; post })

    | Tm_Goto _ -> p
      
  end

and erase_ghost_subterms_branch (g:env) (b:branch) : T.Tac branch =
  let {pat; e=body; norw} = b in
  let g, bs = extend_env'_pattern g pat in
  let body = Pulse.Checker.Match.open_st_term_bs body bs in
  let body = erase_ghost_subterms g body in
  let body = Pulse.Checker.Match.close_st_term_bs body bs in
  { pat; e=body; norw }

let extract_dv_binder (b:Pulse.Syntax.Base.binder) (q:option Pulse.Syntax.Base.qualifier)
  : T.Tac R.binder =
  R.pack_binder {
    sort = b.binder_ty;
    ppname =
      // "__" binders become `int __1 = f();` in karamel
      if T.unseal b.binder_ppname.name = "__" then
        T.seal "_"
      else
        b.binder_ppname.name;
    attrs = T.unseal b.binder_attrs;
    qual = (match q with
      | Some Implicit -> R.Q_Implicit

      (* This translation does not really have to respect implicit/explicit args,
      as that is irrelevant for extraction. We just make these explicit too. *)
      | Some TcArg -> R.Q_Explicit
      | Some (Meta t) -> R.Q_Explicit
      | None -> R.Q_Explicit);
  }

let rec extract_dv_pattern g (p:Pulse.Syntax.Base.pattern) :
    T.Tac (env & R.pattern & list Pulse.Typing.Env.var_binding) =
  match p with
  | Pat_Cons fv pats ->
    let fv = R.pack_fv fv.fv_name in
    let g, pats, bs = extract_dv_patterns g (List.Tot.map fst pats) in
    g, R.Pat_Cons fv None (L.map (fun p -> (p, false)) pats), bs
  | Pat_Constant c ->
    g, R.Pat_Constant c, []
  | Pat_Var ppname sort ->
    let ty = T.unseal sort in
    let n = mk_ppname ppname Range.range_0 in
    let g, (_, x) = extend_env' g n ty in
    g, R.Pat_Var sort ppname, [{n; x; ty} <: Pulse.Typing.Env.var_binding]
  | Pat_Dot_Term t ->
    g, R.Pat_Dot_Term t, []
and extract_dv_patterns g (ps:list Pulse.Syntax.Base.pattern) :
    T.Tac (env & list R.pattern & list Pulse.Typing.Env.var_binding) =
  match ps with
  | [] -> g, [], []
  | p::ps ->
    let g, p, bs = extract_dv_pattern g p in
    let g, ps, bs' = extract_dv_patterns g ps in
    g, p::ps, bs@bs'

let get_type_of_ref (p: term) : T.Tac R.term =
  let fail () = T.fail (Printf.sprintf "expected term (Pulse.Lib.Reference.ref ...), got %s" (term_to_string p)) in
  match R.inspect_ln p with
  | R.Tv_App hd (arg, _) ->
    (* TODO: check that hd is ref *)
    arg
  | _ -> fail ()

let get_type_of_array (p: term) : T.Tac R.term =
  let fail () = T.fail (Printf.sprintf "expected term (Pulse.Lib.Array.Core.array ...), got %s" (term_to_string p)) in
  match R.inspect_ln p with
  | R.Tv_App hd (arg, _) ->
    (* TODO: check that hd is array *)
    arg
  | _ -> fail ()

let mk_abs b e = R.pack_ln <| R.Tv_Abs b e

let unit_binder (ppname: string) =
  R.pack_binder {
    sort = ECL.unit_ty;
    ppname = Sealed.seal ppname;
    attrs = [];
    qual = R.Q_Explicit;
  }

let small_type0 = tm_constant R.C_Unit

open Pulse.Syntax.Naming
let rec extract_dv g (p:st_term) : T.Tac R.term =
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
      mk_abs b' (close_term body x._2)

    | Tm_Return { term } -> ECL.mk_return term

    | Tm_ST { t } -> ECL.mk_meta_monadic t

    | Tm_Bind { binder; head; body } ->
      let b' = extract_dv_binder binder None in
      let e1 = extract_dv g head in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv g (open_st_term_nv body x) in
      if Tm_Abs? head.term then
        // Create a pure let binding for inner functions.
        // This allow extraction to remove them if they're not used,
        // otherwise we get too much magic.
        ECL.mk_pure_let b' e1 (close_term body x._2)
      else
        ECL.mk_let b' e1 (close_term body x._2)

    | Tm_TotBind { binder; head; body } ->
      let b' = extract_dv_binder binder None in
      let e1 = ECL.mk_return head in
      let g, x = extend_env'_binder g binder in
      let e2 = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' e1 (close_term e2 x._2)

    | Tm_If { b; then_; else_ } ->
      let then_ = extract_dv g then_ in
      let else_ = extract_dv g else_ in
      ECL.mk_if b then_ else_

    | Tm_Match { sc; brs } ->
      R.pack_ln (R.Tv_Match sc None (T.map (extract_dv_branch g) brs))

    | Tm_NuWhile { condition; body } ->
      let condition = extract_dv g condition in
      let body = extract_dv g body in
      ECL.mk_meta_monadic
        (R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv ["Pulse"; "Lib"; "Dv"; "while_"])))
          [mk_abs (unit_binder "while_cond") condition, R.Q_Explicit;
           mk_abs (unit_binder "while_body") body, R.Q_Explicit])

    | Tm_WithLocal { binder; initializer; body } ->
      let b' = extract_dv_binder binder None in
      let allocator =
        match initializer with
        | Some initializer -> R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Reference"; "alloc"]) [u0]))
            [get_type_of_ref binder.binder_ty, R.Q_Implicit; small_type0, R.Q_Explicit; initializer, R.Q_Explicit]
        | None -> R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Reference"; "alloc_uninit"]) [u0]))
            [get_type_of_ref binder.binder_ty, R.Q_Implicit; small_type0, R.Q_Explicit; ECL.unit_tm, R.Q_Explicit]
      in
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
      let allocator =
        match initializer with
        | Some initializer -> R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Array"; "PtsTo"; "alloc"]) [u0]))
            [get_type_of_array binder.binder_ty, R.Q_Implicit; small_type0, R.Q_Explicit; initializer, R.Q_Explicit; length, R.Q_Explicit]
        | None -> R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Array"; "Core"; "mask_alloc"]) [u0]))
            [get_type_of_array binder.binder_ty, R.Q_Implicit; small_type0, R.Q_Explicit; length, R.Q_Explicit]
      in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv g (open_st_term_nv body x) in
      ECL.mk_let b' allocator (close_term body x._2)

    | Tm_Admit { typ } ->
      ECL.mk_meta_monadic
        (R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv ["Prims"; "admit"])))
          [typ, R.Q_Implicit; ECL.unit_tm, R.Q_Explicit])

    | Tm_Unreachable { c } ->
      ECL.mk_meta_monadic (R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv ["Pulse"; "Lib"; "Dv"; "unreachable"])))
        [comp_res c, R.Q_Explicit; unit_tm, R.Q_Explicit])

    | Tm_PragmaWithOptions { body } -> extract_dv g body

    | Tm_Goto { lbl; arg } ->
      let lblv: var =
        match R.inspect_ln lbl with
        | R.Tv_Var lbl -> (R.inspect_namedv lbl).uniq
        | _ -> T.fail (Printf.sprintf "invalid goto, label not var: %s" (show p)) in
      let (lbln, c): ppname & st_comp =
        match E.lookup_goto g lblv with
        | Some (name, c) -> name, st_comp_of_comp c
        | _ -> T.fail (Printf.sprintf "invalid goto, no matching block: %s" (show p)) in
      ECL.mk_meta_monadic <|  
        R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Dv"; "goto"]) [c.u])) [
          c.res, R.Q_Implicit;
          tm_var { nm_index = lblv; nm_ppname = lbln }, R.Q_Explicit;
          arg, R.Q_Explicit;
        ]
    
    | Tm_ForwardJumpLabel { lbl; body; post } ->
      let x = fresh g in
      let g' = E.push_goto g x lbl post in
      let body = extract_dv g' (open_st_term_nv body (lbl, x)) in
      let post = st_comp_of_comp post in
      ECL.mk_meta_monadic <|
        R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Dv"; "forward_jump_label"]) [post.u])) [
          post.res, R.Q_Implicit;
          R.pack_ln (R.Tv_Abs (R.pack_binder {
            sort = R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Dv"; "goto_label"]) [post.u]))
              [post.res, R.Q_Explicit];
            qual = R.Q_Explicit;
            attrs = [];
            ppname = lbl.name;
          }) (close_term body x)), R.Q_Explicit;
        ]

  end

and extract_dv_branch g (b:Pulse.Syntax.Base.branch) : T.Tac R.branch =
  let {pat; e=body; norw} = b in
  let g, pat, bs = extract_dv_pattern g pat in
  pat, LN.close_term_n
    (extract_dv g (Pulse.Checker.Match.open_st_term_bs body bs))
    (L.map (fun (b: Pulse.Typing.Env.var_binding) -> b.x) bs)

let extract_pulse_dv (g: env) (p:st_term) : T.Tac ECL.term =
  debug g (fun _ -> Printf.sprintf "input: %s" (show p));
  let p = erase_ghost_subterms g p in
  debug g (fun _ -> Printf.sprintf "post erasure: %s" (show p));
  let p = simplify_st_term g p in
  debug g (fun _ -> Printf.sprintf "after simp: %s" (show p));
  let p = Pulse.ElimGoto.elim_gotos g p in
  debug g (fun _ -> Printf.sprintf "post goto elim: %s" (show p));
  let p = extract_dv g p in
  debug g (fun _ -> Printf.sprintf "output: %s" (show p));
  p

let rec extract_dv_recursive g (p:st_term) (rec_name:R.fv)
  : T.Tac ECL.term
  = match p.term with
    | Tm_Abs { b; q; body } -> (
      match body.term with
      | Tm_Abs _ ->
        let g, x = extend_env'_binder g b in
        let body = open_st_term_nv body x in
        let body = extract_dv_recursive g body rec_name in
        mk_abs (extract_dv_binder b q) (close_term body x._2)
      | _ -> //last binder used for knot; replace it with the recursively bound name
        let body = LN.subst_st_term body [RT.DT 0 (wr R.(pack_ln (Tv_FVar rec_name)) Range.range_0)] in
        extract_pulse_dv g body
    )

    | _ -> T.fail "Unexpected recursive definition of non-function"

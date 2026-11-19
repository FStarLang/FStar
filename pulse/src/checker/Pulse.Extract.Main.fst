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

open Pulse.Typing.Env { env }
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

// Checked native nodes preserve the control structure that must bypass
// ElimGoto. The reserved result type also identifies automatically unwrapped
// calls, including calls whose exceptional post is False. Inspect before
// simplification, and keep ordinary outcome data on the non-native path.
let rec uses_native_exceptions (p:st_term) : Tot bool =
  let native ty = Some? (Pulse.Checker.Exceptions.outcome_types ty) in
  match p.term with
  | Tm_Raise _ | Tm_ExceptionScope _ | Tm_Try _ -> true
  | Tm_NativeRaise _ | Tm_NativeScope _ | Tm_NativeTry _ -> true
  | Tm_ForwardJumpLabel { body; post } ->
    native (comp_res post) || uses_native_exceptions body
  | Tm_Return { expected_type } -> native expected_type
  | Tm_Abs { body }
  | Tm_TotBind { body }
  | Tm_WithLocal { body }
  | Tm_WithLocalArray { body }
  | Tm_PragmaWithOptions { body } -> uses_native_exceptions body
  | Tm_Bind { binder; head; body } ->
    native binder.binder_ty ||
    uses_native_exceptions head || uses_native_exceptions body
  | Tm_ST { args } -> uses_native_exceptions_list args
  | Tm_If { b; then_; else_ } ->
    uses_native_exceptions b ||
    uses_native_exceptions then_ || uses_native_exceptions else_
  | Tm_Match { sc; brs } ->
    uses_native_exceptions sc ||
    uses_native_exceptions_branches brs
  | Tm_While { condition; body } ->
    uses_native_exceptions condition || uses_native_exceptions body
  | Tm_Defer { handler; body } ->
    uses_native_exceptions handler || uses_native_exceptions body
  | Tm_ProofHintWithBinders { t } -> uses_native_exceptions t
  | Tm_IntroPure _ | Tm_ElimExists _ | Tm_IntroExists _
  | Tm_Rewrite _ | Tm_Admit _ | Tm_Unreachable _ | Tm_Goto _ -> false

and uses_native_exceptions_list (ps:list st_term) : Tot bool =
  match ps with
  | [] -> false
  | p::ps -> uses_native_exceptions p || uses_native_exceptions_list ps

and uses_native_exceptions_branches (bs:list branch) : Tot bool =
  match bs with
  | [] -> false
  | b::bs -> uses_native_exceptions b.e || uses_native_exceptions_branches bs

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
    let n = mk_ppname ppname range_0 in
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
  let tag = p.effect_tag in
  match tag with
  | Some STT_Ghost -> true
  | _ -> false
    
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
    source=false;
    seq_lhs=false;
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
  // Exception checking must precede simplification. Only the resulting
  // outcome matches/lexical jumps may be simplified; dropping an unchecked
  // scope or clause here could hide an unproved exceptional resource transfer.
  | Tm_Raise _ | Tm_ExceptionScope _ | Tm_Try _ ->
    T.fail "Internal error: unchecked exception syntax in simplification"
  | Tm_NativeRaise _ -> e
  | Tm_NativeScope { body } -> ret (Tm_NativeScope { body=simplify_st_term g body })
  | Tm_NativeTry { exn_ty; result_ty; body; handler } ->
    let b = mk_binder_ppname exn_ty ppname_default in
    ret (Tm_NativeTry { exn_ty; result_ty;
                       body=simplify_st_term g body; handler=with_open b handler })
  | Tm_Return _
  | Tm_IntroPure _
  | Tm_ElimExists _
  | Tm_IntroExists _
  | Tm_ST _
  | Tm_Rewrite _
  | Tm_Admit _
  | Tm_Goto _
  | Tm_ProofHintWithBinders _ -> e

  | Tm_Defer { result_ty; handler_pre; handler; body } ->
    ret (Tm_Defer { result_ty; handler_pre; handler = simplify_st_term g handler; body = simplify_st_term g body })

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

  | Tm_If { b; then_; else_; pre; post } ->
    ret (Tm_If { b = simplify_st_term g b; then_ = simplify_st_term g then_; else_ = simplify_st_term g else_; pre; post })

  | Tm_Match { sc; returns_; brs } ->
    ret (Tm_Match { sc = simplify_st_term g sc; returns_; brs = T.map (simplify_branch g) brs })

  | Tm_While { invariant; loop_requires; meas; condition; body } ->
    let condition = simplify_st_term g condition in
    let body = simplify_st_term g body in
    { e with term = Tm_While { invariant; loop_requires; meas; condition; body } }

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
    // Native exceptions are stateful, not proof annotations to erase. Their
    // unchecked syntax has no extraction meaning; its contracts must already
    // have been discharged and its control flow lowered by Exceptions.
    | Tm_Raise _ | Tm_ExceptionScope _ | Tm_Try _ ->
      T.fail "Internal error: unchecked exception syntax in erasure"
    | Tm_NativeRaise _ -> p
    | Tm_NativeScope { body } -> ret (Tm_NativeScope { body=erase_ghost_subterms g body })
    | Tm_NativeTry { exn_ty; result_ty; body; handler } ->
      ret (Tm_NativeTry { exn_ty; result_ty; body=erase_ghost_subterms g body;
                         handler=open_erase_close g (mk_binder_ppname exn_ty ppname_default) handler })
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

    | Tm_If { b; then_; else_; pre; post } ->
      let b = erase_ghost_subterms g b in
      let then_ = erase_ghost_subterms g then_ in
      let else_ = erase_ghost_subterms g else_ in
      ret (Tm_If { b; then_; else_; pre; post })

    | Tm_Match { sc; brs; returns_ } ->
      let sc = erase_ghost_subterms g sc in
      let brs = T.map (erase_ghost_subterms_branch g) brs in
      ret (Tm_Match { sc; brs; returns_ })

    | Tm_While { invariant; loop_requires; meas; condition; body } ->
      let condition = erase_ghost_subterms g condition in
      let body = erase_ghost_subterms g body in
      ret (Tm_While { invariant; loop_requires; meas; condition; body })

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

    | Tm_Defer { result_ty; handler_pre; handler; body } ->
      ret (Tm_Defer { result_ty; handler_pre; handler = erase_ghost_subterms g handler; body = erase_ghost_subterms g body })
      
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
    attrs = b.binder_attrs;
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
    let n = mk_ppname ppname range_0 in
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
let runtime_binder ty name =
  R.pack_binder { sort=ty; ppname=T.seal name; attrs=[]; qual=R.Q_Explicit }

let runtime_app name tys args =
  R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv name)))
    (L.map (fun t -> t, R.Q_Implicit) tys @ L.map (fun t -> t, R.Q_Explicit) args)

let runtime_bv0 = tm_bvar { bv_index=0; bv_ppname=ppname_default }
let runtime_exn = R.pack_ln (R.Tv_FVar (R.pack_fv ["Prims"; "exn"]))
let runtime_dyn = R.pack_ln (R.Tv_FVar (R.pack_fv ["FStar"; "Dyn"; "dyn"]))
let runtime_raise ty arg =
  ECL.mk_meta_monadic (runtime_app ["FStar"; "All"; "raise"] [ty] [arg])
let runtime_seq head body =
  // Callers keep surrounding binders opened as named variables.
  ECL.mk_let (runtime_binder ECL.unit_ty "_cleanup") head body
let runtime_try ty body handler =
  ECL.mk_meta_monadic (runtime_app ["FStar"; "All"; "try_with"] [ty]
    [mk_abs (unit_binder "_try") body; handler])

let rec extract_dv native g (p:st_term) : T.Tac R.term =
  if is_erasable p then ECL.mk_return ECL.unit_tm
  else begin
    match p.term with
    // Do not map source raise/try directly to host-language exceptions. The
    // checker has selected lexical destinations and accounted for cleanup;
    // extraction consumes that checked lowering, not a second exception model.
    | Tm_Raise _ | Tm_ExceptionScope _ | Tm_Try _ ->
      T.fail "Internal error: unchecked exception syntax in extraction"
    | Tm_NativeRaise { exn_ty; result_ty; arg } ->
      let packed = runtime_app ["FStar"; "Dyn"; "mkdyn"] [exn_ty] [arg] in
      runtime_raise result_ty
        (runtime_app ["Pulse"; "Lib"; "NativeExceptions"; "NativeException"] [] [packed])
    | Tm_NativeScope { body } -> extract_dv native g body
    | Tm_NativeTry { exn_ty; result_ty; body; handler } ->
      let body = extract_dv native g body in
      let b = mk_binder_ppname exn_ty ppname_default in
      let g', payload = extend_env'_binder g b in
      let handler = extract_dv native g' (open_st_term_nv handler payload) in
      let unpack = runtime_app ["FStar"; "Dyn"; "undyn"] [exn_ty] [runtime_bv0] in
      let handler = ECL.mk_let (extract_dv_binder b None) unpack (close_term handler payload._2) in
      // Only Pulse's payload channel is caught. Lexical returns/breaks and
      // foreign host exceptions must unwind through this handler unchanged.
      let branches = [
        R.Pat_Cons (R.pack_fv ["Pulse"; "Lib"; "NativeExceptions"; "NativeException"]) None
          [R.Pat_Var (T.seal runtime_dyn) (T.seal "_payload"), false], handler;
        R.Pat_Var (T.seal runtime_exn) (T.seal "_other"),
          runtime_raise result_ty runtime_bv0
      ] in
      runtime_try result_ty body
        (mk_abs (runtime_binder runtime_exn "_caught") (R.pack_ln (R.Tv_Match runtime_bv0 None branches)))
    | Tm_IntroPure _
    | Tm_ElimExists _
    | Tm_IntroExists _ 
    | Tm_Rewrite _
    | Tm_ProofHintWithBinders _ -> ECL.mk_return ECL.unit_tm

    | Tm_Abs { b; q; body } ->
      let b' = extract_dv_binder b q in
      let g, x = extend_env'_binder g b in
      let body = extract_dv native g (open_st_term_nv body x) in
      mk_abs b' (close_term body x._2)

    | Tm_Return { term } -> ECL.mk_return term

    | Tm_ST { t } -> ECL.mk_meta_monadic t

    | Tm_Bind { binder; head; body } ->
      let b' = extract_dv_binder binder None in
      let e1 = extract_dv native g head in
      let g, x = extend_env'_binder g binder in
      let body = extract_dv native g (open_st_term_nv body x) in
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
      let e2 = extract_dv native g (open_st_term_nv body x) in
      ECL.mk_let b' e1 (close_term e2 x._2)

    | Tm_If { b; then_; else_ } ->
      let b = (match b.term with
               | Tm_Return { term } -> term
               | _ -> extract_dv native g b) in
      let then_ = extract_dv native g then_ in
      let else_ = extract_dv native g else_ in
      ECL.mk_if b then_ else_

    | Tm_Match { sc; brs } ->
      let sc = (match sc.term with
                | Tm_Return { term } -> term
                | _ -> extract_dv native g sc) in
      R.pack_ln (R.Tv_Match sc None (T.map (extract_dv_branch native g) brs))

    | Tm_While { condition; body } ->
      let condition = extract_dv native g condition in
      let body = extract_dv native g body in
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
      let body = extract_dv native g (open_st_term_nv body x) in
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
      let body = extract_dv native g (open_st_term_nv body x) in
      ECL.mk_let b' allocator (close_term body x._2)

    | Tm_Admit { typ } ->
      ECL.mk_meta_monadic
        (R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv ["Prims"; "admit"])))
          [typ, R.Q_Implicit; ECL.unit_tm, R.Q_Explicit])

    | Tm_Unreachable { c } ->
      ECL.mk_meta_monadic (R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv ["Pulse"; "Lib"; "Dv"; "unreachable"])))
        [comp_res c, R.Q_Explicit; unit_tm, R.Q_Explicit])

    | Tm_PragmaWithOptions { body } -> extract_dv native g body

    | Tm_Goto { lbl; arg } ->
      let lblv: var =
        match R.inspect_ln lbl with
        | R.Tv_Var lbl -> (R.inspect_namedv lbl).uniq
        | _ -> T.fail (Printf.sprintf "invalid goto, label not var: %s" (show p)) in
      let (lbln, c): ppname & st_comp =
        match E.lookup_goto g lblv with
        | Some (name, c) -> name, st_comp_of_comp c
        | _ -> T.fail (Printf.sprintf "invalid goto, no matching block: %s" (show p)) in
      let call = ECL.mk_meta_monadic (R.mk_app (tm_var { nm_index=lblv; nm_ppname=lbln }) [arg, R.Q_Explicit]) in
      // The label function's ABI returns unit, but a jump's continuation has
      // any result type. It cannot run: every label function throws.
      runtime_seq call (ECL.mk_meta_monadic
        (runtime_app ["Pulse"; "Lib"; "Dv"; "unreachable"] [] [tm_unknown; ECL.unit_tm]))
    
    | Tm_ForwardJumpLabel { lbl; body; post } ->
      // A lexical jump carries its value in a scoped slot and throws on a
      // separate channel. None initializes the slot safely even for managed
      // Cherry values. Recursion is safe: each activation catches its own exit,
      // and the checker forbids capturing a label across a function boundary.
      let ty = comp_res post in
      let option_ty = runtime_app ["FStar"; "Pervasives"; "Native"; "option"] [] [ty] in
      let slot_b = mk_binder_ppname (Pulse.Typing.mk_ref option_ty) (mk_ppname_no_range "_jump_result") in
      let g', slot = extend_env'_binder g slot_b in
      let x = fresh g' in
      let g' = E.push_goto g' x lbl post in
      let body = extract_dv native g' (open_st_term_nv body (lbl, x)) in
      let key = String.concat "." (T.cur_module ()) ^ "." ^ Printf.sprintf "%d" (RU.next_id ()) in
      let key_tm = R.pack_ln (R.Tv_Const (R.C_String key)) in
      let jump = runtime_app ["Pulse"; "Lib"; "NativeExceptions"; "ControlFlow"] [] [key_tm] in
      let some = runtime_app ["FStar"; "Pervasives"; "Native"; "Some"] [ty] [runtime_bv0] in
      let write = ECL.mk_meta_monadic
        (runtime_app ["Pulse"; "Lib"; "Reference"; "write"] [option_ty] [term_of_nvar slot; some]) in
      let label_fn = mk_abs (runtime_binder ty "_jump_value")
        (runtime_seq write (runtime_raise ECL.unit_ty jump)) in
      let label_ty = runtime_app ["Pulse"; "Lib"; "Dv"; "goto_label"] [] [ty] in
      let body = ECL.mk_pure_let (R.pack_binder { sort=label_ty; ppname=lbl.name; attrs=[]; qual=R.Q_Explicit })
        label_fn (close_term body x) in
      let read = ECL.mk_meta_monadic (R.mk_app
        (R.pack_ln (R.Tv_UInst (R.pack_fv ["Pulse"; "Lib"; "Reference"; "read"]) [u0]))
        [option_ty, R.Q_Implicit; term_of_nvar slot, R.Q_Explicit;
         ECL.unit_tm, R.Q_Implicit; tm_full_perm, R.Q_Implicit]) in
      let missing = runtime_raise ty jump in
      let value = R.pack_ln (R.Tv_Match read None [
        R.Pat_Cons (R.pack_fv ["FStar"; "Pervasives"; "Native"; "Some"]) None
          [R.Pat_Dot_Term (Some ty), true;
           R.Pat_Var (T.seal ty) (T.seal "_result"), false], runtime_bv0;
        R.Pat_Cons (R.pack_fv ["FStar"; "Pervasives"; "Native"; "None"]) None
          [R.Pat_Dot_Term (Some ty), true], missing
      ]) in
      let handler = mk_abs (runtime_binder runtime_exn "_control")
        (R.pack_ln (R.Tv_Match runtime_bv0 None [
          R.Pat_Cons (R.pack_fv ["Pulse"; "Lib"; "NativeExceptions"; "ControlFlow"]) None
            [R.Pat_Constant (R.C_String key), false], value;
          R.Pat_Var (T.seal runtime_exn) (T.seal "_other"), runtime_raise ty runtime_bv0
        ])) in
      let body = runtime_try ty body handler in
      let initial = runtime_app ["FStar"; "Pervasives"; "Native"; "None"] [ty] [] in
      let alloc = runtime_app ["Pulse"; "Lib"; "Reference"; "alloc"] [option_ty] [small_type0; initial] in
      ECL.mk_let (extract_dv_binder slot_b None) alloc (close_term body slot._2)

    | Tm_Defer { result_ty; handler_pre; handler; body } ->
      let body = extract_dv native g body in
      let handler = extract_dv native g handler in
      if native then
        // Cleanup is outside the protected body's normal continuation. A
        // cleanup failure must not cause the same cleanup to run a second time.
        let _, pending = extend_env' g (mk_ppname_no_range "_pending") runtime_exn in
        let on_exn = mk_abs (runtime_binder runtime_exn "_pending")
          (close_term (runtime_seq handler (runtime_raise result_ty (term_of_nvar pending))) pending._2) in
        let body = runtime_try result_ty body on_exn in
        let _, result = extend_env' g (mk_ppname_no_range "_result") result_ty in
        ECL.mk_let (runtime_binder result_ty "_result") body
          (close_term (runtime_seq handler (term_of_nvar result)) result._2)
      else
        let b = runtime_binder ECL.unit_ty "_" in
        ECL.mk_let b body handler

  end

and extract_dv_branch native g (b:Pulse.Syntax.Base.branch) : T.Tac R.branch =
  let {pat; e=body; norw} = b in
  let g, pat, bs = extract_dv_pattern g pat in
  pat, LN.close_term_n
    (extract_dv native g (Pulse.Checker.Match.open_st_term_bs body bs))
    (L.map (fun (b: Pulse.Typing.Env.var_binding) -> b.x) bs)

let extract_pulse_dv (g: env) (p:st_term) : T.Tac R.term =
  debug g (fun _ -> Printf.sprintf "input: %s" (show p));
  let native = uses_native_exceptions p in
  let p = erase_ghost_subterms g p in
  debug g (fun _ -> Printf.sprintf "post erasure: %s" (show p));
  let p = simplify_st_term g p in
  debug g (fun _ -> Printf.sprintf "after simp: %s" (show p));
  let p = if native then p else Pulse.ElimGoto.elim_gotos g p in
  debug g (fun _ -> Printf.sprintf "post goto elim: %s" (show p));
  let p = extract_dv native g p in
  debug g (fun _ -> Printf.sprintf "output: %s" (show p));
  p

let rec extract_dv_recursive g (p:st_term) (rec_name:R.fv)
  : T.Tac R.term
  = match p.term with
    | Tm_Abs { b; q; body } -> (
      match body.term with
      | Tm_Abs _ ->
        let g, x = extend_env'_binder g b in
        let body = open_st_term_nv body x in
        let body = extract_dv_recursive g body rec_name in
        mk_abs (extract_dv_binder b q) (close_term body x._2)
      | _ -> //last binder used for knot; replace it with the recursively bound name
        let body = LN.subst_st_term body [RT.DT 0 (wr R.(pack_ln (Tv_FVar rec_name)) range_0)] in
        extract_pulse_dv g body
    )

    | _ -> T.fail "Unexpected recursive definition of non-function"

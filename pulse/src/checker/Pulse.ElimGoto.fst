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

module Pulse.ElimGoto
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
open Pulse.Syntax
open Pulse.Typing.Env
open Pulse.Typing
open Pulse.Reflection.Util
open Pulse.Checker.Match
open FStar.List.Tot

let mk_read (u: universe) (ty: term) (x: term) : st_term =
  wtag (Some STT) <| Tm_ST {
    t = R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv (mk_pulse_lib_reference_lid "read")) [u])) [
      ty, R.Q_Implicit;
      x, R.Q_Explicit;
      tm_unit, R.Q_Implicit; // TODO: obtain via existential elimination
      tm_full_perm, R.Q_Implicit;
    ];
    args = [];
  }

let mk_write (u: universe) (ty: term) (x: term) (v: term) : st_term =
  wtag (Some STT) <| Tm_ST {
    t = R.mk_app (R.pack_ln (R.Tv_UInst (R.pack_fv (mk_pulse_lib_reference_lid "write")) [u])) [
      ty, R.Q_Implicit;
      x, R.Q_Explicit;
      v, R.Q_Explicit;
    ];
    args = [];
  }

let rec push_pattern g (p:Pulse.Syntax.Base.pattern) :
    T.Tac (env & list Pulse.Typing.Env.var_binding) =
  match p with
  | Pat_Cons fv pats ->
    let g, bs = push_patterns g (List.Tot.map fst pats) in
    g, bs
  | Pat_Constant c ->
    g, []
  | Pat_Var ppname sort ->
    let ty = T.unseal sort in
    let n = mk_ppname ppname Range.range_0 in
    let x = fresh g in
    let g = push_binding g x n ty in
    g, [{n; x; ty} <: Pulse.Typing.Env.var_binding]
  | Pat_Dot_Term t ->
    g, []
and push_patterns g (ps:list Pulse.Syntax.Base.pattern) :
    T.Tac (env & list Pulse.Typing.Env.var_binding) =
  match ps with
  | [] -> g, []
  | p::ps ->
    let g, bs = push_pattern g p in
    let g, bs' = push_patterns g ps in
    g, bs@bs'

let wtag ct (t:st_term') : st_term =
  { term = t;
    range = FStar.Range.range_0;
    effect_tag = ct;
    source = Sealed.seal false;
    seq_lhs = Sealed.seal false;
  }

let mk_binder_ppname_inline (binder_ty:term) (binder_ppname:ppname) : binder =
  mk_binder_with_attrs binder_ty binder_ppname (T.seal [`CInline])

let mk_if_cond (g: env) (t: st_term) (cond: nvar) : T.Tac st_term =
  wtag t.effect_tag <| Tm_Bind {
    binder = mk_binder_ppname_inline tm_bool (fst cond);
    head = mk_read u0 tm_bool (term_of_nvar cond);
    body = wtag t.effect_tag <| Tm_If {
      b = close_term (term_of_nvar cond) (snd cond);
      then_ = wtag t.effect_tag <| Tm_Return {
        expected_type = tm_unit;
        insert_eq = false;
        term = unit_const;
      };
      else_ = t;
      post = None;
    } }

let mk_seq (s t: st_term) : T.Tac st_term =
  wtag t.effect_tag <| Tm_Bind {
    binder = mk_binder_ppname tm_unit ppname_default;
    head = s;
    body = t;
  }

noeq type cond_params = {
  cond: nvar; // Boolean variable, true if goto has been taken
  cond_arg: option var_binding; // Variable for the result of the goto, None if unit
  result: option var_binding; // Variable for the result of the current expression, None if unit
}

let add_write_if_necessary (g: env) (t: st_term) (cond: cond_params) : T.Tac st_term =
  match cond.result with
  | None -> t
  | Some result ->
    let y = fresh g in
    wtag t.effect_tag <|
      Tm_Bind {
        head = t;
        binder = mk_binder_ppname_inline result.ty ppname_default;
        body = close_st_term (mk_write u0 result.ty (term_of_nvar (result.n, result.x)) (term_of_nvar (ppname_default, y))) y;
      }

(*
Basically replaces:
  - `goto x v` by `cond.cond_arg := v; cond.cond := true`
  - `a; b` by `a; if (!cond.cond) { b }`
  - `v` (a pure value) by `cond.result := v`

The resulting term always has the return type unit,
the previous result value is stored in `cond.result` instead.
*)
let rec conditionalize (g: env) (t: st_term) (cond: cond_params) : T.Tac (option st_term) =
  match t.term with
  | Tm_Return ..
  | Tm_Abs ..
  | Tm_IntroPure ..
  | Tm_ElimExists ..
  | Tm_IntroExists ..
  | Tm_Rewrite ..
  | Tm_Admit ..
  | Tm_Unreachable ..
  | Tm_PragmaWithOptions ..
    -> None
  | Tm_ST { t; args } ->
    // The args are all abs, so no gotos in scope there
    None
  | Tm_Bind { binder; head; body } -> (
    let x = fresh g in
    let g' = push_binding g x binder.binder_ppname binder.binder_ty in
    let body = open_st_term_nv body (binder.binder_ppname, x) in
    let x_ref = fresh g in
    let cond_head = { cond with result = 
      if eq_tm binder.binder_ty tm_unit then None else
        Some { n = binder.binder_ppname; x = x_ref; ty = binder.binder_ty } } in
    match conditionalize g' head cond_head,
          conditionalize g' body cond with
    | None, None -> None
    | None, Some body ->
      Some { t with term = Tm_Bind {
        binder;
        head;
        body = close_st_term body x;
      } }
    | Some head, body' ->
      let body' =
        match body' with
        | None -> add_write_if_necessary g body cond
        | Some body' -> body' in

      let body =
        if None? cond_head.result then
          open_st_term' (close_st_term body' x) unit_const 0
        else
          wtag t.effect_tag <| Tm_Bind {
            binder = mk_binder_ppname_inline binder.binder_ty binder.binder_ppname;
            head = mk_read u0 binder.binder_ty (term_of_nvar (binder.binder_ppname, x_ref));
            body = close_st_term body' x;
          } in
      let body = mk_if_cond g body cond.cond in
      let body = mk_seq head body in
      if None? cond_head.result then
        Some body
      else
        Some <| wtag t.effect_tag <| Tm_WithLocal {
          binder = mk_binder_ppname (mk_ref binder.binder_ty) binder.binder_ppname;
          initializer = None;
          body = close_st_term body x_ref;
        }
  )
  | Tm_TotBind { binder; head; body } -> (
    let x = fresh g in
    let g' = push_binding g x binder.binder_ppname binder.binder_ty in
    match conditionalize g' (open_st_term_nv body (binder.binder_ppname, x)) cond with
    | None -> None
    | Some body ->
      Some { t with term = Tm_TotBind {
        binder;
        head;
        body = close_st_term body x;
      } }
  )
  | Tm_If { b; then_; else_; post } -> (
    let ret then_ else_ =
      Some { t with term = Tm_If { b; then_; else_; post = None } } in
    match conditionalize g then_ cond, conditionalize g else_ cond with
    | Some then_, Some else_ -> ret then_ else_
    | Some then_, None -> ret then_ (add_write_if_necessary g else_ cond)
    | None, Some else_ -> ret (add_write_if_necessary g then_ cond) else_
    | None, None -> None
  )
  | Tm_Match { sc; returns_; brs } ->
    let brs = T.map (fun br ->
      let {pat;e;norw} = br in
      let (g, bs) = push_pattern g pat in
      let e = open_st_term_bs e bs in
      let is_changed, e =
        match conditionalize g e cond with
        | None -> false, add_write_if_necessary g e cond
        | Some e -> true, e
      in
      let e = close_st_term_bs e bs in
      is_changed, {pat;e;norw}) brs in
    if List.Tot.existsb fst brs then
      Some { t with term = Tm_Match {
        sc;
        returns_ = None;
        brs = List.Tot.map snd brs;
      } }
    else
      None
  | Tm_While { invariant; condition; condition_var; body } -> 
    conditionalize g { t with term = Tm_NuWhile { invariant; condition; cont_req = tm_unknown; body } } cond
  | Tm_NuWhile { invariant; cont_req; condition; body } -> (
    let x = fresh g in
    let cond_cond = { cond with result = Some { n = ppname_default; x; ty = tm_bool } } in
    let cond_body = { cond with result = None } in
    match conditionalize g condition cond_cond, conditionalize g body cond_body with
    | None, None -> None
    | None, Some body ->
      let y = fresh g in
      Some { t with term = Tm_NuWhile {
        invariant;
        cont_req;
        condition = wtag condition.effect_tag <|
          Tm_Bind {
            head = mk_read u0 tm_bool (term_of_nvar cond.cond);
            binder = mk_binder_ppname_inline tm_bool ppname_default;
            body = (fun t -> close_st_term t y) <| wtag condition.effect_tag <|
              Tm_If {
                b = term_of_nvar (ppname_default, y);
                then_ = wtag condition.effect_tag <| Tm_Return {
                  expected_type = tm_bool;
                  insert_eq = false;
                  term = tm_false;
                };
                else_ = condition;
                post = None;
              }
          };
        body;
      } }
    | condition, body ->
      T.fail "goto in condition not yet supported"
  )
  | Tm_WithLocal { binder; initializer; body } -> (
    let x = fresh g in
    let g = push_binding g x binder.binder_ppname binder.binder_ty in
    match conditionalize g (open_st_term_nv body (binder.binder_ppname, x)) cond with
    | None -> None
    | Some body ->
      Some { t with term = Tm_WithLocal { binder; initializer; body = close_st_term body x } }
  )
  | Tm_WithLocalArray { binder; initializer; length; body } -> (
    let x = fresh g in
    let g = push_binding g x binder.binder_ppname binder.binder_ty in
    match conditionalize g (open_st_term_nv body (binder.binder_ppname, x)) cond with
    | None -> None
    | Some body ->
      Some { t with term = Tm_WithLocalArray { binder; initializer; length; body = close_st_term body x } }
  )
  | Tm_ProofHintWithBinders { hint_type; binders; t } ->
    T.fail "conditionalize: Unexpected constructor: ProofHintWithBinders should have been desugared away"
  | Tm_ForwardJumpLabel { lbl; body; post } -> (
    let x = fresh g in
    let g = push_goto g x lbl (goto_comp_of_block_comp post) in
    match conditionalize g (open_st_term_nv body (lbl, x)) cond with
    | None -> None
    | Some body ->
      Some { t with term = Tm_ForwardJumpLabel {
        lbl;
        body = close_st_term body x;
        post = with_st_comp post { st_comp_of_comp post with u = u0; res = tm_unit };
      } }
  )
  | Tm_Goto { lbl; arg } -> (
    match R.inspect_ln lbl with
    | R.Tv_Var lbl ->
      if (R.inspect_namedv lbl).uniq <> snd cond.cond then None else
      let body = mk_write u0 tm_bool (term_of_nvar cond.cond) tm_true in
      Some (match cond.cond_arg with
      | Some cond_arg -> mk_seq (mk_write u0 cond_arg.ty (term_of_nvar (cond_arg.n, cond_arg.x)) arg) body
      | None -> body)
    | _ -> None
  )

let rec elim_gotos (g: env) (t: st_term) : T.Tac st_term =
  match t.term with
  | Tm_Return ..
  | Tm_IntroPure ..
  | Tm_ElimExists ..
  | Tm_IntroExists ..
  | Tm_Rewrite ..
  | Tm_Admit ..
  | Tm_Unreachable ..
  | Tm_PragmaWithOptions ..
  | Tm_Goto ..
    -> t
  | Tm_Abs { b; q; ascription; body } ->
    let x = fresh g in
    let g = push_binding (clear_goto g) x b.binder_ppname b.binder_ty in
    { t with term = Tm_Abs {
      b; q; ascription;
      body = close_st_term (elim_gotos g (open_st_term_nv body (b.binder_ppname, x))) x
    } }
  | Tm_ST { t=f; args } ->
    { t with term = Tm_ST { t=f; args = T.map (elim_gotos g) args } }
  | Tm_Bind { binder; head; body } ->
    let head = elim_gotos g head in
    let x = fresh g in
    let g' = push_binding g x binder.binder_ppname binder.binder_ty in
    let body = close_st_term (elim_gotos g' (open_st_term_nv body (binder.binder_ppname, x))) x in
    { t with term = Tm_Bind { binder; head; body } }
  | Tm_TotBind { binder; head; body } ->
    let x = fresh g in
    let g' = push_binding g x binder.binder_ppname binder.binder_ty in
    let body = close_st_term (elim_gotos g' (open_st_term_nv body (binder.binder_ppname, x))) x in
    { t with term = Tm_TotBind { binder; head; body } }
  | Tm_If { b; then_; else_; post } ->
    { t with term = Tm_If {
      b;
      then_ = elim_gotos g then_;
      else_ = elim_gotos g else_;
      post;
    } }
  | Tm_Match { sc; returns_; brs } ->
    { t with term = Tm_Match {
      sc;
      returns_;
      brs = T.map (fun br ->
        let {pat;e;norw} = br in
        let (g, bs) = push_pattern g pat in
        let e = close_st_term_bs (elim_gotos g (open_st_term_bs e bs)) bs in
        {pat;e;norw}) brs
    } }
  | Tm_While { invariant; condition; condition_var; body } ->
    { t with term = Tm_While {
      invariant;
      condition = elim_gotos g condition;
      condition_var;
      body = elim_gotos g body;
    } }
  | Tm_NuWhile { invariant; cont_req; condition; body } ->
    { t with term = Tm_NuWhile {
      invariant;
      cont_req;
      condition = elim_gotos g condition;
      body = elim_gotos g body;
    } }
  | Tm_WithLocal { binder; initializer; body } ->
    let x = fresh g in
    let g = push_binding g x binder.binder_ppname binder.binder_ty in
    let body = close_st_term (elim_gotos g (open_st_term_nv body (binder.binder_ppname, x))) x in
    { t with term = Tm_WithLocal { binder; initializer; body } }
  | Tm_WithLocalArray { binder; initializer; length; body } ->
    let x = fresh g in
    let g = push_binding g x binder.binder_ppname binder.binder_ty in
    let body = close_st_term (elim_gotos g (open_st_term_nv body (binder.binder_ppname, x))) x in
    { t with term = Tm_WithLocalArray { binder; initializer; length; body } }
  | Tm_ProofHintWithBinders { hint_type; binders; t } ->
    T.fail "elim_gotos: Unexpected constructor: ProofHintWithBinders should have been desugared away"
  | Tm_ForwardJumpLabel { lbl; body; post } ->
    let cond_var = fresh g in
    let g' = push_goto g cond_var lbl (goto_comp_of_block_comp post) in
    let res_var = fresh g' in
    let g' = push_binding g' res_var lbl (comp_res post) in
    let body = open_st_term_nv body (lbl, cond_var) in
    let result =
      let ty = comp_res post in
      if eq_tm ty tm_unit then
        None
      else
        Some { n=lbl; x=res_var; ty } in
    let cond = { cond = (lbl, cond_var); cond_arg = result; result } in
    (match conditionalize g' body cond, result with
    | Some body, Some _ ->
      let body = elim_gotos g body in
      let body = wtag t.effect_tag <| Tm_Bind {
        binder = mk_binder_ppname_inline tm_unit ppname_default;
        head = body;
        body = mk_read (comp_u post) (comp_res post) (term_of_nvar (lbl, res_var));
      } in
      let body = wtag t.effect_tag <| Tm_WithLocal {
        binder = mk_binder_ppname (mk_ref tm_bool) lbl;
        initializer = Some tm_false;
        body = close_st_term body cond_var;
      } in
      wtag t.effect_tag <| Tm_WithLocal {
        binder = mk_binder_ppname (mk_ref (comp_res post)) lbl;
        initializer = None;
        body = close_st_term body res_var;
      }
    | Some body, None ->
      let body = elim_gotos g body in
      wtag t.effect_tag <| Tm_WithLocal {
        binder = mk_binder_ppname (mk_ref tm_bool) lbl;
        initializer = Some tm_false;
        body = close_st_term body cond_var;
      }
    | None, _ -> body)
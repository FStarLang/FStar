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

module Pulse.Checker
module RT = FStar.Reflection.Typing
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Bind
open Pulse.Checker.SLPropEquiv
open Pulse.Checker.Base
open Pulse.Show

module P = Pulse.Syntax.Printer
module RU = Pulse.RuntimeUtils

module Abs = Pulse.Checker.Abs
module If = Pulse.Checker.If
module Bind = Pulse.Checker.Bind
module Match = Pulse.Checker.Match
module WithLocal = Pulse.Checker.WithLocal
module WithLocalArray = Pulse.Checker.WithLocalArray
module While = Pulse.Checker.While
module STApp = Pulse.Checker.STApp
module Exists = Pulse.Checker.Exists
module Par = Pulse.Checker.Par
module Admit = Pulse.Checker.Admit
module Return = Pulse.Checker.Return
module Rewrite = Pulse.Checker.Rewrite
module WithInv = Pulse.Checker.WithInv

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

let default_binder_annot = mk_binder_ppname tm_unknown ppname_default

let rec gen_names_for_unknowns (g:env) (t:term) (ws:list term)
  : T.Tac (list (nvar & term) &  // new names with their types
           term &  // opened slprop                                             
           list term)  // new list of witnesses with _ replaced with corresponding new names
  = match ws with
    | [] -> [], t, []
    | w::ws ->
      match inspect_term t with
      | Tm_ExistsSL _ b body ->
        let xopt, w, g =
          match inspect_term w with
          | Tm_Unknown ->
            let x = fresh g in
            Some x,
            tm_var {nm_index=x;nm_ppname=b.binder_ppname},
            push_binding g x b.binder_ppname b.binder_ty
          | _ -> None, w, g in
        let t : term = open_term' body w 0 in
        let new_names, t, ws = gen_names_for_unknowns g t ws in
        (match xopt with
         | Some x ->
           ((b.binder_ppname, x), b.binder_ty)::new_names,
           t,
           w::ws
         | None -> new_names, t, w::ws)
      | _ -> fail g (Some (Pulse.RuntimeUtils.range_of_term t)) "intro exists with non-existential"

let instantiate_unknown_witnesses (g:env) (t:st_term { Tm_IntroExists? t.term })
  : T.Tac (option st_term) =

  let Tm_IntroExists { p; witnesses=ws } = t.term in

  let new_names, opened_p, new_ws = gen_names_for_unknowns g p ws in
  match new_names with
  | [] -> None
  | _ ->
    let e2 = {t with term=Tm_IntroExists { p; witnesses=new_ws }} in
    let e1 =
      let hint_type = ASSERT { p = opened_p } in
      let binders = [] in
      let t = mk_term (Tm_ProofHintWithBinders { hint_type;binders;t=e2 }) t.range in
      { t with effect_tag = as_effect_hint STT_Ghost }
     in
    
    let t = 
      L.fold_right
        (fun new_name (e:st_term { Tm_ProofHintWithBinders? e.term }) ->
          let (ppname, x), ty = new_name in
          let e = close_st_term' e x 0 in
          match e.term with
          | Tm_ProofHintWithBinders {hint_type;binders;t} ->
            let new_binder = mk_binder_ppname ty ppname in
            let t' = Tm_ProofHintWithBinders {hint_type;binders=new_binder::binders;t} in
            {e with term=t'})
        new_names
        e1 in
    Some t

let rec transform_to_unary_intro_exists (g:env) (t:term) (ws:list term)
  : T.Tac st_term =
  
  let t_rng = Pulse.RuntimeUtils.range_of_term t in
  match ws with
  | [] -> fail g (Some t_rng) "intro exists with empty witnesses"
  | [w] ->
    let tv = inspect_term t in
    if Tm_ExistsSL? tv
    then wtag (Some STT_Ghost) (Tm_IntroExists {p=t;witnesses=[w]})
    else fail g (Some t_rng) "intro exists with non-existential"
  | w::ws ->
    match inspect_term t with
    | Tm_ExistsSL u b body ->
      let body = subst_term body [ RT.DT 0 w ] in
      let st = transform_to_unary_intro_exists g body ws in
      // w is the witness
      let intro = wtag None (Tm_IntroExists {p=t;witnesses=[w]}) in
      wtag None
           (Tm_Bind {binder=null_binder tm_unit;
                     head=st;
                     body= intro})

    | _ -> fail g (Some t_rng) "intro exists with non-existential"

let trace (t:st_term) (g:env) (pre:term) (rng:range) : T.Tac unit =
  (* If we're running interactively, print out the context
  and environment. *)
  let open FStar.Pprint in
  let open Pulse.PP in
  let pre = T.norm_well_typed_term (elab_env g) [unascribe; primops; iota] pre in
  let msg = [
    text "TRACE. Current context:" ^^
      indent (pp <| canon_slprop_print pre);
    text "Typing environment (units elided): " ^^
      indent (env_to_doc' true g);
    prefix 2 1 (text "Just before checking:")
      (pp t);
  ] in
  (* This tweaks the range to go to the beginning of the line. *)
  let rng =
    let (f, l1, c1, l2, c2) = FStar.Range.explode (T.unseal rng) in
    FStar.Range.mk_range f l1 0 l1 2
  in
  info_doc g (Some rng) msg

let maybe_trace (t:st_term) (g:env) (pre:term) (rng:range) : T.Tac unit =
  (* pulse:trace turns on tracing, but not for sequencing (binds),
                  and not for terms injected by the checker
     pulse:trace_full turns it on for absolutely everything. *)
  let trace_opt = T.ext_getv "pulse:trace" = "1" in
  let trace_full_opt = T.ext_getv "pulse:trace_full" = "1" in
  let is_source = T.unseal t.source in
  if (trace_opt && is_source && not (Tm_Bind? t.term || Tm_TotBind? t.term))
     || trace_full_opt
  then
    trace t g pre rng

(* We set the error bound from t when t is a source term. Otherwise don't. *)
let maybe_setting_error_bound (t:st_term) (f : unit -> T.Tac 'a) : T.Tac 'a =
  if T.unseal t.source
  then RU.with_error_bound t.range f
  else f ()

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"

let rec maybe_elaborate_stateful_head (g:env) (t:st_term)
: T.Tac (option st_term)
= match t.term with
  | Tm_If {b; then_=e1; else_=e2; post} ->
    let rebuild (b:either term st_term {Inl? b})
    : T.Tac st_term
    = let Inl b = b in
      {t with term=Tm_If { b; then_=e1; else_=e2; post }}
    in
    Pulse.Checker.Base.hoist_stateful_apps g (Inl b) true rebuild  
  | Tm_Match {sc; returns_=post_match; brs} ->
    let rebuild (sc:either term st_term {Inl? sc})
    : T.Tac st_term
    = let Inl sc = sc in
      { t with term=Tm_Match {sc; returns_=post_match; brs} }
    in
    Pulse.Checker.Base.hoist_stateful_apps g (Inl sc) true rebuild
  | Tm_WithLocal { binder; initializer; body } ->
    let rebuild (sc:either term st_term {Inl? sc})
    : T.Tac st_term
    = let Inl initializer = sc in
      { t with term=Tm_WithLocal {binder; initializer; body } }
    in
    Pulse.Checker.Base.hoist_stateful_apps g (Inl initializer) true rebuild
  | Tm_WithLocalArray { binder; initializer; body; length } -> (
    (* Very awkward to compose two of these. *)
    let rebuild_len t (sc:either term st_term {Inl? sc})
    : T.Tac st_term
    = let Inl length = sc in
      { t with term=Tm_WithLocalArray {binder; initializer; body; length } }
    in
    let rebuild_init (sc:either term st_term {Inl? sc})
    : T.Tac st_term
    = let Inl initializer = sc in
      let t = { t with term=Tm_WithLocalArray {binder; initializer; body; length } } in
      match Pulse.Checker.Base.hoist_stateful_apps g (Inl length) true (rebuild_len t) with
      | None -> t
      | Some t -> t
    in
    match Pulse.Checker.Base.hoist_stateful_apps g (Inl initializer) true rebuild_init with
    | Some t -> Some t
    | None ->
      Pulse.Checker.Base.hoist_stateful_apps g (Inl length) true (rebuild_len t)
  )

  | _ -> None

let rec check
  (g0:env)
  (pre0:term)
  (pre0_typing: tot_typing g0 pre0 tm_slprop)
  (post_hint:post_hint_opt g0)
  (res_ppname:ppname)
  (t:st_term)
: T.Tac (checker_result_t g0 pre0 post_hint)
= maybe_setting_error_bound #(checker_result_t g0 pre0 post_hint) t <| fun () ->
  if Pulse.Checker.AssertWithBinders.handle_head_immediately t
  then Pulse.Checker.AssertWithBinders.check g0 pre0 pre0_typing post_hint res_ppname t check
  else (
    maybe_trace t g0 pre0 t.range;  
    if RU.debug_at_level (fstar_env g0) "pulse.checker" then
      T.print (Printf.sprintf "At %s{\nerr context:\n>%s\n\n{\n\tenv=%s\ncontext:\n%s,\n\nst_term: %s\nis_source: %s}}\n"
                (show t.range)
                (RU.print_context (get_context g0))
                (show g0)
                (show pre0)
                (show t)
                (show (T.unseal t.source)));
    
    match maybe_elaborate_stateful_head g0 t with
    | Some t -> 
      check g0 pre0 pre0_typing post_hint res_ppname t
    | None -> 
      let (| g, pre, pre_typing, k_elim_pure |) = 
        Pulse.Checker.Prover.elim_exists_and_pure pre0_typing 
      in
      let r : checker_result_t g pre post_hint =
        let g = push_context (P.tag_of_st_term t) t.range g in
        match t.term with
        | Tm_Return _ ->
          Return.check g pre pre_typing post_hint res_ppname t check
        
        | Tm_Abs _ ->
          // let (| t, c, typing |) = Pulse.Checker.Abs.check_abs g t check in
          // Pulse.Checker.Prover.prove_post_hint (
          //   Pulse.Checker.Prover.try_frame_pre
          //     pre_typing
              
          // )
          T.fail "Tm_Abs check should not have been called in the checker"

        | Tm_STApp _ ->
          STApp.check g pre pre_typing post_hint res_ppname t

        | Tm_ElimExists _ ->
          Exists.check_elim_exists g pre pre_typing post_hint res_ppname t

        | Tm_IntroExists _ ->
          (
          (* First of all, elaborate *)
          let prep (t:st_term{Tm_IntroExists? t.term}) : T.Tac (t:st_term{Tm_IntroExists? t.term}) =
            let Tm_IntroExists { p; witnesses } = t.term in
            let p, _ = instantiate_term_implicits g p (Some tm_slprop) false in
            { t with term=Tm_IntroExists { p; witnesses } }
          in
          let t = prep t in

          let Tm_IntroExists { p; witnesses } = t.term in

          match instantiate_unknown_witnesses g t with
          | Some t ->
            check g pre pre_typing post_hint res_ppname t
          | None ->
            match witnesses with
            | [] -> fail g (Some t.range) "intro exists with empty witnesses"
            | [_] ->
              Exists.check_intro_exists g pre pre_typing post_hint res_ppname t None 
            | _ ->
              let t = transform_to_unary_intro_exists g p witnesses in
              check g pre pre_typing post_hint res_ppname t)
        | Tm_Bind _ ->
          Bind.check_bind g pre pre_typing post_hint res_ppname t check

        | Tm_TotBind _ ->
          Bind.check_tot_bind g pre pre_typing post_hint res_ppname t check

        | Tm_If { b; then_=e1; else_=e2; post=post_if } -> (
          let post : post_hint_opt g =
            match post_if, post_hint with
            | None, Some p ->
              post_hint
            | Some p, None ->
              //We set the computation type to be STT in this case
              //We might allow the post_if annotation to also set the effect tag
              Some <| Checker.Base.intro_post_hint g EffectAnnotSTT None p
            | Some p, Some q ->
              Pulse.Typing.Env.fail g (Some t.range) 
                (Printf.sprintf 
                    "Multiple annotated postconditions---remove one of them.\n\
                    The context expects the postcondition %s,\n\
                    but this conditional was annotated with postcondition %s"
                    (P.term_to_string (q <: post_hint_t).post)
                    (P.term_to_string p))
            | _, _ ->
              None
          in
          let (| x, t, pre', g1, k |) : checker_result_t g pre post =
            If.check g pre pre_typing post res_ppname b e1 e2 check in
          (| x, t, pre', g1, k |)
        )
        | Tm_While _ ->
          While.check g pre pre_typing post_hint res_ppname t check

        | Tm_Match {sc;returns_=post_match;brs} ->
          // TODO : dedup
          let post =
            match post_match, post_hint with
            | None, Some p -> p
            | Some p, None ->
              //See same remark in the If case
              Checker.Base.intro_post_hint g EffectAnnotSTT None p
            | Some p, Some q ->
              Pulse.Typing.Env.fail g (Some t.range)
                (Printf.sprintf
                  "Multiple annotated postconditions---remove one of them.\n\
                    The context expects the postcondition %s,\n\
                    but this conditional was annotated with postcondition %s"
                    (P.term_to_string (q <: post_hint_t).post)
                    (P.term_to_string p))
            | _, _ ->
              Pulse.Typing.Env.fail g (Some t.range)
                (Printf.sprintf
                  "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\n\
                    Either annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")
          in
          let (| x, ty, pre', g1, k |) =
            Match.check g pre pre_typing post res_ppname sc brs check in
          (| x, ty, pre', g1, k |)

        | Tm_ProofHintWithBinders _ ->
          Pulse.Checker.AssertWithBinders.check g pre pre_typing post_hint res_ppname t check

        | Tm_WithLocal _ ->
          WithLocal.check g pre pre_typing post_hint res_ppname t check

        | Tm_WithLocalArray _ ->
          WithLocalArray.check g pre pre_typing post_hint res_ppname t check

        | Tm_Par _ ->
          Par.check g pre pre_typing post_hint res_ppname t check

        | Tm_IntroPure _ -> 
          Pulse.Checker.IntroPure.check g pre pre_typing post_hint res_ppname t

        | Tm_Admit _ ->
          Admit.check g pre pre_typing post_hint res_ppname t

        | Tm_Unreachable _ ->
          Pulse.Checker.Unreachable.check g pre pre_typing post_hint res_ppname t

        | Tm_Rewrite _ ->
          Rewrite.check g pre pre_typing post_hint res_ppname t

        | Tm_WithInv _ ->
          WithInv.check g pre pre_typing post_hint res_ppname t check
      in

      let (| x, g1, t, pre', k |) = r in
      (| x, g1, t, pre', k_elab_trans k_elim_pure k |)
  )

#pop-options

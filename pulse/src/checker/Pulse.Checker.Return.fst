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

module Pulse.Checker.Return

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module TU = FStar.Tactics.Util
module RU = Pulse.RuntimeUtils
module R = FStar.Reflection.V2

let check_effect
    (g:env) (e:term) (eff:T.tot_or_ghost)
    (c:option ctag)
: T.Tac (c:ctag & e:term)
= match c, eff with
  | None, T.E_Total -> 
    (| STT_Atomic, e |)
  | None, T.E_Ghost -> 
    (| STT_Ghost, e |)
  | Some STT_Ghost, T.E_Total ->
    (| STT_Atomic, e |)
  | Some STT_Ghost, T.E_Ghost -> 
    (| STT_Ghost, e |)
  | _, T.E_Total -> 
    (| STT_Atomic, e |)
  | _ -> 
    fail g (Some (RU.range_of_term e)) "Expected a total term, but this term has Ghost effect"
 

let check_tot_or_ghost_term (g:env) (e:term) (t:term) (c:option ctag)
: T.Tac (c:ctag & e:term)
= let (| e, eff |) = check_term_at_type g e t in
  match c, eff with
  | None, T.E_Total
  | Some STT_Ghost, T.E_Total
  | _, T.E_Total -> (| STT_Atomic, e |)
  | None, T.E_Ghost
  | Some STT_Ghost, T.E_Ghost -> (| STT_Ghost, e |)
  | _ ->
    fail g (Some (RU.range_of_term e)) "Expected a total term, but this term has Ghost effect"
  
noeq
type result_of_typing (g:env) =
  | R :
    c:ctag ->
    t:term ->
    u:universe ->
    ty:term ->
    unit ->
    unit ->
    result_of_typing g

let compute_tot_or_ghost_term_type_and_u (g:env) (e:term) (c:option ctag)
: T.Tac (result_of_typing g)
= RU.with_error_bound (RU.range_of_term e) fun () -> // stopgap, ideally remove
  let (| t, eff, ty, u |) = compute_term_type_and_u g e in
  let (| c, e |) = check_effect g t eff c in
  R c e u ty () ()

// Free (named) variables of a term in de Bruijn form: binder-bound variables
// appear as `Tv_BVar` and so are excluded automatically; only `Tv_Var` (named)
// occurrences are collected.
let rec free_named_vars (t:term) : T.Tac (list var) =
  let (++) (a b: list var) : list var = List.Tot.append a b in
  match R.inspect_ln t with
  | R.Tv_Var nv -> [(R.inspect_namedv nv).uniq]
  | R.Tv_App hd (a, _) -> free_named_vars hd ++ free_named_vars a
  | R.Tv_Abs _ body -> free_named_vars body
  | R.Tv_Refine b ref -> free_named_vars (R.inspect_binder b).sort ++ free_named_vars ref
  | R.Tv_Arrow b c ->
    free_named_vars (R.inspect_binder b).sort ++
    (match R.inspect_comp c with
     | R.C_Total ret | R.C_GTotal ret -> free_named_vars ret
     | R.C_Lemma pre post pats -> free_named_vars pre ++ free_named_vars post ++ free_named_vars pats
     | R.C_Eff _ _ ret _ _ -> free_named_vars ret)
  | R.Tv_Let _ _ _ def body -> free_named_vars def ++ free_named_vars body
  | R.Tv_Match sc _ brs ->
    TU.fold_left (fun (acc:list var) (br:R.branch) -> List.Tot.append acc (free_named_vars (snd br)))
                 (free_named_vars sc) brs
  | R.Tv_AscribedT e ty _ _ -> free_named_vars e ++ free_named_vars ty
  | R.Tv_AscribedC e _ _ _ -> free_named_vars e
  | _ -> []

// Does the refinement formula `ref` constrain the refinement binder `bx`, i.e.
// does the result value itself appear in the formula? (`ref` is the opened body
// of a `Tv_Refine`, so `bx` occurs as a named variable iff the formula mentions
// the result.)
let refinement_constrains_result (bx:var) (ref:term) : T.Tac bool =
  List.Tot.mem bx (free_named_vars ref)

// When inferring a return type (no post-condition hint), the Core typechecker
// turns a `Pure`-effect `ensures` into a refinement on the returned value's
// type, e.g. `SZ.lt : Pure bool (ensures z == (v x < v y))` gives a return type
// `z:bool{z == (SZ.v x < SZ.v y)}`. When the operand is a branch-local hoisted
// ANF temporary `__anf0` (introduced by hoisting a stateful read such as `!j`),
// that temporary leaks into the refinement, e.g. `z:bool{z == (SZ.v __anf0 < ...)}`.
// Closing the branch closes the *term* over `__anf0` but not the *type*, so when
// the type is later used in the outer scope where `__anf0` no longer exists it
// fails with Error 76 ("universe_of failed ... Variable not found"); the refined
// result type also blocks joining two `if`/`match` branches whose boolean results
// are refined differently.
//
// We weaken the inferred type by dropping refinements that constrain the result
// value itself, i.e. whose formula mentions the refinement binder -- of *any*
// shape (`z == e`, `z > 0`, ...), not just equalities. Such refinements are
// redundant: in the inference path `comp_return` re-establishes the value via the
// equality `result == term` (`use_eq` below, which holds for any non-`unit`
// result), and any `Pure` postcondition of the operand is in scope at its call.
// Refinements that do *not* mention the result are payload facts with no other
// carrier -- e.g. a lemma application's conclusion (`some_lemma x : Lemma (p x)`
// flows through this same path as `_:unit{ p x }`) -- and are kept.
let rec unrefine_result (t:term) : T.Tac term =
  match T.inspect t with
  | T.Tv_Refine b ref ->
    if refinement_constrains_result b.uniq ref
    then unrefine_result b.sort
    else t
  | T.Tv_AscribedT e _ _ _ -> unrefine_result e
  | T.Tv_AscribedC e _ _ _ -> unrefine_result e
  | _ -> t

#push-options "--z3rlimit_factor 16 --fuel 0 --ifuel 1 --split_queries no"
#restart-solver
let check_core
  (g:env)
  (ctxt:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  (ctag_ctxt:option ctag)
  : T.Tac (checker_result_t g ctxt post_hint) =
  
  let g = push_context "check_return" st.range g in
  let Tm_Return {expected_type; insert_eq=use_eq; term=t} = st.term in
  let return_type
    : option (ty:term & u:universe) =
    match post_hint with
    | PostHint post ->
      assert (g `env_extends` post.g);

      Some (| post.ret_ty, post.u |)
    | _ ->
      match inspect_term expected_type with
      | Tm_Unknown -> (
        match post_hint with
        | NoHint -> None
        | TypeHint expected_type -> 
          let ty, _ = Pulse.Checker.Pure.instantiate_term_implicits g expected_type None false in
          let u = check_universe g ty in
          Some (| ty, u |)
      )
      | _ ->
        let ty, _ = Pulse.Checker.Pure.instantiate_term_implicits g expected_type None false in
        let u = check_universe g ty in
        Some (| ty, u |)
  in
  let R c t u ty uty d : result_of_typing g =
    match return_type with
    | None ->
      let R rc rt ru rty ruty rd = compute_tot_or_ghost_term_type_and_u g t ctag_ctxt in
      R rc rt ru (unrefine_result rty) ruty rd
    | Some (| ret_ty, u |) ->
      let (| c, t |) = check_tot_or_ghost_term g t ret_ty ctag_ctxt in
      R c t u ret_ty () ()
  in
  let x = fresh g in
  let px = res_ppname, x in
  let post_opened : term =
      match post_hint with
      | PostHint post ->
        // we already checked for the return type
        let post : post_hint_t = post in
        if x `Set.mem` (freevars post.post)
        then fail g None
               ("check_return: unexpected variable clash in return post,\
                 please file a bug report")
        else 
         open_term_nv post.post px
      | _ ->
        let t = check_tot_term (push_binding g x (fst px) ty) tm_emp tm_slprop in
        t
  in
  //if we're inferring a postcondition, then add an equality (if it is non-trivial)
  let use_eq = use_eq || (not (PostHint? post_hint) && not (T.term_eq ty (`unit))) in
  assume (open_term (close_term post_opened x) x == post_opened);
  let post = close_term post_opened x in
  let ret_st = wtag (Some c) (Tm_Return {expected_type=tm_unknown; insert_eq=use_eq; term=t}) in
  let ret_c = comp_return c use_eq u ty t post x in

  let c' = match_comp_res_with_post_hint ret_st ret_c post_hint in
  Pulse.Checker.Util.debug g "pulse.return" (fun _ -> 
    Printf.sprintf "Return comp is: %s"
      (Pulse.Syntax.Printer.comp_to_string c'));
  prove_post_hint #g
    (try_frame_pre false #g (|ret_st,c'|) res_ppname)
    post_hint
    st.range
#pop-options

let check
  (g:env)
  (ctxt:term)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_Return? st.term })
  (check:check_t)
: T.Tac (checker_result_t g ctxt post_hint)
= let Tm_Return f = st.term in
  let rebuild (tt: either term st_term) : T.Tac st_term =
    match tt with
    | Inl t -> { st with term = Tm_Return { f with term = t } }
    | Inr st_app -> { st_app with source = st.source }
  in
  match Pulse.Checker.Base.hoist g (Inl f.term) false rebuild with
  | Some tt -> //some elaboration, go back to top
    Pulse.Checker.Util.debug g "pulse.hoist" (fun _ ->
      Printf.sprintf "Hoisted term: %s" (Pulse.Syntax.Printer.st_term_to_string tt)
    );
    check g ctxt post_hint res_ppname tt
  | None -> (
    match post_hint with
    | PostHint p -> (
      let ctag =
        match ctag_of_effect_annot p.effect_annot with
        | Some c -> c
        | None -> STT_Atomic in
      // If we are returning an application, introduce an intermediate binding
      // for it. This makes sure whatever logical payload the call provides (as
      // a postcondition) is available to prove the postcondition of the current
      // function (the caller). See #4314.
      let _, args = T.collect_app_ln f.term in
      if Cons? args then (
        let x = fresh g in
        let expected_type =
          match post_hint with
          | PostHint t -> t.ret_ty
          | TypeHint t -> t
          | NoHint -> f.expected_type // This seems always = to tm_unknown, oh well
        in
        Pulse.Checker.Util.debug g "pulse.return" (fun _ ->
          Printf.sprintf "About to let-bind return, expected type = %s" 
            (Pulse.Show.show expected_type));
        let b = mk_binder_ppname expected_type res_ppname in
        let body =
          mk_term (Tm_Return { expected_type
                             ; insert_eq = false
                             ; term = term_of_no_name_var x }) st.range in
        (* Add a rewrites_to, so the extra alias does not prevent slprop proving. *)
        let assertion =
          ASSERT { elaborated=true;
                   p = tm_pure (mk_rewrites_to_p u_unknown expected_type (term_of_no_name_var x) f.term)
                   }
        in
        let tt = { st with term = Tm_ProofHintWithBinders {
                                    hint_type = assertion;
                                    binders = [];
                                    t = body; } } in
        let tt = close_st_term tt x in
        let tt = { st with term = Tm_TotBind { binder = b; head = f.term; body=tt } } in
        Pulse.Checker.Util.debug g "pulse.return" (fun _ ->
          Printf.sprintf "Sequencing tail return (#4314): %s"
            (Pulse.Syntax.Printer.st_term_to_string tt));
        check g ctxt post_hint res_ppname tt
      ) else
        check_core g ctxt post_hint res_ppname st (Some ctag)
    )
    | _ ->  check_core g ctxt post_hint res_ppname st None
  )

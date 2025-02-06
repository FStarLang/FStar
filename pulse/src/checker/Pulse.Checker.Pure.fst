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

module Pulse.Checker.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.Tactics.V2
open FStar.Reflection.V2 (* shadow named view *)

open Pulse.PP
open Pulse.Reflection
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
module P = Pulse.Syntax.Printer
module RTB = FStar.Stubs.Tactics.V2.Builtins
module RU = Pulse.RuntimeUtils
module CheckLN = FStar.Tactics.CheckLN

let debug (g:env) (msg: unit -> T.Tac string) =
  let tac_debugging = T.debugging () in
  if tac_debugging || RU.debug_at_level (fstar_env g) "refl_tc_callbacks"
  then T.print (print_context g ^ "\n" ^ msg())

let check_ln (g:env) (label:string) (t:R.term) : Tac unit =
  if not (CheckLN.check_ln t) then
    fail_doc g (Some (RU.range_of_term t)) [
      text "Failure: not locally nameless!";
      text "Aborting before calling" ^/^ pp label;
      text "term" ^/^ equals ^/^ pp t;
    ]

let rtb_core_compute_term_type g f e =
  check_ln g "rtb_compute_term_type" e;
  debug g (fun _ ->
    Printf.sprintf "(%s) Calling core_check_term on %s" 
          (T.range_to_string (RU.range_of_term e))
          (T.term_to_string e));
  let res = RU.with_context (get_context g) (fun _ -> RTB.core_compute_term_type f e) in
  res

let rtb_tc_term g f e =
  (* WARN: unary dependence, see comment in RU *)
  check_ln g "rtb_tc_term" e;
  let e = RU.deep_transform_to_unary_applications e in
  debug g (fun _ ->
    Printf.sprintf "(%s) Calling tc_term on %s"
      (T.range_to_string (RU.range_of_term e))
      (T.term_to_string e));
  let res = RU.with_context (get_context g) (fun _ -> RTB.tc_term f e) in
  res

let rtb_universe_of g f e =
  check_ln g "rtb_universe_of" e;
  debug g (fun _ ->
    Printf.sprintf "(%s) Calling universe_of on %s"
      (T.range_to_string (RU.range_of_term e))
      (T.term_to_string e));
  let res = RU.with_context (get_context g) (fun _ -> RTB.universe_of f e) in
  res

let rtb_check_subtyping g (t1 t2:term) : Tac (ret_t (subtyping_token g t1 t2)) =
  check_ln g "rtb_check_subtyping.t1" t1;
  check_ln g "rtb_check_subtyping.t2" t2;
  debug g (fun _ ->
    Printf.sprintf "(%s, %s) Calling check_subtyping on %s <: %s"
        (T.range_to_string (RU.range_of_term t1))
        (T.range_to_string (RU.range_of_term t2))
        (P.term_to_string t1)
        (P.term_to_string t2));
  let res = RU.with_context (get_context g) (fun _ -> RTB.check_subtyping (elab_env g) t1 t2) in
  res

let rtb_instantiate_implicits g f t expected =
  check_ln g "rtb_instantiate_implicits" t;
  debug g (fun _ -> Printf.sprintf "Calling instantiate_implicits on %s"
                                       (T.term_to_string t));
  (* WARN: unary dependence, see comment in RU *)
  let t = RU.deep_transform_to_unary_applications t in
  let res, iss = RU.with_context (get_context g) (fun _ -> RTB.instantiate_implicits f t expected) in
  begin match res with
  | None ->
    debug g (fun _ -> "Returned from instantiate_implicits: None")
  | Some (_, t, _) ->
    debug g (fun _ -> Printf.sprintf "Returned from instantiate_implicits: %s" (Pulse.Show.show t))
  end;
  res, iss

let rtb_core_check_term g f e eff t =
  check_ln g "rtb_core_check_term.e" e;
  check_ln g "rtb_core_check_term.t" t;
  debug g (fun _ ->
    Printf.sprintf "(%s) Calling core_check_term on %s and %s"
                (T.range_to_string (RU.range_of_term e))
                (T.term_to_string e)
                (T.term_to_string t));
  let res = RU.with_context (get_context g) (fun _ -> RTB.core_check_term f e t eff) in
  res

let rtb_core_check_term_at_type g f e t =
  debug g (fun _ ->
    Printf.sprintf "(%s) Calling core_check_term_at_type on %s and %s"
                (T.range_to_string (RU.range_of_term e))
                (T.term_to_string e)
                (T.term_to_string t));
  let res = RU.with_context (get_context g) (fun _ -> RTB.core_check_term_at_type f e t) in
  res

let mk_squash0 t =
  let sq : R.term = pack_ln (Tv_UInst (pack_fv squash_qn) [u_zero]) in
  mk_e_app sq [t]

let squash_prop_validity_token f p (t:prop_validity_token f (mk_squash0 p))
  : prop_validity_token f p
  = admit(); t

let rtb_check_prop_validity (g:env) (sync:bool) (f:_) (p:_) = 
  check_ln g "rtb_check_prop_validity" p;
  debug g (fun _ -> 
    Printf.sprintf "(%s) Calling check_prop_validity on %s"
          (T.range_to_string (RU.range_of_term p))
          (T.term_to_string p));
  let sp = mk_squash0 p in
  let res, issues = 
    RU.with_context (get_context g) 
    (fun _ -> 
      if sync
      then T.with_policy T.ForceSMT (fun _ -> RTB.check_prop_validity f sp)
      else RTB.check_prop_validity f sp)
  in
  match res with
  | None -> None, issues
  | Some tok -> Some (squash_prop_validity_token f p tok), issues

let exn_as_issue (e:exn) : FStar.Issue.issue = 
  FStar.Issue.mk_issue "Error" (RU.print_exn e) None None []

let catch_all (f:unit -> Tac (option 'a & issues))
  : Tac (option 'a & issues)
  = match T.catch f with
    | Inl exn ->
      None, [exn_as_issue exn]
    | Inr v -> v

let readback_failure (s:R.term) =
  Printf.sprintf "Internal error: failed to readback F* term %s"
                 (T.term_to_string s)

(* Set got_typ = None if we don't have a good type for `t`. *)
let ill_typed_term (t:term) (expected_typ:option term) (got_typ:option term) : Tac (list document) =
  let open Pulse.PP in
  match expected_typ, got_typ with
  | None, _ -> [
    prefix 2 1 (text "Ill-typed term:") (pp t)
  ]
  | Some ty, None -> [
    prefix 2 1 (text "Expected term of type") (pp ty) ^/^
    prefix 2 1 (text "got term") (pp t)
  ]
  | Some ty, Some ty' -> [
    prefix 2 1 (text "Expected term of type") (pp ty) ^/^
    prefix 2 1 (text "got term") (pp t) ^/^
    prefix 2 1 (text "of type") (pp ty')
  ]

let instantiate_term_implicits (g:env) (t0:term) (expected:option typ) : Tac _ =
  let f = elab_env g in
  let rng = RU.range_of_term t0 in
  let f = RU.env_set_range f (Pulse.Typing.Env.get_range g (Some rng)) in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f t0 expected) in
  let fail #a issues : Tac a =
    fail_doc_with_subissues g (Some rng) issues []
  in
  match topt with
  | None -> fail issues
  | Some (namedvs, t, ty) ->
    match namedvs with
    | (v, vty) :: _ ->
      fail_doc g (Some rng) [
        prefix 2 1 (doc_of_string "Could not resolve implicit") (pp v) ^/^
        prefix 2 1 (doc_of_string "of type") (pp vty) ^/^
        prefix 2 1 (doc_of_string "in term") (pp t0);
      ]
    | [] ->
      t, ty

let instantiate_term_implicits_uvs (g:env) (t0:term) =
  let f = elab_env g in
  let rng = RU.range_of_term t0 in
  let f = RU.env_set_range f (Pulse.Typing.Env.get_range g (Some rng)) in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f t0 None) in
  match topt with
  | None -> (
    let open Pulse.PP in
    fail_doc_with_subissues g (Some rng) issues []
  )
  | Some (namedvs, t, ty) ->
    let (| uvs, t, ty |)
      : uvs:env { disjoint g uvs } &
        term &
        term =
      T.fold_left (fun (| uvs, t, ty |) (namedv, namedvt) ->
        let nview = R.inspect_namedv namedv in
        let ppname = { name = nview.ppname; range = rng } <: Pulse.Syntax.Base.ppname in
        let x = fresh (push_env g uvs) in
        let ss = [RT.NT nview.uniq (tm_var {nm_index = x; nm_ppname = ppname})] in
        let uvs : uvs:env { disjoint g uvs } = push_binding uvs x ppname namedvt in
        (| uvs,
           subst_term t ss,
           subst_term ty ss |)) (| mk_env (fstar_env g), t, ty |) namedvs in
    (| uvs, t, ty |)

let check_universe (g:env) (t:term)
  : T.Tac (u:universe & universe_of g t u)
  = let f = elab_env g in
    let ru_opt, issues = catch_all (fun _ -> rtb_universe_of g f t) in
    match ru_opt with
    | None -> 
      fail_doc_with_subissues g (Some <| RU.range_of_term t) issues (ill_typed_term t (Some (tm_type u_unknown)) None)

    | Some ru ->
      let proof : squash (T.typing_token f t (E_Total, R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _
      in
      let proof : RT.typing f t (E_Total, R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
      (| ru, E proof |)

let tc_meta_callback g (f:R.env) (e:R.term) 
  : T.Tac (option (e:R.term & eff:T.tot_or_ghost & t:R.term & RT.typing f e (eff, t)) & issues)
  = let res =
      match catch_all (fun _ -> rtb_tc_term g f e) with
      | None, issues ->
        None, issues
      | Some (e, (eff, t)), issues ->
        Some (| e, eff, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), 
        issues
    in
    res

let compute_term_type (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)
  = let fg = elab_env g in
    debug g (fun _ ->
            Printf.sprintf "check_tot : called on %s elaborated to %s"
                      (P.term_to_string t)
                      (T.term_to_string t));
    let res, issues = tc_meta_callback g fg t in
    match res with
    | None -> 
      fail_doc_with_subissues g (Some <| RU.range_of_term t) issues (ill_typed_term t None None)
    | Some (| rt, eff, ty', tok |) -> (| rt, eff, ty', E tok |)

let compute_term_type_and_u (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           (u:universe & universe_of g ty u) &
           typing g t eff ty)
  = let fg = elab_env g in
    let res, issues = tc_meta_callback g fg t in
    match res with
    | None ->
      fail_doc_with_subissues g (Some <| RU.range_of_term t) issues (ill_typed_term t None None)
    | Some (| rt, eff, ty', tok |) ->
      let (| u, uty |) = check_universe g ty' in
      (| rt, eff, ty', (| u, uty |), E tok |)

let check_term (g:env) (e:term) (eff:T.tot_or_ghost) (t:term)
  : T.Tac (e:term & typing g e eff t) =

  let e, _ = instantiate_term_implicits g e (Some t) in

  let fg = elab_env g in

  let topt, issues =
    catch_all (fun _ -> 
      rtb_core_check_term 
        (push_context g "check_term_with_expected_type_and_effect" (range_of_term t))
         fg e eff t) in
  match topt with
  | None ->
    fail_doc_with_subissues g (Some <| RU.range_of_term e) issues (ill_typed_term e (Some t) None)
  | Some tok -> (| e, E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok)) |)

let check_term_at_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & eff:T.tot_or_ghost & typing g e eff t) =

  let e, _ = instantiate_term_implicits g e (Some t) in
  let fg = elab_env g in

  let effopt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "check_term_with_expected_type" (range_of_term t))
      fg e t) in
  match effopt with
  | None ->
    fail_doc_with_subissues g (Some <| RU.range_of_term e) issues (ill_typed_term e (Some t) None)
  | Some eff ->
    (| e, eff, E (RT.T_Token _ _ _ (FStar.Squash.get_proof _)) |)

let tc_with_core g (f:R.env) (e:R.term) 
  : T.Tac (option (eff:T.tot_or_ghost & t:R.term & RT.typing f e (eff, t)) & issues)
  = let ropt, issues = catch_all (fun _ -> rtb_core_compute_term_type (push_context g "tc_with_core" (range_of_term e)) f e) in
    match ropt with
    | None -> None, issues
    | Some (eff, t) ->
      Some (| eff, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), issues

let core_compute_term_type (g:env) (t:term)
  : T.Tac (eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)
  = let fg = elab_env g in
    let res, issues = tc_with_core (push_context g "core_check_term" (range_of_term t)) fg t in
    match res with
    | None -> 
      fail_doc_with_subissues g (Some <| RU.range_of_term t) issues (ill_typed_term t None None)
    | Some (| eff, ty', tok |) -> (| eff, ty', E tok |)

let core_check_term g e eff t =
  let fg = elab_env g in
  let topt, issues =
    catch_all (fun _ ->
     rtb_core_check_term
      (push_context g "core_check_term" (range_of_term t))
       fg e eff t) in
  match topt with
  | None ->
    fail_doc_with_subissues g (Some <| RU.range_of_term e) issues (ill_typed_term e (Some t) None)
  | Some tok -> E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok))

let core_check_term_at_type g e t =
  let fg = elab_env g in
  let effopt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "core_check_term_at_type" (range_of_term t))
       fg e t) in
  match effopt with
  | None ->
    fail_doc_with_subissues g (Some <| RU.range_of_term e) issues (ill_typed_term e (Some t) None)
  | Some eff ->
    (| eff, E (RT.T_Token _ _ _ (FStar.Squash.get_proof _)) |)

let check_slprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_slprop) =
  check_term (push_context_no_range g "check_slprop") t T.E_Total tm_slprop

let check_slprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_slprop) =

  core_check_term
    (push_context_no_range g "check_slprop_with_core") t T.E_Total tm_slprop

  
module WT = Pulse.Lib.Core.Typing
module Metatheory = Pulse.Typing.Metatheory.Base

let non_informative_class_typing
  (g:env) (u:universe) (ty:typ) (ty_typing : universe_of g ty u)
  : my_erased (typing_token (elab_env g) (non_informative_class u ty) (E_Total, R.pack_ln (R.Tv_Type u)))
  = E (magic())

(* This function attempts to construct a dictionary for `NonInformative.non_informative ty`.
To do so, we simply create that constraint (and prove it's well-typed), and then
call the tcresolve typeclass resolution tactic on it to obtain a dictionary and
a proof of typing for the dictionary. *)
let try_get_non_informative_witness_aux (g:env) (u:universe) (ty:term) (ty_typing:universe_of g ty u)
  : T.Tac (option (non_informative_t g u ty) & issues)
  = let goal = non_informative_class u ty in
    let r_env = elab_env g in
    let constraint_typing = non_informative_class_typing g u ty ty_typing in
    let goal_typing_tok : squash (typing_token r_env goal (E_Total, R.pack_ln (R.Tv_Type u))) =
      match constraint_typing with | E tok -> Squash.return_squash tok
    in
    let r = T.call_subtac r_env FStar.Tactics.Typeclasses.tcresolve u goal in
    match r with
    | None, issues ->
      None, issues
    | Some r_dict, issues -> (
      // T.print (Printf.sprintf "Resolved to %s" (T.term_to_string r_dict));
      assert (typing_token r_env r_dict (E_Total, goal));
      assume (~(Tv_Unknown? (inspect_ln r_dict)));
      let dict = wr r_dict (RU.range_of_term ty) in
      let r_dict_typing_token : squash (typing_token r_env r_dict (E_Total, goal)) = () in
      let r_dict_typing : RT.typing r_env r_dict (E_Total, goal) = RT.T_Token _ _ _ () in
      let dict_typing : tot_typing g dict (non_informative_class u ty) = E r_dict_typing in
      Some (| dict, dict_typing |), issues
    )

let try_get_non_informative_witness g u ty ty_typing =
  let ropt, _ = try_get_non_informative_witness_aux g u ty ty_typing in
  ropt

let get_non_informative_witness g u t t_typing
  : T.Tac (non_informative_t g u t)
  = match try_get_non_informative_witness_aux g u t t_typing with
    | None, issues ->
      let open Pulse.PP in
      fail_doc g (Some (RU.range_of_term t)) [
        text "Expected a term with a non-informative (e.g., erased) type.";
        prefix 2 1 (text "Got:")
          (pp t);
      ]
    | Some e, issues ->
      e

let try_check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (option (Pulse.Typing.prop_validity g p))
  = let t_opt, issues = rtb_check_prop_validity g true (elab_env g) p in
    t_opt

let check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (Pulse.Typing.prop_validity g p)
  = let t_opt, issues = rtb_check_prop_validity g false (elab_env g) p in
    match t_opt with
    | None -> 
      let open Pulse.PP in
      fail_doc_with_subissues g (Some <| RU.range_of_term p) issues [
        prefix 2 1 (text "Failed to prove pure property:") (pp p);
      ]
    | Some tok -> tok

let fail_expected_tot_found_ghost (g:env) (t:term) =
  fail_doc g (Some (RU.range_of_term t)) [
    prefix 2 1 (text "Expected a total term, got found ghost term:")
      (pp t);
  ]

let compute_tot_term_type g t =
  let (| t, eff, ty, t_typing |) = compute_term_type g t in
  if eff = T.E_Total then (| t, ty, t_typing |)
  else fail_expected_tot_found_ghost g t

let compute_tot_term_type_and_u g t =
  let (| t, eff, ty, (| u, ty_typing |), t_typing |) = compute_term_type_and_u g t in
  if eff = T.E_Total then (| t, u, ty, ty_typing, t_typing |)
  else fail_expected_tot_found_ghost g t

let check_tot_term g e t =
  check_term g e T.E_Total t

let core_compute_tot_term_type g t =
  let (| eff, ty, d |) = core_compute_term_type g t in
  if eff = T.E_Total then (| ty, d |)
  else fail_expected_tot_found_ghost g t

let core_check_tot_term g e t =
  core_check_term g e T.E_Total t

let is_non_informative g c = 
  let ropt, issues = catch_all (fun _ -> T.is_non_informative (elab_env g) (elab_comp c)) in
  T.log_issues issues;
  ropt

let check_subtyping g t1 t2 =
  T.with_policy ForceSMT (fun () ->
  let res, issues = rtb_check_subtyping g t1 t2 in
  match res with
  | Some tok -> tok
  | None ->
    let open Pulse.PP in
    fail_doc_with_subissues g (Some (RU.range_of_term t1)) issues [
      text "Could not prove subtyping of" ^/^ pp t1 ^/^ text "and" ^/^ pp t2
    ]
  )

let check_equiv g t1 t2 =
  let res, issues =
    Pulse.Typing.Util.check_equiv_now (elab_env g) t1 t2 in
  T.log_issues issues;
  res

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
  let e1 = elab_term t1 in
  let e2 = elab_term t2 in
  check_ln g "rtb_check_subtyping.t1" e1;
  check_ln g "rtb_check_subtyping.t2" e2;
  debug g (fun _ ->
    Printf.sprintf "(%s, %s) Calling check_subtyping on %s <: %s"
        (T.range_to_string (t1.range))
        (T.range_to_string (t2.range))
        (P.term_to_string t1)
        (P.term_to_string t2));
  let res = RU.with_context (get_context g) (fun _ -> RTB.check_subtyping (elab_env g) e1 e2) in
  res

let rtb_instantiate_implicits g f t =
  check_ln g "rtb_instantiate_implicits" t;
  debug g (fun _ -> Printf.sprintf "Calling instantiate_implicits on %s"
                                       (T.term_to_string t));
  (* WARN: unary dependence, see comment in RU *)
  let t = RU.deep_transform_to_unary_applications t in
  let res, iss = RU.with_context (get_context g) (fun _ -> RTB.instantiate_implicits f t) in
  match res with
  | None ->
    debug g (fun _ -> "Returned from instantiate_implicits: None");
    res, iss
  | Some (_, t, _) ->
    debug g (fun _ -> Printf.sprintf "Returned from instantiate_implicits: %s" (T.term_to_string t));
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
      then T.with_policy T.SMTSync (fun _ -> RTB.check_prop_validity f sp)
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

let ill_typed_term (t:term) (expected_typ:option term) (got_typ:option term) : Tac (list FStar.Stubs.Pprint.document) =
  let open Pulse.PP in
  match expected_typ, got_typ with
  | None, _ ->
    [text "Ill-typed term: " ^^ pp t]
  | Some ty, None ->
    [group (text "Expected term of type" ^/^ pp ty) ^/^
     group (text "got term" ^/^ pp t)]
  | Some ty, Some ty' ->
    [group (text "Expected term of type" ^/^ pp ty) ^/^
     group (text "got term" ^/^ pp t) ^/^
     group (text "of type" ^/^ pp ty')]

let maybe_fail_doc (issues:list FStar.Issue.issue)
                   (g:env) (rng:range) (doc:list FStar.Stubs.Pprint.document) =
  let has_localized_error = 
      List.Tot.Base.existsb
        (fun i -> 
          FStar.Issue.level_of_issue i = "Error"
          && Some? (FStar.Issue.range_of_issue i))
        issues
  in
  if has_localized_error
  then let message = FStar.Stubs.Pprint.(pretty_string RU.float_one 80 (concat doc)) in
       T.fail message (* Would be nice to tag this failure with the provided range *)
  else fail_doc g (Some rng) doc

let instantiate_term_implicits (g:env) (t0:term) =
  let f = elab_env g in
  let rt = elab_term t0 in
  let f = RU.env_set_range f (Pulse.Typing.Env.get_range g (Some t0.range)) in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f rt) in
  T.log_issues issues;
  match topt with
  | None -> (
    let open Pulse.PP in
    maybe_fail_doc issues
         g t0.range [
              prefix 4 1 (text "Could not infer implicit arguments in")
                        (pp t0)
            ]
  )
  | Some (namedvs, t, ty) ->
    if L.length namedvs <> 0
    then
      let open Pulse.PP in
      maybe_fail_doc []
        g t0.range [
          prefix 4 1 (text "check_term: could not infer implicit arguments in")
                        (pp t0)
        ]
    else 
      let topt = readback_ty t in
      let tyopt = readback_ty ty in
      match topt, tyopt with
      | Some t, Some ty -> t, ty
      | Some _, None ->
        fail g (Some t0.range) (readback_failure ty)
      | None, _ ->
        fail g (Some t0.range) (readback_failure t)

let instantiate_term_implicits_uvs (g:env) (t0:term) =
  let f = elab_env g in
  let rt = elab_term t0 in
  let f = RU.env_set_range f (Pulse.Typing.Env.get_range g (Some t0.range)) in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f rt) in
  T.log_issues issues;
  match topt with
  | None -> (
    let open Pulse.PP in
    maybe_fail_doc issues
         g t0.range [
              prefix 4 1 (text "Could not infer implicit arguments in")
                        (pp t0)
            ]
  )
  | Some (namedvs, t, ty) ->
    let topt = readback_ty t in
    let tyopt = readback_ty ty in
    match topt, tyopt with
    | Some t, Some ty ->
      let (| uvs, t, ty |)
        : uvs:env { disjoint g uvs } &
          term &
          term =
        T.fold_left (fun (| uvs, t, ty |) (namedv, namedvt) ->
          let nview = R.inspect_namedv namedv in
          let ppname = { name = nview.ppname; range = t0.range } <: Pulse.Syntax.Base.ppname in
          let xt = readback_ty namedvt in
          if None? xt
          then fail g (Some t0.range) (readback_failure namedvt)
          else let Some xt = xt in
               let x = fresh (push_env g uvs) in
               let ss = [NT nview.uniq (tm_var {nm_index = x; nm_ppname = ppname})] in
               let uvs : uvs:env { disjoint g uvs } = push_binding uvs x ppname xt in
               (| uvs,
                  subst_term t ss,
                  subst_term ty ss |)) (| mk_env (fstar_env g), t, ty |) namedvs in
      (| uvs, t, ty |)
    | Some _, None ->
      fail g (Some t0.range) (readback_failure ty)
    | None, _ ->
      fail g (Some t0.range) (readback_failure t)

let check_universe (g:env) (t:term)
  : T.Tac (u:universe & universe_of g t u)
  = let f = elab_env g in
    let rt = elab_term t in
    let ru_opt, issues = catch_all (fun _ -> rtb_universe_of g f rt) in
    T.log_issues issues;
    match ru_opt with
    | None -> 
      maybe_fail_doc
        issues
        g t.range (ill_typed_term t (Some (tm_type u_unknown)) None)

    | Some ru ->
      let proof : squash (T.typing_token f rt (E_Total, R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _
      in
      let proof : RT.typing f rt (E_Total, R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
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
    let rt = elab_term t in
    debug g (fun _ ->
            Printf.sprintf "check_tot : called on %s elaborated to %s"
                      (P.term_to_string t)
                      (T.term_to_string rt));
    let res, issues = tc_meta_callback g fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      maybe_fail_doc issues
            g t.range (ill_typed_term t None None)
    | Some (| rt, eff, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> (| t, eff, ty, E tok |)


let compute_term_type_and_u (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           (u:universe & universe_of g ty u) &
           typing g t eff ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    let res, issues = tc_meta_callback g fg rt in
    T.log_issues issues;
    match res with
    | None ->
      maybe_fail_doc 
        issues
        g t.range (ill_typed_term t None None)
    | Some (| rt, eff, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> 
        let (| u, uty |) = check_universe g ty in
        (| t, eff, ty, (| u, uty |), E tok |)

let check_term (g:env) (e:term) (eff:T.tot_or_ghost) (t:term)
  : T.Tac (e:term & typing g e eff t) =

  let e, _ = instantiate_term_implicits g e in

  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in

  let topt, issues =
    catch_all (fun _ -> 
      rtb_core_check_term 
        (push_context g "check_term_with_expected_type_and_effect" (range_of_term rt))
         fg re eff rt) in
  T.log_issues issues;
  match topt with
  | None ->
    maybe_fail_doc 
      issues
      g e.range (ill_typed_term e (Some t) None)
  | Some tok -> (| e, E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok)) |)

let check_term_at_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & eff:T.tot_or_ghost & typing g e eff t) =

  let e, _ = instantiate_term_implicits g e in
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in

  let effopt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "check_term_with_expected_type" (range_of_term rt))
      fg re rt) in
  T.log_issues issues;
  match effopt with
  | None ->
    maybe_fail_doc 
      issues
      g e.range (ill_typed_term e (Some t) None)
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
    let rt = elab_term t in
    let res, issues = tc_with_core (push_context g "core_check_term" (range_of_term rt)) fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      maybe_fail_doc 
        issues
        g t.range (ill_typed_term t None None)
    | Some (| eff, ty', tok |) ->
        match readback_ty ty' with
        | None ->
          fail g (Some t.range) (readback_failure ty')
        | Some ty -> 
          (| eff, ty, E tok |)

let core_check_term g e eff t =
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in
  let topt, issues =
    catch_all (fun _ ->
     rtb_core_check_term
      (push_context g "core_check_term" (range_of_term rt))
       fg re eff rt) in
  T.log_issues issues;
  match topt with
  | None ->
    maybe_fail_doc
      issues
      g e.range (ill_typed_term e (Some t) None)
  | Some tok -> E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok))

let core_check_term_at_type g e t =
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in
  let effopt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "core_check_term_at_type" (range_of_term rt))
       fg re rt) in
  T.log_issues issues;
  match effopt with
  | None ->
    maybe_fail_doc 
      issues
      g e.range (ill_typed_term e (Some t) None)
  | Some eff ->
    (| eff, E (RT.T_Token _ _ _ (FStar.Squash.get_proof _)) |)

let check_vprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_vprop) =
  check_term (push_context_no_range g "check_vprop") t T.E_Total tm_vprop

let check_vprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_vprop) =

  core_check_term
    (push_context_no_range g "check_vprop_with_core") t T.E_Total tm_vprop

  
let pulse_lib_gref = ["Pulse"; "Lib"; "GhostReference"]
let mk_pulse_lib_gref_lid s = pulse_lib_gref@[s]
let gref_lid = mk_pulse_lib_gref_lid "ref"

let pulse_lib_higher_gref = ["Pulse"; "Lib"; "HigherGhostReference"]
let mk_pulse_lib_higher_gref_lid s = pulse_lib_higher_gref@[s]
let higher_gref_lid = mk_pulse_lib_higher_gref_lid "ref"

module WT = Pulse.Lib.Core.Typing
module Metatheory = Pulse.Typing.Metatheory.Base

let try_get_non_informative_witness g u t t_typing
  : T.Tac (option (non_informative_t g u t))
  = let ropt : option (e:term &
                       option (tot_typing g e (non_informative_witness_t u t))) =
      let ropt = is_fvar_app t in
      match ropt with
      | Some (l, us, q_opt, arg_opt) ->
        is_fvar_app_tm_app t;
        if l = R.unit_lid
        then match us, q_opt, arg_opt with
             | [], None, None ->
               Metatheory.unit_typing_inversion u t_typing;
               let e = tm_fvar (as_fv unit_non_informative_lid) in
               Some (| e, Some (E (WT.unit_non_informative_witness_typing (elab_env g))) |)
             | _ -> None
        else if l = R.prop_qn
        then match us, q_opt, arg_opt with
             | [], None, None ->
               Metatheory.prop_typing_inversion u t_typing;
               let e = tm_fvar (as_fv prop_non_informative_lid) in
               Some (| e, Some (E (WT.prop_non_informative_witness_typing (elab_env g))) |)
             | _ -> None
        else if l = R.squash_qn
        then match q_opt, arg_opt, us with
             | None, Some arg, [u_t] ->
               let e =
                 tm_pureapp
                   (tm_uinst (as_fv squash_non_informative_lid) us)
                   None
                   arg in
               let arg_typing = Metatheory.squash_typing_inversion u_t arg u t_typing in
               let d : tot_typing g e (non_informative_witness_t u t) =
                 let E arg_typing = arg_typing in
                 E (WT.squash_non_informative_witness_typing
                      u_t
                      arg_typing) in
               Some (| e, Some d |)
             | _ -> None
        else if l = erased_lid && Some? arg_opt
        then let e =
               tm_pureapp
                 (tm_uinst (as_fv (mk_pulse_lib_core_lid "erased_non_informative")) us)
                 None
                 (Some?.v arg_opt) in
             Some (| e, None |)
        else if l = gref_lid && Some? arg_opt
        then let e =  
               tm_pureapp
                 (tm_uinst (as_fv (mk_pulse_lib_gref_lid "gref_non_informative")) us)
                 None
                 (Some?.v arg_opt) in
             Some (| e, None |)
        else if l = higher_gref_lid && Some? arg_opt
        then let e =
               tm_pureapp
                 (tm_uinst (as_fv (mk_pulse_lib_higher_gref_lid "gref_non_informative")) us)
                 None
                 (Some?.v arg_opt) in
             Some (| e, None |)
        else None
      | _ ->
        // ghost_pcm_ref #a p
        let is_ghost_pcm_ref () =
          let ropt = is_pure_app t in
          match ropt with
          | None -> None
          | Some (t, _, arg2) ->
            let ropt = is_fvar_app t in
            match ropt with
            | None -> None
            | Some (l, us, _, arg1_opt) ->
              if l = mk_pulse_lib_core_lid "ghost_pcm_ref" &&
                 Some? arg1_opt
              then let t = tm_pureapp
                     (tm_uinst (as_fv (mk_pulse_lib_core_lid "ghost_pcm_ref_non_informative")) us)
                     None
                     (Some?.v arg1_opt) in
                   let t = tm_pureapp t None arg2 in
                   Some (| t, None |)
              else None
        in
        is_ghost_pcm_ref ()
    in
    match ropt with
    | None -> None
    | Some (| e, dopt |) ->
      match dopt with
      | None ->
        let tok =
          check_term
            (push_context_no_range g "get_noninformative_witness")
            e
            T.E_Total
            (non_informative_witness_t u t)
        in
        Some tok
      | Some d -> Some (| e, d |)

let get_non_informative_witness g u t t_typing
  : T.Tac (non_informative_t g u t)
  = match try_get_non_informative_witness g u t t_typing with
    | None ->
      let open Pulse.PP in
      fail_doc g (Some t.range) [
        text "Expected a term with a non-informative (e.g., erased) type; got"
          ^/^ pp t
      ]
    | Some e -> e
    

let try_check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (option (Pulse.Typing.prop_validity g p))
  = let t_opt, issues = rtb_check_prop_validity g true (elab_env g) (elab_term p) in
    t_opt

let check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (Pulse.Typing.prop_validity g p)
  = let t_opt, issues = rtb_check_prop_validity g false (elab_env g) (elab_term p) in
    T.log_issues issues;
    match t_opt with
    | None -> 
      let open Pulse.PP in
      maybe_fail_doc issues g p.range
                     [text "Failed to prove property:" ^/^ pp p]
    | Some tok -> tok

let fail_expected_tot_found_ghost (g:env) (t:term) =
  fail g (Some t.range)
    (Printf.sprintf "Expected a total term, found ghost term %s" (P.term_to_string t))

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
  T.with_policy SMTSync (fun () ->
  let res, issues = rtb_check_subtyping g t1 t2 in
  T.log_issues issues;
  match res with
  | Some tok -> tok
  | None ->
    let open Pulse.PP in
    maybe_fail_doc issues g t1.range
          [ text "Could not prove subtyping of "
            ^/^ pp t1 ^/^ text "and" ^/^ pp t2]
  )

let check_equiv g t1 t2 =
  let res, issues =
    Pulse.Typing.Util.check_equiv_now (elab_env g) (elab_term t1) (elab_term t2) in
  T.log_issues issues;
  res

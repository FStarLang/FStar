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

module Pulse.Main

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
open FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate
open Pulse.Soundness
module Cfg = Pulse.Config
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer
module Rec = Pulse.Recursion

let debug_main g (s: unit -> T.Tac string) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.main"
  then T.print (s ())
  else ()

let rec mk_abs (g:env) (qbs:list (option qualifier & binder & bv)) (body:st_term) (comp:comp)
: TacH st_term (fun _ -> not (Nil? qbs))
               (fun _ r -> match r with FStar.Tactics.Result.Success v _ -> Tm_Abs? v.term | _ -> False)
=
  let with_range (s:st_term') (r:range) : st_term =
    { term = s; range = r; effect_tag = default_effect_hint }
  in
  match qbs with
  | [(q, last, last_bv)] -> 
    let body = close_st_term body last_bv.bv_index in
    let comp = close_comp comp last_bv.bv_index in
    let asc = { annotated = Some comp; elaborated = None } in
    with_range (Pulse.Syntax.Builder.tm_abs last q asc body) body.range
  | (q, b, bv)::qbs ->
    let body = mk_abs g qbs body comp in
    let body = close_st_term body bv.bv_index in
    with_range (Pulse.Syntax.Builder.tm_abs b q empty_ascription body) body.range

let mk_opaque_let_with_impl (g:R.env) (cur_module:R.name) (nm:string) (tm:Ghost.erased R.term) (ty:R.typ{RT.typing g tm (T.E_Total, ty)})
  (impl: R.term)
  : T.Tac (RT.sigelt_for g (Some ty)) =
  let open FStar.List.Tot in
  let fv = R.pack_fv (cur_module @ [nm]) in
  let lb_def = impl in // super hack
  let lb = R.pack_lb ({ lb_fv = fv; lb_us = []; lb_typ = ty; lb_def }) in
  let se = R.pack_sigelt (R.Sg_Let false [lb]) in
  let pf : RT.sigelt_typing g se = admit () in // hack
  (true, se, None)

let set_impl #g #t (se: RT.sigelt_for g t) (r: bool) (impl: R.term) : Dv (RT.sigelt_for g t) =
  admit ();
  let R.Sg_Let false [lb] = R.inspect_sigelt se._2 in
  let lb = R.inspect_lb lb in
  let lb = { lb with lb_def = impl } in // super hack
  true, R.pack_sigelt (R.Sg_Let r [R.pack_lb lb]), se._3

#push-options "--z3rlimit_factor 4"
let check_fndefn
    (d : decl{FnDefn? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
    (expected_t : option term)
    (* Both of these unused: *)
    (pre : term) (pre_typing : tot_typing g pre tm_slprop)
  : T.Tac (RT.dsl_tac_result_t (fstar_env g) expected_t)
= 

  (* Maybe add a recursive knot before starting *)
  let FnDefn fn_d = d.d in
  let nm_orig = fst (inspect_ident fn_d.id) in // keep the original name
  let d =
    if fn_d.isrec
    then Recursion.add_knot g d.range d
    else d
  in

  let FnDefn { id; isrec; bs; comp; meas; body } = d.d in
  let nm_aux = fst (inspect_ident id) in

  if Nil? bs then
    fail g (Some d.range) "main: FnDefn does not have binders";
  let body = mk_abs g bs body comp in
  let rng = body.range in
  debug_main g (fun _ -> Printf.sprintf "\nbody after mk_abs:\n%s\n" (P.st_term_to_string body));

  let (| body, c, t_typing |) = Pulse.Checker.Abs.check_abs g body Pulse.Checker.check in

  Pulse.Checker.Prover.debug_prover g
    (fun _ -> Printf.sprintf "\ncheck call returned in main with:\n%s\nat type %s\n"
              (P.st_term_to_string body)
              (P.comp_to_string c));
  debug_main g
    (fun _ -> Printf.sprintf "\nchecker call returned in main with:\n%s\nderivation=%s\n"
              (P.st_term_to_string body)
              (Pulse.Typing.Printer.print_st_typing t_typing));

  let refl_t = elab_comp c in
  
  let refl_e = Pulse.RuntimeUtils.embed_st_term_for_extraction #st_term body (Some rng) in
  let blob = "pulse", refl_e in
  soundness_lemma g body c t_typing;

  let elab_derivation = T.ext_getv "pulse:elab_derivation" <> "" in
  let cur_module = T.cur_module () in

  let maybe_add_impl t (se: RT.sigelt_for (fstar_env g) t) =
    let open Pulse.Extract.Main in begin
    let uenv = Extract.CompilerLib.new_uenv (fstar_env g) in
    if C_STGhost? comp then
      set_impl se false (extract_dv_ghost { uenv_inner = uenv; coreenv = Extract.CompilerLib.initial_core_env uenv } body)
    else if fn_d.isrec then
      let impl = extract_dv_recursive { uenv_inner = uenv; coreenv = Extract.CompilerLib.initial_core_env uenv } body (R.pack_fv (cur_module @ [nm_orig])) in
      set_impl se true impl
    else
      set_impl se false (extract_pulse_dv uenv body)
    end in

  let mk_main_decl
    (refl_t:typ)
    (_:squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t)) =
    let nm = fst (inspect_ident id) in
    if elab_derivation
    then RT.mk_checked_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
    else Reflection.Util.mk_opaque_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
  in

  if fn_d.isrec
  then begin
    //
    // For the recursive case, the recursive decl is the one that has the
    //   input expected type
    // However, for it, we don't set the checked flag and let F* typecheck it
    //
    // So, nothing to be done for expected type here
    //
    let main_decl = mk_main_decl refl_t () in
    let main_decl : RT.sigelt_for (elab_env g) None = main_decl in
    let (chk, se, _) = main_decl in
    let nm = R.pack_ln (R.Tv_Const (R.C_String nm_orig)) in
    let attribute = `("pulse.recursive", `#(nm)) in
    let se = RU.add_attribute se (`(noextract_to "krml")) in
    let se = RU.add_noextract_qual se in
    let se : T.sigelt = RU.add_attribute se attribute in
    let main_decl = chk, se, Some blob in
    let recursive_decl : RT.sigelt_for (elab_env g) expected_t =
      Rec.tie_knot g rng nm_orig nm_aux refl_t blob in
    [main_decl], maybe_add_impl _ recursive_decl, []
  end
  else begin
    //
    // For the non-recursive case,
    //   we need to check that the computed type is a subtype of the expected type
    //
    let (| refl_t, _ |) :
      refl_t:term { Some? expected_t ==> Some refl_t == expected_t } &
      squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t) =

      match expected_t with
      | None -> (| refl_t, FStar.Squash.get_proof _ |)

      | Some t ->
        let tok = Pulse.Checker.Pure.check_subtyping g refl_t t in
        let refl_t_typing
          : squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t) = () in
        let sq : squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) t) =
          FStar.Squash.bind_squash refl_t_typing (fun refl_t_typing ->
            FStar.Squash.return_squash (
              RT.T_Sub _ _ _ _
                refl_t_typing
                (RT.Relc_typ _ _ _ _ RT.R_Sub
                   (RT.Rel_subtyping_token _ _ _ (FStar.Squash.return_squash tok))))) in

        (| t, sq |)
    in

    let main_decl = mk_main_decl refl_t () in
    let chk, se, _ = main_decl in
    let main_decl = chk, se, Some blob in
    [], maybe_add_impl _ main_decl, []
  end

let check_fndecl
    (d : decl{FnDecl? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
  : T.Tac (RT.dsl_tac_result_t (fstar_env g) None)
=
  let FnDecl { id; bs; comp } = d.d in
  if Nil? bs then
    fail g (Some d.range) "main: FnDecl does not have binders";

  let nm = fst (inspect_ident id) in
  let stc = st_comp_of_comp comp in

  (* We make a dummy FnDefn setting the body to a Tm_Admit, and
  call the checker to elaborate its actual type. *)
  let body : st_term = {
    term = Tm_Admit {
      ctag   = ctag_of_comp_st comp;
      u      = stc.u;
      typ    = stc.res;
      post   = None; // Some stc.post?
    };
    range = d.range;
    effect_tag = seal None;
  }
  in
  let body = mk_abs g bs body comp in
  let rng = body.range in
  let (| _, c, t_typing |) =
    (* We don't want to print the diagnostic for the admit in the body. *)
    RU.with_extv "pulse:no_admit_diag" "1" (fun () ->
      Pulse.Checker.Abs.check_abs g body Pulse.Checker.check
    )
  in
  let typ = elab_comp c in
  let se : sigelt =
    pack_sigelt <|
    Sg_Val {
      nm = cur_module () @ [nm];
      univs = [];
      typ = typ
    }
  in
  ([], (false, se, None), [])

let main' (d:decl) (pre:term) (g:RT.fstar_top_env) (expected_t:option term)
  : T.Tac (RT.dsl_tac_result_t g expected_t)
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse" then 
        T.print (Printf.sprintf "About to check pulse decl:\n%s\n" (P.decl_to_string d));
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.compute_tot_term_type g pre in
      if not (eq_tm ty tm_slprop) then
        fail g (Some (Pulse.RuntimeUtils.range_of_term pre)) "pulse main: cannot typecheck pre at type slprop"; //fix range
      let pre_typing : tot_typing g pre tm_slprop = pre_typing in
      match d.d with
      | FnDefn {} -> check_fndefn d g expected_t pre pre_typing
      | FnDecl {} ->
        if None? expected_t then
          check_fndecl d g
        else
          fail g (Some d.range) "pulse main: expected type provided for a FnDecl?"

let join_smt_goals () : Tac unit =
  let open FStar.Tactics.V2 in
  let open FStar.List.Tot in

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals before join";

  (* Join *)
  let smt_goals = smt_goals () in
  set_goals (goals () @ smt_goals);
  set_smt_goals [];
  let n = List.Tot.length (goals ()) in
  ignore (repeat join);

  (* Heuristic rlimit setting :). Increase by 2 for every joined goal.
  Default rlimit is 5, so this is "saving" 3 rlimit units per joined
  goal. *)
  if not (Nil? (goals ())) then (
    let open FStar.Mul in
    let rlimit = get_rlimit() + (n-1)*2 in
    set_rlimit rlimit
  );

  if RU.debug_at_level (top_env ()) "pulse.join" then
    dump "PULSE: Goals after join";

  ()

let parse_guard_policy (s:string) : Tac guard_policy =
  match s with
  | "Goal" -> Goal
  | "SMT" -> SMT
  | "SMTSync" -> SMTSync
  | "Force" -> Force
  | "ForceSMT" -> ForceSMT
  // | "Drop" -> Drop (* terribly unsound, so not even allowing it here *)
  | _ -> Tactics.fail ("Unknown guard policy: " ^ s)

let main t pre : RT.dsl_tac_t = fun (g, expected_t) ->
  (* We use the ForceSMT policy by default, to discharge guards
  immediately when they show, allowing SMT. This
  proofstate and discharge them all at the end, potentially joining
  them (see below).
  This can be overriden to others by `--ext pulse:guard_policy=<guard>`
  where <guard> is one of of the above (see parse_guard_policy). *)
  set_guard_policy ForceSMT;
  if ext_getv "pulse:guard_policy" <> "" then
    set_guard_policy (parse_guard_policy (ext_getv "pulse:guard_policy"));

  let res = main' t pre g expected_t in

  if ext_getv "pulse:join" = "1"
     (* || ext_getv "pulse:join" <> "" *)
     // ^ Uncomment to make it true by default.
  then
    join_smt_goals();
  res

let check_pulse_core 
        (as_decl: unit -> Tac (either Pulse.Syntax.decl (option (string & R.range))))
  : RT.dsl_tac_t
  = fun (env, expected_t) ->
      if ext_getv "pulse:dump_on_failure" <> "1" then
        set_dump_on_failure false;
      match as_decl () with
      | Inl decl ->
        main decl tm_emp (env, expected_t)

      | Inr None ->
        T.fail "Pulse parser failed"

      | Inr (Some (msg, range)) ->
        let i =
          Issue.mk_issue "Error"
                   (Printf.sprintf "%s: %s" (T.range_to_string range) msg)
                   (Some range)
                   None
                   []
        in
        T.log_issues [i];
        T.fail "Pulse parser failed"



[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
                (nm:string)
  : RT.dsl_tac_t
  = fun (env, expected_t) ->
      check_pulse_core
        (fun () -> PulseSyntaxExtension.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col)
        (env, expected_t)

[@@plugin]
let check_pulse_after_desugar
      (decl:'a)
: RT.dsl_tac_t
= fun (env, expected_t) ->
    check_pulse_core
        (fun () -> 
          let decl : Pulse.Syntax.decl = RU.unembed_pulse_decl decl in
          Inl decl)
        (env, expected_t)

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

#push-options "--z3rlimit_factor 4"
let check_fndecl
    (d : decl{FnDecl? d.d})
    (g : Soundness.Common.stt_env{bindings g == []})
    (expected_t : option term)
    (pre : term) (pre_typing : tot_typing g pre tm_vprop)
  : T.Tac (RT.dsl_tac_result_t (fstar_env g) expected_t)
= 

  (* Maybe add a recursive knot before starting *)
  let FnDecl fn_d = d.d in
  let nm_orig = fst (inspect_ident fn_d.id) in // keep the original name
  let d =
    if fn_d.isrec
    then Recursion.add_knot g d.range d
    else d
  in

  let FnDecl { id; isrec; bs; comp; meas; body } = d.d in
  let nm_aux = fst (inspect_ident id) in

  if Nil? bs then
    fail g (Some d.range) "main: FnDecl does not have binders";
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

  let mk_main_decl
    (refl_t:typ)
    (_:squash (RT.tot_typing (elab_env g) (elab_st_typing t_typing) refl_t)) =
    let nm = fst (inspect_ident id) in
    if elab_derivation
    then RT.mk_checked_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
    else Pulse.Reflection.Util.mk_opaque_let (fstar_env g) cur_module nm (elab_st_typing t_typing) refl_t
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
    [main_decl], recursive_decl, []
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
    [], main_decl, []
  end

let main' (nm:string) (d:decl) (pre:term) (g:RT.fstar_top_env) (expected_t:option term)
  : T.Tac (RT.dsl_tac_result_t g expected_t)
  = match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      if RU.debug_at_level (fstar_env g) "Pulse" then 
        T.print (Printf.sprintf "About to check pulse decl:\n%s\n" (P.decl_to_string d));
      let (| pre, ty, pre_typing |) = Pulse.Checker.Pure.compute_tot_term_type g pre in
      if not (eq_tm ty tm_vprop) then
        fail g (Some (Pulse.RuntimeUtils.range_of_term pre)) "pulse main: cannot typecheck pre at type vprop"; //fix range
      let pre_typing : tot_typing g pre tm_vprop = pre_typing in
      match d.d with
      | FnDecl _ ->
        check_fndecl d g expected_t pre pre_typing

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

let main nm t pre : RT.dsl_tac_t = fun (g, expected_t) ->
  (* We use the SMT policy by default, to collect goals in the
  proofstate and discharge them all at the end, potentially joining
  them (see below). But it can be overriden to ForceSMT by `--ext
  pulse:guard_policy=ForceSMT`. *)
  if ext_getv "pulse:guard_policy" = "ForceSMT" then
    set_guard_policy ForceSMT
  else
    set_guard_policy SMT;

  let res = main' nm t pre g expected_t in

  if ext_getv "pulse:join" = "1"
     (* || ext_getv "pulse:join" <> "" *)
     // ^ Uncomment to make it true by default.
  then
    join_smt_goals();
  res

[@@plugin]
let check_pulse (namespaces:list string)
                (module_abbrevs:list (string & string))
                (content:string)
                (file_name:string)
                (line col:int)
                (nm:string)
  : RT.dsl_tac_t
  = fun (env, expected_t) ->
      if ext_getv "pulse:dump_on_failure" <> "1" then
        set_dump_on_failure false;
      match PulseSyntaxExtension.ASTBuilder.parse_pulse env namespaces module_abbrevs content file_name line col with
      | Inl decl ->
        main nm decl tm_emp (env, expected_t)

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

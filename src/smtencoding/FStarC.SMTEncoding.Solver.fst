(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.Solver

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.SMTEncoding.Z3
open FStarC.SMTEncoding.Term
open FStarC.Util
open FStarC.SMap
open FStarC.TypeChecker
open FStarC.TypeChecker.Env
open FStarC.SMTEncoding
open FStarC.SMTEncoding.ErrorReporting
open FStarC.SMTEncoding.Util
open FStarC.SMTEncoding.Env
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Class.Hashable
open FStarC.RBSet
open FStarC.Syntax.Print {} // instances

module BU       = FStarC.Util
module Env      = FStarC.TypeChecker.Env
module Err      = FStarC.Errors
module Syntax   = FStarC.Syntax.Syntax
exception SplitQueryAndRetry

let dbg_SMTQuery = Debug.get_toggle "SMTQuery"
let dbg_SMTFail  = Debug.get_toggle "SMTFail"

(***********************************************************************************)
(* Invoking the SMT solver and extracting an error report from the model, if any    *)
(*                                                                                  *)
(* A verification condition is split into a tree of goals (see                      *)
(* FStarC.SMTEncoding.ErrorReporting): binders become declarations, hypotheses      *)
(* become assertions, and every leaf gets its own (check-sat).  Shared context is   *)
(* sent to the solver once, and only the goals that failed are retried with more    *)
(* fuel.                                                                            *)
(***********************************************************************************)
type errors = {
    error_reason:string;
    error_rlimit: int;
    error_fuel: int;
    error_ifuel: int;
}

let error_to_short_string err =
    Format.fmt4 "%s (rlimit=%s; fuel=%s; ifuel=%s)"
            err.error_reason
            (show err.error_rlimit)
            (show err.error_fuel)
            (show err.error_ifuel)

type query_settings = {
    query_env:env_t;
    query_decl:decl;
    query_name:string;
    query_index:int;
    query_range:Range.t;
    query_fuel:int;
    query_ifuel:int;
    query_rlimit:int;
    query_goals:goal_tree;
    query_term: FStarC.Syntax.Syntax.term;
}

(* The state of a single proof obligation while we are trying to discharge it. *)
type goal_state = {
    gs_goal     : goal;
    gs_nsuccess : int;
    gs_nfailure : int;
    gs_errors   : list errors; //most recent first
}

let initial_goal_state (g:goal) : goal_state =
  { gs_goal = g; gs_nsuccess = 0; gs_nfailure = 0; gs_errors = [] }

(* Translation from F* rlimit units to Z3 rlimit units.

This used to be defined as exactly 544656 since that roughtly
corresponded to 5 seconds in some "blessed" setting. But rlimit units
are only very roughly correlated to time, and having this very non-round
number makes reading SMT query dumps pretty confusing. So, for new
solvers, we now just make it 500k. *)
let convert_rlimit (r : int) : ML int =
  if Misc.version_ge (Options.z3_version ()) "4.12.3" then
    500000 * r
  else
    544656 * r

(* The block sent to the solver for a single proof obligation: the fuel
settings, the negated goal, and the check-sat itself, all in their own
push/pop frame.  The <goal> markers let us recover one result per block
from a batched round trip. *)
let goal_block (settings:query_settings) (g:goal) : ML (list decl) =
    let n = settings.query_fuel in
    let i = settings.query_ifuel in
    let rlimit = convert_rlimit settings.query_rlimit in
    [  Term.Push 0;
       Term.Caption (Format.fmt3 "<goal %s fuel='%s' ifuel='%s'>"
                       (show g.goal_id) (show n) (show i));
       Util.mkAssume(mkEq(mkApp("MaxFuel", []), n_fuel n), None, "@MaxFuel_assumption");
       Util.mkAssume(mkEq(mkApp("MaxIFuel", []), n_fuel i), None, "@MaxIFuel_assumption");
       Util.mkAssume(mkNot g.goal_term, Some "query", "@query");
       Term.SetOption "rlimit" (show rlimit); //the rlimit setting for the check-sat

       Term.Echo "<goal>";
       // Print stats just before the query, so we know the initial rlimit.
       Term.Echo "<initial_stats>";
       Term.GetStatistics;
       Term.Echo "</initial_stats>";

       Term.CheckSat; //go Z3!
       Term.SetOption "rlimit" "0"; //back to using infinite rlimit
       Term.GetReasonUnknown; //explain why it failed
    ]
    @(if Options.print_z3_statistics() || Options.query_stats ()
      then [Term.GetStatistics] else [])
    @[ Term.Echo "</goal>";
       Term.Pop 0 ]

(* Walk the goal tree, emitting the declarations and hypotheses shared by the
goals we still need to discharge, and a check-sat block for each of them.  A
subtree with no pending goal is skipped entirely.  Returns the decls and the
goals, in the order in which their results will come back. *)
let rec emit_goals (pending : int -> ML bool) (settings:query_settings) (t:goal_tree)
  : ML (list decl & list goal)
  = match t with
    | GTrivial -> [], []
    | GLeaf g ->
      if pending g.goal_id then goal_block settings g, [g] else [], []
    | GCtx ds t ->
      let ds', gs = emit_goals pending settings t in
      (match gs with
       | [] -> [], []
       | _ -> (Term.Push 0 :: ds @ ds') @ [Term.Pop 0], gs)
    | GBranch ts ->
      List.fold_left (fun (ds, gs) t ->
        let ds', gs' = emit_goals pending settings t in
        ds @ ds', gs @ gs') ([], []) ts

let query_errors settings z3result =
    match z3result.z3result_status with
    | UNSAT -> None
    | _ ->
     let msg = Z3.status_string z3result.z3result_status in
     Some {
            error_reason = msg;
            error_rlimit = settings.query_rlimit;
            error_fuel = settings.query_fuel;
            error_ifuel = settings.query_ifuel;
     }

let errors_to_report (tried_recovery : bool) (settings : query_settings) (gst : goal_state)
  : ML (list Errors.error) =
    let open FStarC.Pprint in
    let open FStarC.Errors in
    let format_smt_error (msg:list document) : ML (list document) =
      (* This creates an error component with the answers from Z3. Only used
      for --query_stats. *)
      let d =
        doc_of_string "SMT solver says:" ^^
          sublist empty msg ^^
        hardline ^^
        doc_of_string "Note:" ^^
          bulleted [
            text "'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit";
            text "'incomplete quantifiers' means Z3 could not prove the query, so try to spell out your proof out in greater detail, increase fuel or ifuel";
            text "'unknown' means Z3 provided no further reason for the proof failing"
          ]
      in
      [d] // single error component
    in
    let recovery_failed_msg : Errors.error_message =
      if tried_recovery then
        [text "This query was retried due to the --proof_recovery option, yet it
               still failed on all attempts."]
      else
        []
    in
    (*
     * smt_error is a single error message containing either a multi-line detailed message
     * or a single short component, depending on whether --query_stats is on
     *)
    let smt_error =
      if Options.query_stats () then
        gst.gs_errors
        |> List.map error_to_short_string
        |> List.map doc_of_string
        |> format_smt_error
      else
        (*
         * AR: --query_stats is not set, we want to give a succint but helpful diagnosis
         *
         *     gs_errors is a list of errors, whose field error_reason contains the strings:
         *       unknown because (incomplete ...) or unknown because (resource ...) or unknown because canceled etc.
         *     it's a list as it contains one element per config (e.g. fuel options)
         *
         *     in the following code we go through the error reasons in all the configs,
         *       and if all the error reasons are the same, we provide a hint for that reason
         *     otherwise we just ask the user to run with --query_stats
         *
         *     as per the smt-lib standard, the possible values of reason-unknown are s-expressions,
         *       that are either non-space strings, or strings with spaces enclosed in parenthesis
         *       (I think), so incomplete or resource messages are in parenthesis, whereas
         *       canceled, timeout, etc. are without
         *)
        let incomplete_count, canceled_count, unknown_count, z3_overflow_bug_count =
          List.fold_left (fun (ic, cc, uc, bc) err ->
            let err =
              if BU.starts_with err.error_reason "unknown because "
              then BU.substring_from err.error_reason (String.length "unknown because ")
              else err.error_reason
            in
            //err is (incomplete quantifiers), (resource ...), canceled, or unknown etc.

            match () with
            | _ when BU.starts_with err "(incomplete" ->
                (ic + 1, cc, uc, bc)
            | _ when BU.starts_with err "canceled" || BU.starts_with err "(resource" || BU.starts_with err "timeout" ->
                (ic, cc + 1, uc, bc)
            | _ when BU.starts_with err "Overflow encountered when expanding old_vector" ->
                (ic, cc, uc, bc + 1)
            | _ ->
                (ic, cc, uc + 1, bc)  //note this covers unknowns, overflows, etc.
          ) (0, 0, 0, 0) gst.gs_errors
        in
        (* If we notice the z3 overflow bug, add a separate error to warn the user. *)
        if z3_overflow_bug_count > 0 then
          Errors.log_issue gst.gs_goal.goal_range Errors.Warning_UnexpectedZ3Stderr [
            text "Z3 ran into an internal overflow while trying to prove this query.";
            text "Try breaking it down into smaller pieces."
          ];
        let base =
          match incomplete_count, canceled_count, unknown_count with
          | _, 0, 0 when incomplete_count > 0 -> [text "The SMT solver could not prove the query."]
          | 0, _, 0 when canceled_count > 0   -> [text "The SMT query timed out, you might want to increase the rlimit"]
          | _, _, _                           -> [text "Try with --query_stats to get more details"]
        in
        base @ recovery_failed_msg
    in
    let open FStarC.Errors.Msg in
    let open FStarC.Class.PP in
    let vc_detail =
      if Options.query_stats () then [
        prefix 2 1 (text "Env =")
          (all_binders settings.query_env.tcenv |> Pprint.flow_map (break_ 1) fun (b:Syntax.binder) ->
            group <| parens <| nest 2 <|
              pp b.binder_bv.ppname ^/^ colon ^/^ pp b.binder_bv.sort);
        prefix 2 1 (text "VC =") (pp settings.query_term);
      ] else []
    in
    FStarC.TypeChecker.Err.errors_smt_detail
      settings.query_env.tcenv
      [(Error_Z3SolverError, gst.gs_goal.goal_msg, gst.gs_goal.goal_range, get_ctx())]
      (smt_error @ vc_detail)

type unique_string_accumulator = {
  add: string -> ML unit;
  get: unit -> ML (list string);
  clear: unit -> ML unit
}

(* A generic accumulator of unique strings,
   extracted in sorted order *)
let mk_unique_string_accumulator ()
: ML unique_string_accumulator
= let strings = mk_ref [] in
  let add m =
    let ms = !strings in
    if List.contains m ms then ()
    else strings := m :: ms
  in
  let get () = 
    !strings |> BU.sort_with String.compare
  in
  let clear () = strings := [] in
  { add ; get; clear }

let div_with_decimals (ndec : nat) (x y : int) : ML string =
  let mul =
    (* no power function in F* sources? *)
    let rec aux (n:nat) =
      if n = 0 then 1 else 10 * aux (n - 1)
    in
    aux ndec
  in
  let intg = x / y in
  let frac = mul * x / y % mul in
  (* zero pad *)
  let frac =
    let len = String.length (show frac) in
    let pad = ndec - len in
    String.make pad '0' ^ show frac
  in
  show intg ^ "." ^ frac // pad

let full_query_id settings =
    "(" ^ settings.query_name ^ ", " ^ (show settings.query_index) ^ ")"

let query_info settings (g:goal) z3result =
    if Options.query_stats()
    then begin
        let status_string = Z3.status_string z3result.z3result_status in
        let at_log_file =
            match z3result.z3result_log_file with
            | None -> ""
            | Some s -> "@"^s
        in
        let tag = match z3result.z3result_status with
         | UNSAT -> Format.colorize_green "succeeded"
         | _ -> Format.colorize_red ("failed {reason-unknown=" ^ status_string ^ "}")
        in
        let range = "(" ^ show g.goal_range ^ at_log_file ^ ")" in
        let used_rlimit_str =
          try
            let decimals = 3 in
            let r0 = int_of_string <| Some?.v <| SMap.try_find z3result.z3result_initial_statistics "rlimit-count" in
            let r1 = int_of_string <| Some?.v <| SMap.try_find z3result.z3result_statistics "rlimit-count" in
            let used = r1 - r0 in
            div_with_decimals decimals used (convert_rlimit 1)
          with
          | _ -> "unknown"
        in
        if Options.Ext.enabled "query_stats_trace"
        then (
          Format.print "At %s\nQuery term is %s\n"
                [BU.stack_dump();
                 show settings.query_term]
        );
        Format.print "%s\tQuery-stats (%s, %s)\tgoal %s %s with fuel %s and ifuel %s and rlimit %s (used rlimit %s)\n"
             [  range;
                settings.query_name;
                show settings.query_index;
                show g.goal_id;
                tag;
                show settings.query_fuel;
                show settings.query_ifuel;
                show settings.query_rlimit;
                used_rlimit_str;
             ]
    end

(* An answer for an "ask" to the solver. The ok boolean marks whether
it succeeded or not. The rest is only used for error reporting. *)
type answer = {
    ok                  : bool;
    (* ^ Query was proven *)
    cache_hit           : bool;
    (* ^ Got result from cache. Currently, this also implies
    ok=true (we don't cache failed queries), but don't count
    on it. *)

    quaking             : bool;
    (* ^ Were we quake testing? *)
    quaking_or_retrying : bool;
    (* ^ Were we quake testing *or* retrying? *)
    lo                  : int;
    (* ^ Lower quake bound. *)
    hi                  : int;
    (* ^ Higher quake bound. *)
    tried_recovery      : bool;
    (* ^ Did we try using --proof_recovery for this? *)

    failed              : list goal_state;
    (* ^ The proof obligations that could not be discharged. *)
}

let ans_ok : answer = {
    ok                  = true;
    cache_hit           = false;
    lo                  = 1;
    hi                  = 1;
    quaking             = false;
    quaking_or_retrying = false;
    tried_recovery      = false;
    failed              = [];
}

let ans_fail : answer =
  { ans_ok with ok = false }

instance _ : showable answer = {
  show = (fun ans -> Format.fmt4 "ok=%s lo=%s hi=%s tried_recovery=%s"
                            (show ans.ok)
                            (show ans.lo)
                            (show ans.hi)
                            (show ans.tried_recovery));
}

let make_solver_configs
    (env : env_t)
    (goals : goal_tree)
    (query : decl)
    (query_term : Syntax.term)
 : ML (list query_settings)
 =
    (* Fetch the settings. *)
    let qname, index =
        match env.tcenv.qtbl_name_and_index with
        | None, _ -> failwith "No query name set!"
        | Some (q, _typ, n), _ -> Ident.string_of_lid q, n
    in
    let default_settings =
        let rlimit =
            Options.z3_rlimit_factor () * Options.z3_rlimit ()
        in
        {
            query_env=env;
            query_decl=query;
            query_name=qname;
            query_index=index;
            query_range=Env.get_range env.tcenv;
            query_fuel=Options.initial_fuel();
            query_ifuel=Options.initial_ifuel();
            query_rlimit=rlimit;
            query_goals=goals;
            query_term=query_term;
        }
    in

    let initial_fuel_max_ifuel =
        if Options.max_ifuel() > Options.initial_ifuel()
        then [{default_settings with query_ifuel=Options.max_ifuel()}]
        else []
    in

    let half_max_fuel_max_ifuel =
        if Options.max_fuel() / 2 >  Options.initial_fuel()
        then [{default_settings with query_fuel=Options.max_fuel() / 2;
                                     query_ifuel=Options.max_ifuel()}]
        else []
    in

    let max_fuel_max_ifuel =
      if Options.max_fuel()    >  Options.initial_fuel()
      && Options.max_ifuel()   >=  Options.initial_ifuel()
      then [{default_settings with query_fuel=Options.max_fuel();
                                   query_ifuel=Options.max_ifuel()}]
      else []
    in
    [default_settings]
    @ initial_fuel_max_ifuel
    @ half_max_fuel_max_ifuel
    @ max_fuel_max_ifuel

let killed_result () : ML z3result = {
    z3result_status             = Z3.KILLED;
    z3result_time               = 0;
    z3result_initial_statistics = SMap.create 0;
    z3result_statistics         = SMap.create 0;
    z3result_log_file           = None;
}

(* Results come back in emission order.  If the solver died part-way through we
get fewer of them than we asked for; the remaining goals count as killed. *)
let rec zip_results (gs : list goal) (rs : list z3result) : ML (list (goal & z3result)) =
    match gs with
    | [] -> []
    | g::gs ->
      match rs with
      | r::rs -> (g, r) :: zip_results gs rs
      | [] -> (g, killed_result ()) :: zip_results gs []

(* Ask the solver about every goal in [active], in a single round trip, and
record the outcome in each goal's state. *)
let run_round (settings:query_settings) (active : list goal_state) : ML (list goal_state) =
    match active with
    | [] -> []
    | _ ->
      if Options.z3_refresh()
      then Z3.refresh (Some settings.query_env.tcenv.proof_ns);
      let ids = active |> List.map (fun gst -> gst.gs_goal.goal_id) in
      let decls, emitted =
        emit_goals (fun id -> List.contains id ids) settings settings.query_goals
      in
      let results =
        Z3.ask settings.query_range decls
               (Format.fmt2 "(%s, %s)" settings.query_name (show settings.query_index))
               false
      in
      let results = zip_results emitted results in
      active |> List.map (fun gst ->
        match results |> List.tryFind (fun (g, _) -> g.goal_id = gst.gs_goal.goal_id) with
        | None -> gst
        | Some (g, r) ->
          query_info settings g r;
          match query_errors settings r with
          | None -> { gst with gs_nsuccess = gst.gs_nsuccess + 1 }
          | Some e -> { gst with gs_nfailure = gst.gs_nfailure + 1;
                                 gs_errors = e :: gst.gs_errors })

let quake_bounds () : ML (int & int) =
    let lo = Options.quake_lo () in
    let hi = Options.quake_hi () in
    let hi = if hi < 1 then 1 else hi in
    let lo = if lo < 1 then 1 else if lo > hi then hi else lo in
    lo, hi

(* Ask the solver about all the goals in [goals] at one fuel setting, repeating
each of them as needed for --quake / --retry.  Every repetition is a separate
check-sat, but all the still-undecided goals of a given round go into a single
round trip. *)
let ask_config (settings:query_settings) (goals : list goal_state) : ML (list goal_state) =
    let lo, hi = quake_bounds () in
    let decided gst =
      not (Options.quake_keep ())
      && (gst.gs_nsuccess >= lo || gst.gs_nfailure > hi - lo)
    in
    let rec rounds (n:int) (active : list goal_state) (acc : list goal_state)
      : ML (list goal_state)
      = if n <= 0 then active @ acc
        else
          let active = run_round settings active in
          let done_, active = List.partition decided active in
          rounds (n-1) active (done_ @ acc)
    in
    rounds hi goals []

(* Try to discharge all the goals, raising the fuel of the ones that fail until
the configurations are exhausted.  Returns the goals that never succeeded. *)
let rec ask_configs (configs : list query_settings) (goals : list goal_state)
  : ML (list goal_state)
  = let lo, _ = quake_bounds () in
    match configs with
    | [] -> goals
    | cfg :: configs ->
      let goals = ask_config cfg goals in
      let failed = goals |> List.filter (fun gst -> gst.gs_nsuccess < lo) in
      match failed, configs with
      | [], _ -> []
      | _, [] -> failed
      | _ ->
        (* Retry the failures at the next fuel setting, keeping the errors we
           have accumulated so far. *)
        ask_configs configs
          (failed |> List.map (fun gst -> { gst with gs_nsuccess = 0; gs_nfailure = 0 }))

let mk_answer (failed : list goal_state) : ML answer =
    let lo, hi = quake_bounds () in
    { ans_ok with
      ok                  = Nil? failed;
      lo                  = lo;
      hi                  = hi;
      quaking             = hi > 1 && not (Options.retry ());
      quaking_or_retrying = hi > 1;
      failed              = failed }

let ask_solver_quake (configs : list query_settings) : ML answer =
    let default_settings = List.hd configs in
    let goals = goals_of default_settings.query_goals |> List.map initial_goal_state in
    let ans = mk_answer (ask_configs configs goals) in
    if ans.quaking then begin
      let name = full_query_id default_settings in
      let ngoals = List.length goals in
      let nfail = List.length ans.failed in
      let ratio = Format.fmt2 "%s/%s" (show (ngoals - nfail)) (show ngoals) in
      let ratio =
        if nfail = 0 then Format.colorize_green ratio else Format.colorize_red ratio
      in
      Format.print2 "Quake: query %s \tproved %s goals\n" name ratio
    end;
    ans

(* A very simple command language for recovering, though keep in
mind its execution is stateful in the sense that anything after a
(RestartSolver h) will run in the new solver instance. *)
type recovery_hammer =
  | IncreaseRLimit of (*factor : *)int
  | RestartAnd of recovery_hammer

let rec pp_hammer (h : recovery_hammer) : ML Pprint.document =
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  match h with
  | IncreaseRLimit factor ->
    text "increasing its rlimit by" ^/^ pp factor ^^ doc_of_string "x"
  | RestartAnd h ->
    text "restarting the solver and" ^/^ pp_hammer h

(* If --proof_recovery is on, then we retry the query multiple
times, increasing rlimits, until we get a success. If not, we just
call ask_solver_quake. *)
let ask_solver_recover
    (configs : list query_settings)
 : ML answer
 =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let open FStarC.Class.PP in
  if Options.proof_recovery () then (
    let r = ask_solver_quake configs in
    if r.ok then r else (
      let cfg = List.last configs in

      Errors.diag cfg.query_range [
        text "This query failed to be solved. Will now retry with higher rlimits due to --proof_recovery.";
      ];

      let try_factor (n:int) : ML answer =
        Errors.diag cfg.query_range [text "Retrying query with rlimit factor" ^/^ pp n];
        let cfg = { cfg with query_rlimit = n * cfg.query_rlimit } in
        ask_solver_quake [cfg]
      in

      let rec try_hammer (h : recovery_hammer) : ML answer =
        match h with
        | IncreaseRLimit factor -> try_factor factor
        | RestartAnd h ->
          Errors.diag cfg.query_range [text "Trying a solver restart"];
          cfg.query_env.tcenv.solver.refresh (Some cfg.query_env.tcenv.proof_ns);
          try_hammer h
      in

      let rec aux (hammers : list recovery_hammer) : ML answer =
        match hammers with
        | [] -> { r with tried_recovery = true }
        | h::hs ->
          let r = try_hammer h in
          if r.ok then (
            Errors.log_issue cfg.query_range Errors.Warning_ProofRecovery [
               text "This query succeeded after " ^/^ pp_hammer h;
               text "Increase the rlimit in the file or simplify the proof. \
                     This is only succeeding due to --proof_recovery being given."
               ];
            r
          ) else
            aux hs
      in
      aux [
        IncreaseRLimit 2;
        IncreaseRLimit 4;
        IncreaseRLimit 8;
        RestartAnd (IncreaseRLimit 8);
      ]
    )
  ) else
    ask_solver_quake configs

let failing_query_ctr : ref int = mk_ref 0

let maybe_save_failing_query (env:env_t) (qs:query_settings) : ML unit =
  (* Save failing query to a clean file if --log_failing_queries. *)
  if Options.log_failing_queries () then (
    let mod = show (Env.current_module env.tcenv) in
    let n = (failing_query_ctr := !failing_query_ctr + 1; !failing_query_ctr) in
    let file_name = Format.fmt2 "failedQueries-%s-%s.smt2" mod (show n) in
    let decls, _ = emit_goals (fun _ -> true) qs qs.query_goals in
    let query_str = Z3.ask_text
                            qs.query_range
                            decls
                            (Format.fmt2 "(%s, %s)" qs.query_name (show qs.query_index))
    in
    write_file file_name query_str;
    ()
  );
  (* Also print it out if --debug SMTFail. *)
  if !dbg_SMTFail then (
    let open FStarC.Pprint in
    let open FStarC.Class.PP in
    let open FStarC.Errors.Msg in
    Errors.diag qs.query_range [
      text "A query failed.";
      prefix 2 1 (text "Env =")
        (all_binders qs.query_env.tcenv |> Pprint.flow_map (break_ 1) fun (b:Syntax.binder) ->
          group <| parens <| nest 2 <|
            pp b.binder_bv.ppname ^/^ colon ^/^ pp b.binder_bv.sort);
      prefix 2 1 (text "VC =") (pp qs.query_term);
    ]
  );
  ()

let ask_solver
    (env : FStarC.SMTEncoding.Env.env_t)
    (configs: list query_settings)
 : ML (list query_settings & answer)
 =  (* The default config is at the head. We distinguish this one since
    it includes some metadata that we need, such as the query name, etc.
    (Though all other configs also contain it.) *)
    let default_settings = List.hd configs in
    let skip : bool =
        env.tcenv.admit ||
        (match Options.admit_except () with
         | Some id ->
           if BU.starts_with id "("
           then full_query_id default_settings <> id
           else default_settings.query_name <> id
         | None -> false)
    in
    let ans =
      if skip
      then ans_ok
      else (
        let ans = ask_solver_recover configs in
        let cfg = List.last configs in
        if not ans.ok then
          maybe_save_failing_query env cfg;
        ans

      )
    in
    configs, ans

(* Reports query errors to the user. The errors are logged, not raised. *)
let report (env:Env.env) (default_settings : query_settings) (a : answer) : ML unit =
    let name = full_query_id default_settings in
    a.failed |> List.iter (fun gst ->
      FStarC.Errors.add_errors (errors_to_report a.tried_recovery default_settings gst);
      (* Adding another explanatory error for the threshold if --quake is on
         (but not for --retry) *)
      if a.quaking then
        FStarC.TypeChecker.Err.log_issue
          env gst.gs_goal.goal_range
          (Errors.Error_QuakeFailed, [
            Errors.text <|
            Format.fmt5
              "This goal of query %s failed the quake test, %s out of %s attempts succeeded, \
               but the threshold was %s out of %s"
              name
              (show gst.gs_nsuccess)
              (show (gst.gs_nsuccess + gst.gs_nfailure))
              (show a.lo)
              (show a.hi)]))

(* This type represents the configuration under which the solver was
_started_. If anything changes, the solver should be restarted for these
settings to take effect. See `maybe_refresh` below. *)
type solver_cfg = {
  seed             : int;
  cliopt           : list string;
  smtopt           : list string;
  facts            : list (list string & bool);
  z3version        : string;
  context_pruning  : bool;
}

let _last_cfg : ref (option solver_cfg) = mk_ref None

let get_cfg env : ML solver_cfg =
    { seed             = Options.z3_seed ()
    ; cliopt           = Options.z3_cliopt ()
    ; smtopt           = Options.z3_smtopt ()
    ; facts            = env.proof_ns
    ; z3version        = Options.z3_version ()
    ; context_pruning  = Options.Ext.enabled "context_pruning"
    }

let save_cfg env =
    _last_cfg := Some (get_cfg env)

(* If the the solver's configuration has changed, then restart it so
it can take on the new values. *)
let maybe_refresh_solver env =
    match !_last_cfg with
    | None -> save_cfg env
    | Some cfg ->
        if cfg <> get_cfg env then (
          save_cfg env;
          Z3.refresh (Some env.proof_ns)
        )

(* The query_settings list is non-empty unless the query was trivial. *)
let encode_and_ask use_env_msg tcenv q : ML (list query_settings & answer) =
  let do () : ML (list query_settings & answer) =
    maybe_refresh_solver tcenv;
    let msg =  (Format.fmt1 "Starting query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
    Encode.push_encoding_state msg;
    let prefix, goals, qry = Encode.encode_query use_env_msg tcenv q in
    Z3.start_query msg prefix qry;
    let finish_query () = 
      let msg = (Format.fmt1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
      Encode.pop_encoding_state msg;
      Z3.finish_query msg
    in
    finally finish_query (fun () ->
      let tcenv = incr_query_index tcenv in
      match goals with
      (* trivial cases *)
      | GTrivial -> ([], ans_ok)
      | _ when tcenv.admit -> ([], ans_ok)

      | _ ->
        if !dbg_SMTQuery
        then
          FStarC.Errors.diag
              (Env.get_range tcenv)
              (Format.fmt3 "Encoded query %s\nto %s\nwith %s goals"
                        (show q)
                        (Term.declToSmt "" qry)
                        (show (List.length (goals_of goals))));
        let env = FStarC.SMTEncoding.Encode.get_current_env tcenv in
        let configs = make_solver_configs env goals qry q in
        ask_solver env configs
    )
  in
  if Options.admit_smt_queries () then (
    ([], ans_ok)
  )
  else if Solver.Cache.try_find_query_cache tcenv q then (
    ([], { ans_ok with cache_hit = true })
  ) 
  else (
    let (cfgs, ans) = FStarC.Stats.record "Solver.encode_and_ask" do in
    if ans.ok then
      Solver.Cache.query_cache_add tcenv q;
    (cfgs, ans)
  )

(* Asks the solver and reports errors. Does quake if needed. *)
let do_solve use_env_msg tcenv q : ML unit =
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  let open FStarC.Class.PP in
  if !dbg_SMTQuery then
    Errors.diag tcenv [
      text "Before calling solver.";
      prefix 2 1 (text "Env =")
        (all_binders tcenv |> Pprint.flow_map (break_ 1) fun (b:Syntax.binder) ->
          group <| parens <| nest 2 <|
            pp b.binder_bv.ppname ^/^ colon ^/^ pp b.binder_bv.sort);
      prefix 2 1 (text "VC =") (pp q);
    ];
  let ans_opt = encode_and_ask use_env_msg tcenv q in
  match ans_opt with
  | default_settings::_, ans when not ans.ok ->
    report tcenv default_settings ans

  | _, ans when ans.ok ->
    () (* trivial or succeeded *)

  | [], ans when not ans.ok ->
    failwith "impossible: bad answer from encode_and_ask"

let disable_quake_for (f : unit -> ML 'a) : ML 'a =
  Options.with_saved_options (fun () ->
    Options.set_option "quake_hi" (Options.Int 1);
    f ())

(* Attempt to discharge a VC through the SMT solver. Will
automatically retry increasing fuel as needed, and perform quake testing
(repeating the query to make sure it is robust). This function will
_log_ (not raise) an error if the VC could not be proven. *)
let solve use_env_msg tcenv q : ML unit =
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  if Options.no_smt () then
    FStarC.TypeChecker.Err.log_issue
      tcenv tcenv.range
        (Errors.Error_NoSMTButNeeded,
         [text "A query could not be solved internally, and --no_smt was given.";
          text "Query = " ^/^ pp q])
  else if tcenv.admit then ()
  else (
    Encode.flush_deferred_encodings ();
    Profiling.profile
      (fun () -> do_solve use_env_msg tcenv q)
      (Some (Ident.string_of_lid (Env.current_module tcenv)))
      "FStarC.SMTEncoding.solve_top_level"
  )

(* This asks the SMT to solve a query, and returns the answer without
logging any kind of error. Mostly useful for the smt_sync tactic
primitive.

It will NOT do quake testing.
It WILL raise fuel incrementally to attempt to solve the query

*)
let solve_sync use_env_msg tcenv (q:Syntax.term) : ML answer =
    if Options.no_smt () then ans_fail
    else
    let _ = Encode.flush_deferred_encodings () in
    let go () =
      if !dbg_SMTQuery then (
        let open FStarC.Errors.Msg in
        let open FStarC.Pprint in
        Errors.diag q.pos [
          prefix 2 1 (text "Running synchronous SMT query. Q =") (pp q);
        ]
      );
      let _cfgs, ans = disable_quake_for (fun () -> encode_and_ask use_env_msg tcenv q) in
      ans
    in
    Profiling.profile
      go
      (Some (Ident.string_of_lid (Env.current_module tcenv)))
      "FStarC.SMTEncoding.solve_sync_top_level"

(* The version actually exported, and used by tactics. *)
let solve_sync_bool use_env_msg tcenv q : ML bool =
    let ans = solve_sync use_env_msg tcenv q in
    ans.ok

(**********************************************************************************************)
(* Top-level interface *)
(**********************************************************************************************)

let snapshot msg =
  let v0, v1 = Encode.snapshot_encoding msg in
  let v2 = Z3.snapshot msg in
  (v0, v1, v2), ()
let rollback msg tok =
  let tok01, tok2 =
    match tok with
    | None -> None, None
    | Some (v0, v1, v2) -> Some (v0, v1), Some v2
  in
  Encode.rollback_encoding msg tok01;
  Z3.rollback msg tok2

let solver = {
    init=(fun e -> save_cfg e; Encode.init e);
    snapshot;
    rollback;
    encode_sig=Encode.encode_sig;

    (* These two to be overriden by FStarC.Universal.init_env *)
    preprocess=(fun e g -> (false, [e,g, FStarC.Options.peek ()]));
    handle_smt_goal=(fun e g -> [e,g]);

    solve=solve;
    solve_sync=solve_sync_bool;
    finish=Z3.stop;
    refresh=Z3.refresh;
}

let dummy = {
    init=(fun _ -> ());
    snapshot=(fun _ -> (0, 0, 0), ());
    rollback=(fun _ _ -> ());
    encode_sig=(fun _ _ -> ());
    preprocess=(fun e g -> (false, [e,g, FStarC.Options.peek ()]));
    handle_smt_goal=(fun e g -> [e,g]);
    solve=(fun _ _ _ -> ());
    solve_sync=(fun _ _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun _ -> ());
}

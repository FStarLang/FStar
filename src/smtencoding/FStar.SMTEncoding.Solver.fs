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
#light "off"

module FStar.SMTEncoding.Solver
open FStar.ST
open FStar.All
open FStar
open FStar.SMTEncoding.Z3
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.SMTEncoding
open FStar.SMTEncoding.ErrorReporting
open FStar.SMTEncoding.Encode
open FStar.SMTEncoding.Util
module BU = FStar.Util
module U = FStar.Syntax.Util
module TcUtil = FStar.TypeChecker.Util
module Print = FStar.Syntax.Print
module Env = FStar.TypeChecker.Env

(****************************************************************************)
(* Hint databases for record and replay (private)                           *)
(****************************************************************************)

// The type definition is now in [FStar.Util], since it needs to be visible to
// both the F# and OCaml implementations.

type z3_replay_result = either<Z3.unsat_core, error_labels>
let z3_result_as_replay_result = function
    | Inl l -> Inl l
    | Inr (r, _) -> Inr r
let recorded_hints : ref<(option<hints>)> = BU.mk_ref None
let replaying_hints: ref<(option<hints>)> = BU.mk_ref None
let format_hints_file_name src_filename = BU.format1 "%s.hints" src_filename

(****************************************************************************)
(* Hint databases (public)                                                  *)
(****************************************************************************)
let initialize_hints_db src_filename format_filename : unit =
    if Options.record_hints() then recorded_hints := Some [];
    if Options.use_hints()
    then let norm_src_filename = BU.normalize_file_path src_filename in
         let val_filename = match Options.hint_file() with
                            | Some fn -> fn
                            | None -> (format_hints_file_name norm_src_filename) in
         begin match BU.read_hints val_filename with
            | Some hints ->
                let expected_digest = BU.digest_of_file norm_src_filename in
                if Options.hint_info()
                then begin
                    BU.print3 "(%s) digest is %s%s.\n" norm_src_filename
                        (if hints.module_digest = expected_digest
                         then "valid; using hints"
                         else "invalid; using potentially stale hints")
                        (match Options.hint_file() with
                         | Some fn -> " from '" ^ val_filename ^ "'"
                         | _ -> "")
                end;
                replaying_hints := Some hints.hints
            | None ->
                if Options.hint_info()
                then BU.print1 "(%s) Unable to read hint file.\n" norm_src_filename
         end

let finalize_hints_db src_filename :unit =
    begin if Options.record_hints () then
          let hints = Option.get !recorded_hints in
          let hints_db = {
                module_digest = BU.digest_of_file src_filename;
                hints = hints
              }  in
          let norm_src_filename = BU.normalize_file_path src_filename in
          let val_filename = match Options.hint_file() with
                            | Some fn -> fn
                            | None -> (format_hints_file_name norm_src_filename) in
          BU.write_hints val_filename hints_db
    end;
    recorded_hints := None;
    replaying_hints := None

let with_hints_db fname f =
    initialize_hints_db fname false;
    let result = f () in
    // for the moment, there should be no need to trap exceptions to finalize the hints db
    // no cleanup needs to occur if an error occurs.
    finalize_hints_db fname;
    result

let filter_using_facts_from (e:env) (theory:decls_t) =
    let matches_fact_ids (include_assumption_names:BU.smap<bool>) (a:Term.assumption) =
      match a.assumption_fact_ids with
      | [] -> true //retaining `a` because it is not tagged with a fact id
      | _ ->
        a.assumption_fact_ids |> BU.for_some (function | Name lid -> Env.should_enc_lid e lid | _ -> false)
        || Option.isSome (BU.smap_try_find include_assumption_names a.assumption_name)
    in
    //theory can have ~10k elements; fold_right on it is dangerous, since it's not tail recursive
    //AR: reversing the list is also crucial for correctness because of RetainAssumption 
    //    specifically (RetainAssumption a) comes after (a) in the theory list
    //    as a result, it is crucial that we consider the (RetainAssumption a) before we encounter (a)
    let theory_rev = List.rev theory in  //List.rev is already the tail recursive version of rev
    let pruned_theory =
        let include_assumption_names =
            //this map typically grows to 10k+ elements
            //using a map for it is important, otherwise the list scanning
            //becomes near quadratic in the # of facts
            BU.smap_create 10000
        in
        let keep_decl :decl -> bool = function  //effectful function, adds decls to the include_assumption_names map
          | Assume a -> matches_fact_ids include_assumption_names a
          | RetainAssumptions names ->
            List.iter (fun x -> BU.smap_add include_assumption_names x true) names;
            true
          | Module _ -> failwith "Solver.fs::keep_decl should never have been called with a Module decl"
          | _ -> true
        in
        List.fold_left (fun out d ->
          match d with
          | Module (name, decls) -> decls |> List.filter keep_decl |> (fun decls -> Module (name, decls)::out)
          | _ -> if keep_decl d then d::out else out) [] theory_rev
    in
    pruned_theory

let rec filter_assertions_with_stats (e:env) (core:Z3.unsat_core) (theory:decls_t) :(decls_t * bool * int * int) =  //(filtered theory, if core used, retained, pruned)
    match core with
    | None ->
      filter_using_facts_from e theory, false, 0, 0  //no stats if no core
    | Some core ->
        //so that we can use the tail-recursive fold_left
        let theory_rev = List.rev theory in
        let theory', n_retained, n_pruned =
            List.fold_left (fun (theory, n_retained, n_pruned) d -> match d with
            | Assume a ->
                if List.contains a.assumption_name core
                then d::theory, n_retained+1, n_pruned
                else if BU.starts_with a.assumption_name "@"
                then d::theory, n_retained, n_pruned
                else theory, n_retained, n_pruned+1
            | Module (name, decls) ->
              decls |> filter_assertions_with_stats e (Some core)
                    |> (fun (decls, _, r, p) -> Module (name, decls)::theory, n_retained + r, n_pruned + p)
            | _ -> d::theory, n_retained, n_pruned)
            ([Caption ("UNSAT CORE: " ^ (core |> String.concat ", "))], 0, 0) theory_rev in  //start with the unsat core caption at the end
        theory', true, n_retained, n_pruned

let filter_assertions (e:env) (core:Z3.unsat_core) (theory:decls_t) =
  let (theory, b, _, _) = filter_assertions_with_stats e core theory in theory, b

let filter_facts_without_core (e:env) x = filter_using_facts_from e x, false

(***********************************************************************************)
(* Invoking the SMT solver and extracting an error report from the model, if any   *)
(***********************************************************************************)
type errors = {
    error_reason:string;
    error_fuel: int;
    error_ifuel: int;
    error_hint: option<(list<string>)>;
    error_messages: list<(Errors.raw_error * string * Range.range)>
}

let error_to_short_string err =
    BU.format4 "%s (fuel=%s; ifuel=%s; %s)"
            err.error_reason
            (string_of_int err.error_fuel)
            (string_of_int err.error_ifuel)
            (if Option.isSome err.error_hint then "with hint" else "")

type query_settings = {
    query_env:env;
    query_decl:decl;
    query_name:string;
    query_index:int;
    query_range:Range.range;
    query_fuel:int;
    query_ifuel:int;
    query_rlimit:int;
    query_hint:Z3.unsat_core;
    query_errors:list<errors>;
    query_all_labels:error_labels;
    query_suffix:list<decl>;
    query_hash:option<string>
}


//surround the query with fuel options and various diagnostics
let with_fuel_and_diagnostics settings label_assumptions =
    let n = settings.query_fuel in
    let i = settings.query_ifuel in
    let rlimit = settings.query_rlimit in
    [  //fuel and ifuel settings
        Term.Caption (BU.format2 "<fuel='%s' ifuel='%s'>"
                        (string_of_int n)
                        (string_of_int i));
        Util.mkAssume(mkEq(mkApp("MaxFuel", []), n_fuel n), None, "@MaxFuel_assumption");
        Util.mkAssume(mkEq(mkApp("MaxIFuel", []), n_fuel i), None, "@MaxIFuel_assumption");
        settings.query_decl        //the query itself
    ]
    @label_assumptions         //the sub-goals that are currently disabled
    @[  Term.SetOption ("rlimit", string_of_int rlimit); //the rlimit setting
        Term.CheckSat; //go Z3!
        Term.GetReasonUnknown //explain why it failed
    ]
    @(if Options.record_hints()        then [Term.GetUnsatCore]  else []) //unsat core is the recorded hint
    @(if Options.print_z3_statistics() then [Term.GetStatistics] else []) //stats
    @settings.query_suffix //recover error labels and a final "Done!" message


let used_hint s = Option.isSome s.query_hint

let get_hint_for qname qindex =
    match !replaying_hints with
    | Some hints ->
      BU.find_map hints (function
        | Some hint when hint.hint_name=qname && hint.hint_index=qindex -> Some hint
        | _ -> None)
    | _ -> None

let query_errors settings z3result =
    match z3result.z3result_status with
    | UNSAT _ -> None
    | _ ->
     let msg, error_labels = Z3.status_string_and_errors z3result.z3result_status in
     let err =  {
            error_reason = msg;
            error_fuel = settings.query_fuel;
            error_ifuel = settings.query_ifuel;
            error_hint = settings.query_hint;
            error_messages = List.map (fun (_, x, y) -> Errors.Error_Z3SolverError,x,y) error_labels
        }
     in
     Some err

let detail_hint_replay settings z3result =
    if used_hint settings
    && Options.detail_hint_replay ()
    then match z3result.z3result_status with
         | UNSAT _ -> ()
         | _failed ->
           let ask_z3 label_assumptions =
               let res = BU.mk_ref None in
               Z3.ask settings.query_range
                      (filter_assertions settings.query_env settings.query_hint)
                      settings.query_hash
                      settings.query_all_labels
                      (with_fuel_and_diagnostics settings label_assumptions)
                      None
                      (fun r -> res := Some r);
               Option.get (!res)
           in
           detail_errors true settings.query_env settings.query_all_labels ask_z3

let find_localized_errors errs =
    errs |> List.tryFind (fun err -> match err.error_messages with [] -> false | _ -> true)

let has_localized_errors errs = Option.isSome (find_localized_errors errs)

let report_errors settings : unit =
    let _basic_error_report =
        match find_localized_errors settings.query_errors with
        | Some err ->
          settings.query_errors |> List.iter (fun e ->
          FStar.Errors.diag settings.query_range ("SMT solver says: " ^ error_to_short_string e));
          FStar.TypeChecker.Err.add_errors settings.query_env err.error_messages
        | None ->
          let err_detail =
            settings.query_errors |>
            List.map (fun e -> "SMT solver says: " ^ error_to_short_string e) |>
            String.concat "; " in
          FStar.TypeChecker.Err.add_errors
                   settings.query_env
                   [(Errors.Error_UnknownFatal_AssertionFailure, BU.format1 "Unknown assertion failed (%s)" err_detail,
                     settings.query_range)]
    in
    if Options.detail_errors()
    && Options.n_cores() = 1
    then let initial_fuel = {
                settings with query_fuel=Options.initial_fuel();
                              query_ifuel=Options.initial_ifuel();
                              query_hint=None
            }
         in
         let ask_z3 label_assumptions =
            let res = BU.mk_ref None in
            Z3.ask  settings.query_range
                    (filter_facts_without_core settings.query_env)
                    settings.query_hash
                    settings.query_all_labels
                    (with_fuel_and_diagnostics initial_fuel label_assumptions)
                    None
                    (fun r -> res := Some r);
            Option.get (!res)
            in
         detail_errors false settings.query_env settings.query_all_labels ask_z3

let query_info settings z3result =
    if Options.hint_info()
    || Options.print_z3_statistics()
    then begin
        let status_string, errs = Z3.status_string_and_errors z3result.z3result_status in
        let tag = match z3result.z3result_status with
         | UNSAT _ -> "succeeded"
         | _ -> "failed {reason-unknown=" ^ status_string ^ "}"in
        let range = "(" ^ (Range.string_of_range settings.query_range) ^ at_log_file() ^ ")" in
        let used_hint_tag = if used_hint settings then " (with hint)" else "" in
        let stats =
            if Options.print_z3_statistics() then
                let f k v a = a ^ k ^ "=" ^ v ^ " " in
                let str = smap_fold z3result.z3result_statistics f "statistics={" in
                    (substring str 0 ((String.length str) - 1)) ^ "}"
            else "" in
        BU.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
             [  range;
                settings.query_name;
                BU.string_of_int settings.query_index;
                tag;
                used_hint_tag;
                BU.string_of_int z3result.z3result_time;
                BU.string_of_int settings.query_fuel;
                BU.string_of_int settings.query_ifuel;
                BU.string_of_int settings.query_rlimit;
                stats ];
        errs |> List.iter (fun (_, msg, range) ->
            let tag = if used_hint settings then "(Hint-replay failed): " else "" in
            FStar.Errors.log_issue range (FStar.Errors.Warning_HitReplayFailed, (tag ^ msg)))
    end

let record_hint settings z3result =
    if not (Options.record_hints()) then () else
    begin
      let mk_hint core = {
                  hint_name=settings.query_name;
                  hint_index=settings.query_index;
                  fuel=settings.query_fuel;
                  ifuel=settings.query_ifuel;
                  unsat_core=core;
                  query_elapsed_time=0; //recording the elapsed_time prevents us from reaching a fixed point
                  hash=(match z3result.z3result_status with
                        | UNSAT core -> z3result.z3result_query_hash
                        | _ -> None)
          }
      in
      let store_hint hint =
          match !recorded_hints with
          | Some l -> recorded_hints := Some (l@[Some hint])
          | _ -> assert false; ()
      in
      match z3result.z3result_status with
      | UNSAT None ->
        // we succeeded by just matching a query hash
        store_hint (Option.get (get_hint_for settings.query_name settings.query_index))
      | UNSAT unsat_core ->
        if used_hint settings //if we already successfully use a hint
        then //just re-use the successful hint, but record the hash of the pruned theory
             store_hint (mk_hint settings.query_hint)
        else store_hint (mk_hint unsat_core)          //else store the new unsat core
      | _ ->  () //the query failed, so nothing to do
    end

let process_result settings result : option<errors> =
    if used_hint settings && not (Options.z3_refresh()) then Z3.refresh();
    let errs = query_errors settings result in
    query_info settings result;
    record_hint settings result;
    detail_hint_replay settings result;
    errs

let fold_queries (qs:list<query_settings>)
                 (ask:query_settings -> (z3result -> unit) -> unit)
                 (f:query_settings -> z3result -> option<errors>)
                 (report:list<errors> -> unit) : unit =
    let rec aux acc qs =
        match qs with
        | [] -> report acc
        | q::qs ->
          ask q (fun res ->
                  match f q res with
                  | None -> () //done
                  | Some errs ->
                    aux (errs::acc) qs)
    in
    aux [] qs

let ask_and_report_errors env all_labels prefix query suffix =
    Z3.giveZ3 prefix; //feed the context of the query to the solver

    let default_settings, next_hint =
        let qname, index =
            match env.qtbl_name_and_index with
            | _, None -> failwith "No query name set!"
            | _, Some (q, n) -> Ident.text_of_lid q, n
        in
        let rlimit =
            Prims.op_Multiply
                (Options.z3_rlimit_factor ())
                (Prims.op_Multiply (Options.z3_rlimit ()) 544656)
        in
        let next_hint = get_hint_for qname index in
        let default_settings = {
            query_env=env;
            query_decl=query;
            query_name=qname;
            query_index=index;
            query_range=Env.get_range env;
            query_fuel=Options.initial_fuel();
            query_ifuel=Options.initial_ifuel();
            query_rlimit=rlimit;
            query_hint=None;
            query_errors=[];
            query_all_labels=all_labels;
            query_suffix=suffix;
            query_hash=(match next_hint with
                        | None -> None
                        | Some {hash=h} -> h)
        } in
        default_settings, next_hint
    in

    let use_hints_setting =
        match next_hint with
        | Some ({unsat_core=Some core; fuel=i; ifuel=j; hash=h}) ->
          [{default_settings with query_hint=Some core;
                                  query_fuel=i;
                                  query_ifuel=j}]
        | _ ->
          []
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

    let min_fuel =
        if Options.min_fuel() < Options.initial_fuel()
        then [{default_settings with query_fuel=Options.min_fuel();
                                     query_ifuel=1}]
        else []
    in

    let all_configs =
        use_hints_setting
        @ [default_settings]
        @ initial_fuel_max_ifuel
        @ half_max_fuel_max_ifuel
        @ max_fuel_max_ifuel
    in

    let check_one_config config (k:z3result -> unit) : unit =
          if used_hint config || Options.z3_refresh() then Z3.refresh();
          Z3.ask config.query_range
                  (filter_assertions config.query_env config.query_hint)
                  config.query_hash
                  config.query_all_labels
                  (with_fuel_and_diagnostics config [])
                  (Some (Z3.mk_fresh_scope()))
                  k
    in

    let check_all_configs configs =
        let report errs = report_errors ({default_settings with query_errors=errs}) in
        fold_queries configs check_one_config process_result report
    in

    match Options.admit_smt_queries(), Options.admit_except() with
    | true, _ -> ()
    | false, None -> check_all_configs all_configs
    | false, Some id ->
      let skip =
        if BU.starts_with id "("
        then let full_query_id = "(" ^ default_settings.query_name ^ ", " ^ (BU.string_of_int default_settings.query_index) ^ ")" in
             full_query_id <> id
        else default_settings.query_name <> id
      in
      if not skip then check_all_configs all_configs

let solve use_env_msg tcenv q : unit =
    Encode.push (BU.format1 "Starting query at %s" (Range.string_of_range <| Env.get_range tcenv));
    if Options.no_smt ()
    then
        FStar.TypeChecker.Err.add_errors
                 tcenv
                 [(Errors.Error_NoSMTButNeeded,
                    BU.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" (Print.term_to_string q),
                        tcenv.range)]
    else
    let tcenv = incr_query_index tcenv in
    let prefix, labels, qry, suffix = Encode.encode_query use_env_msg tcenv q in
    let pop () = Encode.pop (BU.format1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
    match qry with
    | Assume({assumption_term={tm=App(FalseOp, _)}}) -> pop()
    | _ when tcenv.admit -> pop()
    | Assume _ ->
        ask_and_report_errors tcenv labels prefix qry suffix;
        pop ()

    | _ -> failwith "Impossible"

(**********************************************************************************************)
(* Top-level interface *)
(**********************************************************************************************)
open FStar.TypeChecker.Env
let solver = {
    init=Encode.init;
    push=Encode.push;
    pop=Encode.pop;
    snapshot=Encode.snapshot;
    rollback=Encode.rollback;
    encode_sig=Encode.encode_sig;
    encode_modul=Encode.encode_modul;
    preprocess=(fun e g -> [e,g, FStar.Options.peek ()]);
    solve=solve;
    finish=Z3.finish;
    refresh=Z3.refresh;
}
let dummy = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    snapshot=(fun _ -> (0, 0, 0), ());
    rollback=(fun _ _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    preprocess=(fun e g -> [e,g, FStar.Options.peek ()]);
    solve=(fun _ _ _ -> ());
    finish=(fun () -> ());
    refresh=(fun () -> ());
}

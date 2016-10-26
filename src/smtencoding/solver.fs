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
open FStar
open FStar.SMTEncoding.Z3
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.SMTEncoding.ErrorReporting
open FStar.SMTEncoding.Encode
open FStar.SMTEncoding.Util

(****************************************************************************)
(* Hint databases for record and replay (private)                           *)
(****************************************************************************)

// The type definition is now in [FStar.Util], since it needs to be visible to
// both the F# and OCaml implementations.

type z3_err = error_labels * bool
type z3_result = either<Z3.unsat_core, z3_err>
type z3_replay_result = either<Z3.unsat_core, error_labels>
let z3_result_as_replay_result = function
    | Inl l -> Inl l
    | Inr (r, _) -> Inr r
type hint_stat = {
    hint:option<hint>;
    replay_result:z3_replay_result;
    elapsed_time:int;
    source_location:Range.range
}
type hint_stats_t = list<hint_stat>
let recorded_hints : ref<(option<hints>)> = Util.mk_ref None
let replaying_hints: ref<(option<hints>)> = Util.mk_ref None
let hint_stats     : ref<hint_stats_t>    = Util.mk_ref []

let format_hints_file_name src_filename =
    Util.format1 "%s.hints" src_filename

(****************************************************************************)
(* Hint databases (public)                                                  *)
(****************************************************************************)
let initialize_hints_db src_filename force_record : unit =
    hint_stats := [];
    if Options.record_hints() then recorded_hints := Some [];
    if Options.use_hints()
    then let norm_src_filename = Util.normalize_file_path src_filename in
         let val_filename = format_hints_file_name norm_src_filename in
         begin match Util.read_hints val_filename with
            | Some hints ->
                let expected_digest = Util.digest_of_file norm_src_filename in
                if Options.hint_info()
                then begin 
                     if hints.module_digest = expected_digest 
                     then Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_filename
                     else Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_filename
                end;
                replaying_hints := Some hints.hints
            | None ->
                if Options.hint_info() 
                then Util.print1 "(%s) Unable to read hints db.\n" norm_src_filename
         end
    
let finalize_hints_db src_filename : unit =
    begin if Options.record_hints () then
          let hints = Option.get !recorded_hints in
          let hints_db = {
                module_digest = Util.digest_of_file src_filename;
                hints = hints
              }  in
          let hints_file_name = format_hints_file_name src_filename in
          Util.write_hints hints_file_name hints_db
    end;
    begin if Options.hint_info() then 
        let stats = !hint_stats |> List.rev in
        stats |> List.iter (fun s -> match s.replay_result with
            | Inl _unsat_core -> 
              Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                (Range.string_of_range s.source_location)
                (Util.string_of_int s.elapsed_time)
            | Inr _error ->
              Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n"
                (Range.string_of_range s.source_location)
                (Util.string_of_int s.elapsed_time))
    end;
    recorded_hints := None;
    replaying_hints := None;
    hint_stats := []

let with_hints_db fname f =
    initialize_hints_db fname false;
    let result = f () in
    // for the moment, there should be no need to trap exceptions to finalize the hints db 
    // no cleanup needs to occur if an error occurs.
    finalize_hints_db fname;
    result

let next_hint qname qindex = 
    match !replaying_hints with 
    | Some hints ->
      Util.find_map hints (function 
        | Some hint when hint.hint_name=qname && hint.hint_index=qindex -> Some hint
        | _ -> None)
    | _ -> None

let record_hint hint = 
    let hint = match hint with 
        | None -> None //recording the elapsed time prevents us from reaching a fixpoint in the hints db
        | Some h -> Some ({h with query_elapsed_time=0}) in
    match !recorded_hints with 
    | Some l -> recorded_hints := Some (l@[hint]) 
    | _ -> ()

let record_hint_stat (h:option<hint>) (res:z3_result) (time:int) (r:Range.range) = 
    let s = {
        hint=h;
        replay_result=z3_result_as_replay_result res;
        elapsed_time=time;
        source_location=r;
    } in
    hint_stats := s::!hint_stats

(***********************************************************************************)
(* Invoking the SMT solver and extracting an error report from the model, if any   *)
(***********************************************************************************)
let ask_and_report_errors env all_labels prefix query suffix = 
    Z3.giveZ3 prefix;
    let query_name, query_index = match env.qname_and_index with 
        | None -> failwith "No query name set!"
        | Some (q, n) -> Ident.text_of_lid q, n in
    let minimum_workable_fuel = Util.mk_ref None in
    let set_minimum_workable_fuel f = function 
        | [], _ -> ()
        | errs -> match !minimum_workable_fuel with 
                    | Some _ -> ()
                    | None -> minimum_workable_fuel := Some (f, errs) in

    let with_fuel label_assumptions p (n, i, timeout_ms) =
       [Term.Caption (Util.format2 "<fuel='%s' ifuel='%s'>" (string_of_int n) (string_of_int i));
        Term.Assume(mkEq(mkApp("MaxFuel", []), n_fuel n), None, None);
        Term.Assume(mkEq(mkApp("MaxIFuel", []), n_fuel i), None, None);
        p]
        @label_assumptions
        @[Term.SetOption ("timeout", string_of_int timeout_ms)]
        @[Term.CheckSat]
        @(if Options.record_hints() then [Term.GetUnsatCore] else [])
        @suffix in

    let check (p:decl) =
        let default_timeout = Options.z3_timeout () * 1000 in
        let default_initial_config = Options.initial_fuel(), Options.initial_ifuel(), default_timeout in
        let hint_opt = next_hint query_name query_index in
        let unsat_core, initial_config =
            match hint_opt with
            | None -> None, default_initial_config 
            | Some hint -> 
              let core, timeout = 
                if Option.isSome hint.unsat_core 
                then hint.unsat_core, default_timeout
                else None, 60 * 1000 in
              core,
              (hint.fuel, hint.ifuel, timeout) in
        let alt_configs = List.flatten 
           [(if default_initial_config <> initial_config  
             || Option.isSome unsat_core                          then [default_initial_config]                                       else []); 
            (if Options.max_ifuel()    >  Options.initial_ifuel() then [Options.initial_fuel(), Options.max_ifuel(), default_timeout] else []);
            (if Options.max_fuel() / 2 >  Options.initial_fuel()  then [Options.max_fuel() / 2, Options.max_ifuel(), default_timeout] else []);
            (if Options.max_fuel()     >  Options.initial_fuel() && 
                Options.max_ifuel()    >  Options.initial_ifuel() then [Options.max_fuel(),     Options.max_ifuel(), default_timeout] else []);
            (if Options.min_fuel()     <  Options.initial_fuel()  then [Options.min_fuel(), 1, default_timeout]                       else [])] in
        let report p (errs:z3_err) : unit =
            let errs : z3_err = 
                if Options.detail_errors() && Options.n_cores() = 1
                then let min_fuel, potential_errors = match !minimum_workable_fuel with 
                        | Some (f, errs) -> f, errs
                        | None -> (Options.min_fuel(), 1, default_timeout), errs in
                     let ask_z3 label_assumptions = 
                        let res = Util.mk_ref None in
                        Z3.ask None all_labels (with_fuel label_assumptions p min_fuel) (fun r -> res := Some r);
                        Option.get (!res) in
                     detail_errors env all_labels ask_z3, false
                else errs in

            let errs = 
                match errs with
                | [], true -> [(("", Term_sort), "Timeout: Unknown assertion failed", Range.dummyRange)], true
                | [], false -> [(("", Term_sort), "Unknown assertion failed", Range.dummyRange)], false
                | _ -> errs in
            record_hint None;
            if Options.print_fuels()
            then Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                    (Range.string_of_range (Env.get_range env))
                    (Options.max_fuel()  |> Util.string_of_int)
                    (Options.max_ifuel() |> Util.string_of_int);
            Errors.add_errors env (fst errs |> List.map (fun (_, x, y) -> x, y)) 
        in

        let use_errors (errs:error_labels * bool) (result:z3_result) : z3_result = 
            match errs, result with 
            | ([], _), _
            | _, Inl _ -> result
            | _, Inr _ -> Inr errs in
        let rec try_alt_configs prev_f (p:decl) (errs:z3_err) cfgs = 
            set_minimum_workable_fuel prev_f errs;
            match cfgs with
            | [] -> report p errs
            | [mi] -> //we're down to our last config; last ditch effort to get a counterexample with very low fuel
                begin match errs with
                | [], _ -> Z3.ask None all_labels (with_fuel [] p mi) (cb false mi p [])
                | _ -> set_minimum_workable_fuel prev_f errs;
                       report p errs
                end

            | mi::tl ->
                Z3.ask None all_labels (with_fuel [] p mi) 
                    (fun (result, elapsed_time) -> cb false mi p tl (use_errors errs result, elapsed_time))

        and cb used_hint (prev_fuel, prev_ifuel, timeout) (p:decl) alt (result, elapsed_time) =
            if used_hint then (Z3.refresh(); record_hint_stat hint_opt result elapsed_time (Env.get_range env));
            let at_log_file () = 
                if Options.log_queries() 
                then "@" ^ (Z3.query_logging.log_file_name())
                else "" in
            let query_info tag = 
                 Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n"
                                [Range.string_of_range (Env.get_range env);
                                 at_log_file();
                                 query_name;
                                 Util.string_of_int query_index;
                                 tag;
                                 (if used_hint then " (with hint)" else "");
                                 Util.string_of_int elapsed_time;
                                 Util.string_of_int prev_fuel;
                                 Util.string_of_int prev_ifuel] 
            in
            match result with 
            | Inl unsat_core ->
                if not used_hint
                then let hint = { hint_name=query_name;
                                  hint_index=query_index;
                                  fuel=prev_fuel;
                                  ifuel=prev_ifuel;
                                  query_elapsed_time=elapsed_time;
                                  unsat_core=unsat_core } in
                     record_hint (Some hint)
                else record_hint hint_opt;
                if Options.print_fuels()
                || Options.hint_info()
                then query_info "succeeded"
            | Inr errs -> 
                 if Options.print_fuels()
                 || Options.hint_info()
                 then query_info "failed";
                 try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt in

        if Option.isSome unsat_core then Z3.refresh();
        Z3.ask unsat_core
               all_labels 
               (with_fuel [] p initial_config)
               (cb (Option.isSome unsat_core) initial_config p alt_configs)  in

    let process_query (q:decl) :unit =
        if (Options.split_cases()) > 0 then
            let (b, cb) = SplitQueryCases.can_handle_query (Options.split_cases()) q in
            if b then SplitQueryCases.handle_query cb check else check q
        else check q
    in

    if Options.admit_smt_queries() then () else process_query query


let solve use_env_msg tcenv q : unit =
    Encode.push (Util.format1 "Starting query at %s" (Range.string_of_range <| Env.get_range tcenv));
    let tcenv = incr_query_index tcenv in
    let prefix, labels, qry, suffix = Encode.encode_query use_env_msg tcenv q in
    let pop () = Encode.pop (Util.format1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
    match qry with
    | Assume({tm=App(False, _)}, _, _) -> pop(); ()
    | _ when tcenv.admit -> pop(); ()
    | Assume(q, _, _) ->
        ask_and_report_errors tcenv labels prefix qry suffix;
        pop ()

    | _ -> failwith "Impossible"
    
(**********************************************************************************************)
(* Top-level interface *)
(**********************************************************************************************)
let solver = {
    init=init;
    push=push;
    pop=pop;
    mark=mark;
    reset_mark=reset_mark;
    commit_mark=commit_mark;
    encode_sig=encode_sig;
    encode_modul=encode_modul;
    solve=solve;
    is_trivial=is_trivial;
    finish=Z3.finish;
    refresh=Z3.refresh;
}
let dummy = {
    init=(fun _ -> ());
    push=(fun _ -> ());
    pop=(fun _ -> ());
    mark=(fun _ -> ());
    reset_mark=(fun _ -> ());
    commit_mark=(fun _ -> ());
    encode_sig=(fun _ _ -> ());
    encode_modul=(fun _ _ -> ());
    solve=(fun _ _ _ -> ());
    is_trivial=(fun _ _ -> false);
    finish=(fun () -> ());
    refresh=(fun () -> ());
}


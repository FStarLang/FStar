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
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.SMTEncoding.ErrorReporting
open FStar.SMTEncoding.Encode

(****************************************************************************)
(* Hint databases for record and replay (private)                           *)
(****************************************************************************)
type hint = {
    fuel:int;  //fuel for unrolling recursive functions
    ifuel:int; //fuel for inverting inductive datatypes
    unsat_core:option<(list<string>)>; //unsat core, if requested
    query_elapsed_time:int //time in milliseconds taken for the query, to decide if a fresh replay is worth it
}

type hints = list<(option<hint>)>

type hints_db = {
    module_digest:string;
    hints: hints
}

let recorded_hints : ref<option<hints>> = Util.mk_ref None
let replaying_hints: ref<option<hints>> = Util.mk_ref None

let format_hints_file_name src_fn =
    Util.format_value_file_name <| Util.format1 "%s.hints" src_fn

(****************************************************************************)
(* Hint databases (public)                                                  *)
(****************************************************************************)
let initialize_hints_db src_fn force_record : unit =
    if Options.record_hints() then recorded_hints := Some [];
    if Options.use_hints()
    then let norm_src_fn = Util.normalize_file_path src_fn in
         let val_fn = format_hints_file_name norm_src_fn in
         begin match Util.load_value_from_file val_fn with
            | Some hints ->
                let expected_digest = Util.digest_of_file norm_src_fn in
                if Options.hint_info()
                then begin 
                     if hints.module_digest = expected_digest 
                     then Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_fn
                     else Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_fn
                end;
                replaying_hints := Some hints.hints
            | None ->
                if Options.hint_info() 
                then Util.print1 "(%s) Unable to read hints db.\n" norm_src_fn
         end
    
let finalize_hints_db src_fn : unit =
    begin if Options.record_hints () then
          let hints = Option.get !recorded_hints in
          let hints_db = {
                module_digest = Util.digest_of_file src_fn;
                hints = hints
              }  in
          let hints_file_name = format_hints_file_name src_fn in
          Util.save_value_to_file hints_file_name hints_db
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

let next_hint () = 
    match !replaying_hints with 
    | Some (hd::tl) -> 
      replaying_hints := Some tl;
      hd
    | _ -> None

let record_hint hint = 
    match !recorded_hints with 
    | Some l -> recorded_hints := Some (l@[hint])
    | _ -> ()

(***********************************************************************************)
(* Invoking the SMT solver and extracting an error report from the model, if any   *)
(***********************************************************************************)

let ask_and_report_errors env use_fresh_z3_context all_labels prefix query suffix = 
    Z3.giveZ3 prefix;
    let minimum_workable_fuel = Util.mk_ref None in
    let set_minimum_workable_fuel f = function 
        | [] -> ()
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
        let unsat_core, initial_config =
            match next_hint() with
            | None -> None, default_initial_config 
            | Some hint -> 
              let core, timeout = 
                if Option.isSome hint.unsat_core 
                //&& hint.query_elapsed_time >= 200 (*ms*) 
                then hint.unsat_core, 3 * 1000
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
        let report p (errs:labels) : unit =
            let errs = if Options.detail_errors() && Options.n_cores() = 1
                       then let min_fuel, potential_errors = match !minimum_workable_fuel with 
                                | Some (f, errs) -> f, errs
                                | None -> (Options.min_fuel(), 1, default_timeout), errs in
                            let ask_z3 label_assumptions = 
                                let res = Util.mk_ref None in
                                Z3.ask use_fresh_z3_context None all_labels (with_fuel label_assumptions p min_fuel) (fun r -> res := Some r);
                                Option.get (!res) in
                            detail_errors all_labels errs ask_z3
                       else errs in

            let errs = 
                match errs with
                | [] -> [(("", Term_sort), "Unknown assertion failed", Range.dummyRange)]
                | _ -> errs in
            record_hint None;
            if Options.print_fuels() || Options.hint_info()
            then Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                    (Range.string_of_range (Env.get_range env))
                    (Options.max_fuel()  |> Util.string_of_int)
                    (Options.max_ifuel() |> Util.string_of_int);
            Errors.add_errors env (errs |> List.map (fun (_, x, y) -> x, y));
            if (Options.detail_errors())
            then raise (FStar.Syntax.Syntax.Err("Detailed error report follows\n")) in

        let use_errors errs result = 
            match errs, result with 
            | [], _
            | _, Inl _ -> result
            | _, Inr _ -> Inr errs in
        let rec try_alt_configs prev_f (p:decl) (errs:labels) cfgs = 
            set_minimum_workable_fuel prev_f errs;
            match cfgs with
            | [] -> report p errs
            | [mi] -> //we're down to our last config; last ditch effort to get a counterexample with very low fuel
                begin match errs with
                | [] -> Z3.ask use_fresh_z3_context None all_labels (with_fuel [] p mi) (cb false mi p [])
                | _ -> set_minimum_workable_fuel prev_f errs;
                       report p errs
                end

            | mi::tl ->
                Z3.ask use_fresh_z3_context None all_labels (with_fuel [] p mi) 
                    (fun (result, elapsed_time) -> cb false mi p tl (use_errors errs result, elapsed_time))

        and cb refresh (prev_fuel, prev_ifuel, timeout) (p:decl) alt (result, elapsed_time) =
            if refresh then Z3.refresh();
            match result with 
            | Inl unsat_core ->
                let hint = { fuel=prev_fuel;
                             ifuel=prev_ifuel;
                             query_elapsed_time=elapsed_time;
                             unsat_core=unsat_core } in
                record_hint (Some hint);
                if Options.print_fuels() || Options.hint_info()
                then Util.print4 "(%s) Query succeeded in %s milliseconds with fuel %s and ifuel %s\n"
                                (Range.string_of_range (Env.get_range env))
                                (Util.string_of_int elapsed_time)
                                (Util.string_of_int prev_fuel)
                                (Util.string_of_int prev_ifuel)
            | Inr errs -> 
                 if Options.print_fuels() || Options.hint_info()
                 then Util.print4 "(%s) Query failed in %s milliseconds with fuel %s and ifuel %s ... retrying \n"
                       (Range.string_of_range (Env.get_range env))
                       (Util.string_of_int elapsed_time)
                       (Util.string_of_int prev_fuel)
                       (Util.string_of_int prev_ifuel);
                 try_alt_configs (prev_fuel, prev_ifuel, timeout) p errs alt in

        if Option.isSome unsat_core then Z3.refresh();
        Z3.ask use_fresh_z3_context  //only relevant if we're running with n_cores > 1
               unsat_core
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
    let prefix, labels, qry, suffix = Encode.encode_query use_env_msg tcenv q in
    let pop () = Encode.pop (Util.format1 "Ending query at %s" (Range.string_of_range <| Env.get_range tcenv)) in
    match qry with
    | Assume({tm=App(False, _)}, _, _) -> pop(); ()
    | _ when tcenv.admit -> pop(); ()
    | Assume(q, _, _) ->
        ask_and_report_errors tcenv false labels prefix qry suffix;
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


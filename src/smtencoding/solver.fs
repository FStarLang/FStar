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
open FStar.Util

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
                if hints.module_digest = expected_digest then 
                    begin
                       if Options.print_fuels()
                       then Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_fn;
                       replaying_hints := Some hints.hints
                    end
                else if Options.print_fuels() 
                     then Util.print1 "(%s) digest is invalid.\n" norm_src_fn
            | None ->
                if (Options.print_fuels()) then
                    Util.print1 "(%s) Unable to read hints db.\n" norm_src_fn
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
open FStar.TypeChecker
open FStar.SMTEncoding.ErrorReporting

let ask_and_report_errors env use_fresh_z3_context all_labels prefix query suffix = 
    Z3.giveZ3 prefix;
    let minimum_workable_fuel = Util.mk_ref None in
    let set_minimum_workable_fuel f = function 
        | [] -> ()
        | errs -> match !minimum_workable_fuel with 
                    | Some _ -> ()
                    | None -> minimum_workable_fuel := Some (f, errs) in

    let with_fuel label_assumptions p (n, i) use_timeout =
        let timeout_ms =
            if use_timeout then
                Options.z3_timeout () * 1000
            else
                60 * 1000
        in
       [Term.Caption (Util.format2 "<fuel='%s' ifuel='%s'>" (string_of_int n) (string_of_int i));
        Term.Assume(mkEq(mkApp("MaxFuel", []), n_fuel n), None, None);
        Term.Assume(mkEq(mkApp("MaxIFuel", []), n_fuel i), None, None);
        p]
        @label_assumptions
        @[Term.SetOption ("timeout", string_of_int timeout_ms)]
        @[Term.CheckSat]
        @suffix in

    let check (p:decl) =
        let default_initial_config = Options.initial_fuel(), Options.initial_ifuel() in
        let is_cached_config = Util.mk_ref false in
        let initial_config =
            match next_hint() with
            | None -> default_initial_config 
            | Some hint -> hint.fuel, hint.ifuel in
        let alt_configs = List.flatten 
           [(if default_initial_config <> initial_config          then [default_initial_config]                      else []); 
            (if Options.max_ifuel()    >  Options.initial_ifuel() then [Options.initial_fuel(), Options.max_ifuel()] else []);
            (if Options.max_fuel() / 2 >  Options.initial_fuel()  then [Options.max_fuel() / 2, Options.max_ifuel()] else []);
            (if Options.max_fuel()     >  Options.initial_fuel() && 
                Options.max_ifuel()    >  Options.initial_ifuel() then [Options.max_fuel(),     Options.max_ifuel()] else []);
            (if Options.min_fuel()     <  Options.initial_fuel()  then [Options.min_fuel(), 1]                       else [])] in

        let report p (errs:labels) : unit =
            let errs = if Options.detail_errors() && Options.n_cores() = 1
                       then let min_fuel, potential_errors = match !minimum_workable_fuel with 
                                | Some (f, errs) -> f, errs
                                | None -> (Options.min_fuel(), 1), errs in
                            let ask_z3 label_assumptions = 
                                let res = Util.mk_ref None in
                                Z3.ask use_fresh_z3_context all_labels (with_fuel label_assumptions p min_fuel true) (fun r -> res := Some r);
                                Option.get (!res) in
                            detail_errors all_labels errs ask_z3
                       else errs in

            let errs = 
                match errs with
                | [] -> [(("", Term_sort), "Unknown assertion failed", Range.dummyRange)]
                | _ -> errs in
            record_hint None;
            if (Options.print_fuels())
            then (Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                    (Range.string_of_range (Env.get_range env))
                    ((Options.max_fuel()) |> Util.string_of_int)
                    ((Options.max_ifuel()) |> Util.string_of_int));
            Errors.add_errors env (errs |> List.map (fun (_, x, y) -> x, y));
            if (Options.detail_errors())
            then raise (FStar.Syntax.Syntax.Err("Detailed error report follows\n")) in

        let rec try_alt_configs prev_f (p:decl) (errs:labels) cfgs = 
            set_minimum_workable_fuel prev_f errs;
            match cfgs with
            | [] -> report p errs
            | [mi] -> //we're down to our last config; last ditch effort to get a counterexample with very low fuel
                begin match errs with
                | [] -> Z3.ask use_fresh_z3_context all_labels (with_fuel [] p mi true) (cb mi p [])
                | _ -> set_minimum_workable_fuel prev_f errs;
                       report p errs
                end

            | mi::tl ->
                Z3.ask use_fresh_z3_context all_labels (with_fuel [] p mi true) (fun (ok, errs') ->
                match errs with
                    | [] -> cb mi p tl (ok, errs')
                    | _ -> cb mi p tl (ok, errs))

        and cb (prev_fuel, prev_ifuel) (p:decl) alt (ok, errs) =
            if ok 
            then begin
                let hint = { fuel=prev_fuel;
                             ifuel=prev_ifuel;
                             query_elapsed_time=0;
                             unsat_core=None } in
                record_hint (Some hint);
                if Options.print_fuels()
                then Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n"
                                (Range.string_of_range (Env.get_range env))
                                (Util.string_of_int prev_fuel)
                                (Util.string_of_int prev_ifuel)
            end
            else begin
                 if Options.print_fuels()
                 then Util.print3 "(%s) Query failed with fuel %s and ifuel %s ... retrying \n"
                       (Range.string_of_range (Env.get_range env))
                       (Util.string_of_int prev_fuel)
                       (Util.string_of_int prev_ifuel);
                 try_alt_configs (prev_fuel, prev_ifuel) p errs alt
            end in

        Z3.ask use_fresh_z3_context  //only relevant if we're running with n_cores > 1
               all_labels 
               (with_fuel [] p initial_config (not !is_cached_config))
               (cb initial_config p alt_configs)  in

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
        let fresh = String.length q.hash >= 2048 in
        ask_and_report_errors tcenv fresh labels prefix qry suffix;
        pop ()

    | _ -> failwith "Impossible"
    
(**********************************************************************************************)
(* Top-level interface *)
(**********************************************************************************************)
open FStar.TypeChecker.Env
open FStar.SMTEncoding.Encode
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


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

module FStar.SMTEncoding.Z3
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
module BU = FStar.Util

(****************************************************************************)
(* Z3 Specifics                                                             *)
(****************************************************************************)

(* Check the Z3 commit hash once, and issue a warning if it is not
   equal to the one that we are expecting from the Z3 url below
*)
let _z3hash_checked : ref<bool> = BU.mk_ref false

let _z3hash_expected = "1f29cebd4df6"

let _z3url = "https://github.com/FStarLang/binaries/tree/master/z3-tested"

let parse_z3_version_lines out =
    match splitlines out with
    | x :: _ ->
        begin
            let trimmed = trim_string x in
            let parts = split trimmed " " in
            let rec aux = function
            | [hash] ->
              let n = min (String.strlen _z3hash_expected) (String.strlen hash) in
              let hash_prefix = String.substring hash 0 n in
              if hash_prefix = _z3hash_expected
              then begin
                  if Options.debug_any ()
                  then
                      let msg =
                          BU.format1
                              "Successfully found expected Z3 commit hash %s\n"
                              hash
                      in
                      print_string msg
                  else ();
                  None
              end else
                  let msg =
                      BU.format2
                          "Expected Z3 commit hash \"%s\", got \"%s\""
                          _z3hash_expected
                          trimmed
                  in
                  Some msg
            | _ :: q -> aux q
            | _ -> Some "No Z3 commit hash found"
            in
            aux parts
        end
    | _ -> Some "No Z3 version string found"

let z3hash_warning_message () =
    let run_proc_result =
        try
            Some (BU.run_process "z3_version" (Options.z3_exe()) ["-version"] None)
        with _ -> None
    in
    match run_proc_result with
    | None -> Some (FStar.Errors.Error_Z3InvocationError, "Could not run Z3")
    | Some out ->
        begin match parse_z3_version_lines out with
        | None -> None
        | Some msg -> Some (FStar.Errors.Warning_Z3InvocationWarning, msg)
        end

let check_z3hash () =
    if not !_z3hash_checked
    then begin
        _z3hash_checked := true;
        match z3hash_warning_message () with
        | None -> ()
        | Some (e, msg) ->
          let msg =
              BU.format4
                  "%s\n%s\n%s\n%s\n"
                  msg
                  "Please download the version of Z3 corresponding to your platform from:"
                  _z3url
                  "and add the bin/ subdirectory into your PATH"
          in
          FStar.Errors.log_issue Range.dummyRange (e, msg)
    end

let ini_params () =
  check_z3hash ();
  List.append ["-smt2"; "-in"; "auto_config=false";
               "model=true"; "smt.relevancy=2"; "smt.case_split=3";
               (Util.format1 "smt.random_seed=%s" (string_of_int (Options.z3_seed ())))]
              (Options.z3_cliopt ())

type label = string
type unsat_core = option<list<string>>
type z3status =
    | UNSAT   of unsat_core
    | SAT     of error_labels * option<string>         //error labels
    | UNKNOWN of error_labels * option<string>         //error labels
    | TIMEOUT of error_labels * option<string>         //error labels
    | KILLED
type z3statistics = BU.smap<string>

let status_tag = function
    | SAT  _ -> "sat"
    | UNSAT _ -> "unsat"
    | UNKNOWN _ -> "unknown"
    | TIMEOUT _ -> "timeout"
    | KILLED -> "killed"

let status_string_and_errors s =
    match s with
    | KILLED
    | UNSAT _ -> status_tag s, []
    | SAT (errs, msg)
    | UNKNOWN (errs, msg)
    | TIMEOUT (errs, msg) -> BU.format2 "%s%s" (status_tag s) (match msg with None -> "" | Some msg -> " because " ^ msg), errs

let tid () = BU.current_tid() |> BU.string_of_int
let new_z3proc id =
    BU.start_process id (Options.z3_exe ()) (ini_params ()) (fun s -> s = "Done!")

type bgproc = {
    ask: string -> string;
    refresh:unit -> unit;
    restart:unit -> unit
}

type query_log = {
    get_module_name: unit -> string;
    set_module_name: string -> unit;
    write_to_log:   string -> unit;
    close_log:       unit -> unit;
    log_file_name:   unit -> string
}


let query_logging =
    let query_number = BU.mk_ref 0 in
    let log_file_opt : ref<option<file_handle>> = BU.mk_ref None in
    let used_file_names : ref<list<(string * int)>> = BU.mk_ref [] in
    let current_module_name : ref<option<string>> = BU.mk_ref None in
    let current_file_name : ref<option<string>> = BU.mk_ref None in
    let set_module_name n = current_module_name := Some n in
    let get_module_name () = match !current_module_name with
        | None -> failwith "Module name not set"
        | Some n -> n in
    let new_log_file () =
        match !current_module_name with
        | None -> failwith "current module not set"
        | Some n ->
          let file_name =
              match List.tryFind (fun (m, _) -> n=m) !used_file_names with
              | None ->
                used_file_names := (n, 0)::!used_file_names;
                n
              | Some (_, k) ->
                used_file_names := (n, k+1)::!used_file_names;
                BU.format2 "%s-%s" n (BU.string_of_int (k+1)) in
          let file_name = BU.format1 "queries-%s.smt2" file_name in
          current_file_name := Some file_name;
          let fh = BU.open_file_for_writing file_name in
          log_file_opt := Some fh;
          fh in
    let get_log_file () = match !log_file_opt with
        | None -> new_log_file()
        | Some fh -> fh in
    let append_to_log str = BU.append_to_file (get_log_file()) str in
    let write_to_new_log str =
      let dir_name = match !current_file_name with
        | None ->
          let dir_name = match !current_module_name with
            | None -> failwith "current module not set"
            | Some n -> BU.format1 "queries-%s" n in
          BU.mkdir true dir_name;
          current_file_name := Some dir_name;
          dir_name
        | Some n -> n in
      let qnum = !query_number in
      query_number := !query_number + 1;
      let file_name = BU.format1 "query-%s.smt2" (BU.string_of_int qnum) in
      let file_name = BU.concat_dir_filename dir_name file_name in
      write_file file_name str in
    let write_to_log str =
      if (Options.n_cores() > 1) then write_to_new_log str
      else append_to_log str
      in
    let close_log () = match !log_file_opt with
        | None -> ()
        | Some fh -> BU.close_file fh; log_file_opt := None in
    let log_file_name () = match !current_file_name with
        | None -> failwith "no log file"
        | Some n -> n in
     {set_module_name=set_module_name;
      get_module_name=get_module_name;
      write_to_log=write_to_log;
      close_log=close_log;
      log_file_name=log_file_name}

let bg_z3_proc =
    let the_z3proc = BU.mk_ref None in
    let new_proc =
        let ctr = BU.mk_ref (-1) in
        fun () -> new_z3proc (BU.format1 "bg-%s" (incr ctr; !ctr |> string_of_int)) in
    let z3proc () =
      if !the_z3proc = None then
        the_z3proc := Some (new_proc ());
      must (!the_z3proc) in
    let x : list<unit> = [] in
    let ask input =
        let kill_handler () = "\nkilled\n" in
        BU.ask_process (z3proc ()) input kill_handler in
    let refresh () =
        BU.kill_process (z3proc ());
        the_z3proc := Some (new_proc ());
        query_logging.close_log() in
    let restart () =
        query_logging.close_log();
        the_z3proc := None;
        the_z3proc := Some (new_proc ()) in
    BU.mk_ref ({ask = BU.with_monitor x ask;
                refresh = BU.with_monitor x refresh;
                restart = BU.with_monitor x restart})

let set_bg_z3_proc bgp =
    bg_z3_proc := bgp

let at_log_file () =
  if Options.log_queries()
  then "@" ^ (query_logging.log_file_name())
  else ""

type smt_output_section = list<string>
type smt_output = {
  smt_result:         smt_output_section;
  smt_reason_unknown: option<smt_output_section>;
  smt_unsat_core:     option<smt_output_section>;
  smt_statistics:     option<smt_output_section>;
  smt_labels:         option<smt_output_section>;
}

let smt_output_sections (r:Range.range) (lines:list<string>) : smt_output =
    let rec until tag lines =
        match lines with
        | [] -> None
        | l::lines ->
          if tag = l then Some ([], lines)
          else BU.map_opt (until tag lines) (fun (until_tag, rest) ->
                          (l::until_tag, rest))
    in
    let start_tag tag = "<" ^ tag ^ ">" in
    let end_tag tag = "</" ^ tag ^ ">" in
    let find_section tag lines : option<(list<string>)> * list<string> =
       match until (start_tag tag) lines with
       | None -> None, lines
       | Some (prefix, suffix) ->
         match until (end_tag tag) suffix with
         | None -> failwith ("Parse error: " ^ end_tag tag ^ " not found")
         | Some (section, suffix) -> Some section, prefix @ suffix
    in
    let result_opt, lines = find_section "result" lines in
    let result = BU.must result_opt in
    let reason_unknown, lines = find_section "reason-unknown" lines in
    let unsat_core, lines = find_section "unsat-core" lines in
    let statistics, lines = find_section "statistics" lines in
    let labels, lines = find_section "labels" lines in
    let remaining =
      match until "Done!" lines with
      | None -> lines
      | Some (prefix, suffix) -> prefix@suffix in
    let _ =
        match remaining with
        | [] -> ()
        | _ ->
            FStar.Errors.log_issue
                     r
                     (Errors.Warning_UnexpectedZ3Output, (BU.format1 "Unexpected output from Z3: %s\n"
                                    (String.concat "\n" remaining))) in
    {smt_result = BU.must result_opt;
     smt_reason_unknown = reason_unknown;
     smt_unsat_core = unsat_core;
     smt_statistics = statistics;
     smt_labels = labels}

let doZ3Exe (r:Range.range) (fresh:bool) (input:string) (label_messages:error_labels) : z3status * z3statistics =
  let parse (z3out:string) =
    let lines = String.split ['\n'] z3out |> List.map BU.trim_string in
    let smt_output = smt_output_sections r lines in
    let unsat_core =
        match smt_output.smt_unsat_core with
        | None -> None
        | Some s ->
          let s = BU.trim_string (String.concat " " s) in
          let s = BU.substring s 1 (String.length s - 2) in
          if BU.starts_with s "error"
          then None
          else Some (BU.split s " " |> BU.sort_with String.compare)
    in
    let labels =
        match smt_output.smt_labels with
        | None -> []
        | Some lines ->
          let rec lblnegs lines =
            match lines with
            | lname::"false"::rest when BU.starts_with lname "label_" -> lname::lblnegs rest
            | lname::_::rest when BU.starts_with lname "label_" -> lblnegs rest
            | _ -> [] in
          let lblnegs = lblnegs lines in
          lblnegs |> List.collect
            (fun l -> match label_messages |> List.tryFind (fun (m, _, _) -> fst m = l) with
                   | None -> []
                   | Some (lbl, msg, r) -> [(lbl, msg, r)])
    in
    let statistics =
        let statistics : z3statistics = BU.smap_create 0 in
        match smt_output.smt_statistics with
        | None -> statistics
        | Some lines ->
          let parse_line line =
            let pline = BU.split (BU.trim_string line) ":" in
            match pline with
            | "(" :: entry :: []
            |  "" :: entry :: [] ->
               let tokens = BU.split entry " " in
               let key = List.hd tokens in
               let ltok = List.nth tokens ((List.length tokens) - 1) in
               let value = if BU.ends_with ltok ")" then (BU.substring ltok 0 ((String.length ltok) - 1)) else ltok in
               BU.smap_add statistics key value
            | _ -> ()
          in
          List.iter parse_line lines;
          statistics
    in
    let reason_unknown = BU.map_opt smt_output.smt_reason_unknown (fun x ->
        let ru = String.concat " " x in
        if BU.starts_with ru "(:reason-unknown \""
        then let reason = FStar.Util.substring_from ru (String.length "(:reason-unknown \"" ) in
             let res = String.substring reason 0 (String.length reason - 2) in //it ends with '")'
             res
        else ru) in
    let status =
      if Options.debug_any() then print_string <| format1 "Z3 says: %s\n" (String.concat "\n" smt_output.smt_result);
      match smt_output.smt_result with
      | ["unsat"]   -> UNSAT unsat_core
      | ["sat"]     -> SAT     (labels, reason_unknown)
      | ["unknown"] -> UNKNOWN (labels, reason_unknown)
      | ["timeout"] -> TIMEOUT (labels, reason_unknown)
      | ["killed"]  -> (!bg_z3_proc).restart(); KILLED
      | _ ->
        failwith (format1 "Unexpected output from Z3: got output result: %s\n"
                          (String.concat "\n" smt_output.smt_result))
    in
    status, statistics
  in
  let stdout =
    if fresh then
      BU.run_process (tid ()) (Options.z3_exe ()) (ini_params ()) (Some input)
    else
      (!bg_z3_proc).ask input
  in
  parse (BU.trim_string stdout)

let z3_options = BU.mk_ref
    "(set-option :global-decls false)\n\
     (set-option :smt.mbqi false)\n\
     (set-option :auto_config false)\n\
     (set-option :produce-unsat-cores true)\n"

// Use by F*.js
let set_z3_options opts =
    z3_options := opts

type job_t<'a> = {
    job:unit -> 'a;
    callback: 'a -> unit
}

type z3result = {
      z3result_status      : z3status;
      z3result_time        : int;
      z3result_statistics  : z3statistics;
      z3result_query_hash  : option<string>
}

type z3job = job_t<z3result>

let job_queue : ref<list<z3job>> = BU.mk_ref []

let pending_jobs = BU.mk_ref 0

let z3_job (r:Range.range) fresh (label_messages:error_labels) input qhash () : z3result =
  let start = BU.now() in
  let status, statistics =
    try doZ3Exe r fresh input label_messages
    with e when not (Options.trace_error()) ->
         (!bg_z3_proc).refresh();
         raise e
  in
  let _, elapsed_time = BU.time_diff start (BU.now()) in
  { z3result_status     = status;
    z3result_time       = elapsed_time;
    z3result_statistics = statistics;
    z3result_query_hash = qhash }

let running = BU.mk_ref false

let rec dequeue' () =
    (*print_string (BU.string_of_int (List.length !job_queue));*)
    let j = match !job_queue with
        | [] -> failwith "Impossible"
        | hd::tl ->
          job_queue := tl;
          hd in
    incr pending_jobs;
    BU.monitor_exit job_queue;
    run_job j;
    BU.with_monitor job_queue (fun () -> decr pending_jobs) (); dequeue (); ()

and dequeue () = match !running with
  | true ->
    let rec aux () =
      BU.monitor_enter (job_queue);
      match !job_queue with
        | [] ->
          BU.monitor_exit job_queue;
          BU.sleep(50);
          aux ()
        | _ -> dequeue'() in
    aux()
  | false -> ()

and run_job j = j.callback <| j.job ()

(* threads are spawned only if fresh, I.e. we check here and in ask the mode of execution,
   should be improved by using another option, see ask *)
let init () =
    running := true;
    let n_cores = (Options.n_cores()) in
    if (n_cores > 1) then
      let rec aux n =
          if n = 0 then ()
          else (spawn dequeue; aux (n - 1)) in
      aux n_cores
    else ()

let enqueue j =
    BU.with_monitor job_queue (fun () ->
        job_queue := !job_queue@[j];
        BU.monitor_pulse job_queue) ()

let finish () =
    let rec aux () =
        let n, m = BU.with_monitor job_queue (fun () -> !pending_jobs,  List.length !job_queue) () in
        //Printf.printf "In finish: pending jobs = %d, job queue len = %d\n" n m;
        if n+m=0
        then running := false
        else let _ = BU.sleep(500) in
             aux() in
    aux()

type scope_t = list<list<decl>>

// bg_scope is a global, mutable variable that keeps a list of the declarations
// that we have given to z3 so far. In order to allow rollback of history,
// one can enter a new "scope" by pushing a new, empty z3 list of declarations
// on fresh_scope (a stack) -- one can then, for instance, verify these
// declarations immediately, then call pop so that subsequent queries will not
// reverify or use these declarations
let fresh_scope : ref<scope_t> = BU.mk_ref [[]]
let mk_fresh_scope () = !fresh_scope

// bg_scope: Is the flat sequence of declarations already given to Z3
//           When refreshing the solver, the bg_scope is set to
//           a flattened version of fresh_scope
let bg_scope : ref<list<decl>> = BU.mk_ref []

// fresh_scope is a mutable reference; this pushes a new list at the front;
// then, givez3 modifies the reference so that within the new list at the front,
// new queries are pushed
let push msg    = BU.atomically (fun () ->
    fresh_scope := [Caption msg; Push]::!fresh_scope;
    bg_scope := !bg_scope @ [Push; Caption msg])

let pop msg      = BU.atomically (fun () ->
    fresh_scope := List.tl !fresh_scope;
    bg_scope := !bg_scope @ [Caption msg; Pop])

let snapshot msg = Common.snapshot push fresh_scope msg
let rollback msg depth = Common.rollback (fun () -> pop msg) fresh_scope depth

//giveZ3 decls: adds decls to the stack of declarations
//              to be actually given to Z3 only when the next
//              query comes up
let giveZ3 decls =
   decls |> List.iter (function Push | Pop -> failwith "Unexpected push/pop" | _ -> ());
   // This is where we prepend new queries to the head of the list at the head
   // of fresh_scope
   begin match !fresh_scope with
    | hd::tl -> fresh_scope := (hd@decls)::tl
    | _ -> failwith "Impossible"
   end;
   bg_scope := !bg_scope @ decls

//refresh: create a new z3 process, and reset the bg_scope
let refresh () =
    if (Options.n_cores() < 2) then
        (!bg_z3_proc).refresh();
        bg_scope := List.flatten (List.rev !fresh_scope)

let mk_input theory =
    let options = !z3_options in
    let r, hash =
        if Options.record_hints()
        || (Options.use_hints() && Options.use_hint_hashes()) then
            //the suffix of a "theory" that follows the "CheckSat" call
            //contains semantically irrelevant things
            //(e.g., get-model, get-statistics etc.)
            //that vary depending on some user options (e.g., record_hints etc.)
            //They should not be included in the query hash,
            //so split the prefix out and use only it for the hash
            let prefix, check_sat, suffix =
                theory |>
                BU.prefix_until (function CheckSat -> true | _ -> false) |>
                Option.get
            in
            let pp = List.map (declToSmt options) in
            let suffix = check_sat::suffix in
            let ps_lines = pp prefix in
            let ss_lines = pp suffix in
            let ps = String.concat "\n" ps_lines in
            let ss = String.concat "\n" ss_lines in

            (* Ignore captions AND ranges when hashing, otherwise we depend on file names *)
            let hs =
              if Options.log_queries()
              && Options.keep_query_captions ()
              then prefix
                   |> List.map (declToSmt_no_caps options)
                   |> String.concat "\n"
              else ps
            in
            ps ^ "\n" ^ ss, Some (BU.digest_of_string hs)
        else
            List.map (declToSmt options) theory |> String.concat "\n", None
    in
    if Options.log_queries() then query_logging.write_to_log r ;
    r, hash

type cb = z3result -> unit

let cache_hit
    (cache:option<string>)
    (qhash:option<string>)
    (cb:cb) =
    if Options.use_hints() && Options.use_hint_hashes() then
        match qhash with
        | Some (x) when qhash = cache ->
            let stats : z3statistics = BU.smap_create 0 in
            smap_add stats "fstar_cache_hit" "1";
            let result = {
              z3result_status = UNSAT None;
              z3result_time = 0;
              z3result_statistics = stats;
              z3result_query_hash = qhash
            } in
            cb result;
            true
        | _ ->
            false
    else
        false

let ask_1_core
    (r:Range.range)
    (filter_theory:decls_t -> decls_t * bool)
    (cache:option<string>)
    (label_messages:error_labels)
    (qry:decls_t)
    (cb:cb)
  = let theory = !bg_scope@[Push]@qry@[Pop] in
    let theory, used_unsat_core = filter_theory theory in
    let input, qhash = mk_input theory in
    bg_scope := [] ; // Now consumed.
    if not (cache_hit cache qhash cb) then
        run_job ({job=z3_job r false label_messages input qhash; callback=cb})

let ask_n_cores
    (r:Range.range)
    (filter_theory:decls_t -> decls_t * bool)
    (cache:option<string>)
    (label_messages:error_labels)
    (qry:decls_t)
    (scope:option<scope_t>)
    (cb:cb)
  = let theory = List.flatten (match scope with
        | Some s -> (List.rev s)
        | None   -> bg_scope := [] ; // Not needed; discard.
                    (List.rev !fresh_scope)) in
    let theory = theory@[Push]@qry@[Pop] in
    let theory, used_unsat_core = filter_theory theory in
    let input, qhash = mk_input theory in
    if not (cache_hit cache qhash cb) then
        enqueue ({job=z3_job r true label_messages input qhash; callback=cb})

let ask
    (r:Range.range)
    (filter:decls_t -> decls_t * bool)
    (cache:option<string>)
    (label_messages:error_labels)
    (qry:decls_t)
    (scope:option<scope_t>)
    (cb:cb)
  = if Options.n_cores() = 1 then
        ask_1_core r filter cache label_messages qry cb
    else
        ask_n_cores r filter cache label_messages qry scope cb

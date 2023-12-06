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
module FStar.SMTEncoding.Z3
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Compiler.Util

module M = FStar.Compiler.Misc
module BU = FStar.Compiler.Util

(****************************************************************************)
(* Z3 Specifics                                                             *)
(****************************************************************************)

(* We only warn once about these things *)
let _already_warned_solver_mismatch : ref bool = BU.mk_ref false
let _already_warned_version_mismatch : ref bool = BU.mk_ref false

let z3url = "https://github.com/Z3Prover/z3/releases"

(* Check if [path] is potentially a valid z3, by trying to run
it with -version and checking for non-empty output. Alternatively
we could call [which] on it (if it's not an absolute path), but
we shouldn't rely on the existence of a binary which. *)
let inpath (path:string) : bool =
  try
    let s = BU.run_process "z3_pathtest" path ["-version"] None in
    s <> ""
  with
  | _ -> false

(* Find the Z3 executable that we should invoke, according to the
needed version. The logic is as follows:

- If the user provided the --smt option, use that binary unconditionally.
- If z3-VER (or z3-VER.exe) exists in the PATH (where VER is either
  the default version or the user-provided --z3version) use it.
- Otherwise, default to "z3" in the PATH.

We cache the chosen executable for every Z3 version we've ran.
*)
let z3_exe : unit -> string =
  let cache : BU.smap string = BU.smap_create 5 in
  let find_or (k:string) (f : string -> string) : string =
    match smap_try_find cache k with
    | Some v -> v
    | None ->
      let v = f k in
      smap_add cache k v;
      v
  in
  fun () ->
    find_or (Options.z3_version()) (fun version ->
      let path =
        let z3_v = Platform.exe ("z3-" ^ version) in
        let smto = Options.smt () in
        if Some? smto then Some?.v smto
        else if inpath z3_v then z3_v
        else Platform.exe "z3"
      in
      if Options.debug_any () then
        BU.print1 "Chosen Z3 executable: %s\n" path;
      path
    )

type label = string

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
                             //(match msg with None -> "unknown" | Some msg -> msg), errs


let query_logging =
    let query_number = BU.mk_ref 0 in
    let log_file_opt : ref (option (out_channel * string)) = BU.mk_ref None in
    let used_file_names : ref (list (string * int)) = BU.mk_ref [] in
    let current_module_name : ref (option string) = BU.mk_ref None in
    let current_file_name : ref (option string) = BU.mk_ref None in
    let set_module_name n = current_module_name := Some n in
    let get_module_name () =
        match !current_module_name with
        | None -> failwith "Module name not set"
        | Some n -> n
    in
    let next_file_name () =
        let n = get_module_name() in
        let file_name =
            match List.tryFind (fun (m, _) -> n=m) !used_file_names with
            | None ->
              used_file_names := (n, 0)::!used_file_names;
              n
            | Some (_, k) ->
              used_file_names := (n, k+1)::!used_file_names;
              BU.format2 "%s-%s" n (BU.string_of_int (k+1))
        in
        BU.format1 "queries-%s.smt2" file_name
    in
    let new_log_file () =
        let file_name = next_file_name() in
        current_file_name := Some file_name;
        let c = BU.open_file_for_writing file_name in
        log_file_opt := Some (c, file_name);
        c, file_name
    in
    let get_log_file () =
        match !log_file_opt with
        | None -> new_log_file()
        | Some c -> c
    in
    let append_to_log str =
        let f, nm = get_log_file () in
        BU.append_to_file f str;
        nm
    in
    let write_to_new_log str =
      let file_name = next_file_name() in
      write_file file_name str;
      file_name
    in
    let write_to_log fresh str =
      if fresh
      then write_to_new_log str
      else append_to_log str
    in
    let close_log () =
        match !log_file_opt with
        | None -> ()
        | Some (c, _) ->
          BU.close_out_channel c; log_file_opt := None
    in
    let log_file_name () =
        match !current_file_name with
        | None -> failwith "no log file"
        | Some n -> n
    in
     {set_module_name=set_module_name;
      get_module_name=get_module_name;
      write_to_log=write_to_log;
      append_to_log=append_to_log;
      close_log=close_log;
     }

(*  Z3 background process handling *)
let z3_cmd_and_args () =
  let cmd = z3_exe () in
  let cmd_args =
    List.append ["-smt2";
                 "-in";
                 Util.format1 "smt.random_seed=%s" (string_of_int (Options.z3_seed ()))]
                (Options.z3_cliopt ()) in
  (cmd, cmd_args)

let warn_handler (suf:Errors.error_message) (s:string) : unit =
  let open FStar.Errors.Msg in
  let open FStar.Pprint in
  Errors.log_issue_doc Range.dummyRange (Errors.Warning_UnexpectedZ3Output, [
    text "Unexpected output from Z3:" ^^ hardline ^^
     blank 2 ^^ align (dquotes (arbitrary_string s));
    ] @ suf)

(* Talk to the process to see if it's the correct version of Z3
(i.e. the one in the optionstate). Also check that it indeed is Z3. By
default, each of these generates an error, but they can be downgraded
into warnings. The warnings are anyway printed only once per F*
invocation. *)
let check_z3version (p:proc) : unit =
  let getinfo (arg:string) : string =
    let s = BU.ask_process p (Util.format1 "(get-info :%s)\n(echo \"Done!\")\n" arg) (fun _ -> "Killed") (warn_handler []) in
    if BU.starts_with s ("(:" ^ arg) then
      let ss = String.split ['"'] s in
      List.nth ss 1
    else (
      warn_handler [] s;
      Errors.raise_err (Errors.Error_Z3InvocationError, BU.format1 "Could not run Z3 from `%s'" (proc_prog p))
    )
  in
  let name = getinfo "name" in
  if name <> "Z3" && not (!_already_warned_solver_mismatch) then (
    Errors.log_issue Range.dummyRange (Errors.Warning_SolverMismatch,
      BU.format3 "Unexpected SMT solver: expected to be talking to Z3, got %s.\n\
                  Please download the correct version of Z3 from %s\n\
                  and install it into your $PATH as `%s'."
        name
        z3url (Platform.exe ("z3-" ^ Options.z3_version  ()))
        );
    _already_warned_solver_mismatch := true
  );
  let ver_found : string = BU.trim_string (List.hd (BU.split (getinfo "version") "-")) in
  let ver_conf  : string = BU.trim_string (Options.z3_version ()) in
  if ver_conf <> ver_found && not (!_already_warned_version_mismatch) then (
    let open FStar.Errors in
    let open FStar.Pprint in
    Errors.log_issue_doc Range.dummyRange (Errors.Warning_SolverMismatch, [
      text (BU.format3 "Unexpected Z3 version for '%s': expected '%s', got '%s'."
                  (proc_prog p) ver_conf ver_found);
      prefix 4 1 (text "Please download the correct version of Z3 from")
                 (url z3url) ^/^
        group (text "and install it into your $PATH as" ^/^ squotes
          (doc_of_string (Platform.exe ("z3-" ^ Options.z3_version  ()))) ^^ dot);
    ]);
    Errors.stop_if_err(); (* stop now if this was a hard error *)
    _already_warned_version_mismatch := true
  );
  ()

let new_z3proc (id:string) (cmd_and_args : string & list string) : BU.proc =
    let proc = BU.start_process id (fst cmd_and_args) (snd cmd_and_args) (fun s -> s = "Done!") in
    check_z3version proc;
    proc

let new_z3proc_with_id =
    let ctr = BU.mk_ref (-1) in
    (fun cmd_and_args ->
      let p = new_z3proc (BU.format1 "z3-bg-%s" (incr ctr; !ctr |> string_of_int)) cmd_and_args in
      p)

type bgproc = {
    ask:      string -> string;
    refresh:  unit -> unit;
    restart:  unit -> unit;
    version:  unit -> string;
}

let cmd_and_args_to_string cmd_and_args =
  String.concat "" [
   "cmd="; (fst cmd_and_args);
   " args=["; (String.concat ", " (snd cmd_and_args));
   "]"
    ]

(* the current background process is stored in the_z3proc
   the params with which it was started are stored in the_z3proc_params
   refresh will kill and restart the process if the params changed or
   we have asked the z3 process something
 *)
let bg_z3_proc =
    let the_z3proc = BU.mk_ref None in
    let the_z3proc_params = BU.mk_ref (Some ("", [""])) in
    let the_z3proc_ask_count = BU.mk_ref 0 in
    let the_z3proc_version = BU.mk_ref "" in
    // NOTE: We keep track of the version and restart on changes
    // just to be safe: the executable name in the_z3proc_params should
    // be enough to distinguish between the different executables.
    let make_new_z3_proc cmd_and_args =
      the_z3proc := Some (new_z3proc_with_id cmd_and_args);
      the_z3proc_params := Some cmd_and_args;
      the_z3proc_ask_count := 0 in
      the_z3proc_version := Options.z3_version ();
    let z3proc () =
      if !the_z3proc = None then make_new_z3_proc (z3_cmd_and_args ());
      must (!the_z3proc)
    in
    let ask input =
        incr the_z3proc_ask_count;
        let kill_handler () = "\nkilled\n" in
        BU.ask_process (z3proc ()) input kill_handler (warn_handler [])
    in
    let maybe_kill_z3proc () =
      if !the_z3proc <> None then begin
         BU.kill_process (must (!the_z3proc));
         the_z3proc := None
      end
    in
    let refresh () =
        let next_params = z3_cmd_and_args () in
        let old_params = must (!the_z3proc_params) in

        let old_version = !the_z3proc_version in
        let next_version = Options.z3_version () in

        (* We only refresh the solver if we have used it at all, or if the
        parameters/version must be changed. We also force a refresh if log_queries is
        on. I (GM 2023/07/23) think this might have been for making sure we get
        a new file after checking a dependency, and that it might not be needed
        now. However it's not a big performance hit, and it's only when logging
        queries, so I'm maintaining this. *)
        if Options.log_queries() ||
           (!the_z3proc_ask_count > 0) ||
           old_params <> next_params ||
           old_version <> next_version
        then begin
          maybe_kill_z3proc();
          if Options.query_stats()
          then begin
             BU.print3 "Refreshing the z3proc (ask_count=%s old=[%s] new=[%s])\n"
               (BU.string_of_int !the_z3proc_ask_count)
               (cmd_and_args_to_string old_params)
               (cmd_and_args_to_string next_params)
          end;
          make_new_z3_proc next_params
        end;
        query_logging.close_log()
    in
    let restart () =
        maybe_kill_z3proc();
        query_logging.close_log();
        let next_params = z3_cmd_and_args () in
        make_new_z3_proc next_params
    in
    let x : list unit = [] in
    BU.mk_ref ({ask = BU.with_monitor x ask;
                refresh = BU.with_monitor x refresh;
                restart = BU.with_monitor x restart;
                version = (fun () -> !the_z3proc_version)})


type smt_output_section = list string
type smt_output = {
  smt_result:         smt_output_section;
  smt_reason_unknown: option smt_output_section;
  smt_unsat_core:     option smt_output_section;
  smt_statistics:     option smt_output_section;
  smt_labels:         option smt_output_section;
}

let smt_output_sections (log_file:option string) (r:Range.range) (lines:list string) : smt_output =
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
    let find_section tag lines : option (list string) * list string =
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
          let msg = String.concat "\n" remaining in
          let suf =
            let open FStar.Errors.Msg in
            let open FStar.Pprint in
            match log_file with
            | Some log_file -> [text "Log file:" ^/^ doc_of_string log_file]
            | None -> []
          in
          warn_handler suf msg
    in
    {smt_result = BU.must result_opt;
     smt_reason_unknown = reason_unknown;
     smt_unsat_core = unsat_core;
     smt_statistics = statistics;
     smt_labels = labels}

let doZ3Exe (log_file:_) (r:Range.range) (fresh:bool) (input:string) (label_messages:error_labels) (queryid:string) : z3status * z3statistics =
  let parse (z3out:string) =
    let lines = String.split ['\n'] z3out |> List.map BU.trim_string in
    let smt_output = smt_output_sections log_file r lines in
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
            (fun l -> match label_messages |> List.tryFind (fun (m, _, _) -> fv_name m = l) with
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
        then let reason = FStar.Compiler.Util.substring_from ru (String.length "(:reason-unknown \"" ) in
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
  let log_result fwrite (res, _stats) =
    (* If we are logging, write some more information to the
    smt2 file, such as the result of the query and the new unsat
    core generated. We take a call back to do so, since for the
    bg z3 process we must call query_logging.append_to_log, but for
    fresh invocations (such as hints) we must reopen the file to write
    to it. *)
    begin match log_file with
    | Some fname ->
      fwrite fname ("; QUERY ID: " ^ queryid);
      fwrite fname ("; STATUS: " ^ fst (status_string_and_errors res));
      begin match res with
      | UNSAT (Some core) ->
        fwrite fname ("; UNSAT CORE GENERATED: " ^ String.concat ", " core)
      | _ -> ()
      end
    | None -> ()
    end
  in
  if fresh then
    let proc = new_z3proc_with_id (z3_cmd_and_args ()) in
    let kill_handler () = "\nkilled\n" in
    let out = BU.ask_process proc input kill_handler (warn_handler []) in
    let r = parse (BU.trim_string out) in
    log_result (fun fname s ->
      let h = BU.open_file_for_appending fname in
      BU.append_to_file h s;
      BU.close_out_channel h
    ) r;
    BU.kill_process proc;
    r
  else
    let out = (!bg_z3_proc).ask input in
    let r = parse (BU.trim_string out) in
    log_result (fun _fname s -> ignore (query_logging.append_to_log s)) r;
    r

let z3_options (ver:string) =
 (* Common z3 prefix for all supported versions (at minimum 4.8.5).
  Note: smt.arith.solver defaults to 2 in 4.8.5, but it doesn't hurt to
  specify it. *)
  let opts =
    "(set-option :global-decls false)\n\
     (set-option :smt.mbqi false)\n\
     (set-option :auto_config false)\n\
     (set-option :produce-unsat-cores true)\n\
     (set-option :model true)\n\
     (set-option :smt.case_split 3)\n\
     (set-option :smt.relevancy 2)\n\
     (set-option :smt.arith.solver 2)\n"
  in

  (* We need the following options for Z3 >= 4.12.3 *)
  let opts = opts ^ begin
    if M.version_ge ver "4.12.3" then
    "(set-option :rewriter.enable_der false)\n\
     (set-option :rewriter.sort_disjunctions false)\n\
     (set-option :pi.decompose_patterns false)\n"
    else "" end
  in
  opts

// bg_scope is a global, mutable variable that keeps a list of the declarations
// that we have given to z3 so far. In order to allow rollback of history,
// one can enter a new "scope" by pushing a new, empty z3 list of declarations
// on fresh_scope (a stack) -- one can then, for instance, verify these
// declarations immediately, then call pop so that subsequent queries will not
// reverify or use these declarations
let fresh_scope : ref scope_t = BU.mk_ref [[]]
let mk_fresh_scope () = !fresh_scope
let flatten_fresh_scope () = List.flatten (List.rev !fresh_scope)

// bg_scope: Is the flat sequence of declarations already given to Z3
//           When refreshing the solver, the bg_scope is set to
//           a flattened version of fresh_scope
let bg_scope : ref (list decl) = BU.mk_ref []

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
    (!bg_z3_proc).refresh();
    bg_scope := flatten_fresh_scope ()

let context_profile (theory:list decl) =
    let modules, total_decls =
        List.fold_left (fun (out, _total) d ->
            match d with
            | Module(name, decls) ->
              let decls =
                List.filter
                    (function Assume _ -> true
                             | _ -> false)
                    decls in
              let n = List.length decls in
              (name, n)::out, n + _total
            | _ -> out, _total)
            ([], 0)
            theory
    in
    let modules = List.sortWith (fun (_, n) (_, m) -> m - n) modules in
    if modules <> []
    then BU.print1 "Z3 Proof Stats: context_profile with %s assertions\n"
                  (BU.string_of_int total_decls);
    List.iter (fun (m, n) ->
        if n <> 0 then
            BU.print2 "Z3 Proof Stats: %s produced %s SMT decls\n"
                        m
                        (string_of_int n))
               modules

let mk_input (fresh : bool) (theory : list decl) : string & option string & option string =
    let ver = Options.z3_version () in
    let options = "; Z3 invocation started by F*\n" in
    let options = options ^ "; F* version: " ^ !Options._version ^ " -- hash: " ^ !Options._commit ^ "\n" in
    let options = options ^ "; Z3 version (according to F*): " ^ Options.z3_version() ^ "\n" in
    let options = options ^ z3_options ver in
    let options = options ^ (Options.z3_smtopt() |> String.concat "\n") in
    if Options.print_z3_statistics() then context_profile theory;
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
              if Options.keep_query_captions ()
              then prefix
                   |> List.map (declToSmt_no_caps options)
                   |> String.concat "\n"
              else ps
            in
            (* Add the Z3 version to the string, so we get a mismatch if we switch versions. *)
            let hs = hs ^ "Z3 version: " ^ ver in
            ps ^ "\n" ^ ss, Some (BU.digest_of_string hs)
        else
            List.map (declToSmt options) theory |> String.concat "\n", None
    in
    let log_file_name =
        if Options.log_queries()
        then Some (query_logging.write_to_log fresh r)
        else None
    in
    r, hash, log_file_name

let cache_hit
    (log_file:option string)
    (cache:option string)
    (qhash:option string) : option z3result =
    if Options.use_hints() && Options.use_hint_hashes() then
        match qhash with
        | Some (x) when qhash = cache ->
            let stats : z3statistics = BU.smap_create 0 in
            smap_add stats "fstar_cache_hit" "1";
            let result = {
              z3result_status = UNSAT None;
              z3result_time = 0;
              z3result_statistics = stats;
              z3result_query_hash = qhash;
              z3result_log_file = log_file
            } in
            Some result
        | _ ->
            None
    else
        None

let z3_job (log_file:_) (r:Range.range) fresh (label_messages:error_labels) input qhash queryid () : z3result =
  //This code is a little ugly:
  //We insert a profiling call to accumulate total time spent in Z3
  //But, we also record the time of this particular call so that we can
  //record the elapsed time in the z3result_time field.
  //That field is printed out in the query-stats output, which is a separate
  //profiling feature. We could try in the future to unify all the different
  //kinds of profiling features ... but that's beyond scope for now.
  let (status, statistics), elapsed_time =
    Profiling.profile
      (fun () ->
        try
          BU.record_time (fun () -> doZ3Exe log_file r fresh input label_messages queryid)
        with e ->
          refresh(); //refresh the solver but don't handle the exception; it'll be caught upstream
          raise e)
      (Some (query_logging.get_module_name()))
      "FStar.SMTEncoding.Z3 (aggregate query time)"
  in
  { z3result_status     = status;
    z3result_time       = elapsed_time;
    z3result_statistics = statistics;
    z3result_query_hash = qhash;
    z3result_log_file   = log_file }

let ask
    (r:Range.range)
    (filter_theory:list decl -> list decl * bool)
    (cache:option string)
    (label_messages:error_labels)
    (qry:list decl)
    (queryid:string)
    (_scope : option scope_t) // GM: This was only used in ask_n_cores
    (fresh:bool) : z3result
  = let theory =
        if fresh
        then flatten_fresh_scope()
        else let theory = !bg_scope in
             bg_scope := [];//now consumed
             theory
    in
    let theory = theory @[Push]@qry@[Pop] in
    let theory, _used_unsat_core = filter_theory theory in
    let input, qhash, log_file_name = mk_input fresh theory in

    let just_ask () = z3_job log_file_name r fresh label_messages input qhash queryid () in
    if fresh then
        match cache_hit log_file_name cache qhash with
        | Some z3r -> z3r
        | None -> just_ask ()
    else
        just_ask ()

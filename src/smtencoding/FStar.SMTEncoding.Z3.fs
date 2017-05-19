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
open FStar.All
open FStar
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Util
module BU = FStar.Util

(****************************************************************************)
(* Z3 Specifics                                                             *)
(****************************************************************************)
type z3version =
| Z3V_Unknown of string
| Z3V of int * int * int

let z3version_as_string = function
    | Z3V_Unknown s -> BU.format1 "unknown version: %s" s
    | Z3V (i, j, k) -> BU.format3 "%s.%s.%s" (BU.string_of_int i) (BU.string_of_int j) (BU.string_of_int k)

let z3v_compare known (w1, w2, w3) =
    match known with
    | Z3V_Unknown _-> None
    | Z3V (k1, k2, k3) -> Some(
        if k1 <> w1 then w1 - k1 else
        if k2 <> w2 then w2 - k2 else
        w3 - k3
    )

let z3v_le known wanted =
    match z3v_compare known wanted with
    | None   -> false
    | Some i -> i >= 0

let _z3version : ref<option<z3version>> = BU.mk_ref None

let get_z3version () =
    let prefix = "Z3 version " in

    match !_z3version with
    | Some version -> version
    | None ->
        let _, out, _ = BU.run_proc (Options.z3_exe()) "-version" "" in
        let out =
            match splitlines out with
            | x :: _ when starts_with x prefix -> begin
                let x = trim_string (substring_from x (String.length prefix)) in
                let x = try List.map int_of_string (split x ".") with _ -> [] in
                match x with
                | [i1; i2; i3] -> Z3V (i1, i2, i3)
                | _ -> Z3V_Unknown out
            end
            | _ -> Z3V_Unknown out
        in
            _z3version := Some out; out

let ini_params () =
  let z3_v = get_z3version () in
  begin if z3v_le (get_z3version ()) (4, 4, 0)
  then raise <| BU.Failure (BU.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" (z3version_as_string z3_v))
  else ()
  end;
  (String.concat " "
                (List.append
                 [ "-smt2 -in auto_config=false model=true smt.relevancy=2";
                   (Util.format1 "smt.random_seed=%s" (string_of_int (Options.z3_seed()))) ]
                 (Options.z3_cliopt())))

type label = string
type unsat_core = option<list<string>>
type z3status =
    | UNSAT   of unsat_core
    | SAT     of list<label>          //error labels
    | UNKNOWN of list<label>          //error labels
    | TIMEOUT of list<label>          //error labels
    | KILLED
type z3statistics = BU.smap<string>

let status_to_string = function
    | SAT  _ -> "sat"
    | UNSAT _ -> "unsat"
    | UNKNOWN _ -> "unknown"
    | TIMEOUT _ -> "timeout"
    | KILLED -> "killed"

let tid () = BU.current_tid() |> BU.string_of_int
let new_z3proc id =
   let cond pid (s:string) =
    (let x = BU.trim_string s = "Done!" in
//     BU.print5 "On thread %s, Z3 %s (%s) says: %s\n\t%s\n" (tid()) id pid s (if x then "finished" else "waiting for more output");
     x) in
   BU.start_process id ((Options.z3_exe())) (ini_params()) cond

type bgproc = {
    grab:unit -> proc;
    release:unit -> unit;
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
    let grab () = BU.monitor_enter x; z3proc () in
    let release () = BU.monitor_exit(x) in
    let refresh () =
        let proc = grab() in
        BU.kill_process proc;
        the_z3proc := Some (new_proc ());
        query_logging.close_log();
        release() in
    let restart () =
        BU.monitor_enter();
        query_logging.close_log();
        the_z3proc := None;
        the_z3proc := Some (new_proc ());
        BU.monitor_exit() in
    {grab=grab;
     release=release;
     refresh=refresh;
     restart=restart}

let at_log_file () =
  if Options.log_queries()
  then "@" ^ (query_logging.log_file_name())
  else ""

let doZ3Exe' (fresh:bool) (input:string) : z3status * z3statistics =
  let parse (z3out:string) =
    let lines = String.split ['\n'] z3out |> List.map BU.trim_string in
    let get_data lines =
        let parse_core s : unsat_core =
            let s = BU.trim_string s in
            let s = BU.substring s 1 (String.length s - 2) in
            if BU.starts_with s "error"
            then None
            else BU.split s " " |> BU.sort_with String.compare |> Some in
        let core = BU.mk_ref None in
        let statistics : z3statistics = BU.smap_create 0 in
        let reason_unknown = BU.mk_ref "" in
        let in_core = BU.mk_ref false in
        let in_statistics = BU.mk_ref false in
        let in_reason_unknown = BU.mk_ref false in
        let parse line =
            match line with
            | "<unsat-core>" -> in_core := true
            | "<statistics>" -> in_statistics := true
            | "<reason-unknown>" -> in_reason_unknown := true
            | "</unsat-core>" -> in_core := false
            | "</statistics>" -> in_statistics := false
            | "</reason-unknown>" -> in_reason_unknown := false
            | _ ->
                if !in_core then
                    core := parse_core line
                else if !in_statistics then
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
                else if !in_reason_unknown then
                    let tkns = BU.split line "\"" in
                    let rsn = match tkns with
                    | _ :: txt :: _ :: [] -> txt
                    | _ -> line in
                    if rsn <> "unknown" then
                        BU.smap_add statistics "reason-unknown" rsn in
        List.iter (fun line -> parse line) lines ;
        !core, statistics, !reason_unknown
    in
    let rec lblnegs lines = match lines with
      | lname::"false"::rest when BU.starts_with lname "label_" -> lname::lblnegs rest
      | lname::_::rest when BU.starts_with lname "label_" -> lblnegs rest
      | _ -> [] in
    let rec result lines core = match lines with
      | "timeout"::tl -> TIMEOUT []
      | "unknown"::tl -> UNKNOWN (lblnegs tl)
      | "sat"::tl     -> SAT     (lblnegs tl)
      | "unsat"::tl   -> UNSAT   core
      | "killed"::tl  -> bg_z3_proc.restart(); KILLED
      | hd::tl ->
        FStar.Errors.warn Range.dummyRange (BU.format2 "%s: Unexpected output from Z3: %s\n" (query_logging.get_module_name()) hd);
        result tl core
      | _ -> failwith <| format1 "Unexpected output from Z3: got output lines: %s\n"
                            (String.concat "\n" (List.map (fun (l:string) -> format1 "<%s>" (BU.trim_string l)) lines)) in
    let core, statistics, reason_unknown = get_data lines in
    result lines core, statistics in

  let cond pid (s:string) =
    (let x = BU.trim_string s = "Done!" in
//     BU.print5 "On thread %s, Z3 %s (%s) says: %s\n\t%s\n" (tid()) id pid s (if x then "finished" else "waiting for more output");
     x) in
  let stdout =
    if fresh then
      BU.launch_process (tid()) ((Options.z3_exe())) (ini_params()) input cond
    else
      let proc = bg_z3_proc.grab() in
      let stdout = BU.ask_process proc input in
      bg_z3_proc.release(); stdout
  in
  parse (BU.trim_string stdout)

let doZ3Exe =
    fun (fresh:bool) (input:string) ->
        doZ3Exe' fresh input

let z3_options () =
    "(set-option :global-decls false)\n\
     (set-option :smt.mbqi false)\n\
     (set-option :auto_config false)\n\
     (set-option :produce-unsat-cores true)\n"

type job<'a> = {
    job:unit -> 'a;
    callback: 'a -> unit
}
type error_kind =
    | Timeout
    | Kill
    | Default
type z3job = job<(either<unsat_core, (error_labels * error_kind)> * int * z3statistics)>

let job_queue : ref<list<z3job>> = BU.mk_ref []

let pending_jobs = BU.mk_ref 0
let with_monitor m f =
    BU.monitor_enter(m);
    let res = f () in
    BU.monitor_exit(m);
    res

let z3_job fresh (label_messages:error_labels) input () : either<unsat_core, (error_labels * error_kind)> * int * z3statistics =
  let ekind = function
    | TIMEOUT _ -> Timeout
    | SAT _
    | UNKNOWN _ -> Default
    | KILLED -> Kill
    | _ -> failwith "Impossible" in
  let start = BU.now() in
  let status, statistics = doZ3Exe fresh input in
  let _, elapsed_time = BU.time_diff start (BU.now()) in
  let result = match status with
    | UNSAT core -> Inl core, elapsed_time, statistics
    | KILLED -> Inr ([], Kill), elapsed_time, statistics
    | TIMEOUT lblnegs
    | SAT lblnegs
    | UNKNOWN lblnegs ->
        if Options.debug_any() then print_string <| format1 "Z3 says: %s\n" (status_to_string status);
        let failing_assertions = lblnegs |> List.collect (fun l ->
        match label_messages |> List.tryFind (fun (m, _, _) -> fst m = l) with
            | None -> []
            | Some (lbl, msg, r) -> [(lbl, msg, r)]) in
        Inr (failing_assertions, ekind status), elapsed_time, statistics in
    result

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
    with_monitor job_queue (fun () -> decr pending_jobs); dequeue (); ()

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
    BU.monitor_enter job_queue;
    job_queue := !job_queue@[j];
    BU.monitor_pulse job_queue;
    BU.monitor_exit job_queue

let finish () =
    let rec aux () =
        let n, m = with_monitor job_queue (fun () -> !pending_jobs,  List.length !job_queue)  in
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
let push msg    =
    fresh_scope := [Term.Caption msg; Term.Push]::!fresh_scope;
    bg_scope := !bg_scope @ [Term.Push; Term.Caption msg]

let pop msg      =
    fresh_scope := List.tl !fresh_scope;
    bg_scope := !bg_scope @ [Term.Caption msg; Term.Pop]

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
        bg_z3_proc.refresh();
        bg_scope := List.flatten (List.rev !fresh_scope)

//mark, reset_mark, commit_mark:
//    setting rollback points for the interactive mode
// JP: I suspect the expected usage for the interactive mode is as follows:
// - the stack (fresh_scope) has size >= 1, the top scope contains the queries
//   that have been successful so far
// - one calls "mark" to push a new scope of tentative queries
// - in case of success, the new scope is collapsed with the previous scope,
//   effectively bringing the new queries into the scope of successful queries so far
// - in case of failure, the new scope is discarded
let mark msg =
    push msg
let reset_mark msg =
    // JP: pop_context (in universal.fs) does the same thing: it calls pop,
    // followed by refresh
    pop msg;
    refresh ()
let commit_mark (msg:string) =
    begin match !fresh_scope with
        | hd::s::tl -> fresh_scope := (hd@s)::tl
        | _ -> failwith "Impossible"
    end

let mk_cb used_unsat_core cb (uc_errs, time, statistics) =
    if used_unsat_core
    then match uc_errs with
        | Inl _ -> cb (uc_errs, time, statistics)
        | Inr (_, ek) -> cb (Inr ([],ek), time, statistics) // if we filtered the theory, then the error message is unreliable
    else cb (uc_errs, time, statistics)

let mk_input theory =
    let r = List.map (declToSmt (z3_options ())) theory |> String.concat "\n" in
    if Options.log_queries() then query_logging.write_to_log r ;
    r

type z3result =
    either<unsat_core, (error_labels*error_kind)>
    * int
    * z3statistics
type cb = z3result -> unit

let ask_1_core
    (filter_theory:decls_t -> decls_t * bool)
    (label_messages:error_labels)
    (qry:decls_t)
    (cb: cb)
  = let theory = !bg_scope@[Term.Push]@qry@[Term.Pop] in
    let theory, used_unsat_core = filter_theory theory in
    let cb = mk_cb used_unsat_core cb in
    let input = mk_input theory in
    bg_scope := [] ; // Now consumed.
    run_job ({job=z3_job false label_messages input; callback=cb})

let ask_n_cores
    (filter_theory:decls_t -> decls_t * bool)
    (label_messages:error_labels)
    (qry:decls_t)
    (scope:option<scope_t>)
    (cb:cb)
  = let theory = List.flatten (match scope with
        | Some s -> (List.rev s)
        | None   -> bg_scope := [] ; // Not needed; discard.
                    (List.rev !fresh_scope)) in
    let theory = theory@[Term.Push]@qry@[Term.Pop] in
    let theory, used_unsat_core = filter_theory theory in
    let cb = mk_cb used_unsat_core cb in
    let input = mk_input theory in
    enqueue ({job=z3_job true label_messages input; callback=cb})

let ask
    (filter:decls_t -> decls_t * bool)
    (label_messages:error_labels)
    (qry:decls_t)
    (scope:option<scope_t>)
    (cb:cb)
  = if Options.n_cores() = 1 then
        ask_1_core filter label_messages qry cb
    else
        ask_n_cores filter label_messages qry scope cb

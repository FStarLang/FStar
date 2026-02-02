open Prims
type z3status =
  | UNSAT of FStarC_SMTEncoding_UnsatCore.unsat_core
  FStar_Pervasives_Native.option 
  | SAT of (FStarC_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | UNKNOWN of (FStarC_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | TIMEOUT of (FStarC_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | KILLED 
let uu___is_UNSAT (projectee : z3status) : Prims.bool=
  match projectee with | UNSAT _0 -> true | uu___ -> false
let __proj__UNSAT__item___0 (projectee : z3status) :
  FStarC_SMTEncoding_UnsatCore.unsat_core FStar_Pervasives_Native.option=
  match projectee with | UNSAT _0 -> _0
let uu___is_SAT (projectee : z3status) : Prims.bool=
  match projectee with | SAT _0 -> true | uu___ -> false
let __proj__SAT__item___0 (projectee : z3status) :
  (FStarC_SMTEncoding_Term.error_labels * Prims.string
    FStar_Pervasives_Native.option)=
  match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN (projectee : z3status) : Prims.bool=
  match projectee with | UNKNOWN _0 -> true | uu___ -> false
let __proj__UNKNOWN__item___0 (projectee : z3status) :
  (FStarC_SMTEncoding_Term.error_labels * Prims.string
    FStar_Pervasives_Native.option)=
  match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT (projectee : z3status) : Prims.bool=
  match projectee with | TIMEOUT _0 -> true | uu___ -> false
let __proj__TIMEOUT__item___0 (projectee : z3status) :
  (FStarC_SMTEncoding_Term.error_labels * Prims.string
    FStar_Pervasives_Native.option)=
  match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED (projectee : z3status) : Prims.bool=
  match projectee with | KILLED -> true | uu___ -> false
type z3statistics = Prims.string FStarC_SMap.t
type z3result =
  {
  z3result_status: z3status ;
  z3result_time: Prims.int ;
  z3result_initial_statistics: z3statistics ;
  z3result_statistics: z3statistics ;
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option ;
  z3result_log_file: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkz3result__item__z3result_status (projectee : z3result) :
  z3status=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_status
let __proj__Mkz3result__item__z3result_time (projectee : z3result) :
  Prims.int=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_time
let __proj__Mkz3result__item__z3result_initial_statistics
  (projectee : z3result) : z3statistics=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_initial_statistics
let __proj__Mkz3result__item__z3result_statistics (projectee : z3result) :
  z3statistics=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_statistics
let __proj__Mkz3result__item__z3result_query_hash (projectee : z3result) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_query_hash
let __proj__Mkz3result__item__z3result_log_file (projectee : z3result) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { z3result_status; z3result_time; z3result_initial_statistics;
      z3result_statistics; z3result_query_hash; z3result_log_file;_} ->
      z3result_log_file
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.bool -> Prims.string -> Prims.string ;
  append_to_log: Prims.string -> Prims.string ;
  close_log: unit -> unit }
let __proj__Mkquery_log__item__get_module_name (projectee : query_log) :
  unit -> Prims.string=
  match projectee with
  | { get_module_name; set_module_name; write_to_log; append_to_log;
      close_log;_} -> get_module_name
let __proj__Mkquery_log__item__set_module_name (projectee : query_log) :
  Prims.string -> unit=
  match projectee with
  | { get_module_name; set_module_name; write_to_log; append_to_log;
      close_log;_} -> set_module_name
let __proj__Mkquery_log__item__write_to_log (projectee : query_log) :
  Prims.bool -> Prims.string -> Prims.string=
  match projectee with
  | { get_module_name; set_module_name; write_to_log; append_to_log;
      close_log;_} -> write_to_log
let __proj__Mkquery_log__item__append_to_log (projectee : query_log) :
  Prims.string -> Prims.string=
  match projectee with
  | { get_module_name; set_module_name; write_to_log; append_to_log;
      close_log;_} -> append_to_log
let __proj__Mkquery_log__item__close_log (projectee : query_log) :
  unit -> unit=
  match projectee with
  | { get_module_name; set_module_name; write_to_log; append_to_log;
      close_log;_} -> close_log
let _already_warned_solver_mismatch : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
let _already_warned_version_mismatch : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
type label = Prims.string
let status_tag (uu___ : z3status) : Prims.string=
  match uu___ with
  | SAT uu___1 -> "sat"
  | UNSAT uu___1 -> "unsat"
  | UNKNOWN uu___1 -> "unknown"
  | TIMEOUT uu___1 -> "timeout"
  | KILLED -> "killed"
let status_string_and_errors (s : z3status) :
  (Prims.string * FStarC_SMTEncoding_Term.error_labels)=
  match s with
  | KILLED -> ((status_tag s), [])
  | UNSAT uu___ -> ((status_tag s), [])
  | SAT (errs, msg) ->
      let uu___ =
        FStarC_Format.fmt2 "%s%s" (status_tag s)
          (match msg with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some msg1 ->
               Prims.strcat " because " msg1) in
      (uu___, errs)
  | UNKNOWN (errs, msg) ->
      let uu___ =
        FStarC_Format.fmt2 "%s%s" (status_tag s)
          (match msg with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some msg1 ->
               Prims.strcat " because " msg1) in
      (uu___, errs)
  | TIMEOUT (errs, msg) ->
      let uu___ =
        FStarC_Format.fmt2 "%s%s" (status_tag s)
          (match msg with
           | FStar_Pervasives_Native.None -> ""
           | FStar_Pervasives_Native.Some msg1 ->
               Prims.strcat " because " msg1) in
      (uu___, errs)
let query_logging : query_log=
  let query_number = FStarC_Effect.mk_ref Prims.int_zero in
  let log_file_opt = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStarC_Effect.mk_ref [] in
  let current_module_name = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let current_file_name = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n =
    FStarC_Effect.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n) in
  let get_module_name uu___ =
    let uu___1 = FStarC_Effect.op_Bang current_module_name in
    match uu___1 with
    | FStar_Pervasives_Native.None -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n -> n in
  let next_file_name uu___ =
    let n = get_module_name () in
    let file_name =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang used_file_names in
        FStarC_List.tryFind
          (fun uu___3 -> match uu___3 with | (m, uu___4) -> n = m) uu___2 in
      match uu___1 with
      | FStar_Pervasives_Native.None ->
          ((let uu___3 =
              let uu___4 = FStarC_Effect.op_Bang used_file_names in
              (n, Prims.int_zero) :: uu___4 in
            FStarC_Effect.op_Colon_Equals used_file_names uu___3);
           n)
      | FStar_Pervasives_Native.Some (uu___2, k) ->
          ((let uu___4 =
              let uu___5 = FStarC_Effect.op_Bang used_file_names in
              (n, (k + Prims.int_one)) :: uu___5 in
            FStarC_Effect.op_Colon_Equals used_file_names uu___4);
           (let uu___4 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int
                (k + Prims.int_one) in
            FStarC_Format.fmt2 "%s-%s" n uu___4)) in
    FStarC_Format.fmt1 "queries-%s.smt2" file_name in
  let new_log_file uu___ =
    let file_name = next_file_name () in
    FStarC_Effect.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let c = FStarC_Util.open_file_for_writing file_name in
     FStarC_Effect.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (c, file_name));
     (c, file_name)) in
  let get_log_file uu___ =
    let uu___1 = FStarC_Effect.op_Bang log_file_opt in
    match uu___1 with
    | FStar_Pervasives_Native.None -> new_log_file ()
    | FStar_Pervasives_Native.Some c -> c in
  let append_to_log str =
    let uu___ = get_log_file () in
    match uu___ with | (f, nm) -> (FStarC_Util.append_to_file f str; nm) in
  let write_to_new_log str =
    let file_name = next_file_name () in
    FStarC_Util.write_file file_name str; file_name in
  let write_to_log fresh str =
    if fresh then write_to_new_log str else append_to_log str in
  let close_log uu___ =
    let uu___1 = FStarC_Effect.op_Bang log_file_opt in
    match uu___1 with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some (c, uu___2) ->
        (FStarC_Util.close_out_channel c;
         FStarC_Effect.op_Colon_Equals log_file_opt
           FStar_Pervasives_Native.None) in
  let log_file_name uu___ =
    let uu___1 = FStarC_Effect.op_Bang current_file_name in
    match uu___1 with
    | FStar_Pervasives_Native.None -> failwith "no log file"
    | FStar_Pervasives_Native.Some n -> n in
  { get_module_name; set_module_name; write_to_log; append_to_log; close_log
  }
let z3_cmd_and_args (uu___ : unit) :
  (Prims.string * Prims.string Prims.list)=
  let ver = FStarC_Options.z3_version () in
  let cmd =
    let uu___1 = FStarC_Find_Z3.locate_z3 ver in
    match uu___1 with
    | FStar_Pervasives_Native.Some fn -> fn
    | FStar_Pervasives_Native.None ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Errors_Msg.text "Z3 solver not found." in
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Errors_Msg.text "Required version: " in
                FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___7
                  (FStar_Pprint.doc_of_string ver) in
              [uu___6] in
            uu___4 :: uu___5 in
          let uu___4 = FStarC_Find_Z3.z3_install_suggestion ver in
          FStarC_List.op_At uu___3 uu___4 in
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_Z3InvocationError ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___2) in
  let cmd_args =
    let uu___1 = FStarC_Options.z3_cliopt () in
    FStarC_List.append ["-smt2"; "-in"] uu___1 in
  (cmd, cmd_args)
let warn_handler (suf : FStarC_Errors_Msg.error_message) (s : Prims.string) :
  unit=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Errors_Msg.text "Unexpected output from Z3:" in
        FStar_Pprint.op_Hat_Hat uu___3
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
             (FStar_Pprint.op_Hat_Hat (FStar_Pprint.blank (Prims.of_int (2)))
                (FStar_Pprint.align
                   (FStar_Pprint.dquotes (FStar_Pprint.arbitrary_string s))))) in
      [uu___2] in
    FStarC_List.op_At uu___1 suf in
  FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_UnexpectedZ3Output ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc) (Obj.magic uu___)
let check_z3version (p : FStarC_Util.proc) : unit=
  let getinfo arg =
    let s =
      let uu___ = FStarC_Format.fmt1 "(get-info :%s)\n(echo \"Done!\")\n" arg in
      FStarC_Util.ask_process p uu___ (fun uu___1 -> "Killed")
        (warn_handler []) in
    if FStarC_Util.starts_with s (Prims.strcat "(:" arg)
    then
      let ss = FStarC_String.split [34] s in FStarC_List.nth ss Prims.int_one
    else
      (warn_handler [] s;
       (let uu___2 =
          let uu___3 = FStarC_Util.proc_prog p in
          FStarC_Format.fmt1 "Could not run Z3 from `%s'" uu___3 in
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_Z3InvocationError ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___2))) in
  let name = getinfo "name" in
  (let uu___1 =
     (name <> "Z3") &&
       (let uu___2 = FStarC_Effect.op_Bang _already_warned_solver_mismatch in
        Prims.op_Negation uu___2) in
   if uu___1
   then
     ((let uu___3 =
         let uu___4 =
           let uu___5 =
             let uu___6 =
               FStarC_Format.fmt1
                 "Unexpected SMT solver: expected to be talking to Z3, got %s."
                 name in
             FStarC_Errors_Msg.text uu___6 in
           [uu___5] in
         let uu___5 =
           let uu___6 = FStarC_Options.z3_version () in
           FStarC_Find_Z3.z3_install_suggestion uu___6 in
         FStarC_List.op_At uu___4 uu___5 in
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_SolverMismatch ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic uu___3));
      FStarC_Effect.op_Colon_Equals _already_warned_solver_mismatch true)
   else ());
  (let ver_found =
     let uu___1 =
       let uu___2 =
         let uu___3 = getinfo "version" in FStarC_Util.split uu___3 "-" in
       FStarC_List.hd uu___2 in
     FStarC_Util.trim_string uu___1 in
   let ver_conf =
     let uu___1 = FStarC_Options.z3_version () in
     FStarC_Util.trim_string uu___1 in
   let uu___2 =
     (ver_conf <> ver_found) &&
       (let uu___3 = FStarC_Effect.op_Bang _already_warned_version_mismatch in
        Prims.op_Negation uu___3) in
   if uu___2
   then
     ((let uu___4 =
         let uu___5 =
           let uu___6 =
             let uu___7 =
               let uu___8 = FStarC_Util.proc_prog p in
               FStarC_Format.fmt3
                 "Unexpected Z3 version for '%s': expected '%s', got '%s'."
                 uu___8 ver_conf ver_found in
             FStarC_Errors_Msg.text uu___7 in
           [uu___6] in
         let uu___6 = FStarC_Find_Z3.z3_install_suggestion ver_conf in
         FStarC_List.op_At uu___5 uu___6 in
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_SolverMismatch ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
         (Obj.magic uu___4));
      FStarC_Errors.stop_if_err ();
      FStarC_Effect.op_Colon_Equals _already_warned_version_mismatch true)
   else ())
let new_z3proc (id : Prims.string)
  (cmd_and_args : (Prims.string * Prims.string Prims.list)) :
  FStarC_Util.proc=
  let proc =
    try
      (fun uu___ ->
         match () with
         | () ->
             FStarC_Util.start_process id
               (FStar_Pervasives_Native.fst cmd_and_args)
               (FStar_Pervasives_Native.snd cmd_and_args)
               (fun s -> s = "Done!")) ()
    with
    | uu___ ->
        let uu___1 =
          let uu___2 =
            FStarC_Errors_Msg.text "Could not start SMT solver process." in
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Errors_Msg.text "Command:" in
              FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___5
                (FStar_Pprint.squotes
                   (FStar_Pprint.arbitrary_string
                      (FStar_Pervasives_Native.fst cmd_and_args))) in
            let uu___5 =
              let uu___6 =
                let uu___7 = FStarC_Errors_Msg.text "Exception:" in
                let uu___8 =
                  let uu___9 = FStarC_Util.print_exn uu___ in
                  FStar_Pprint.arbitrary_string uu___9 in
                FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one uu___7
                  uu___8 in
              [uu___6] in
            uu___4 :: uu___5 in
          uu___2 :: uu___3 in
        FStarC_Errors.raise_error0
          FStarC_Errors_Codes.Error_Z3InvocationError ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic uu___1) in
  check_z3version proc; proc
let new_z3proc_with_id :
  (Prims.string * Prims.string Prims.list) -> FStarC_Util.proc=
  let ctr = FStarC_Effect.mk_ref (Prims.of_int (-1)) in
  fun cmd_and_args ->
    let p =
      let uu___ =
        let uu___1 =
          FStarC_Util.incr ctr;
          (let uu___3 = FStarC_Effect.op_Bang ctr in
           FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___3) in
        FStarC_Format.fmt1 "z3-bg-%s" uu___1 in
      new_z3proc uu___ cmd_and_args in
    p
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit ;
  version: unit -> Prims.string ;
  ctxt: FStarC_SMTEncoding_SolverState.solver_state }
let __proj__Mkbgproc__item__ask (projectee : bgproc) :
  Prims.string -> Prims.string=
  match projectee with | { ask; refresh; restart; version; ctxt;_} -> ask
let __proj__Mkbgproc__item__refresh (projectee : bgproc) : unit -> unit=
  match projectee with | { ask; refresh; restart; version; ctxt;_} -> refresh
let __proj__Mkbgproc__item__restart (projectee : bgproc) : unit -> unit=
  match projectee with | { ask; refresh; restart; version; ctxt;_} -> restart
let __proj__Mkbgproc__item__version (projectee : bgproc) :
  unit -> Prims.string=
  match projectee with | { ask; refresh; restart; version; ctxt;_} -> version
let __proj__Mkbgproc__item__ctxt (projectee : bgproc) :
  FStarC_SMTEncoding_SolverState.solver_state=
  match projectee with | { ask; refresh; restart; version; ctxt;_} -> ctxt
let bg_z3_proc : bgproc FStarC_Effect.ref=
  let the_z3proc = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let the_z3proc_params =
    FStarC_Effect.mk_ref (FStar_Pervasives_Native.Some ("", [""])) in
  let the_z3proc_ask_count = FStarC_Effect.mk_ref Prims.int_zero in
  let the_z3proc_version = FStarC_Effect.mk_ref "" in
  let make_new_z3_proc cmd_and_args =
    (let uu___1 = FStarC_Options.hint_info () in
     if uu___1
     then
       let uu___2 =
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_string
              (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string))
           cmd_and_args in
       let uu___3 =
         let uu___4 = FStarC_Options.z3_version () in
         FStarC_Class_Show.show FStarC_Class_Show.showable_string uu___4 in
       FStarC_Format.print2 "Creating new z3proc (cmd=[%s], version=[%s])\n"
         uu___2 uu___3
     else ());
    (let uu___2 =
       let uu___3 = new_z3proc_with_id cmd_and_args in
       FStar_Pervasives_Native.Some uu___3 in
     FStarC_Effect.op_Colon_Equals the_z3proc uu___2);
    FStarC_Effect.op_Colon_Equals the_z3proc_params
      (FStar_Pervasives_Native.Some cmd_and_args);
    FStarC_Effect.op_Colon_Equals the_z3proc_ask_count Prims.int_zero in
  (let uu___1 = FStarC_Options.z3_version () in
   FStarC_Effect.op_Colon_Equals the_z3proc_version uu___1);
  (let z3proc uu___1 =
     (let uu___3 =
        let uu___4 = FStarC_Effect.op_Bang the_z3proc in
        uu___4 = FStar_Pervasives_Native.None in
      if uu___3
      then let uu___4 = z3_cmd_and_args () in make_new_z3_proc uu___4
      else ());
     (let uu___3 = FStarC_Effect.op_Bang the_z3proc in
      FStarC_Option.must uu___3) in
   let ask input =
     FStarC_Util.incr the_z3proc_ask_count;
     (let kill_handler uu___2 = "\nkilled\n" in
      let uu___2 = z3proc () in
      FStarC_Util.ask_process uu___2 input kill_handler (warn_handler [])) in
   let maybe_kill_z3proc uu___1 =
     let uu___2 =
       let uu___3 = FStarC_Effect.op_Bang the_z3proc in
       uu___3 <> FStar_Pervasives_Native.None in
     if uu___2
     then
       let old_params =
         let uu___3 = FStarC_Effect.op_Bang the_z3proc_params in
         FStarC_Option.must uu___3 in
       let old_version = FStarC_Effect.op_Bang the_z3proc_version in
       ((let uu___4 = FStarC_Options.hint_info () in
         if uu___4
         then
           let uu___5 =
             let uu___6 = FStarC_Effect.op_Bang the_z3proc_ask_count in
             FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___6 in
           let uu___6 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_tuple2
                  FStarC_Class_Show.showable_string
                  (FStarC_Class_Show.show_list
                     FStarC_Class_Show.showable_string)) old_params in
           FStarC_Format.print2
             "Killing old z3proc (ask_count=%s, old_cmd=[%s])\n" uu___5
             uu___6
         else ());
        (let uu___5 =
           let uu___6 = FStarC_Effect.op_Bang the_z3proc in
           FStarC_Option.must uu___6 in
         FStarC_Util.kill_process uu___5);
        FStarC_Effect.op_Colon_Equals the_z3proc_ask_count Prims.int_zero;
        FStarC_Effect.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None)
     else () in
   let refresh uu___1 = maybe_kill_z3proc (); query_logging.close_log () in
   let restart uu___1 =
     maybe_kill_z3proc ();
     query_logging.close_log ();
     (let next_params = z3_cmd_and_args () in make_new_z3_proc next_params) in
   let x = [] in
   let uu___1 =
     let uu___2 = FStarC_SMTEncoding_SolverState.init () in
     {
       ask = (FStarC_Util.with_monitor x ask);
       refresh = (FStarC_Util.with_monitor x refresh);
       restart = (FStarC_Util.with_monitor x restart);
       version = (fun uu___3 -> FStarC_Effect.op_Bang the_z3proc_version);
       ctxt = uu___2
     } in
   FStarC_Effect.mk_ref uu___1)
type smt_output_section = Prims.string Prims.list
type smt_output =
  {
  smt_result: smt_output_section ;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option ;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option ;
  smt_initial_statistics: smt_output_section FStar_Pervasives_Native.option ;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option ;
  smt_labels: smt_output_section FStar_Pervasives_Native.option }
let __proj__Mksmt_output__item__smt_result (projectee : smt_output) :
  smt_output_section=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_result
let __proj__Mksmt_output__item__smt_reason_unknown (projectee : smt_output) :
  smt_output_section FStar_Pervasives_Native.option=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_reason_unknown
let __proj__Mksmt_output__item__smt_unsat_core (projectee : smt_output) :
  smt_output_section FStar_Pervasives_Native.option=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_unsat_core
let __proj__Mksmt_output__item__smt_initial_statistics
  (projectee : smt_output) :
  smt_output_section FStar_Pervasives_Native.option=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_initial_statistics
let __proj__Mksmt_output__item__smt_statistics (projectee : smt_output) :
  smt_output_section FStar_Pervasives_Native.option=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_statistics
let __proj__Mksmt_output__item__smt_labels (projectee : smt_output) :
  smt_output_section FStar_Pervasives_Native.option=
  match projectee with
  | { smt_result; smt_reason_unknown; smt_unsat_core; smt_initial_statistics;
      smt_statistics; smt_labels;_} -> smt_labels
let parse_stats
  (smt_stats : smt_output_section FStar_Pervasives_Native.option) :
  z3statistics=
  let statistics = FStarC_SMap.create Prims.int_zero in
  match smt_stats with
  | FStar_Pervasives_Native.None -> statistics
  | FStar_Pervasives_Native.Some lines ->
      let parse_line line =
        let pline = FStarC_Util.split (FStarC_Util.trim_string line) ":" in
        match pline with
        | "("::entry::[] ->
            let tokens = FStarC_Util.split entry " " in
            let key = FStarC_List.hd tokens in
            let ltok =
              FStarC_List.nth tokens
                ((FStarC_List.length tokens) - Prims.int_one) in
            let value =
              if FStarC_Util.ends_with ltok ")"
              then
                FStarC_Util.substring ltok Prims.int_zero
                  ((FStarC_String.length ltok) - Prims.int_one)
              else ltok in
            FStarC_SMap.add statistics key value
        | ""::entry::[] ->
            let tokens = FStarC_Util.split entry " " in
            let key = FStarC_List.hd tokens in
            let ltok =
              FStarC_List.nth tokens
                ((FStarC_List.length tokens) - Prims.int_one) in
            let value =
              if FStarC_Util.ends_with ltok ")"
              then
                FStarC_Util.substring ltok Prims.int_zero
                  ((FStarC_String.length ltok) - Prims.int_one)
              else ltok in
            FStarC_SMap.add statistics key value
        | uu___ -> () in
      (FStarC_List.iter parse_line lines; statistics)
let smt_output_sections
  (log_file : Prims.string FStar_Pervasives_Native.option)
  (r : FStarC_Range_Type.t) (lines : Prims.string Prims.list) : smt_output=
  let rec until tag lines1 =
    match lines1 with
    | [] -> FStar_Pervasives_Native.None
    | l::lines2 ->
        if tag = l
        then FStar_Pervasives_Native.Some ([], lines2)
        else
          (let uu___1 = until tag lines2 in
           FStarC_Option.map
             (fun uu___2 ->
                match uu___2 with
                | (until_tag, rest) -> ((l :: until_tag), rest)) uu___1) in
  let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
  let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
  let find_section tag lines1 =
    let uu___ = until (start_tag tag) lines1 in
    match uu___ with
    | FStar_Pervasives_Native.None -> (FStar_Pervasives_Native.None, lines1)
    | FStar_Pervasives_Native.Some (prefix, suffix) ->
        let uu___1 = until (end_tag tag) suffix in
        (match uu___1 with
         | FStar_Pervasives_Native.None ->
             failwith
               (Prims.strcat "Parse error: "
                  (Prims.strcat (end_tag tag) " not found"))
         | FStar_Pervasives_Native.Some (section, suffix1) ->
             ((FStar_Pervasives_Native.Some section),
               (FStarC_List.op_At prefix suffix1))) in
  let uu___ = find_section "initial_stats" lines in
  match uu___ with
  | (initial_stats_opt, lines1) ->
      let uu___1 = find_section "result" lines1 in
      (match uu___1 with
       | (result_opt, lines2) ->
           let result =
             match result_opt with
             | FStar_Pervasives_Native.None ->
                 let uu___2 =
                   FStarC_Format.fmt1
                     "Unexpected output from Z3: no result section found:\n%s"
                     (FStarC_String.concat "\n" lines2) in
                 failwith uu___2
             | FStar_Pervasives_Native.Some result1 -> result1 in
           let uu___2 = find_section "reason-unknown" lines2 in
           (match uu___2 with
            | (reason_unknown, lines3) ->
                let uu___3 = find_section "unsat-core" lines3 in
                (match uu___3 with
                 | (unsat_core, lines4) ->
                     let uu___4 = find_section "statistics" lines4 in
                     (match uu___4 with
                      | (statistics, lines5) ->
                          let uu___5 = find_section "labels" lines5 in
                          (match uu___5 with
                           | (labels, lines6) ->
                               let remaining =
                                 let uu___6 = until "Done!" lines6 in
                                 match uu___6 with
                                 | FStar_Pervasives_Native.None -> lines6
                                 | FStar_Pervasives_Native.Some
                                     (prefix, suffix) ->
                                     FStarC_List.op_At prefix suffix in
                               ((match remaining with
                                 | [] -> ()
                                 | uu___7 ->
                                     let msg =
                                       FStarC_String.concat "\n" remaining in
                                     let suf =
                                       match log_file with
                                       | FStar_Pervasives_Native.Some
                                           log_file1 ->
                                           let uu___8 =
                                             let uu___9 =
                                               FStarC_Errors_Msg.text
                                                 "Log file:" in
                                             FStar_Pprint.op_Hat_Slash_Hat
                                               uu___9
                                               (FStar_Pprint.doc_of_string
                                                  log_file1) in
                                           [uu___8]
                                       | FStar_Pervasives_Native.None -> [] in
                                     warn_handler suf msg);
                                {
                                  smt_result =
                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                       result_opt);
                                  smt_reason_unknown = reason_unknown;
                                  smt_unsat_core = unsat_core;
                                  smt_initial_statistics = initial_stats_opt;
                                  smt_statistics = statistics;
                                  smt_labels = labels
                                }))))))
let with_solver_state
  (f :
    FStarC_SMTEncoding_SolverState.solver_state ->
      ('a * FStarC_SMTEncoding_SolverState.solver_state))
  : 'a=
  let ss = FStarC_Effect.op_Bang bg_z3_proc in
  let uu___ = f ss.ctxt in
  match uu___ with
  | (res, ctxt) ->
      (FStarC_Effect.op_Colon_Equals bg_z3_proc
         {
           ask = (ss.ask);
           refresh = (ss.refresh);
           restart = (ss.restart);
           version = (ss.version);
           ctxt
         };
       res)
let with_solver_state_unit
  (f :
    FStarC_SMTEncoding_SolverState.solver_state ->
      FStarC_SMTEncoding_SolverState.solver_state)
  : unit= with_solver_state (fun x -> let uu___ = f x in ((), uu___))
let reading_solver_state
  (f : FStarC_SMTEncoding_SolverState.solver_state -> 'a) : 'a=
  let ss = FStarC_Effect.op_Bang bg_z3_proc in f ss.ctxt
let push (msg : Prims.string) : unit=
  with_solver_state_unit FStarC_SMTEncoding_SolverState.push;
  with_solver_state_unit
    (FStarC_SMTEncoding_SolverState.give
       [FStarC_SMTEncoding_Term.Caption msg])
let pop (msg : Prims.string) : unit=
  with_solver_state_unit
    (FStarC_SMTEncoding_SolverState.give
       [FStarC_SMTEncoding_Term.Caption msg]);
  with_solver_state_unit FStarC_SMTEncoding_SolverState.pop
let snapshot (msg : Prims.string) : Prims.int=
  let d = reading_solver_state FStarC_SMTEncoding_SolverState.depth in
  push msg; d
let rollback (msg : Prims.string)
  (depth : Prims.int FStar_Pervasives_Native.option) : unit=
  let rec rollback_aux msg1 depth1 =
    let d = reading_solver_state FStarC_SMTEncoding_SolverState.depth in
    match depth1 with
    | FStar_Pervasives_Native.None -> pop msg1
    | FStar_Pervasives_Native.Some n ->
        if d = n then () else (pop msg1; rollback_aux msg1 depth1) in
  rollback_aux msg depth
let start_query (msg : Prims.string)
  (roots_to_push : FStarC_SMTEncoding_Term.decl Prims.list)
  (qry : FStarC_SMTEncoding_Term.decl) : unit=
  with_solver_state_unit
    (FStarC_SMTEncoding_SolverState.start_query msg roots_to_push qry)
let finish_query (msg : Prims.string) : unit=
  with_solver_state_unit (FStarC_SMTEncoding_SolverState.finish_query msg)
let giveZ3 (decls : FStarC_SMTEncoding_Term.decl Prims.list) : unit=
  with_solver_state_unit (FStarC_SMTEncoding_SolverState.give decls)
let refresh
  (using_facts_from :
    FStarC_SMTEncoding_SolverState.using_facts_from_setting
      FStar_Pervasives_Native.option)
  : unit=
  (let uu___1 = FStarC_Effect.op_Bang bg_z3_proc in uu___1.refresh ());
  with_solver_state_unit
    (FStarC_SMTEncoding_SolverState.reset using_facts_from)
let stop (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang bg_z3_proc in uu___1.refresh ()
let doZ3Exe (log_file : Prims.string FStar_Pervasives_Native.option)
  (r : FStarC_Range_Type.t) (fresh : Prims.bool) (input : Prims.string)
  (label_messages : FStarC_SMTEncoding_Term.error_labels)
  (queryid : Prims.string) : (z3status * z3statistics * z3statistics)=
  let parse z3out =
    let lines =
      FStarC_List.map FStarC_Util.trim_string
        (FStarC_String.split [10] z3out) in
    let smt_output1 = smt_output_sections log_file r lines in
    let unsat_core =
      match smt_output1.smt_unsat_core with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some s ->
          let s1 = FStarC_Util.trim_string (FStarC_String.concat " " s) in
          let s2 =
            FStarC_Util.substring s1 Prims.int_one
              ((FStarC_String.length s1) - (Prims.of_int (2))) in
          if FStarC_Util.starts_with s2 "error"
          then FStar_Pervasives_Native.None
          else
            (let uu___1 =
               FStarC_Util.sort_with FStarC_String.compare
                 (FStarC_Util.split s2 " ") in
             FStar_Pervasives_Native.Some uu___1) in
    let labels =
      match smt_output1.smt_labels with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some lines1 ->
          let rec lblnegs lines2 =
            match lines2 with
            | lname::"false"::rest when
                FStarC_Util.starts_with lname "label_" ->
                let uu___ = lblnegs rest in lname :: uu___
            | lname::uu___::rest when FStarC_Util.starts_with lname "label_"
                -> lblnegs rest
            | uu___ -> [] in
          let lblnegs1 = lblnegs lines1 in
          FStarC_List.collect
            (fun l ->
               let uu___ =
                 FStarC_List.tryFind
                   (fun uu___1 ->
                      match uu___1 with
                      | (m, uu___2, uu___3) ->
                          let uu___4 = FStarC_SMTEncoding_Term.fv_name m in
                          uu___4 = l) label_messages in
               match uu___ with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some (lbl, msg, r1) ->
                   [(lbl, msg, r1)]) lblnegs1 in
    let initial_statistics = parse_stats smt_output1.smt_initial_statistics in
    let statistics = parse_stats smt_output1.smt_statistics in
    let reason_unknown =
      FStarC_Option.map
        (fun x ->
           let ru = FStarC_String.concat " " x in
           if FStarC_Util.starts_with ru "(:reason-unknown \""
           then
             let reason =
               FStarC_Util.substring_from ru
                 (FStarC_String.length "(:reason-unknown \"") in
             let res =
               FStarC_String.substring reason Prims.int_zero
                 ((FStarC_String.length reason) - (Prims.of_int (2))) in
             res
           else ru) smt_output1.smt_reason_unknown in
    let status =
      (let uu___1 = FStarC_Debug.any () in
       if uu___1
       then
         FStarC_Format.print1 "Z3 says: %s\n"
           (FStarC_String.concat "\n" smt_output1.smt_result)
       else ());
      (match smt_output1.smt_result with
       | "unsat"::[] -> UNSAT unsat_core
       | "sat"::[] -> SAT (labels, reason_unknown)
       | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
       | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
       | "killed"::[] ->
           ((let uu___2 = FStarC_Effect.op_Bang bg_z3_proc in
             uu___2.restart ());
            KILLED)
       | uu___1 ->
           let uu___2 =
             FStarC_Format.fmt1
               "Unexpected output from Z3: got output result: %s\n"
               (FStarC_String.concat "\n" smt_output1.smt_result) in
           failwith uu___2) in
    (status, initial_statistics, statistics) in
  let log_result fwrite uu___ =
    match uu___ with
    | (res, _initial_stats, _stats) ->
        ((match log_file with
          | FStar_Pervasives_Native.Some fname ->
              (fwrite fname (Prims.strcat "; QUERY ID: " queryid);
               (let uu___4 =
                  let uu___5 =
                    let uu___6 = status_string_and_errors res in
                    FStar_Pervasives_Native.fst uu___6 in
                  Prims.strcat "; STATUS: " uu___5 in
                fwrite fname uu___4);
               (match res with
                | UNSAT (FStar_Pervasives_Native.Some core) ->
                    fwrite fname
                      (Prims.strcat "; UNSAT CORE GENERATED: "
                         (FStarC_String.concat ", " core))
                | uu___4 -> ()))
          | FStar_Pervasives_Native.None -> ());
         (let log_file_name =
            match log_file with
            | FStar_Pervasives_Native.Some fname -> fname
            | uu___2 -> "<nofile>" in
          let uu___3 =
            let uu___4 =
              reading_solver_state
                FStarC_SMTEncoding_SolverState.would_have_pruned in
            (uu___4, res) in
          match uu___3 with
          | (FStar_Pervasives_Native.Some names, UNSAT
             (FStar_Pervasives_Native.Some core)) ->
              let whitelist =
                ["BoxInt";
                "BoxBool";
                "BoxString";
                "BoxReal";
                "Tm_unit";
                "FString_const"] in
              let missing =
                FStarC_List.filter
                  (fun name ->
                     (((((let uu___4 =
                            FStarC_Util.for_some
                              (fun wl -> FStarC_Util.contains name wl)
                              whitelist in
                          Prims.op_Negation uu___4) &&
                           (Prims.op_Negation
                              (FStarC_Util.starts_with name "binder_")))
                          &&
                          (Prims.op_Negation
                             (FStarC_Util.starts_with name "@query")))
                         &&
                         (Prims.op_Negation
                            (FStarC_Util.starts_with name "@MaxFuel")))
                        &&
                        (Prims.op_Negation
                           (FStarC_Util.starts_with name "@MaxIFuel")))
                       &&
                       (let uu___4 =
                          FStarC_Util.for_some (fun name' -> name = name')
                            names in
                        Prims.op_Negation uu___4)) core in
              (match missing with
               | [] -> ()
               | uu___4 ->
                   FStarC_Format.print3
                     "Query %s (%s): Pruned theory would miss %s\n" queryid
                     log_file_name (FStarC_String.concat ", " missing))
          | uu___4 -> ())) in
  if fresh
  then
    let proc = let uu___ = z3_cmd_and_args () in new_z3proc_with_id uu___ in
    let kill_handler uu___ = "\nkilled\n" in
    let out =
      FStarC_Util.ask_process proc input kill_handler (warn_handler []) in
    let r1 = parse (FStarC_Util.trim_string out) in
    (log_result
       (fun fname s ->
          let h = FStarC_Util.open_file_for_appending fname in
          FStarC_Util.append_to_file h s; FStarC_Util.close_out_channel h) r1;
     FStarC_Util.kill_process proc;
     r1)
  else
    (let out =
       let uu___1 = FStarC_Effect.op_Bang bg_z3_proc in uu___1.ask input in
     let r1 = parse (FStarC_Util.trim_string out) in
     log_result
       (fun _fname s -> let uu___2 = query_logging.append_to_log s in ()) r1;
     r1)
let z3_options (ver : Prims.string) : Prims.string=
  let opts =
    ["(set-option :global-decls false)";
    "(set-option :smt.mbqi false)";
    "(set-option :auto_config false)";
    "(set-option :produce-unsat-cores true)";
    "(set-option :model true)";
    "(set-option :smt.case_split 3)";
    "(set-option :smt.relevancy 2)"] in
  let opts1 =
    let uu___ =
      let uu___1 = FStarC_Misc.version_ge ver "4.12.3" in
      if uu___1
      then
        ["(set-option :rewriter.enable_der false)";
        "(set-option :rewriter.sort_disjunctions false)";
        "(set-option :pi.decompose_patterns false)";
        "(set-option :smt.arith.solver 6)"]
      else ["(set-option :smt.arith.solver 2)"] in
    FStarC_List.op_At opts uu___ in
  Prims.strcat (FStarC_String.concat "\n" opts1) "\n"
let context_profile (theory : FStarC_SMTEncoding_Term.decl Prims.list) :
  unit=
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 d ->
         match uu___1 with
         | (out, _total) ->
             (match d with
              | FStarC_SMTEncoding_Term.Module (name, decls) ->
                  let decls1 =
                    FStarC_List.filter
                      (fun uu___2 ->
                         match uu___2 with
                         | FStarC_SMTEncoding_Term.Assume uu___3 -> true
                         | uu___3 -> false) decls in
                  let n = FStarC_List.length decls1 in
                  (((name, n) :: out), (n + _total))
              | uu___2 -> (out, _total))) ([], Prims.int_zero) theory in
  match uu___ with
  | (modules, total_decls) ->
      let modules1 =
        FStarC_List.sortWith
          (fun uu___1 uu___2 ->
             match (uu___1, uu___2) with
             | ((uu___3, n), (uu___4, m)) -> m - n) modules in
      (if modules1 <> []
       then
         (let uu___2 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int total_decls in
          FStarC_Format.print1
            "Z3 Proof Stats: context_profile with %s assertions\n" uu___2)
       else ();
       FStarC_List.iter
         (fun uu___2 ->
            match uu___2 with
            | (m, n) ->
                if n <> Prims.int_zero
                then
                  let uu___3 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
                  FStarC_Format.print2
                    "Z3 Proof Stats: %s produced %s SMT decls\n" m uu___3
                else ()) modules1)
let mk_input (fresh : Prims.bool)
  (theory : FStarC_SMTEncoding_Term.decl Prims.list) :
  (Prims.string * Prims.string FStar_Pervasives_Native.option * Prims.string
    FStar_Pervasives_Native.option)=
  let ver = FStarC_Options.z3_version () in
  let theory1 =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Effect.op_Bang FStarC_Options._version in
        let uu___3 = FStarC_Effect.op_Bang FStarC_Options._commit in
        FStarC_Format.fmt3
          "Z3 invocation started by F*\nF* version: %s -- commit hash: %s\nZ3 version (according to F*): %s"
          uu___2 uu___3 ver in
      FStarC_SMTEncoding_Term.Caption uu___1 in
    uu___ :: FStarC_SMTEncoding_Term.EmptyLine :: theory in
  let options = z3_options ver in
  let options1 =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Options.z3_seed () in
        FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
      FStarC_Format.fmt1 "(set-option :smt.random-seed %s)\n" uu___1 in
    Prims.strcat options uu___ in
  let options2 =
    let uu___ =
      let uu___1 =
        let uu___2 = FStarC_Options.z3_smtopt () in
        FStarC_String.concat "\n" uu___2 in
      Prims.strcat uu___1 "\n\n" in
    Prims.strcat options1 uu___ in
  (let uu___1 = FStarC_Options.print_z3_statistics () in
   if uu___1 then context_profile theory1 else ());
  (let uu___1 =
     let uu___2 =
       (FStarC_Options.record_hints ()) ||
         ((FStarC_Options.use_hints ()) &&
            (FStarC_Options.use_hint_hashes ())) in
     if uu___2
     then
       let uu___3 =
         let uu___4 =
           FStarC_Util.prefix_until
             (fun uu___5 ->
                match uu___5 with
                | FStarC_SMTEncoding_Term.CheckSat -> true
                | uu___6 -> false) theory1 in
         FStarC_Option.must uu___4 in
       match uu___3 with
       | (prefix, check_sat, suffix) ->
           let pp =
             FStarC_List.map (FStarC_SMTEncoding_Term.declToSmt options2) in
           let suffix1 = check_sat :: suffix in
           let ps_lines = pp prefix in
           let ss_lines = pp suffix1 in
           let ps = FStarC_String.concat "\n" ps_lines in
           let ss = FStarC_String.concat "\n" ss_lines in
           let hs =
             let uu___4 = FStarC_Options.keep_query_captions () in
             if uu___4
             then
               let uu___5 =
                 FStarC_List.map
                   (FStarC_SMTEncoding_Term.declToSmt_no_caps options2)
                   prefix in
               FStarC_String.concat "\n" uu___5
             else ps in
           let hs1 = Prims.strcat hs (Prims.strcat "Z3 version: " ver) in
           let hs2 =
             let uu___4 =
               let uu___5 =
                 let uu___6 = FStarC_Options.z3_rlimit () in
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___6 in
               Prims.strcat "Z3 rlimit: " uu___5 in
             Prims.strcat hs1 uu___4 in
           let hs3 =
             let uu___4 =
               let uu___5 =
                 let uu___6 = FStarC_Options.z3_seed () in
                 FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___6 in
               Prims.strcat "Z3 seed: " uu___5 in
             Prims.strcat hs2 uu___4 in
           let uu___4 =
             let uu___5 = FStarC_Util.digest_of_string hs3 in
             FStar_Pervasives_Native.Some uu___5 in
           ((Prims.strcat ps (Prims.strcat "\n" ss)), uu___4)
     else
       (let uu___4 =
          let uu___5 =
            FStarC_List.map (FStarC_SMTEncoding_Term.declToSmt options2)
              theory1 in
          FStarC_String.concat "\n" uu___5 in
        (uu___4, FStar_Pervasives_Native.None)) in
   match uu___1 with
   | (r, hash) ->
       let log_file_name =
         let uu___2 = FStarC_Options.log_queries () in
         if uu___2
         then
           let uu___3 = query_logging.write_to_log fresh r in
           FStar_Pervasives_Native.Some uu___3
         else FStar_Pervasives_Native.None in
       (r, hash, log_file_name))
let cache_hit (log_file : Prims.string FStar_Pervasives_Native.option)
  (cache : Prims.string FStar_Pervasives_Native.option)
  (qhash : Prims.string FStar_Pervasives_Native.option) :
  z3result FStar_Pervasives_Native.option=
  let uu___ =
    (FStarC_Options.use_hints ()) && (FStarC_Options.use_hint_hashes ()) in
  if uu___
  then
    match qhash with
    | FStar_Pervasives_Native.Some x when qhash = cache ->
        let stats = FStarC_SMap.create Prims.int_zero in
        (FStarC_SMap.add stats "fstar_cache_hit" "1";
         (let result =
            {
              z3result_status = (UNSAT FStar_Pervasives_Native.None);
              z3result_time = Prims.int_zero;
              z3result_initial_statistics = stats;
              z3result_statistics = stats;
              z3result_query_hash = qhash;
              z3result_log_file = log_file
            } in
          FStar_Pervasives_Native.Some result))
    | uu___1 -> FStar_Pervasives_Native.None
  else FStar_Pervasives_Native.None
let z3_job (log_file : Prims.string FStar_Pervasives_Native.option)
  (r : FStarC_Range_Type.t) (fresh : Prims.bool)
  (label_messages : FStarC_SMTEncoding_Term.error_labels)
  (input : Prims.string)
  (qhash : Prims.string FStar_Pervasives_Native.option)
  (queryid : Prims.string) : z3result=
  let uu___ =
    let uu___1 =
      let uu___2 = query_logging.get_module_name () in
      FStar_Pervasives_Native.Some uu___2 in
    FStarC_Profiling.profile
      (fun uu___2 ->
         try
           (fun uu___3 ->
              match () with
              | () ->
                  FStarC_Timing.record_ms
                    (fun uu___4 ->
                       doZ3Exe log_file r fresh input label_messages queryid))
             ()
         with
         | uu___3 ->
             (refresh FStar_Pervasives_Native.None;
              FStarC_Effect.raise uu___3)) uu___1
      "FStarC.SMTEncoding.Z3 (aggregate query time)" in
  match uu___ with
  | ((status, initial_statistics, statistics), elapsed_time) ->
      {
        z3result_status = status;
        z3result_time = elapsed_time;
        z3result_initial_statistics = initial_statistics;
        z3result_statistics = statistics;
        z3result_query_hash = qhash;
        z3result_log_file = log_file
      }
let ask_text (r : FStarC_Range_Type.t)
  (cache : Prims.string FStar_Pervasives_Native.option)
  (label_messages : FStarC_SMTEncoding_Term.error_labels)
  (qry : FStarC_SMTEncoding_Term.decl Prims.list) (queryid : Prims.string)
  (core :
    FStarC_SMTEncoding_UnsatCore.unsat_core FStar_Pervasives_Native.option)
  : Prims.string=
  let theory =
    match core with
    | FStar_Pervasives_Native.None ->
        with_solver_state FStarC_SMTEncoding_SolverState.flush
    | FStar_Pervasives_Native.Some core1 ->
        reading_solver_state
          (FStarC_SMTEncoding_SolverState.filter_with_unsat_core queryid
             core1) in
  let query_tail =
    FStarC_List.op_At ((FStarC_SMTEncoding_Term.Push Prims.int_zero) :: qry)
      [FStarC_SMTEncoding_Term.Pop Prims.int_zero] in
  let theory1 = FStarC_List.op_At theory query_tail in
  let uu___ = mk_input true theory1 in
  match uu___ with | (input, qhash, log_file_name) -> input
let ask (r : FStarC_Range_Type.t)
  (cache : Prims.string FStar_Pervasives_Native.option)
  (label_messages : FStarC_SMTEncoding_Term.error_labels)
  (qry : FStarC_SMTEncoding_Term.decl Prims.list) (queryid : Prims.string)
  (fresh : Prims.bool)
  (core :
    FStarC_SMTEncoding_UnsatCore.unsat_core FStar_Pervasives_Native.option)
  : z3result=
  let theory =
    match core with
    | FStar_Pervasives_Native.None ->
        with_solver_state FStarC_SMTEncoding_SolverState.flush
    | FStar_Pervasives_Native.Some core1 ->
        (if Prims.op_Negation fresh
         then
           failwith
             "Unexpected: unsat core must only be used with fresh solvers"
         else ();
         reading_solver_state
           (FStarC_SMTEncoding_SolverState.filter_with_unsat_core queryid
              core1)) in
  let theory1 =
    FStarC_List.op_At theory
      (FStarC_List.op_At ((FStarC_SMTEncoding_Term.Push Prims.int_zero) ::
         qry)
         [FStarC_SMTEncoding_Term.Pop Prims.int_zero;
         FStarC_SMTEncoding_Term.EmptyLine]) in
  let uu___ = mk_input fresh theory1 in
  match uu___ with
  | (input, qhash, log_file_name) ->
      let just_ask uu___1 =
        z3_job log_file_name r fresh label_messages input qhash queryid in
      let result =
        if fresh
        then
          let uu___1 = cache_hit log_file_name cache qhash in
          match uu___1 with
          | FStar_Pervasives_Native.Some z3r -> z3r
          | FStar_Pervasives_Native.None -> just_ask ()
        else just_ask () in
      result

open Prims
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
type z3status =
  | UNSAT of unsat_core 
  | SAT of (FStar_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | UNKNOWN of (FStar_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | TIMEOUT of (FStar_SMTEncoding_Term.error_labels * Prims.string
  FStar_Pervasives_Native.option) 
  | KILLED 
let (uu___is_UNSAT : z3status -> Prims.bool) =
  fun projectee -> match projectee with | UNSAT _0 -> true | uu___ -> false
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee -> match projectee with | UNSAT _0 -> _0
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee -> match projectee with | SAT _0 -> true | uu___ -> false
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | SAT _0 -> _0
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee -> match projectee with | UNKNOWN _0 -> true | uu___ -> false
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | UNKNOWN _0 -> _0
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee -> match projectee with | TIMEOUT _0 -> true | uu___ -> false
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TIMEOUT _0 -> _0
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee -> match projectee with | KILLED -> true | uu___ -> false
type z3statistics = Prims.string FStar_Compiler_Util.smap
type z3result =
  {
  z3result_status: z3status ;
  z3result_time: Prims.int ;
  z3result_statistics: z3statistics ;
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option ;
  z3result_log_file: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkz3result__item__z3result_status : z3result -> z3status) =
  fun projectee ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_status
let (__proj__Mkz3result__item__z3result_time : z3result -> Prims.int) =
  fun projectee ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_time
let (__proj__Mkz3result__item__z3result_statistics :
  z3result -> z3statistics) =
  fun projectee ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_statistics
let (__proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_query_hash
let (__proj__Mkz3result__item__z3result_log_file :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_log_file
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.bool -> Prims.string -> Prims.string ;
  append_to_log: Prims.string -> Prims.string ;
  close_log: unit -> unit }
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; append_to_log;
        close_log;_} -> get_module_name
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; append_to_log;
        close_log;_} -> set_module_name
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.bool -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; append_to_log;
        close_log;_} -> write_to_log
let (__proj__Mkquery_log__item__append_to_log :
  query_log -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; append_to_log;
        close_log;_} -> append_to_log
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; append_to_log;
        close_log;_} -> close_log
let (_already_warned_solver_mismatch : Prims.bool FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref false
let (_already_warned_version_mismatch : Prims.bool FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref false
let (z3url : Prims.string) = "https://github.com/Z3Prover/z3/releases"
let (inpath : Prims.string -> Prims.bool) =
  fun path ->
    try
      (fun uu___ ->
         match () with
         | () ->
             let s =
               FStar_Compiler_Util.run_process "z3_pathtest" path
                 ["-version"] FStar_Pervasives_Native.None in
             s <> "") ()
    with | uu___ -> false
let (z3_exe : unit -> Prims.string) =
  let cache = FStar_Compiler_Util.smap_create (Prims.of_int (5)) in
  let find_or k f =
    let uu___ = FStar_Compiler_Util.smap_try_find cache k in
    match uu___ with
    | FStar_Pervasives_Native.Some v -> v
    | FStar_Pervasives_Native.None ->
        let v = f k in (FStar_Compiler_Util.smap_add cache k v; v) in
  fun uu___ ->
    let uu___1 = FStar_Options.z3_version () in
    find_or uu___1
      (fun version ->
         let path =
           let z3_v = FStar_Platform.exe (Prims.strcat "z3-" version) in
           let smto = FStar_Options.smt () in
           if FStar_Pervasives_Native.uu___is_Some smto
           then FStar_Pervasives_Native.__proj__Some__item__v smto
           else
             (let uu___3 = inpath z3_v in
              if uu___3 then z3_v else FStar_Platform.exe "z3") in
         (let uu___3 = FStar_Options.debug_any () in
          if uu___3
          then FStar_Compiler_Util.print1 "Chosen Z3 executable: %s\n" path
          else ());
         path)
type label = Prims.string
let (status_tag : z3status -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | SAT uu___1 -> "sat"
    | UNSAT uu___1 -> "unsat"
    | UNKNOWN uu___1 -> "unknown"
    | TIMEOUT uu___1 -> "timeout"
    | KILLED -> "killed"
let (status_string_and_errors :
  z3status -> (Prims.string * FStar_SMTEncoding_Term.error_labels)) =
  fun s ->
    match s with
    | KILLED -> ((status_tag s), [])
    | UNSAT uu___ -> ((status_tag s), [])
    | SAT (errs, msg) ->
        let uu___ =
          FStar_Compiler_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu___, errs)
    | UNKNOWN (errs, msg) ->
        let uu___ =
          FStar_Compiler_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu___, errs)
    | TIMEOUT (errs, msg) ->
        let uu___ =
          FStar_Compiler_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu___, errs)
let (query_logging : query_log) =
  let query_number = FStar_Compiler_Util.mk_ref Prims.int_zero in
  let log_file_opt = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStar_Compiler_Util.mk_ref [] in
  let current_module_name =
    FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let current_file_name =
    FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n =
    FStar_Compiler_Effect.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n) in
  let get_module_name uu___ =
    let uu___1 = FStar_Compiler_Effect.op_Bang current_module_name in
    match uu___1 with
    | FStar_Pervasives_Native.None -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n -> n in
  let next_file_name uu___ =
    let n = get_module_name () in
    let file_name =
      let uu___1 =
        let uu___2 = FStar_Compiler_Effect.op_Bang used_file_names in
        FStar_Compiler_List.tryFind
          (fun uu___3 -> match uu___3 with | (m, uu___4) -> n = m) uu___2 in
      match uu___1 with
      | FStar_Pervasives_Native.None ->
          ((let uu___3 =
              let uu___4 = FStar_Compiler_Effect.op_Bang used_file_names in
              (n, Prims.int_zero) :: uu___4 in
            FStar_Compiler_Effect.op_Colon_Equals used_file_names uu___3);
           n)
      | FStar_Pervasives_Native.Some (uu___2, k) ->
          ((let uu___4 =
              let uu___5 = FStar_Compiler_Effect.op_Bang used_file_names in
              (n, (k + Prims.int_one)) :: uu___5 in
            FStar_Compiler_Effect.op_Colon_Equals used_file_names uu___4);
           (let uu___4 =
              FStar_Compiler_Util.string_of_int (k + Prims.int_one) in
            FStar_Compiler_Util.format2 "%s-%s" n uu___4)) in
    FStar_Compiler_Util.format1 "queries-%s.smt2" file_name in
  let new_log_file uu___ =
    let file_name = next_file_name () in
    FStar_Compiler_Effect.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let c = FStar_Compiler_Util.open_file_for_writing file_name in
     FStar_Compiler_Effect.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (c, file_name));
     (c, file_name)) in
  let get_log_file uu___ =
    let uu___1 = FStar_Compiler_Effect.op_Bang log_file_opt in
    match uu___1 with
    | FStar_Pervasives_Native.None -> new_log_file ()
    | FStar_Pervasives_Native.Some c -> c in
  let append_to_log str =
    let uu___ = get_log_file () in
    match uu___ with
    | (f, nm) -> (FStar_Compiler_Util.append_to_file f str; nm) in
  let write_to_new_log str =
    let file_name = next_file_name () in
    FStar_Compiler_Util.write_file file_name str; file_name in
  let write_to_log fresh str =
    if fresh then write_to_new_log str else append_to_log str in
  let close_log uu___ =
    let uu___1 = FStar_Compiler_Effect.op_Bang log_file_opt in
    match uu___1 with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some (c, uu___2) ->
        (FStar_Compiler_Util.close_out_channel c;
         FStar_Compiler_Effect.op_Colon_Equals log_file_opt
           FStar_Pervasives_Native.None) in
  let log_file_name uu___ =
    let uu___1 = FStar_Compiler_Effect.op_Bang current_file_name in
    match uu___1 with
    | FStar_Pervasives_Native.None -> failwith "no log file"
    | FStar_Pervasives_Native.Some n -> n in
  { get_module_name; set_module_name; write_to_log; append_to_log; close_log
  }
let (z3_cmd_and_args : unit -> (Prims.string * Prims.string Prims.list)) =
  fun uu___ ->
    let cmd = z3_exe () in
    let cmd_args =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_Options.z3_seed () in
                FStar_Compiler_Util.string_of_int uu___6 in
              FStar_Compiler_Util.format1 "smt.random_seed=%s" uu___5 in
            [uu___4] in
          "-in" :: uu___3 in
        "-smt2" :: uu___2 in
      let uu___2 = FStar_Options.z3_cliopt () in
      FStar_Compiler_List.append uu___1 uu___2 in
    (cmd, cmd_args)
let (warn_handler : FStar_Errors_Msg.error_message -> Prims.string -> unit) =
  fun suf ->
    fun s ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Errors_Msg.text "Unexpected output from Z3:" in
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStar_Pprint.blank (Prims.of_int (2)) in
                  let uu___8 =
                    let uu___9 =
                      let uu___10 = FStar_Pprint.arbitrary_string s in
                      FStar_Pprint.dquotes uu___10 in
                    FStar_Pprint.align uu___9 in
                  FStar_Pprint.op_Hat_Hat uu___7 uu___8 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___6 in
              FStar_Pprint.op_Hat_Hat uu___4 uu___5 in
            [uu___3] in
          FStar_Compiler_List.op_At uu___2 suf in
        (FStar_Errors_Codes.Warning_UnexpectedZ3Output, uu___1) in
      FStar_Errors.log_issue_doc FStar_Compiler_Range_Type.dummyRange uu___
let (check_z3version : FStar_Compiler_Util.proc -> unit) =
  fun p ->
    let getinfo arg =
      let s =
        let uu___ =
          FStar_Compiler_Util.format1 "(get-info :%s)\n(echo \"Done!\")\n"
            arg in
        FStar_Compiler_Util.ask_process p uu___ (fun uu___1 -> "Killed")
          (warn_handler []) in
      if FStar_Compiler_Util.starts_with s (Prims.strcat "(:" arg)
      then
        let ss = FStar_Compiler_String.split [34] s in
        FStar_Compiler_List.nth ss Prims.int_one
      else
        (warn_handler [] s;
         (let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Compiler_Util.proc_prog p in
              FStar_Compiler_Util.format1 "Could not run Z3 from `%s'" uu___4 in
            (FStar_Errors_Codes.Error_Z3InvocationError, uu___3) in
          FStar_Errors.raise_err uu___2)) in
    let name = getinfo "name" in
    (let uu___1 =
       (name <> "Z3") &&
         (let uu___2 =
            FStar_Compiler_Effect.op_Bang _already_warned_solver_mismatch in
          Prims.op_Negation uu___2) in
     if uu___1
     then
       ((let uu___3 =
           let uu___4 =
             let uu___5 =
               let uu___6 =
                 let uu___7 = FStar_Options.z3_version () in
                 Prims.strcat "z3-" uu___7 in
               FStar_Platform.exe uu___6 in
             FStar_Compiler_Util.format3
               "Unexpected SMT solver: expected to be talking to Z3, got %s.\nPlease download the correct version of Z3 from %s\nand install it into your $PATH as `%s'."
               name z3url uu___5 in
           (FStar_Errors_Codes.Warning_SolverMismatch, uu___4) in
         FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange uu___3);
        FStar_Compiler_Effect.op_Colon_Equals _already_warned_solver_mismatch
          true)
     else ());
    (let ver_found =
       let uu___1 =
         let uu___2 =
           let uu___3 = getinfo "version" in
           FStar_Compiler_Util.split uu___3 "-" in
         FStar_Compiler_List.hd uu___2 in
       FStar_Compiler_Util.trim_string uu___1 in
     let ver_conf =
       let uu___1 = FStar_Options.z3_version () in
       FStar_Compiler_Util.trim_string uu___1 in
     let uu___2 =
       (ver_conf <> ver_found) &&
         (let uu___3 =
            FStar_Compiler_Effect.op_Bang _already_warned_version_mismatch in
          Prims.op_Negation uu___3) in
     if uu___2
     then
       ((let uu___4 =
           let uu___5 =
             let uu___6 =
               let uu___7 =
                 let uu___8 = FStar_Compiler_Util.proc_prog p in
                 FStar_Compiler_Util.format3
                   "Unexpected Z3 version for '%s': expected '%s', got '%s'."
                   uu___8 ver_conf ver_found in
               FStar_Errors_Msg.text uu___7 in
             let uu___7 =
               let uu___8 =
                 let uu___9 =
                   let uu___10 =
                     FStar_Errors_Msg.text
                       "Please download the correct version of Z3 from" in
                   let uu___11 = FStar_Pprint.url z3url in
                   FStar_Pprint.prefix (Prims.of_int (4)) Prims.int_one
                     uu___10 uu___11 in
                 let uu___10 =
                   let uu___11 =
                     let uu___12 =
                       FStar_Errors_Msg.text
                         "and install it into your $PATH as" in
                     let uu___13 =
                       let uu___14 =
                         let uu___15 =
                           let uu___16 =
                             let uu___17 =
                               let uu___18 = FStar_Options.z3_version () in
                               Prims.strcat "z3-" uu___18 in
                             FStar_Platform.exe uu___17 in
                           FStar_Pprint.doc_of_string uu___16 in
                         FStar_Pprint.squotes uu___15 in
                       FStar_Pprint.op_Hat_Hat uu___14 FStar_Pprint.dot in
                     FStar_Pprint.op_Hat_Slash_Hat uu___12 uu___13 in
                   FStar_Pprint.group uu___11 in
                 FStar_Pprint.op_Hat_Slash_Hat uu___9 uu___10 in
               [uu___8] in
             uu___6 :: uu___7 in
           (FStar_Errors_Codes.Warning_SolverMismatch, uu___5) in
         FStar_Errors.log_issue_doc FStar_Compiler_Range_Type.dummyRange
           uu___4);
        FStar_Errors.stop_if_err ();
        FStar_Compiler_Effect.op_Colon_Equals
          _already_warned_version_mismatch true)
     else ())
let (new_z3proc :
  Prims.string ->
    (Prims.string * Prims.string Prims.list) -> FStar_Compiler_Util.proc)
  =
  fun id ->
    fun cmd_and_args ->
      let proc =
        FStar_Compiler_Util.start_process id
          (FStar_Pervasives_Native.fst cmd_and_args)
          (FStar_Pervasives_Native.snd cmd_and_args) (fun s -> s = "Done!") in
      check_z3version proc; proc
let (new_z3proc_with_id :
  (Prims.string * Prims.string Prims.list) -> FStar_Compiler_Util.proc) =
  let ctr = FStar_Compiler_Util.mk_ref (Prims.of_int (-1)) in
  fun cmd_and_args ->
    let p =
      let uu___ =
        let uu___1 =
          FStar_Compiler_Util.incr ctr;
          (let uu___3 = FStar_Compiler_Effect.op_Bang ctr in
           FStar_Compiler_Effect.op_Bar_Greater uu___3
             FStar_Compiler_Util.string_of_int) in
        FStar_Compiler_Util.format1 "z3-bg-%s" uu___1 in
      new_z3proc uu___ cmd_and_args in
    p
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit ;
  version: unit -> Prims.string }
let (__proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with | { ask; refresh; restart; version;_} -> ask
let (__proj__Mkbgproc__item__refresh : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with | { ask; refresh; restart; version;_} -> refresh
let (__proj__Mkbgproc__item__restart : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with | { ask; refresh; restart; version;_} -> restart
let (__proj__Mkbgproc__item__version : bgproc -> unit -> Prims.string) =
  fun projectee ->
    match projectee with | { ask; refresh; restart; version;_} -> version
let (cmd_and_args_to_string :
  (Prims.string * Prims.string Prims.list) -> Prims.string) =
  fun cmd_and_args ->
    FStar_Compiler_String.concat ""
      ["cmd=";
      FStar_Pervasives_Native.fst cmd_and_args;
      " args=[";
      FStar_Compiler_String.concat ", "
        (FStar_Pervasives_Native.snd cmd_and_args);
      "]"]
let (bg_z3_proc : bgproc FStar_Compiler_Effect.ref) =
  let the_z3proc = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let the_z3proc_params =
    FStar_Compiler_Util.mk_ref (FStar_Pervasives_Native.Some ("", [""])) in
  let the_z3proc_ask_count = FStar_Compiler_Util.mk_ref Prims.int_zero in
  let the_z3proc_version = FStar_Compiler_Util.mk_ref "" in
  let make_new_z3_proc cmd_and_args =
    (let uu___1 =
       let uu___2 = new_z3proc_with_id cmd_and_args in
       FStar_Pervasives_Native.Some uu___2 in
     FStar_Compiler_Effect.op_Colon_Equals the_z3proc uu___1);
    FStar_Compiler_Effect.op_Colon_Equals the_z3proc_params
      (FStar_Pervasives_Native.Some cmd_and_args);
    FStar_Compiler_Effect.op_Colon_Equals the_z3proc_ask_count Prims.int_zero in
  (let uu___1 = FStar_Options.z3_version () in
   FStar_Compiler_Effect.op_Colon_Equals the_z3proc_version uu___1);
  (let z3proc uu___1 =
     (let uu___3 =
        let uu___4 = FStar_Compiler_Effect.op_Bang the_z3proc in
        uu___4 = FStar_Pervasives_Native.None in
      if uu___3
      then let uu___4 = z3_cmd_and_args () in make_new_z3_proc uu___4
      else ());
     (let uu___3 = FStar_Compiler_Effect.op_Bang the_z3proc in
      FStar_Compiler_Util.must uu___3) in
   let ask input =
     FStar_Compiler_Util.incr the_z3proc_ask_count;
     (let kill_handler uu___2 = "\nkilled\n" in
      let uu___2 = z3proc () in
      FStar_Compiler_Util.ask_process uu___2 input kill_handler
        (warn_handler [])) in
   let maybe_kill_z3proc uu___1 =
     let uu___2 =
       let uu___3 = FStar_Compiler_Effect.op_Bang the_z3proc in
       uu___3 <> FStar_Pervasives_Native.None in
     if uu___2
     then
       ((let uu___4 =
           let uu___5 = FStar_Compiler_Effect.op_Bang the_z3proc in
           FStar_Compiler_Util.must uu___5 in
         FStar_Compiler_Util.kill_process uu___4);
        FStar_Compiler_Effect.op_Colon_Equals the_z3proc
          FStar_Pervasives_Native.None)
     else () in
   let refresh uu___1 =
     let next_params = z3_cmd_and_args () in
     let old_params =
       let uu___2 = FStar_Compiler_Effect.op_Bang the_z3proc_params in
       FStar_Compiler_Util.must uu___2 in
     let old_version = FStar_Compiler_Effect.op_Bang the_z3proc_version in
     let next_version = FStar_Options.z3_version () in
     (let uu___3 =
        (((FStar_Options.log_queries ()) ||
            (let uu___4 = FStar_Compiler_Effect.op_Bang the_z3proc_ask_count in
             uu___4 > Prims.int_zero))
           || (old_params <> next_params))
          || (old_version <> next_version) in
      if uu___3
      then
        (maybe_kill_z3proc ();
         (let uu___6 = FStar_Options.query_stats () in
          if uu___6
          then
            let uu___7 =
              let uu___8 = FStar_Compiler_Effect.op_Bang the_z3proc_ask_count in
              FStar_Compiler_Util.string_of_int uu___8 in
            FStar_Compiler_Util.print3
              "Refreshing the z3proc (ask_count=%s old=[%s] new=[%s])\n"
              uu___7 (cmd_and_args_to_string old_params)
              (cmd_and_args_to_string next_params)
          else ());
         make_new_z3_proc next_params)
      else ());
     query_logging.close_log () in
   let restart uu___1 =
     maybe_kill_z3proc ();
     query_logging.close_log ();
     (let next_params = z3_cmd_and_args () in make_new_z3_proc next_params) in
   let x = [] in
   FStar_Compiler_Util.mk_ref
     {
       ask = (FStar_Compiler_Util.with_monitor x ask);
       refresh = (FStar_Compiler_Util.with_monitor x refresh);
       restart = (FStar_Compiler_Util.with_monitor x restart);
       version =
         (fun uu___1 -> FStar_Compiler_Effect.op_Bang the_z3proc_version)
     })
type smt_output_section = Prims.string Prims.list
type smt_output =
  {
  smt_result: smt_output_section ;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option ;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option ;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option ;
  smt_labels: smt_output_section FStar_Pervasives_Native.option }
let (__proj__Mksmt_output__item__smt_result :
  smt_output -> smt_output_section) =
  fun projectee ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_result
let (__proj__Mksmt_output__item__smt_reason_unknown :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_reason_unknown
let (__proj__Mksmt_output__item__smt_unsat_core :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_unsat_core
let (__proj__Mksmt_output__item__smt_statistics :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_statistics
let (__proj__Mksmt_output__item__smt_labels :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_labels
let (smt_output_sections :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Compiler_Range_Type.range -> Prims.string Prims.list -> smt_output)
  =
  fun log_file ->
    fun r ->
      fun lines ->
        let rec until tag lines1 =
          match lines1 with
          | [] -> FStar_Pervasives_Native.None
          | l::lines2 ->
              if tag = l
              then FStar_Pervasives_Native.Some ([], lines2)
              else
                (let uu___1 = until tag lines2 in
                 FStar_Compiler_Util.map_opt uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | (until_tag, rest) -> ((l :: until_tag), rest))) in
        let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
        let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
        let find_section tag lines1 =
          let uu___ = until (start_tag tag) lines1 in
          match uu___ with
          | FStar_Pervasives_Native.None ->
              (FStar_Pervasives_Native.None, lines1)
          | FStar_Pervasives_Native.Some (prefix, suffix) ->
              let uu___1 = until (end_tag tag) suffix in
              (match uu___1 with
               | FStar_Pervasives_Native.None ->
                   failwith
                     (Prims.strcat "Parse error: "
                        (Prims.strcat (end_tag tag) " not found"))
               | FStar_Pervasives_Native.Some (section, suffix1) ->
                   ((FStar_Pervasives_Native.Some section),
                     (FStar_Compiler_List.op_At prefix suffix1))) in
        let uu___ = find_section "result" lines in
        match uu___ with
        | (result_opt, lines1) ->
            let result = FStar_Compiler_Util.must result_opt in
            let uu___1 = find_section "reason-unknown" lines1 in
            (match uu___1 with
             | (reason_unknown, lines2) ->
                 let uu___2 = find_section "unsat-core" lines2 in
                 (match uu___2 with
                  | (unsat_core1, lines3) ->
                      let uu___3 = find_section "statistics" lines3 in
                      (match uu___3 with
                       | (statistics, lines4) ->
                           let uu___4 = find_section "labels" lines4 in
                           (match uu___4 with
                            | (labels, lines5) ->
                                let remaining =
                                  let uu___5 = until "Done!" lines5 in
                                  match uu___5 with
                                  | FStar_Pervasives_Native.None -> lines5
                                  | FStar_Pervasives_Native.Some
                                      (prefix, suffix) ->
                                      FStar_Compiler_List.op_At prefix suffix in
                                ((match remaining with
                                  | [] -> ()
                                  | uu___6 ->
                                      let msg =
                                        FStar_Compiler_String.concat "\n"
                                          remaining in
                                      let suf =
                                        match log_file with
                                        | FStar_Pervasives_Native.Some
                                            log_file1 ->
                                            let uu___7 =
                                              let uu___8 =
                                                FStar_Errors_Msg.text
                                                  "Log file:" in
                                              let uu___9 =
                                                FStar_Pprint.doc_of_string
                                                  log_file1 in
                                              FStar_Pprint.op_Hat_Slash_Hat
                                                uu___8 uu___9 in
                                            [uu___7]
                                        | FStar_Pervasives_Native.None -> [] in
                                      warn_handler suf msg);
                                 (let uu___6 =
                                    FStar_Compiler_Util.must result_opt in
                                  {
                                    smt_result = uu___6;
                                    smt_reason_unknown = reason_unknown;
                                    smt_unsat_core = unsat_core1;
                                    smt_statistics = statistics;
                                    smt_labels = labels
                                  }))))))
let (doZ3Exe :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Compiler_Range_Type.range ->
      Prims.bool ->
        Prims.string ->
          FStar_SMTEncoding_Term.error_labels ->
            Prims.string -> (z3status * z3statistics))
  =
  fun log_file ->
    fun r ->
      fun fresh ->
        fun input ->
          fun label_messages ->
            fun queryid ->
              let parse z3out =
                let lines =
                  FStar_Compiler_Effect.op_Bar_Greater
                    (FStar_Compiler_String.split [10] z3out)
                    (FStar_Compiler_List.map FStar_Compiler_Util.trim_string) in
                let smt_output1 = smt_output_sections log_file r lines in
                let unsat_core1 =
                  match smt_output1.smt_unsat_core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None
                  | FStar_Pervasives_Native.Some s ->
                      let s1 =
                        FStar_Compiler_Util.trim_string
                          (FStar_Compiler_String.concat " " s) in
                      let s2 =
                        FStar_Compiler_Util.substring s1 Prims.int_one
                          ((FStar_Compiler_String.length s1) -
                             (Prims.of_int (2))) in
                      if FStar_Compiler_Util.starts_with s2 "error"
                      then FStar_Pervasives_Native.None
                      else
                        (let uu___1 =
                           FStar_Compiler_Effect.op_Bar_Greater
                             (FStar_Compiler_Util.split s2 " ")
                             (FStar_Compiler_Util.sort_with
                                FStar_Compiler_String.compare) in
                         FStar_Pervasives_Native.Some uu___1) in
                let labels =
                  match smt_output1.smt_labels with
                  | FStar_Pervasives_Native.None -> []
                  | FStar_Pervasives_Native.Some lines1 ->
                      let rec lblnegs lines2 =
                        match lines2 with
                        | lname::"false"::rest when
                            FStar_Compiler_Util.starts_with lname "label_" ->
                            let uu___ = lblnegs rest in lname :: uu___
                        | lname::uu___::rest when
                            FStar_Compiler_Util.starts_with lname "label_" ->
                            lblnegs rest
                        | uu___ -> [] in
                      let lblnegs1 = lblnegs lines1 in
                      FStar_Compiler_Effect.op_Bar_Greater lblnegs1
                        (FStar_Compiler_List.collect
                           (fun l ->
                              let uu___ =
                                FStar_Compiler_Effect.op_Bar_Greater
                                  label_messages
                                  (FStar_Compiler_List.tryFind
                                     (fun uu___1 ->
                                        match uu___1 with
                                        | (m, uu___2, uu___3) ->
                                            let uu___4 =
                                              FStar_SMTEncoding_Term.fv_name
                                                m in
                                            uu___4 = l)) in
                              match uu___ with
                              | FStar_Pervasives_Native.None -> []
                              | FStar_Pervasives_Native.Some (lbl, msg, r1)
                                  -> [(lbl, msg, r1)])) in
                let statistics =
                  let statistics1 =
                    FStar_Compiler_Util.smap_create Prims.int_zero in
                  match smt_output1.smt_statistics with
                  | FStar_Pervasives_Native.None -> statistics1
                  | FStar_Pervasives_Native.Some lines1 ->
                      let parse_line line =
                        let pline =
                          FStar_Compiler_Util.split
                            (FStar_Compiler_Util.trim_string line) ":" in
                        match pline with
                        | "("::entry::[] ->
                            let tokens = FStar_Compiler_Util.split entry " " in
                            let key = FStar_Compiler_List.hd tokens in
                            let ltok =
                              FStar_Compiler_List.nth tokens
                                ((FStar_Compiler_List.length tokens) -
                                   Prims.int_one) in
                            let value =
                              if FStar_Compiler_Util.ends_with ltok ")"
                              then
                                FStar_Compiler_Util.substring ltok
                                  Prims.int_zero
                                  ((FStar_Compiler_String.length ltok) -
                                     Prims.int_one)
                              else ltok in
                            FStar_Compiler_Util.smap_add statistics1 key
                              value
                        | ""::entry::[] ->
                            let tokens = FStar_Compiler_Util.split entry " " in
                            let key = FStar_Compiler_List.hd tokens in
                            let ltok =
                              FStar_Compiler_List.nth tokens
                                ((FStar_Compiler_List.length tokens) -
                                   Prims.int_one) in
                            let value =
                              if FStar_Compiler_Util.ends_with ltok ")"
                              then
                                FStar_Compiler_Util.substring ltok
                                  Prims.int_zero
                                  ((FStar_Compiler_String.length ltok) -
                                     Prims.int_one)
                              else ltok in
                            FStar_Compiler_Util.smap_add statistics1 key
                              value
                        | uu___ -> () in
                      (FStar_Compiler_List.iter parse_line lines1;
                       statistics1) in
                let reason_unknown =
                  FStar_Compiler_Util.map_opt smt_output1.smt_reason_unknown
                    (fun x ->
                       let ru = FStar_Compiler_String.concat " " x in
                       if
                         FStar_Compiler_Util.starts_with ru
                           "(:reason-unknown \""
                       then
                         let reason =
                           FStar_Compiler_Util.substring_from ru
                             (FStar_Compiler_String.length
                                "(:reason-unknown \"") in
                         let res =
                           FStar_Compiler_String.substring reason
                             Prims.int_zero
                             ((FStar_Compiler_String.length reason) -
                                (Prims.of_int (2))) in
                         res
                       else ru) in
                let status =
                  (let uu___1 = FStar_Options.debug_any () in
                   if uu___1
                   then
                     let uu___2 =
                       FStar_Compiler_Util.format1 "Z3 says: %s\n"
                         (FStar_Compiler_String.concat "\n"
                            smt_output1.smt_result) in
                     FStar_Compiler_Effect.op_Less_Bar
                       FStar_Compiler_Util.print_string uu___2
                   else ());
                  (match smt_output1.smt_result with
                   | "unsat"::[] -> UNSAT unsat_core1
                   | "sat"::[] -> SAT (labels, reason_unknown)
                   | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
                   | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
                   | "killed"::[] ->
                       ((let uu___2 =
                           FStar_Compiler_Effect.op_Bang bg_z3_proc in
                         uu___2.restart ());
                        KILLED)
                   | uu___1 ->
                       let uu___2 =
                         FStar_Compiler_Util.format1
                           "Unexpected output from Z3: got output result: %s\n"
                           (FStar_Compiler_String.concat "\n"
                              smt_output1.smt_result) in
                       failwith uu___2) in
                (status, statistics) in
              let log_result fwrite uu___ =
                match uu___ with
                | (res, _stats) ->
                    (match log_file with
                     | FStar_Pervasives_Native.Some fname ->
                         (fwrite fname (Prims.strcat "; QUERY ID: " queryid);
                          (let uu___3 =
                             let uu___4 =
                               let uu___5 = status_string_and_errors res in
                               FStar_Pervasives_Native.fst uu___5 in
                             Prims.strcat "; STATUS: " uu___4 in
                           fwrite fname uu___3);
                          (match res with
                           | UNSAT (FStar_Pervasives_Native.Some core) ->
                               fwrite fname
                                 (Prims.strcat "; UNSAT CORE GENERATED: "
                                    (FStar_Compiler_String.concat ", " core))
                           | uu___3 -> ()))
                     | FStar_Pervasives_Native.None -> ()) in
              if fresh
              then
                let proc =
                  let uu___ = z3_cmd_and_args () in new_z3proc_with_id uu___ in
                let kill_handler uu___ = "\nkilled\n" in
                let out =
                  FStar_Compiler_Util.ask_process proc input kill_handler
                    (warn_handler []) in
                let r1 = parse (FStar_Compiler_Util.trim_string out) in
                (log_result
                   (fun fname ->
                      fun s ->
                        let h =
                          FStar_Compiler_Util.open_file_for_appending fname in
                        FStar_Compiler_Util.append_to_file h s;
                        FStar_Compiler_Util.close_out_channel h) r1;
                 FStar_Compiler_Util.kill_process proc;
                 r1)
              else
                (let out =
                   let uu___1 = FStar_Compiler_Effect.op_Bang bg_z3_proc in
                   uu___1.ask input in
                 let r1 = parse (FStar_Compiler_Util.trim_string out) in
                 log_result
                   (fun _fname ->
                      fun s ->
                        let uu___2 = query_logging.append_to_log s in ()) r1;
                 r1)
let (z3_options : Prims.string -> Prims.string) =
  fun ver ->
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
        let uu___1 = FStar_Compiler_Misc.version_ge ver "4.12.3" in
        if uu___1
        then
          ["(set-option :rewriter.enable_der false)";
          "(set-option :rewriter.sort_disjunctions false)";
          "(set-option :pi.decompose_patterns false)";
          "(set-option :smt.arith.solver 6)"]
        else ["(set-option :smt.arith.solver 2)"] in
      FStar_Compiler_List.op_At opts uu___ in
    Prims.strcat (FStar_Compiler_String.concat "\n" opts1) "\n"
let (fresh_scope : scope_t FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref [[]]
let (mk_fresh_scope : unit -> scope_t) =
  fun uu___ -> FStar_Compiler_Effect.op_Bang fresh_scope
let (flatten_fresh_scope : unit -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Compiler_Effect.op_Bang fresh_scope in
      FStar_Compiler_List.rev uu___2 in
    FStar_Compiler_List.flatten uu___1
let (bg_scope :
  FStar_SMTEncoding_Term.decl Prims.list FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref []
let (push : Prims.string -> unit) =
  fun msg ->
    FStar_Compiler_Util.atomically
      (fun uu___ ->
         (let uu___2 =
            let uu___3 = FStar_Compiler_Effect.op_Bang fresh_scope in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu___3 in
          FStar_Compiler_Effect.op_Colon_Equals fresh_scope uu___2);
         (let uu___2 =
            let uu___3 = FStar_Compiler_Effect.op_Bang bg_scope in
            FStar_Compiler_List.op_At uu___3
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg] in
          FStar_Compiler_Effect.op_Colon_Equals bg_scope uu___2))
let (pop : Prims.string -> unit) =
  fun msg ->
    FStar_Compiler_Util.atomically
      (fun uu___ ->
         (let uu___2 =
            let uu___3 = FStar_Compiler_Effect.op_Bang fresh_scope in
            FStar_Compiler_List.tl uu___3 in
          FStar_Compiler_Effect.op_Colon_Equals fresh_scope uu___2);
         (let uu___2 =
            let uu___3 = FStar_Compiler_Effect.op_Bang bg_scope in
            FStar_Compiler_List.op_At uu___3
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop] in
          FStar_Compiler_Effect.op_Colon_Equals bg_scope uu___2))
let (snapshot : Prims.string -> (Prims.int * unit)) =
  fun msg -> FStar_Common.snapshot push fresh_scope msg
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg ->
    fun depth ->
      FStar_Common.rollback (fun uu___ -> pop msg) fresh_scope depth
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls ->
    FStar_Compiler_Effect.op_Bar_Greater decls
      (FStar_Compiler_List.iter
         (fun uu___1 ->
            match uu___1 with
            | FStar_SMTEncoding_Term.Push -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop -> failwith "Unexpected push/pop"
            | uu___2 -> ()));
    (let uu___2 = FStar_Compiler_Effect.op_Bang fresh_scope in
     match uu___2 with
     | hd::tl ->
         FStar_Compiler_Effect.op_Colon_Equals fresh_scope
           ((FStar_Compiler_List.op_At hd decls) :: tl)
     | uu___3 -> failwith "Impossible");
    (let uu___2 =
       let uu___3 = FStar_Compiler_Effect.op_Bang bg_scope in
       FStar_Compiler_List.op_At uu___3 decls in
     FStar_Compiler_Effect.op_Colon_Equals bg_scope uu___2)
let (refresh : unit -> unit) =
  fun uu___ ->
    (let uu___2 = FStar_Compiler_Effect.op_Bang bg_z3_proc in
     uu___2.refresh ());
    (let uu___2 = flatten_fresh_scope () in
     FStar_Compiler_Effect.op_Colon_Equals bg_scope uu___2)
let (context_profile : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun theory ->
    let uu___ =
      FStar_Compiler_List.fold_left
        (fun uu___1 ->
           fun d ->
             match uu___1 with
             | (out, _total) ->
                 (match d with
                  | FStar_SMTEncoding_Term.Module (name, decls) ->
                      let decls1 =
                        FStar_Compiler_List.filter
                          (fun uu___2 ->
                             match uu___2 with
                             | FStar_SMTEncoding_Term.Assume uu___3 -> true
                             | uu___3 -> false) decls in
                      let n = FStar_Compiler_List.length decls1 in
                      (((name, n) :: out), (n + _total))
                  | uu___2 -> (out, _total))) ([], Prims.int_zero) theory in
    match uu___ with
    | (modules, total_decls) ->
        let modules1 =
          FStar_Compiler_List.sortWith
            (fun uu___1 ->
               fun uu___2 ->
                 match (uu___1, uu___2) with
                 | ((uu___3, n), (uu___4, m)) -> m - n) modules in
        (if modules1 <> []
         then
           (let uu___2 = FStar_Compiler_Util.string_of_int total_decls in
            FStar_Compiler_Util.print1
              "Z3 Proof Stats: context_profile with %s assertions\n" uu___2)
         else ();
         FStar_Compiler_List.iter
           (fun uu___2 ->
              match uu___2 with
              | (m, n) ->
                  if n <> Prims.int_zero
                  then
                    let uu___3 = FStar_Compiler_Util.string_of_int n in
                    FStar_Compiler_Util.print2
                      "Z3 Proof Stats: %s produced %s SMT decls\n" m uu___3
                  else ()) modules1)
let (mk_input :
  Prims.bool ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (Prims.string * Prims.string FStar_Pervasives_Native.option *
        Prims.string FStar_Pervasives_Native.option))
  =
  fun fresh ->
    fun theory ->
      let ver = FStar_Options.z3_version () in
      let options = "; Z3 invocation started by F*\n" in
      let options1 =
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Compiler_Effect.op_Bang FStar_Options._version in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStar_Compiler_Effect.op_Bang FStar_Options._commit in
                Prims.strcat uu___5 "\n" in
              Prims.strcat " -- hash: " uu___4 in
            Prims.strcat uu___2 uu___3 in
          Prims.strcat "; F* version: " uu___1 in
        Prims.strcat options uu___ in
      let options2 =
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Options.z3_version () in
            Prims.strcat uu___2 "\n" in
          Prims.strcat "; Z3 version (according to F*): " uu___1 in
        Prims.strcat options1 uu___ in
      let options3 =
        let uu___ = z3_options ver in Prims.strcat options2 uu___ in
      let options4 =
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Options.z3_smtopt () in
            FStar_Compiler_Effect.op_Bar_Greater uu___2
              (FStar_Compiler_String.concat "\n") in
          Prims.strcat uu___1 "\n\n" in
        Prims.strcat options3 uu___ in
      (let uu___1 = FStar_Options.print_z3_statistics () in
       if uu___1 then context_profile theory else ());
      (let uu___1 =
         let uu___2 =
           (FStar_Options.record_hints ()) ||
             ((FStar_Options.use_hints ()) &&
                (FStar_Options.use_hint_hashes ())) in
         if uu___2
         then
           let uu___3 =
             let uu___4 =
               FStar_Compiler_Effect.op_Bar_Greater theory
                 (FStar_Compiler_Util.prefix_until
                    (fun uu___5 ->
                       match uu___5 with
                       | FStar_SMTEncoding_Term.CheckSat -> true
                       | uu___6 -> false)) in
             FStar_Compiler_Effect.op_Bar_Greater uu___4
               FStar_Compiler_Option.get in
           match uu___3 with
           | (prefix, check_sat, suffix) ->
               let pp =
                 FStar_Compiler_List.map
                   (FStar_SMTEncoding_Term.declToSmt options4) in
               let suffix1 = check_sat :: suffix in
               let ps_lines = pp prefix in
               let ss_lines = pp suffix1 in
               let ps = FStar_Compiler_String.concat "\n" ps_lines in
               let ss = FStar_Compiler_String.concat "\n" ss_lines in
               let hs =
                 let uu___4 = FStar_Options.keep_query_captions () in
                 if uu___4
                 then
                   let uu___5 =
                     FStar_Compiler_Effect.op_Bar_Greater prefix
                       (FStar_Compiler_List.map
                          (FStar_SMTEncoding_Term.declToSmt_no_caps options4)) in
                   FStar_Compiler_Effect.op_Bar_Greater uu___5
                     (FStar_Compiler_String.concat "\n")
                 else ps in
               let hs1 = Prims.strcat hs (Prims.strcat "Z3 version: " ver) in
               let uu___4 =
                 let uu___5 = FStar_Compiler_Util.digest_of_string hs1 in
                 FStar_Pervasives_Native.Some uu___5 in
               ((Prims.strcat ps (Prims.strcat "\n" ss)), uu___4)
         else
           (let uu___4 =
              let uu___5 =
                FStar_Compiler_List.map
                  (FStar_SMTEncoding_Term.declToSmt options4) theory in
              FStar_Compiler_Effect.op_Bar_Greater uu___5
                (FStar_Compiler_String.concat "\n") in
            (uu___4, FStar_Pervasives_Native.None)) in
       match uu___1 with
       | (r, hash) ->
           let log_file_name =
             let uu___2 = FStar_Options.log_queries () in
             if uu___2
             then
               let uu___3 = query_logging.write_to_log fresh r in
               FStar_Pervasives_Native.Some uu___3
             else FStar_Pervasives_Native.None in
           (r, hash, log_file_name))
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string FStar_Pervasives_Native.option ->
        z3result FStar_Pervasives_Native.option)
  =
  fun log_file ->
    fun cache ->
      fun qhash ->
        let uu___ =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()) in
        if uu___
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Compiler_Util.smap_create Prims.int_zero in
              (FStar_Compiler_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status = (UNSAT FStar_Pervasives_Native.None);
                    z3result_time = Prims.int_zero;
                    z3result_statistics = stats;
                    z3result_query_hash = qhash;
                    z3result_log_file = log_file
                  } in
                FStar_Pervasives_Native.Some result))
          | uu___1 -> FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.None
let (z3_job :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Compiler_Range_Type.range ->
      Prims.bool ->
        FStar_SMTEncoding_Term.error_labels ->
          Prims.string ->
            Prims.string FStar_Pervasives_Native.option ->
              Prims.string -> unit -> z3result)
  =
  fun log_file ->
    fun r ->
      fun fresh ->
        fun label_messages ->
          fun input ->
            fun qhash ->
              fun queryid ->
                fun uu___ ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 = query_logging.get_module_name () in
                      FStar_Pervasives_Native.Some uu___3 in
                    FStar_Profiling.profile
                      (fun uu___3 ->
                         try
                           (fun uu___4 ->
                              match () with
                              | () ->
                                  FStar_Compiler_Util.record_time
                                    (fun uu___5 ->
                                       doZ3Exe log_file r fresh input
                                         label_messages queryid)) ()
                         with
                         | uu___4 ->
                             (refresh (); FStar_Compiler_Effect.raise uu___4))
                      uu___2 "FStar.SMTEncoding.Z3 (aggregate query time)" in
                  match uu___1 with
                  | ((status, statistics), elapsed_time) ->
                      {
                        z3result_status = status;
                        z3result_time = elapsed_time;
                        z3result_statistics = statistics;
                        z3result_query_hash = qhash;
                        z3result_log_file = log_file
                      }
let (ask_text :
  FStar_Compiler_Range_Type.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            Prims.string -> Prims.string)
  =
  fun r ->
    fun filter_theory ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun queryid ->
              let theory = flatten_fresh_scope () in
              let theory1 =
                FStar_Compiler_List.op_At theory
                  (FStar_Compiler_List.op_At [FStar_SMTEncoding_Term.Push]
                     (FStar_Compiler_List.op_At qry
                        [FStar_SMTEncoding_Term.Pop])) in
              let uu___ = filter_theory theory1 in
              match uu___ with
              | (theory2, _used_unsat_core) ->
                  let uu___1 = mk_input true theory2 in
                  (match uu___1 with | (input, qhash, log_file_name) -> input)
let (ask :
  FStar_Compiler_Range_Type.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            Prims.string ->
              scope_t FStar_Pervasives_Native.option ->
                Prims.bool -> z3result)
  =
  fun r ->
    fun filter_theory ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun queryid ->
              fun _scope ->
                fun fresh ->
                  let theory =
                    if fresh
                    then flatten_fresh_scope ()
                    else
                      (let theory1 = FStar_Compiler_Effect.op_Bang bg_scope in
                       FStar_Compiler_Effect.op_Colon_Equals bg_scope [];
                       theory1) in
                  let theory1 =
                    FStar_Compiler_List.op_At theory
                      (FStar_Compiler_List.op_At
                         [FStar_SMTEncoding_Term.Push]
                         (FStar_Compiler_List.op_At qry
                            [FStar_SMTEncoding_Term.Pop])) in
                  let uu___ = filter_theory theory1 in
                  match uu___ with
                  | (theory2, _used_unsat_core) ->
                      let uu___1 = mk_input fresh theory2 in
                      (match uu___1 with
                       | (input, qhash, log_file_name) ->
                           let just_ask uu___2 =
                             z3_job log_file_name r fresh label_messages
                               input qhash queryid () in
                           if fresh
                           then
                             let uu___2 = cache_hit log_file_name cache qhash in
                             (match uu___2 with
                              | FStar_Pervasives_Native.Some z3r -> z3r
                              | FStar_Pervasives_Native.None -> just_ask ())
                           else just_ask ())
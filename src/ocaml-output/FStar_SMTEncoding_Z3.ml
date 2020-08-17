open Prims
let (_z3version_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (_z3version_expected : Prims.string) = "Z3 version 4.8.5"
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested"
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out ->
    match FStar_Util.splitlines out with
    | version::uu____29 ->
        if FStar_Util.starts_with version _z3version_expected
        then
          ((let uu____35 = FStar_Options.debug_any () in
            if uu____35
            then
              let uu____36 =
                FStar_Util.format1
                  "Successfully found expected Z3 version %s\n" version in
              FStar_Util.print_string uu____36
            else ());
           FStar_Pervasives_Native.None)
        else
          (let msg =
             FStar_Util.format2 "Expected Z3 version \"%s\", got \"%s\""
               _z3version_expected out in
           FStar_Pervasives_Native.Some msg)
    | uu____40 -> FStar_Pervasives_Native.Some "No Z3 version string found"
let (z3version_warning_message :
  unit ->
    (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____53 ->
    let run_proc_result =
      try
        (fun uu___15_61 ->
           match () with
           | () ->
               let uu____64 =
                 let uu____65 = FStar_Options.z3_exe () in
                 FStar_Util.run_process "z3_version" uu____65 ["-version"]
                   FStar_Pervasives_Native.None in
               FStar_Pervasives_Native.Some uu____64) ()
      with | uu___14_67 -> FStar_Pervasives_Native.None in
    match run_proc_result with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____81 = parse_z3_version_lines out in
        (match uu____81 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
let (check_z3version : unit -> unit) =
  fun uu____103 ->
    let uu____104 =
      let uu____105 = FStar_ST.op_Bang _z3version_checked in
      Prims.op_Negation uu____105 in
    if uu____104
    then
      (FStar_ST.op_Colon_Equals _z3version_checked true;
       (let uu____119 = z3version_warning_message () in
        match uu____119 with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some (e, msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH" in
            FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)))
    else ()
type label = Prims.string
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
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
  fun projectee ->
    match projectee with | UNSAT _0 -> true | uu____186 -> false
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee -> match projectee with | UNSAT _0 -> _0
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee -> match projectee with | SAT _0 -> true | uu____205 -> false
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | SAT _0 -> _0
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee ->
    match projectee with | UNKNOWN _0 -> true | uu____242 -> false
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | UNKNOWN _0 -> _0
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee ->
    match projectee with | TIMEOUT _0 -> true | uu____279 -> false
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | TIMEOUT _0 -> _0
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee -> match projectee with | KILLED -> true | uu____309 -> false
type z3statistics = Prims.string FStar_Util.smap
let (status_tag : z3status -> Prims.string) =
  fun uu___0_316 ->
    match uu___0_316 with
    | SAT uu____317 -> "sat"
    | UNSAT uu____324 -> "unsat"
    | UNKNOWN uu____325 -> "unknown"
    | TIMEOUT uu____332 -> "timeout"
    | KILLED -> "killed"
let (status_string_and_errors :
  z3status -> (Prims.string * FStar_SMTEncoding_Term.error_labels)) =
  fun s ->
    match s with
    | KILLED -> ((status_tag s), [])
    | UNSAT uu____352 -> ((status_tag s), [])
    | SAT (errs, msg) ->
        let uu____359 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1) in
        (uu____359, errs)
    | UNKNOWN (errs, msg) ->
        let uu____367 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1) in
        (uu____367, errs)
    | TIMEOUT (errs, msg) ->
        let uu____375 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1) in
        (uu____375, errs)
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.bool -> Prims.string -> Prims.string ;
  close_log: unit -> unit }
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        get_module_name
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        set_module_name
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.bool -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        write_to_log
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        close_log
let (query_logging : query_log) =
  let query_number = FStar_Util.mk_ref Prims.int_zero in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n =
    FStar_ST.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n) in
  let get_module_name uu____629 =
    let uu____630 = FStar_ST.op_Bang current_module_name in
    match uu____630 with
    | FStar_Pervasives_Native.None -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n -> n in
  let next_file_name uu____649 =
    let n = get_module_name () in
    let file_name =
      let uu____652 =
        let uu____659 = FStar_ST.op_Bang used_file_names in
        FStar_List.tryFind
          (fun uu____691 -> match uu____691 with | (m, uu____697) -> n = m)
          uu____659 in
      match uu____652 with
      | FStar_Pervasives_Native.None ->
          ((let uu____703 =
              let uu____710 = FStar_ST.op_Bang used_file_names in
              (n, Prims.int_zero) :: uu____710 in
            FStar_ST.op_Colon_Equals used_file_names uu____703);
           n)
      | FStar_Pervasives_Native.Some (uu____757, k) ->
          ((let uu____764 =
              let uu____771 = FStar_ST.op_Bang used_file_names in
              (n, (k + Prims.int_one)) :: uu____771 in
            FStar_ST.op_Colon_Equals used_file_names uu____764);
           (let uu____818 = FStar_Util.string_of_int (k + Prims.int_one) in
            FStar_Util.format2 "%s-%s" n uu____818)) in
    FStar_Util.format1 "queries-%s.smt2" file_name in
  let new_log_file uu____828 =
    let file_name = next_file_name () in
    FStar_ST.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let fh = FStar_Util.open_file_for_writing file_name in
     FStar_ST.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (fh, file_name));
     (fh, file_name)) in
  let get_log_file uu____874 =
    let uu____875 = FStar_ST.op_Bang log_file_opt in
    match uu____875 with
    | FStar_Pervasives_Native.None -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____923 = get_log_file () in
    match uu____923 with | (f, nm) -> (FStar_Util.append_to_file f str; nm) in
  let write_to_new_log str =
    let file_name = next_file_name () in
    FStar_Util.write_file file_name str; file_name in
  let write_to_log fresh str =
    if fresh then write_to_new_log str else append_to_log str in
  let close_log uu____956 =
    let uu____957 = FStar_ST.op_Bang log_file_opt in
    match uu____957 with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some (fh, uu____987) ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____1020 =
    let uu____1021 = FStar_ST.op_Bang current_file_name in
    match uu____1021 with
    | FStar_Pervasives_Native.None -> failwith "no log file"
    | FStar_Pervasives_Native.Some n -> n in
  { get_module_name; set_module_name; write_to_log; close_log }
let (z3_cmd_and_args : unit -> (Prims.string * Prims.string Prims.list)) =
  fun uu____1045 ->
    let cmd = FStar_Options.z3_exe () in
    let cmd_args =
      let uu____1050 =
        let uu____1053 =
          let uu____1056 =
            let uu____1059 =
              let uu____1060 =
                let uu____1061 = FStar_Options.z3_seed () in
                FStar_Util.string_of_int uu____1061 in
              FStar_Util.format1 "smt.random_seed=%s" uu____1060 in
            [uu____1059] in
          "-in" :: uu____1056 in
        "-smt2" :: uu____1053 in
      let uu____1062 = FStar_Options.z3_cliopt () in
      FStar_List.append uu____1050 uu____1062 in
    (cmd, cmd_args)
let (new_z3proc :
  Prims.string -> (Prims.string * Prims.string Prims.list) -> FStar_Util.proc)
  =
  fun id ->
    fun cmd_and_args ->
      check_z3version ();
      FStar_Util.start_process id (FStar_Pervasives_Native.fst cmd_and_args)
        (FStar_Pervasives_Native.snd cmd_and_args) (fun s -> s = "Done!")
let (new_z3proc_with_id :
  (Prims.string * Prims.string Prims.list) -> FStar_Util.proc) =
  let ctr = FStar_Util.mk_ref (~- Prims.int_one) in
  fun cmd_and_args ->
    let uu____1116 =
      let uu____1117 =
        FStar_Util.incr ctr;
        (let uu____1119 = FStar_ST.op_Bang ctr in
         FStar_All.pipe_right uu____1119 FStar_Util.string_of_int) in
      FStar_Util.format1 "bg-%s" uu____1117 in
    new_z3proc uu____1116 cmd_and_args
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit }
let (__proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string) =
  fun projectee -> match projectee with | { ask; refresh; restart;_} -> ask
let (__proj__Mkbgproc__item__refresh : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with | { ask; refresh; restart;_} -> refresh
let (__proj__Mkbgproc__item__restart : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with | { ask; refresh; restart;_} -> restart
let (cmd_and_args_to_string :
  (Prims.string * Prims.string Prims.list) -> Prims.string) =
  fun cmd_and_args ->
    FStar_String.concat ""
      ["cmd=";
      FStar_Pervasives_Native.fst cmd_and_args;
      " args=[";
      FStar_String.concat ", " (FStar_Pervasives_Native.snd cmd_and_args);
      "]"]
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let the_z3proc_params =
    FStar_Util.mk_ref (FStar_Pervasives_Native.Some ("", [""])) in
  let the_z3proc_ask_count = FStar_Util.mk_ref Prims.int_zero in
  let make_new_z3_proc cmd_and_args =
    (let uu____1307 =
       let uu____1310 = new_z3proc_with_id cmd_and_args in
       FStar_Pervasives_Native.Some uu____1310 in
     FStar_ST.op_Colon_Equals the_z3proc uu____1307);
    FStar_ST.op_Colon_Equals the_z3proc_params
      (FStar_Pervasives_Native.Some cmd_and_args);
    FStar_ST.op_Colon_Equals the_z3proc_ask_count Prims.int_zero in
  let z3proc uu____1361 =
    (let uu____1363 =
       let uu____1364 = FStar_ST.op_Bang the_z3proc in
       uu____1364 = FStar_Pervasives_Native.None in
     if uu____1363
     then let uu____1379 = z3_cmd_and_args () in make_new_z3_proc uu____1379
     else ());
    (let uu____1387 = FStar_ST.op_Bang the_z3proc in
     FStar_Util.must uu____1387) in
  let ask input =
    FStar_Util.incr the_z3proc_ask_count;
    (let kill_handler uu____1412 = "\nkilled\n" in
     let uu____1413 = z3proc () in
     FStar_Util.ask_process uu____1413 input kill_handler) in
  let refresh uu____1419 =
    let next_params = z3_cmd_and_args () in
    let old_params =
      let uu____1434 = FStar_ST.op_Bang the_z3proc_params in
      FStar_Util.must uu____1434 in
    (let uu____1472 =
       ((FStar_Options.log_queries ()) ||
          (let uu____1474 = FStar_ST.op_Bang the_z3proc_ask_count in
           uu____1474 > Prims.int_zero))
         || (Prims.op_Negation (old_params = next_params)) in
     if uu____1472
     then
       ((let uu____1488 =
           (FStar_Options.query_stats ()) &&
             (let uu____1490 =
                let uu____1491 = FStar_ST.op_Bang the_z3proc in
                uu____1491 = FStar_Pervasives_Native.None in
              Prims.op_Negation uu____1490) in
         if uu____1488
         then
           let uu____1506 =
             let uu____1507 = FStar_ST.op_Bang the_z3proc_ask_count in
             FStar_Util.string_of_int uu____1507 in
           FStar_Util.print3
             "Refreshing the z3proc (ask_count=%s old=[%s] new=[%s]) \n"
             uu____1506 (cmd_and_args_to_string old_params)
             (cmd_and_args_to_string next_params)
         else ());
        (let uu____1516 = z3proc () in FStar_Util.kill_process uu____1516);
        make_new_z3_proc next_params)
     else ());
    query_logging.close_log () in
  let restart uu____1523 =
    query_logging.close_log ();
    (let next_params = z3_cmd_and_args () in make_new_z3_proc next_params) in
  let x = [] in
  FStar_Util.mk_ref
    {
      ask = (FStar_Util.with_monitor x ask);
      refresh = (FStar_Util.with_monitor x refresh);
      restart = (FStar_Util.with_monitor x restart)
    }
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
    FStar_Range.range -> Prims.string Prims.list -> smt_output)
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
                (let uu____1775 = until tag lines2 in
                 FStar_Util.map_opt uu____1775
                   (fun uu____1805 ->
                      match uu____1805 with
                      | (until_tag, rest) -> ((l :: until_tag), rest))) in
        let start_tag tag = Prims.op_Hat "<" (Prims.op_Hat tag ">") in
        let end_tag tag = Prims.op_Hat "</" (Prims.op_Hat tag ">") in
        let find_section tag lines1 =
          let uu____1883 = until (start_tag tag) lines1 in
          match uu____1883 with
          | FStar_Pervasives_Native.None ->
              (FStar_Pervasives_Native.None, lines1)
          | FStar_Pervasives_Native.Some (prefix, suffix) ->
              let uu____1938 = until (end_tag tag) suffix in
              (match uu____1938 with
               | FStar_Pervasives_Native.None ->
                   failwith
                     (Prims.op_Hat "Parse error: "
                        (Prims.op_Hat (end_tag tag) " not found"))
               | FStar_Pervasives_Native.Some (section, suffix1) ->
                   ((FStar_Pervasives_Native.Some section),
                     (FStar_List.append prefix suffix1))) in
        let uu____2003 = find_section "result" lines in
        match uu____2003 with
        | (result_opt, lines1) ->
            let result = FStar_Util.must result_opt in
            let uu____2033 = find_section "reason-unknown" lines1 in
            (match uu____2033 with
             | (reason_unknown, lines2) ->
                 let uu____2058 = find_section "unsat-core" lines2 in
                 (match uu____2058 with
                  | (unsat_core1, lines3) ->
                      let uu____2083 = find_section "statistics" lines3 in
                      (match uu____2083 with
                       | (statistics, lines4) ->
                           let uu____2108 = find_section "labels" lines4 in
                           (match uu____2108 with
                            | (labels, lines5) ->
                                let remaining =
                                  let uu____2136 = until "Done!" lines5 in
                                  match uu____2136 with
                                  | FStar_Pervasives_Native.None -> lines5
                                  | FStar_Pervasives_Native.Some
                                      (prefix, suffix) ->
                                      FStar_List.append prefix suffix in
                                ((match remaining with
                                  | [] -> ()
                                  | uu____2176 ->
                                      let msg =
                                        FStar_Util.format2
                                          "%sUnexpected output from Z3: %s\n"
                                          (match log_file with
                                           | FStar_Pervasives_Native.None ->
                                               ""
                                           | FStar_Pervasives_Native.Some f
                                               -> Prims.op_Hat f ": ")
                                          (FStar_String.concat "\n" remaining) in
                                      FStar_Errors.log_issue r
                                        (FStar_Errors.Warning_UnexpectedZ3Output,
                                          msg));
                                 (let uu____2181 = FStar_Util.must result_opt in
                                  {
                                    smt_result = uu____2181;
                                    smt_reason_unknown = reason_unknown;
                                    smt_unsat_core = unsat_core1;
                                    smt_statistics = statistics;
                                    smt_labels = labels
                                  }))))))
let (doZ3Exe :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      Prims.bool ->
        Prims.string ->
          FStar_SMTEncoding_Term.error_labels -> (z3status * z3statistics))
  =
  fun log_file ->
    fun r ->
      fun fresh ->
        fun input ->
          fun label_messages ->
            let parse z3out =
              let lines =
                FStar_All.pipe_right (FStar_String.split [10] z3out)
                  (FStar_List.map FStar_Util.trim_string) in
              let smt_output1 = smt_output_sections log_file r lines in
              let unsat_core1 =
                match smt_output1.smt_unsat_core with
                | FStar_Pervasives_Native.None ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some s ->
                    let s1 =
                      FStar_Util.trim_string (FStar_String.concat " " s) in
                    let s2 =
                      FStar_Util.substring s1 Prims.int_one
                        ((FStar_String.length s1) - (Prims.of_int (2))) in
                    if FStar_Util.starts_with s2 "error"
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____2248 =
                         FStar_All.pipe_right (FStar_Util.split s2 " ")
                           (FStar_Util.sort_with FStar_String.compare) in
                       FStar_Pervasives_Native.Some uu____2248) in
              let labels =
                match smt_output1.smt_labels with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some lines1 ->
                    let rec lblnegs lines2 =
                      match lines2 with
                      | lname::"false"::rest when
                          FStar_Util.starts_with lname "label_" ->
                          let uu____2277 = lblnegs rest in lname ::
                            uu____2277
                      | lname::uu____2281::rest when
                          FStar_Util.starts_with lname "label_" ->
                          lblnegs rest
                      | uu____2285 -> [] in
                    let lblnegs1 = lblnegs lines1 in
                    FStar_All.pipe_right lblnegs1
                      (FStar_List.collect
                         (fun l ->
                            let uu____2302 =
                              FStar_All.pipe_right label_messages
                                (FStar_List.tryFind
                                   (fun uu____2338 ->
                                      match uu____2338 with
                                      | (m, uu____2346, uu____2347) ->
                                          let uu____2348 =
                                            FStar_SMTEncoding_Term.fv_name m in
                                          uu____2348 = l)) in
                            match uu____2302 with
                            | FStar_Pervasives_Native.None -> []
                            | FStar_Pervasives_Native.Some (lbl, msg, r1) ->
                                [(lbl, msg, r1)])) in
              let statistics =
                let statistics = FStar_Util.smap_create Prims.int_zero in
                match smt_output1.smt_statistics with
                | FStar_Pervasives_Native.None -> statistics
                | FStar_Pervasives_Native.Some lines1 ->
                    let parse_line line =
                      let pline =
                        FStar_Util.split (FStar_Util.trim_string line) ":" in
                      match pline with
                      | "("::entry::[] ->
                          let tokens = FStar_Util.split entry " " in
                          let key = FStar_List.hd tokens in
                          let ltok =
                            FStar_List.nth tokens
                              ((FStar_List.length tokens) - Prims.int_one) in
                          let value =
                            if FStar_Util.ends_with ltok ")"
                            then
                              FStar_Util.substring ltok Prims.int_zero
                                ((FStar_String.length ltok) - Prims.int_one)
                            else ltok in
                          FStar_Util.smap_add statistics key value
                      | ""::entry::[] ->
                          let tokens = FStar_Util.split entry " " in
                          let key = FStar_List.hd tokens in
                          let ltok =
                            FStar_List.nth tokens
                              ((FStar_List.length tokens) - Prims.int_one) in
                          let value =
                            if FStar_Util.ends_with ltok ")"
                            then
                              FStar_Util.substring ltok Prims.int_zero
                                ((FStar_String.length ltok) - Prims.int_one)
                            else ltok in
                          FStar_Util.smap_add statistics key value
                      | uu____2418 -> () in
                    (FStar_List.iter parse_line lines1; statistics) in
              let reason_unknown =
                FStar_Util.map_opt smt_output1.smt_reason_unknown
                  (fun x ->
                     let ru = FStar_String.concat " " x in
                     if FStar_Util.starts_with ru "(:reason-unknown \""
                     then
                       let reason =
                         FStar_Util.substring_from ru
                           (FStar_String.length "(:reason-unknown \"") in
                       let res =
                         FStar_String.substring reason Prims.int_zero
                           ((FStar_String.length reason) - (Prims.of_int (2))) in
                       res
                     else ru) in
              let status =
                (let uu____2436 = FStar_Options.debug_any () in
                 if uu____2436
                 then
                   let uu____2437 =
                     FStar_Util.format1 "Z3 says: %s\n"
                       (FStar_String.concat "\n" smt_output1.smt_result) in
                   FStar_All.pipe_left FStar_Util.print_string uu____2437
                 else ());
                (match smt_output1.smt_result with
                 | "unsat"::[] -> UNSAT unsat_core1
                 | "sat"::[] -> SAT (labels, reason_unknown)
                 | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
                 | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
                 | "killed"::[] ->
                     ((let uu____2446 = FStar_ST.op_Bang bg_z3_proc in
                       uu____2446.restart ());
                      KILLED)
                 | uu____2453 ->
                     let uu____2454 =
                       FStar_Util.format1
                         "Unexpected output from Z3: got output result: %s\n"
                         (FStar_String.concat "\n" smt_output1.smt_result) in
                     failwith uu____2454) in
              (status, statistics) in
            let stdout =
              if fresh
              then
                let proc =
                  let uu____2457 = z3_cmd_and_args () in
                  new_z3proc_with_id uu____2457 in
                let kill_handler uu____2469 = "\nkilled\n" in
                let out = FStar_Util.ask_process proc input kill_handler in
                (FStar_Util.kill_process proc; out)
              else
                (let uu____2473 = FStar_ST.op_Bang bg_z3_proc in
                 uu____2473.ask input) in
            parse (FStar_Util.trim_string stdout)
let (z3_options : Prims.string FStar_ST.ref) =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n(set-option :model true)\n(set-option :smt.case_split 3)\n(set-option :smt.relevancy 2)\n"
let (set_z3_options : Prims.string -> unit) =
  fun opts -> FStar_ST.op_Colon_Equals z3_options opts
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
let (init : unit -> unit) = fun uu____2604 -> ()
let (finish : unit -> unit) = fun uu____2609 -> ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let (fresh_scope : scope_t FStar_ST.ref) = FStar_Util.mk_ref [[]]
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____2624 -> FStar_ST.op_Bang fresh_scope
let (flatten_fresh_scope : unit -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun uu____2637 ->
    let uu____2638 =
      let uu____2643 = FStar_ST.op_Bang fresh_scope in
      FStar_List.rev uu____2643 in
    FStar_List.flatten uu____2638
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (push : Prims.string -> unit) =
  fun msg ->
    FStar_Util.atomically
      (fun uu____2670 ->
         (let uu____2672 =
            let uu____2673 = FStar_ST.op_Bang fresh_scope in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu____2673 in
          FStar_ST.op_Colon_Equals fresh_scope uu____2672);
         (let uu____2692 =
            let uu____2695 = FStar_ST.op_Bang bg_scope in
            FStar_List.append uu____2695
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg] in
          FStar_ST.op_Colon_Equals bg_scope uu____2692))
let (pop : Prims.string -> unit) =
  fun msg ->
    FStar_Util.atomically
      (fun uu____2726 ->
         (let uu____2728 =
            let uu____2729 = FStar_ST.op_Bang fresh_scope in
            FStar_List.tl uu____2729 in
          FStar_ST.op_Colon_Equals fresh_scope uu____2728);
         (let uu____2748 =
            let uu____2751 = FStar_ST.op_Bang bg_scope in
            FStar_List.append uu____2751
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop] in
          FStar_ST.op_Colon_Equals bg_scope uu____2748))
let (snapshot : Prims.string -> (Prims.int * unit)) =
  fun msg -> FStar_Common.snapshot push fresh_scope msg
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg ->
    fun depth ->
      FStar_Common.rollback (fun uu____2802 -> pop msg) fresh_scope depth
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___1_2816 ->
            match uu___1_2816 with
            | FStar_SMTEncoding_Term.Push -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop -> failwith "Unexpected push/pop"
            | uu____2817 -> ()));
    (let uu____2819 = FStar_ST.op_Bang fresh_scope in
     match uu____2819 with
     | hd::tl ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd decls)
           :: tl)
     | uu____2844 -> failwith "Impossible");
    (let uu____2845 =
       let uu____2848 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____2848 decls in
     FStar_ST.op_Colon_Equals bg_scope uu____2845)
let (refresh : unit -> unit) =
  fun uu____2875 ->
    (let uu____2877 = FStar_ST.op_Bang bg_z3_proc in uu____2877.refresh ());
    (let uu____2884 = flatten_fresh_scope () in
     FStar_ST.op_Colon_Equals bg_scope uu____2884)
let (context_profile : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun theory ->
    let uu____2906 =
      FStar_List.fold_left
        (fun uu____2935 ->
           fun d ->
             match uu____2935 with
             | (out, _total) ->
                 (match d with
                  | FStar_SMTEncoding_Term.Module (name, decls) ->
                      let decls1 =
                        FStar_List.filter
                          (fun uu___2_2992 ->
                             match uu___2_2992 with
                             | FStar_SMTEncoding_Term.Assume uu____2993 ->
                                 true
                             | uu____2994 -> false) decls in
                      let n = FStar_List.length decls1 in
                      (((name, n) :: out), (n + _total))
                  | uu____3006 -> (out, _total))) ([], Prims.int_zero) theory in
    match uu____2906 with
    | (modules, total_decls) ->
        let modules1 =
          FStar_List.sortWith
            (fun uu____3054 ->
               fun uu____3055 ->
                 match (uu____3054, uu____3055) with
                 | ((uu____3072, n), (uu____3074, m)) -> m - n) modules in
        (if modules1 <> []
         then
           (let uu____3095 = FStar_Util.string_of_int total_decls in
            FStar_Util.print1
              "Z3 Proof Stats: context_profile with %s assertions\n"
              uu____3095)
         else ();
         FStar_List.iter
           (fun uu____3105 ->
              match uu____3105 with
              | (m, n) ->
                  if n <> Prims.int_zero
                  then
                    let uu____3112 = FStar_Util.string_of_int n in
                    FStar_Util.print2
                      "Z3 Proof Stats: %s produced %s SMT decls\n" m
                      uu____3112
                  else ()) modules1)
let (mk_input :
  Prims.bool ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (Prims.string * Prims.string FStar_Pervasives_Native.option *
        Prims.string FStar_Pervasives_Native.option))
  =
  fun fresh ->
    fun theory ->
      let options = FStar_ST.op_Bang z3_options in
      (let uu____3146 = FStar_Options.print_z3_statistics () in
       if uu____3146 then context_profile theory else ());
      (let uu____3148 =
         let uu____3155 =
           (FStar_Options.record_hints ()) ||
             ((FStar_Options.use_hints ()) &&
                (FStar_Options.use_hint_hashes ())) in
         if uu____3155
         then
           let uu____3162 =
             let uu____3173 =
               FStar_All.pipe_right theory
                 (FStar_Util.prefix_until
                    (fun uu___3_3201 ->
                       match uu___3_3201 with
                       | FStar_SMTEncoding_Term.CheckSat -> true
                       | uu____3202 -> false)) in
             FStar_All.pipe_right uu____3173 FStar_Option.get in
           match uu____3162 with
           | (prefix, check_sat, suffix) ->
               let pp =
                 FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) in
               let suffix1 = check_sat :: suffix in
               let ps_lines = pp prefix in
               let ss_lines = pp suffix1 in
               let ps = FStar_String.concat "\n" ps_lines in
               let ss = FStar_String.concat "\n" ss_lines in
               let hs =
                 let uu____3273 = FStar_Options.keep_query_captions () in
                 if uu____3273
                 then
                   let uu____3274 =
                     FStar_All.pipe_right prefix
                       (FStar_List.map
                          (FStar_SMTEncoding_Term.declToSmt_no_caps options)) in
                   FStar_All.pipe_right uu____3274 (FStar_String.concat "\n")
                 else ps in
               let uu____3284 =
                 let uu____3287 = FStar_Util.digest_of_string hs in
                 FStar_Pervasives_Native.Some uu____3287 in
               ((Prims.op_Hat ps (Prims.op_Hat "\n" ss)), uu____3284)
         else
           (let uu____3291 =
              let uu____3292 =
                FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)
                  theory in
              FStar_All.pipe_right uu____3292 (FStar_String.concat "\n") in
            (uu____3291, FStar_Pervasives_Native.None)) in
       match uu____3148 with
       | (r, hash) ->
           let log_file_name =
             let uu____3318 = FStar_Options.log_queries () in
             if uu____3318
             then
               let uu____3321 = query_logging.write_to_log fresh r in
               FStar_Pervasives_Native.Some uu____3321
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
        let uu____3358 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()) in
        if uu____3358
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Util.smap_create Prims.int_zero in
              (FStar_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status = (UNSAT FStar_Pervasives_Native.None);
                    z3result_time = Prims.int_zero;
                    z3result_statistics = stats;
                    z3result_query_hash = qhash;
                    z3result_log_file = log_file
                  } in
                FStar_Pervasives_Native.Some result))
          | uu____3371 -> FStar_Pervasives_Native.None
        else FStar_Pervasives_Native.None
let (z3_job :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_SMTEncoding_Term.error_labels ->
          Prims.string ->
            Prims.string FStar_Pervasives_Native.option -> unit -> z3result)
  =
  fun log_file ->
    fun r ->
      fun fresh ->
        fun label_messages ->
          fun input ->
            fun qhash ->
              fun uu____3413 ->
                let uu____3418 =
                  let uu____3427 =
                    let uu____3430 = query_logging.get_module_name () in
                    FStar_Pervasives_Native.Some uu____3430 in
                  FStar_Profiling.profile
                    (fun uu____3440 ->
                       try
                         (fun uu___487_3450 ->
                            match () with
                            | () ->
                                FStar_Util.record_time
                                  (fun uu____3464 ->
                                     doZ3Exe log_file r fresh input
                                       label_messages)) ()
                       with
                       | uu___486_3467 ->
                           (refresh (); FStar_Exn.raise uu___486_3467))
                    uu____3427 "FStar.SMTEncoding.Z3 (aggregate query time)" in
                match uu____3418 with
                | ((status, statistics), elapsed_time) ->
                    {
                      z3result_status = status;
                      z3result_time = elapsed_time;
                      z3result_statistics = statistics;
                      z3result_query_hash = qhash;
                      z3result_log_file = log_file
                    }
let (ask :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            scope_t FStar_Pervasives_Native.option -> Prims.bool -> z3result)
  =
  fun r ->
    fun filter_theory ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun _scope ->
              fun fresh ->
                let theory =
                  if fresh
                  then flatten_fresh_scope ()
                  else
                    (let theory = FStar_ST.op_Bang bg_scope in
                     FStar_ST.op_Colon_Equals bg_scope []; theory) in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
                let uu____3593 = filter_theory theory1 in
                match uu____3593 with
                | (theory2, _used_unsat_core) ->
                    let uu____3606 = mk_input fresh theory2 in
                    (match uu____3606 with
                     | (input, qhash, log_file_name) ->
                         let just_ask uu____3633 =
                           z3_job log_file_name r fresh label_messages input
                             qhash () in
                         if fresh
                         then
                           let uu____3634 =
                             cache_hit log_file_name cache qhash in
                           (match uu____3634 with
                            | FStar_Pervasives_Native.Some z3r -> z3r
                            | FStar_Pervasives_Native.None -> just_ask ())
                         else just_ask ())
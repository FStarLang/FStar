open Prims
let _z3hash_checked: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let _z3hash_expected: Prims.string = "1f29cebd4df6"
let _z3url: Prims.string =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested"
let parse_z3_version_lines:
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____19 ->
        let trimmed = FStar_Util.trim_string x in
        let parts = FStar_Util.split trimmed " " in
        let rec aux uu___95_33 =
          match uu___95_33 with
          | hash::[] ->
              if hash = _z3hash_expected
              then
                ((let uu____42 = FStar_Options.debug_any () in
                  if uu____42
                  then
                    let msg =
                      FStar_Util.format1
                        "Successfully found expected Z3 commit hash %s"
                        _z3hash_expected in
                    FStar_Util.print_string msg
                  else ());
                 FStar_Pervasives_Native.None)
              else
                (let msg =
                   FStar_Util.format2 "Expected Z3 commit hash %s, got %s"
                     _z3hash_expected hash in
                 FStar_Pervasives_Native.Some msg)
          | uu____47::q -> aux q
          | uu____51 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found" in
        aux parts
    | uu____54 -> FStar_Pervasives_Native.Some "No Z3 version string found"
let z3hash_warning_message:
  Prims.unit ->
    (FStar_Errors.issue_level,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun uu____66  ->
    let run_proc_result =
      try
        let uu____95 =
          let uu____102 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____102 "-version" "" in
        FStar_Pervasives_Native.Some uu____95
      with | uu____120 -> FStar_Pervasives_Native.None in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.EError, "Could not run Z3")
    | FStar_Pervasives_Native.Some (uu____143,out,uu____145) ->
        let uu____152 = parse_z3_version_lines out in
        (match uu____152 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some (FStar_Errors.EWarning, msg))
let check_z3hash: Prims.unit -> Prims.unit =
  fun uu____173  ->
    let uu____174 =
      let uu____175 = FStar_ST.op_Bang _z3hash_checked in
      Prims.op_Negation uu____175 in
    if uu____174
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____197 = z3hash_warning_message () in
        match uu____197 with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some (level,msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH" in
            FStar_Errors.add_one
              (FStar_Errors.mk_issue level FStar_Pervasives_Native.None msg1)))
    else ()
let ini_params: Prims.unit -> Prims.string =
  fun uu____219  ->
    check_z3hash ();
    (let uu____221 =
       let uu____224 =
         let uu____227 =
           let uu____230 =
             let uu____231 =
               let uu____232 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____232 in
             FStar_Util.format1 "smt.random_seed=%s" uu____231 in
           [uu____230] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____227 in
       let uu____233 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____224 uu____233 in
     FStar_String.concat " " uu____221)
type label = Prims.string
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
type z3status =
  | UNSAT of unsat_core
  | SAT of
  (FStar_SMTEncoding_Term.error_labels,Prims.string
                                         FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | UNKNOWN of
  (FStar_SMTEncoding_Term.error_labels,Prims.string
                                         FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | TIMEOUT of
  (FStar_SMTEncoding_Term.error_labels,Prims.string
                                         FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2
  | KILLED
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____279 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____299 -> false
let __proj__SAT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____337 -> false
let __proj__UNKNOWN__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____375 -> false
let __proj__TIMEOUT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____406 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_tag: z3status -> Prims.string =
  fun uu___96_412  ->
    match uu___96_412 with
    | SAT uu____413 -> "sat"
    | UNSAT uu____420 -> "unsat"
    | UNKNOWN uu____421 -> "unknown"
    | TIMEOUT uu____428 -> "timeout"
    | KILLED  -> "killed"
let status_string_and_errors:
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____449 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____458 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____458, errs)
    | UNKNOWN (errs,msg) ->
        let uu____466 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____466, errs)
    | TIMEOUT (errs,msg) ->
        let uu____474 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____474, errs)
let tid: Prims.unit -> Prims.string =
  fun uu____479  ->
    let uu____480 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____480 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____493 = FStar_Options.z3_exe () in
    let uu____494 = ini_params () in
    FStar_Util.start_process id uu____493 uu____494 cond
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc;
  release: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;
  restart: Prims.unit -> Prims.unit;}
let __proj__Mkbgproc__item__grab: bgproc -> Prims.unit -> FStar_Util.proc =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__grab
let __proj__Mkbgproc__item__release: bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__release
let __proj__Mkbgproc__item__refresh: bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__refresh
let __proj__Mkbgproc__item__restart: bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__restart
type query_log =
  {
  get_module_name: Prims.unit -> Prims.string;
  set_module_name: Prims.string -> Prims.unit;
  write_to_log: Prims.string -> Prims.unit;
  close_log: Prims.unit -> Prims.unit;
  log_file_name: Prims.unit -> Prims.string;}
let __proj__Mkquery_log__item__get_module_name:
  query_log -> Prims.unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
let __proj__Mkquery_log__item__set_module_name:
  query_log -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
let __proj__Mkquery_log__item__write_to_log:
  query_log -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
let __proj__Mkquery_log__item__close_log:
  query_log -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
let __proj__Mkquery_log__item__log_file_name:
  query_log -> Prims.unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
let query_logging: query_log =
  let query_number = FStar_Util.mk_ref (Prims.parse_int "0") in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n1 =
    FStar_ST.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n1) in
  let get_module_name uu____853 =
    let uu____854 = FStar_ST.op_Bang current_module_name in
    match uu____854 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____893 =
    let uu____894 = FStar_ST.op_Bang current_module_name in
    match uu____894 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____931 =
            let uu____938 = FStar_ST.op_Bang used_file_names in
            FStar_List.tryFind
              (fun uu____1000  ->
                 match uu____1000 with | (m,uu____1006) -> n1 = m) uu____938 in
          match uu____931 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1012 =
                  let uu____1019 = FStar_ST.op_Bang used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____1019 in
                FStar_ST.op_Colon_Equals used_file_names uu____1012);
               n1)
          | FStar_Pervasives_Native.Some (uu____1126,k) ->
              ((let uu____1133 =
                  let uu____1140 = FStar_ST.op_Bang used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1140 in
                FStar_ST.op_Colon_Equals used_file_names uu____1133);
               (let uu____1247 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____1247)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh)) in
  let get_log_file uu____1319 =
    let uu____1320 = FStar_ST.op_Bang log_file_opt in
    match uu____1320 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____1360 = get_log_file () in
    FStar_Util.append_to_file uu____1360 str in
  let write_to_new_log str =
    let dir_name =
      let uu____1366 = FStar_ST.op_Bang current_file_name in
      match uu____1366 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1402 = FStar_ST.op_Bang current_module_name in
            match uu____1402 with
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.op_Colon_Equals current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
      | FStar_Pervasives_Native.Some n1 -> n1 in
    let qnum = FStar_ST.op_Bang query_number in
    (let uu____1499 =
       let uu____1500 = FStar_ST.op_Bang query_number in
       uu____1500 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals query_number uu____1499);
    (let file_name =
       let uu____1550 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____1550 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____1556 =
      let uu____1557 = FStar_Options.n_cores () in
      uu____1557 > (Prims.parse_int "1") in
    if uu____1556 then write_to_new_log str else append_to_log str in
  let close_log uu____1562 =
    let uu____1563 = FStar_ST.op_Bang log_file_opt in
    match uu____1563 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____1635 =
    let uu____1636 = FStar_ST.op_Bang current_file_name in
    match uu____1636 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____1685  ->
      let uu____1686 =
        let uu____1687 =
          FStar_Util.incr ctr;
          (let uu____1710 = FStar_ST.op_Bang ctr in
           FStar_All.pipe_right uu____1710 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____1687 in
      new_z3proc uu____1686 in
  let z3proc uu____1738 =
    (let uu____1740 =
       let uu____1741 = FStar_ST.op_Bang the_z3proc in
       uu____1741 = FStar_Pervasives_Native.None in
     if uu____1740
     then
       let uu____1778 =
         let uu____1781 = new_proc () in
         FStar_Pervasives_Native.Some uu____1781 in
       FStar_ST.op_Colon_Equals the_z3proc uu____1778
     else ());
    (let uu____1815 = FStar_ST.op_Bang the_z3proc in
     FStar_Util.must uu____1815) in
  let x = [] in
  let grab uu____1856 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____1863 = FStar_Util.monitor_exit x in
  let refresh uu____1869 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____1873 =
       let uu____1876 = new_proc () in
       FStar_Pervasives_Native.Some uu____1876 in
     FStar_ST.op_Colon_Equals the_z3proc uu____1873);
    query_logging.close_log ();
    release () in
  let restart uu____1913 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____1950 =
       let uu____1953 = new_proc () in
       FStar_Pervasives_Native.Some uu____1953 in
     FStar_ST.op_Colon_Equals the_z3proc uu____1950);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____1989  ->
    let uu____1990 = FStar_Options.log_queries () in
    if uu____1990
    then
      let uu____1991 = query_logging.log_file_name () in
      Prims.strcat "@" uu____1991
    else ""
type smt_output_section = Prims.string Prims.list
type smt_output =
  {
  smt_result: smt_output_section;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option;
  smt_labels: smt_output_section FStar_Pervasives_Native.option;}
let __proj__Mksmt_output__item__smt_result: smt_output -> smt_output_section
  =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_result
let __proj__Mksmt_output__item__smt_reason_unknown:
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_reason_unknown
let __proj__Mksmt_output__item__smt_unsat_core:
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_unsat_core
let __proj__Mksmt_output__item__smt_statistics:
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_statistics
let __proj__Mksmt_output__item__smt_labels:
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_labels
let smt_output_sections: Prims.string Prims.list -> smt_output =
  fun lines  ->
    let rec until tag lines1 =
      match lines1 with
      | [] -> FStar_Pervasives_Native.None
      | l::lines2 ->
          if tag = l
          then FStar_Pervasives_Native.Some ([], lines2)
          else
            (let uu____2198 = until tag lines2 in
             FStar_Util.map_opt uu____2198
               (fun uu____2228  ->
                  match uu____2228 with
                  | (until_tag,rest) -> ((l :: until_tag), rest))) in
    let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
    let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
    let find_section tag lines1 =
      let uu____2298 = until (start_tag tag) lines1 in
      match uu____2298 with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, lines1)
      | FStar_Pervasives_Native.Some (prefix1,suffix) ->
          let uu____2353 = until (end_tag tag) suffix in
          (match uu____2353 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.strcat "Parse error: "
                    (Prims.strcat (end_tag tag) " not found"))
           | FStar_Pervasives_Native.Some (section,suffix1) ->
               ((FStar_Pervasives_Native.Some section),
                 (FStar_List.append prefix1 suffix1))) in
    let uu____2418 = find_section "result" lines in
    match uu____2418 with
    | (result_opt,lines1) ->
        let result = FStar_Util.must result_opt in
        let uu____2448 = find_section "reason-unknown" lines1 in
        (match uu____2448 with
         | (reason_unknown,lines2) ->
             let uu____2473 = find_section "unsat-core" lines2 in
             (match uu____2473 with
              | (unsat_core,lines3) ->
                  let uu____2498 = find_section "statistics" lines3 in
                  (match uu____2498 with
                   | (statistics,lines4) ->
                       let uu____2523 = find_section "labels" lines4 in
                       (match uu____2523 with
                        | (labels,lines5) ->
                            let remaining =
                              let uu____2551 = until "Done!" lines5 in
                              match uu____2551 with
                              | FStar_Pervasives_Native.None  -> lines5
                              | FStar_Pervasives_Native.Some (prefix1,suffix)
                                  -> FStar_List.append prefix1 suffix in
                            ((match remaining with
                              | [] -> ()
                              | uu____2591 ->
                                  let uu____2594 =
                                    let uu____2595 =
                                      query_logging.get_module_name () in
                                    FStar_Util.format2
                                      "%s: Unexpected output from Z3: %s\n"
                                      uu____2595
                                      (FStar_String.concat "\n" remaining) in
                                  FStar_Errors.warn FStar_Range.dummyRange
                                    uu____2594);
                             (let uu____2596 = FStar_Util.must result_opt in
                              {
                                smt_result = uu____2596;
                                smt_reason_unknown = reason_unknown;
                                smt_unsat_core = unsat_core;
                                smt_statistics = statistics;
                                smt_labels = labels
                              }))))))
let doZ3Exe:
  Prims.bool ->
    Prims.string ->
      FStar_SMTEncoding_Term.error_labels ->
        (z3status,z3statistics) FStar_Pervasives_Native.tuple2
  =
  fun fresh1  ->
    fun input  ->
      fun label_messages  ->
        let parse z3out =
          let lines =
            FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
              (FStar_List.map FStar_Util.trim_string) in
          let smt_output = smt_output_sections lines in
          let unsat_core =
            match smt_output.smt_unsat_core with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some s ->
                let s1 = FStar_Util.trim_string (FStar_String.concat " " s) in
                let s2 =
                  FStar_Util.substring s1 (Prims.parse_int "1")
                    ((FStar_String.length s1) - (Prims.parse_int "2")) in
                if FStar_Util.starts_with s2 "error"
                then FStar_Pervasives_Native.None
                else
                  (let uu____2656 =
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_Util.sort_with FStar_String.compare) in
                   FStar_Pervasives_Native.Some uu____2656) in
          let labels =
            match smt_output.smt_labels with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some lines1 ->
                let rec lblnegs lines2 =
                  match lines2 with
                  | lname::"false"::rest when
                      FStar_Util.starts_with lname "label_" ->
                      let uu____2717 = lblnegs rest in lname :: uu____2717
                  | lname::uu____2721::rest when
                      FStar_Util.starts_with lname "label_" -> lblnegs rest
                  | uu____2725 -> [] in
                let lblnegs1 = lblnegs lines1 in
                FStar_All.pipe_right lblnegs1
                  (FStar_List.collect
                     (fun l  ->
                        let uu____2758 =
                          FStar_All.pipe_right label_messages
                            (FStar_List.tryFind
                               (fun uu____2797  ->
                                  match uu____2797 with
                                  | (m,uu____2809,uu____2810) ->
                                      (FStar_Pervasives_Native.fst m) = l)) in
                        match uu____2758 with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some (lbl,msg,r) ->
                            [(lbl, msg, r)])) in
          let statistics =
            let statistics = FStar_Util.smap_create (Prims.parse_int "0") in
            match smt_output.smt_statistics with
            | FStar_Pervasives_Native.None  -> statistics
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
                          ((FStar_List.length tokens) - (Prims.parse_int "1")) in
                      let value =
                        if FStar_Util.ends_with ltok ")"
                        then
                          FStar_Util.substring ltok (Prims.parse_int "0")
                            ((FStar_String.length ltok) -
                               (Prims.parse_int "1"))
                        else ltok in
                      FStar_Util.smap_add statistics key value
                  | ""::entry::[] ->
                      let tokens = FStar_Util.split entry " " in
                      let key = FStar_List.hd tokens in
                      let ltok =
                        FStar_List.nth tokens
                          ((FStar_List.length tokens) - (Prims.parse_int "1")) in
                      let value =
                        if FStar_Util.ends_with ltok ")"
                        then
                          FStar_Util.substring ltok (Prims.parse_int "0")
                            ((FStar_String.length ltok) -
                               (Prims.parse_int "1"))
                        else ltok in
                      FStar_Util.smap_add statistics key value
                  | uu____2922 -> () in
                (FStar_List.iter parse_line lines1; statistics) in
          let reason_unknown =
            FStar_Util.map_opt smt_output.smt_reason_unknown
              (fun x  ->
                 let ru = FStar_String.concat " " x in
                 if FStar_Util.starts_with ru "(:reason-unknown \""
                 then
                   let reason =
                     FStar_Util.substring_from ru
                       (FStar_String.length "(:reason-unknown \"") in
                   let res =
                     FStar_String.substring reason (Prims.parse_int "0")
                       ((FStar_String.length reason) - (Prims.parse_int "2")) in
                   res
                 else ru) in
          let status =
            (let uu____2940 = FStar_Options.debug_any () in
             if uu____2940
             then
               let uu____2941 =
                 FStar_Util.format1 "Z3 says: %s\n"
                   (FStar_String.concat "\n" smt_output.smt_result) in
               FStar_All.pipe_left FStar_Util.print_string uu____2941
             else ());
            (match smt_output.smt_result with
             | "unsat"::[] -> UNSAT unsat_core
             | "sat"::[] -> SAT (labels, reason_unknown)
             | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
             | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
             | "killed"::[] -> (bg_z3_proc.restart (); KILLED)
             | uu____2986 ->
                 let uu____2987 =
                   FStar_Util.format1
                     "Unexpected output from Z3: got output result: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result) in
                 failwith uu____2987) in
          (status, statistics) in
        let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
        let stdout1 =
          if fresh1
          then
            let uu____2997 = tid () in
            let uu____2998 = FStar_Options.z3_exe () in
            let uu____2999 = ini_params () in
            FStar_Util.launch_process uu____2997 uu____2998 uu____2999 input
              cond
          else
            (let proc = bg_z3_proc.grab () in
             let stdout1 = FStar_Util.ask_process proc input in
             bg_z3_proc.release (); stdout1) in
        parse (FStar_Util.trim_string stdout1)
let z3_options: Prims.unit -> Prims.string =
  fun uu____3007  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
let __proj__Mkjob__item__job: 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback: 'a . 'a job -> 'a -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
type z3job =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3 job
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor:
  'Auu____3110 'Auu____3111 .
    'Auu____3111 -> (Prims.unit -> 'Auu____3110) -> 'Auu____3110
  =
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f () in FStar_Util.monitor_exit m; res)
let z3_job:
  Prims.bool ->
    FStar_SMTEncoding_Term.error_labels ->
      Prims.string ->
        Prims.unit ->
          (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____3149  ->
          let start = FStar_Util.now () in
          let uu____3157 = doZ3Exe fresh1 input label_messages in
          match uu____3157 with
          | (status,statistics) ->
              let uu____3170 =
                let uu____3175 = FStar_Util.now () in
                FStar_Util.time_diff start uu____3175 in
              (match uu____3170 with
               | (uu____3182,elapsed_time) ->
                   (status, elapsed_time, statistics))
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____3199  ->
    let j =
      let uu____3201 = FStar_ST.op_Bang job_queue in
      match uu____3201 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____3258  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____3260  ->
    let uu____3261 = FStar_ST.op_Bang running in
    if uu____3261
    then
      let rec aux uu____3275 =
        FStar_Util.monitor_enter job_queue;
        (let uu____3281 = FStar_ST.op_Bang job_queue in
         match uu____3281 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____3308 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____3312 = j.job () in FStar_All.pipe_left j.callback uu____3312
let init: Prims.unit -> Prims.unit =
  fun uu____3340  ->
    FStar_ST.op_Colon_Equals running true;
    (let n_cores1 = FStar_Options.n_cores () in
     if n_cores1 > (Prims.parse_int "1")
     then
       let rec aux n1 =
         if n1 = (Prims.parse_int "0")
         then ()
         else (FStar_Util.spawn dequeue; aux (n1 - (Prims.parse_int "1"))) in
       aux n_cores1
     else ())
let enqueue: z3job -> Prims.unit =
  fun j  ->
    FStar_Util.monitor_enter job_queue;
    (let uu____3370 =
       let uu____3373 = FStar_ST.op_Bang job_queue in
       FStar_List.append uu____3373 [j] in
     FStar_ST.op_Colon_Equals job_queue uu____3370);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____3424  ->
    let rec aux uu____3428 =
      let uu____3429 =
        with_monitor job_queue
          (fun uu____3445  ->
             let uu____3446 = FStar_ST.op_Bang pending_jobs in
             let uu____3457 =
               let uu____3458 = FStar_ST.op_Bang job_queue in
               FStar_List.length uu____3458 in
             (uu____3446, uu____3457)) in
      match uu____3429 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let mk_fresh_scope: Prims.unit -> scope_t =
  fun uu____3529  -> FStar_ST.op_Bang fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3574 =
       let uu____3579 = FStar_ST.op_Bang fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____3579 in
     FStar_ST.op_Colon_Equals fresh_scope uu____3574);
    (let uu____3638 =
       let uu____3641 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3641
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.op_Colon_Equals bg_scope uu____3638)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3685 =
       let uu____3690 = FStar_ST.op_Bang fresh_scope in
       FStar_List.tl uu____3690 in
     FStar_ST.op_Colon_Equals fresh_scope uu____3685);
    (let uu____3749 =
       let uu____3752 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3752
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.op_Colon_Equals bg_scope uu____3749)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___97_3803  ->
            match uu___97_3803 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____3804 -> ()));
    (let uu____3806 = FStar_ST.op_Bang fresh_scope in
     match uu____3806 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____3875 -> failwith "Impossible");
    (let uu____3880 =
       let uu____3883 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3883 decls in
     FStar_ST.op_Colon_Equals bg_scope uu____3880)
let refresh: Prims.unit -> Prims.unit =
  fun uu____3925  ->
    (let uu____3927 =
       let uu____3928 = FStar_Options.n_cores () in
       uu____3928 < (Prims.parse_int "2") in
     if uu____3927 then bg_z3_proc.refresh () else ());
    (let uu____3930 =
       let uu____3933 =
         let uu____3938 = FStar_ST.op_Bang fresh_scope in
         FStar_List.rev uu____3938 in
       FStar_List.flatten uu____3933 in
     FStar_ST.op_Colon_Equals bg_scope uu____3930)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____4002 = FStar_ST.op_Bang fresh_scope in
    match uu____4002 with
    | hd1::s::tl1 ->
        FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 s) ::
          tl1)
    | uu____4076 -> failwith "Impossible"
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____4090 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____4090 (FStar_String.concat "\n") in
    (let uu____4096 = FStar_Options.log_queries () in
     if uu____4096 then query_logging.write_to_log r else ());
    r
type z3result =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
type cb = z3result -> Prims.unit
let ask_1_core:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun cb  ->
          let theory =
            let uu____4140 = FStar_ST.op_Bang bg_scope in
            FStar_List.append uu____4140
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____4161 = filter_theory theory in
          match uu____4161 with
          | (theory1,used_unsat_core) ->
              let input = mk_input theory1 in
              (FStar_ST.op_Colon_Equals bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb })
let ask_n_cores:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t ->
        scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let theory =
              let uu____4238 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.op_Colon_Equals bg_scope [];
                     (let uu____4269 = FStar_ST.op_Bang fresh_scope in
                      FStar_List.rev uu____4269)) in
              FStar_List.flatten uu____4238 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____4305 = filter_theory theory1 in
            match uu____4305 with
            | (theory2,used_unsat_core) ->
                let input = mk_input theory2 in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb }
let ask:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
  fun filter1  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let uu____4362 =
              let uu____4363 = FStar_Options.n_cores () in
              uu____4363 = (Prims.parse_int "1") in
            if uu____4362
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
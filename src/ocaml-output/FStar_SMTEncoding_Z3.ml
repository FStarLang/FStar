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
        let rec aux uu___124_33 =
          match uu___124_33 with
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
       (let uu____269 = z3hash_warning_message () in
        match uu____269 with
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
  fun uu____291  ->
    check_z3hash ();
    (let uu____293 =
       let uu____296 =
         let uu____299 =
           let uu____302 =
             let uu____303 =
               let uu____304 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____304 in
             FStar_Util.format1 "smt.random_seed=%s" uu____303 in
           [uu____302] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____299 in
       let uu____305 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____296 uu____305 in
     FStar_String.concat " " uu____293)
type label = Prims.string[@@deriving show]
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
[@@deriving show]
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
  | KILLED[@@deriving show]
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____351 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____371 -> false
let __proj__SAT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____409 -> false
let __proj__UNKNOWN__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____447 -> false
let __proj__TIMEOUT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____478 -> false
type z3statistics = Prims.string FStar_Util.smap[@@deriving show]
let status_tag: z3status -> Prims.string =
  fun uu___125_484  ->
    match uu___125_484 with
    | SAT uu____485 -> "sat"
    | UNSAT uu____492 -> "unsat"
    | UNKNOWN uu____493 -> "unknown"
    | TIMEOUT uu____500 -> "timeout"
    | KILLED  -> "killed"
let status_string_and_errors:
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____521 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____530 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____530, errs)
    | UNKNOWN (errs,msg) ->
        let uu____538 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____538, errs)
    | TIMEOUT (errs,msg) ->
        let uu____546 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____546, errs)
let tid: Prims.unit -> Prims.string =
  fun uu____551  ->
    let uu____552 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____552 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____565 = FStar_Options.z3_exe () in
    let uu____566 = ini_params () in
    FStar_Util.start_process false id uu____565 uu____566 cond
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc;
  release: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;
  restart: Prims.unit -> Prims.unit;}[@@deriving show]
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
  log_file_name: Prims.unit -> Prims.string;}[@@deriving show]
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
  let get_module_name uu____957 =
    let uu____958 = FStar_ST.op_Bang current_module_name in
    match uu____958 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____1029 =
    let uu____1030 = FStar_ST.op_Bang current_module_name in
    match uu____1030 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____1099 =
            let uu____1106 = FStar_ST.op_Bang used_file_names in
            FStar_List.tryFind
              (fun uu____1192  ->
                 match uu____1192 with | (m,uu____1198) -> n1 = m) uu____1106 in
          match uu____1099 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1204 =
                  let uu____1211 = FStar_ST.op_Bang used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____1211 in
                FStar_ST.op_Colon_Equals used_file_names uu____1204);
               n1)
          | FStar_Pervasives_Native.Some (uu____1366,k) ->
              ((let uu____1373 =
                  let uu____1380 = FStar_ST.op_Bang used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1380 in
                FStar_ST.op_Colon_Equals used_file_names uu____1373);
               (let uu____1535 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____1535)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh)) in
  let get_log_file uu____1671 =
    let uu____1672 = FStar_ST.op_Bang log_file_opt in
    match uu____1672 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____1744 = get_log_file () in
    FStar_Util.append_to_file uu____1744 str in
  let write_to_new_log str =
    let dir_name =
      let uu____1750 = FStar_ST.op_Bang current_file_name in
      match uu____1750 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1818 = FStar_ST.op_Bang current_module_name in
            match uu____1818 with
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
    (let uu____2015 =
       let uu____2016 = FStar_ST.op_Bang query_number in
       uu____2016 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals query_number uu____2015);
    (let file_name =
       let uu____2138 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____2138 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____2144 =
      let uu____2145 = FStar_Options.n_cores () in
      uu____2145 > (Prims.parse_int "1") in
    if uu____2144 then write_to_new_log str else append_to_log str in
  let close_log uu____2150 =
    let uu____2151 = FStar_ST.op_Bang log_file_opt in
    match uu____2151 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____2287 =
    let uu____2288 = FStar_ST.op_Bang current_file_name in
    match uu____2288 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____2369  ->
      let uu____2370 =
        let uu____2371 =
          FStar_Util.incr ctr;
          (let uu____2394 = FStar_ST.op_Bang ctr in
           FStar_All.pipe_right uu____2394 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____2371 in
      new_z3proc uu____2370 in
  let z3proc uu____2458 =
    (let uu____2460 =
       let uu____2461 = FStar_ST.op_Bang the_z3proc in
       uu____2461 = FStar_Pervasives_Native.None in
     if uu____2460
     then
       let uu____2530 =
         let uu____2533 = new_proc () in
         FStar_Pervasives_Native.Some uu____2533 in
       FStar_ST.op_Colon_Equals the_z3proc uu____2530
     else ());
    (let uu____2599 = FStar_ST.op_Bang the_z3proc in
     FStar_Util.must uu____2599) in
  let x = [] in
  let grab uu____2672 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____2679 = FStar_Util.monitor_exit x in
  let refresh uu____2685 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____2689 =
       let uu____2692 = new_proc () in
       FStar_Pervasives_Native.Some uu____2692 in
     FStar_ST.op_Colon_Equals the_z3proc uu____2689);
    query_logging.close_log ();
    release () in
  let restart uu____2761 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2830 =
       let uu____2833 = new_proc () in
       FStar_Pervasives_Native.Some uu____2833 in
     FStar_ST.op_Colon_Equals the_z3proc uu____2830);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____2901  ->
    let uu____2902 = FStar_Options.log_queries () in
    if uu____2902
    then
      let uu____2903 = query_logging.log_file_name () in
      Prims.strcat "@" uu____2903
    else ""
type smt_output_section = Prims.string Prims.list[@@deriving show]
type smt_output =
  {
  smt_result: smt_output_section;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option;
  smt_labels: smt_output_section FStar_Pervasives_Native.option;}[@@deriving
                                                                   show]
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
            (let uu____3110 = until tag lines2 in
             FStar_Util.map_opt uu____3110
               (fun uu____3140  ->
                  match uu____3140 with
                  | (until_tag,rest) -> ((l :: until_tag), rest))) in
    let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
    let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
    let find_section tag lines1 =
      let uu____3210 = until (start_tag tag) lines1 in
      match uu____3210 with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, lines1)
      | FStar_Pervasives_Native.Some (prefix1,suffix) ->
          let uu____3265 = until (end_tag tag) suffix in
          (match uu____3265 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.strcat "Parse error: "
                    (Prims.strcat (end_tag tag) " not found"))
           | FStar_Pervasives_Native.Some (section,suffix1) ->
               ((FStar_Pervasives_Native.Some section),
                 (FStar_List.append prefix1 suffix1))) in
    let uu____3330 = find_section "result" lines in
    match uu____3330 with
    | (result_opt,lines1) ->
        let result = FStar_Util.must result_opt in
        let uu____3360 = find_section "reason-unknown" lines1 in
        (match uu____3360 with
         | (reason_unknown,lines2) ->
             let uu____3385 = find_section "unsat-core" lines2 in
             (match uu____3385 with
              | (unsat_core,lines3) ->
                  let uu____3410 = find_section "statistics" lines3 in
                  (match uu____3410 with
                   | (statistics,lines4) ->
                       let uu____3435 = find_section "labels" lines4 in
                       (match uu____3435 with
                        | (labels,lines5) ->
                            let remaining =
                              let uu____3463 = until "Done!" lines5 in
                              match uu____3463 with
                              | FStar_Pervasives_Native.None  -> lines5
                              | FStar_Pervasives_Native.Some (prefix1,suffix)
                                  -> FStar_List.append prefix1 suffix in
                            ((match remaining with
                              | [] -> ()
                              | uu____3503 ->
                                  let uu____3506 =
                                    let uu____3507 =
                                      query_logging.get_module_name () in
                                    FStar_Util.format2
                                      "%s: Unexpected output from Z3: %s\n"
                                      uu____3507
                                      (FStar_String.concat "\n" remaining) in
                                  FStar_Errors.warn FStar_Range.dummyRange
                                    uu____3506);
                             (let uu____3508 = FStar_Util.must result_opt in
                              {
                                smt_result = uu____3508;
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
            FStar_All.pipe_right (FStar_String.split [10] z3out)
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
                  (let uu____3568 =
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_Util.sort_with FStar_String.compare) in
                   FStar_Pervasives_Native.Some uu____3568) in
          let labels =
            match smt_output.smt_labels with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some lines1 ->
                let rec lblnegs lines2 =
                  match lines2 with
                  | lname::"false"::rest when
                      FStar_Util.starts_with lname "label_" ->
                      let uu____3629 = lblnegs rest in lname :: uu____3629
                  | lname::uu____3633::rest when
                      FStar_Util.starts_with lname "label_" -> lblnegs rest
                  | uu____3637 -> [] in
                let lblnegs1 = lblnegs lines1 in
                FStar_All.pipe_right lblnegs1
                  (FStar_List.collect
                     (fun l  ->
                        let uu____3670 =
                          FStar_All.pipe_right label_messages
                            (FStar_List.tryFind
                               (fun uu____3709  ->
                                  match uu____3709 with
                                  | (m,uu____3721,uu____3722) ->
                                      (FStar_Pervasives_Native.fst m) = l)) in
                        match uu____3670 with
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
                  | uu____3834 -> () in
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
            (let uu____3852 = FStar_Options.debug_any () in
             if uu____3852
             then
               let uu____3853 =
                 FStar_Util.format1 "Z3 says: %s\n"
                   (FStar_String.concat "\n" smt_output.smt_result) in
               FStar_All.pipe_left FStar_Util.print_string uu____3853
             else ());
            (match smt_output.smt_result with
             | "unsat"::[] -> UNSAT unsat_core
             | "sat"::[] -> SAT (labels, reason_unknown)
             | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
             | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
             | "killed"::[] -> (bg_z3_proc.restart (); KILLED)
             | uu____3898 ->
                 let uu____3899 =
                   FStar_Util.format1
                     "Unexpected output from Z3: got output result: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result) in
                 failwith uu____3899) in
          (status, statistics) in
        let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
        let stdout1 =
          if fresh1
          then
            let uu____3909 = tid () in
            let uu____3910 = FStar_Options.z3_exe () in
            let uu____3911 = ini_params () in
            FStar_Util.launch_process false uu____3909 uu____3910 uu____3911
              input cond
          else
            (let proc = bg_z3_proc.grab () in
             let stdout1 = FStar_Util.ask_process proc input in
             bg_z3_proc.release (); stdout1) in
        parse (FStar_Util.trim_string stdout1)
let z3_options: Prims.unit -> Prims.string =
  fun uu____3919  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}[@@deriving show]
let __proj__Mkjob__item__job: 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback: 'a . 'a job -> 'a -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
type z3result =
  {
  z3result_status: z3status;
  z3result_time: Prims.int;
  z3result_statistics: z3statistics;
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option;}[@@deriving
                                                                    show]
let __proj__Mkz3result__item__z3result_status: z3result -> z3status =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_status
let __proj__Mkz3result__item__z3result_time: z3result -> Prims.int =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_time
let __proj__Mkz3result__item__z3result_statistics: z3result -> z3statistics =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_statistics
let __proj__Mkz3result__item__z3result_query_hash:
  z3result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_query_hash
type z3job = z3result job[@@deriving show]
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor:
  'Auu____4078 'Auu____4079 .
    'Auu____4079 -> (Prims.unit -> 'Auu____4078) -> 'Auu____4078
  =
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f () in FStar_Util.monitor_exit m; res)
let z3_job:
  Prims.bool ->
    FStar_SMTEncoding_Term.error_labels ->
      Prims.string ->
        Prims.string FStar_Pervasives_Native.option -> Prims.unit -> z3result
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun qhash  ->
          fun uu____4117  ->
            let start = FStar_Util.now () in
            let uu____4121 =
              try doZ3Exe fresh1 input label_messages
              with
              | uu____4145 when
                  let uu____4146 = FStar_Options.trace_error () in
                  Prims.op_Negation uu____4146 ->
                  (bg_z3_proc.refresh ();
                   (let uu____4148 =
                      FStar_Util.smap_create (Prims.parse_int "0") in
                    ((UNKNOWN
                        ([],
                          (FStar_Pervasives_Native.Some
                             "Z3 raised an exception"))), uu____4148))) in
            match uu____4121 with
            | (status,statistics) ->
                let uu____4159 =
                  let uu____4164 = FStar_Util.now () in
                  FStar_Util.time_diff start uu____4164 in
                (match uu____4159 with
                 | (uu____4165,elapsed_time) ->
                     {
                       z3result_status = status;
                       z3result_time = elapsed_time;
                       z3result_statistics = statistics;
                       z3result_query_hash = qhash
                     })
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____4182  ->
    let j =
      let uu____4184 = FStar_ST.op_Bang job_queue in
      match uu____4184 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____4305  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____4307  ->
    let uu____4308 = FStar_ST.op_Bang running in
    if uu____4308
    then
      let rec aux uu____4358 =
        FStar_Util.monitor_enter job_queue;
        (let uu____4364 = FStar_ST.op_Bang job_queue in
         match uu____4364 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____4423 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____4427 = j.job () in FStar_All.pipe_left j.callback uu____4427
let init: Prims.unit -> Prims.unit =
  fun uu____4431  ->
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
    (let uu____4497 =
       let uu____4500 = FStar_ST.op_Bang job_queue in
       FStar_List.append uu____4500 [j] in
     FStar_ST.op_Colon_Equals job_queue uu____4497);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____4615  ->
    let rec aux uu____4619 =
      let uu____4620 =
        with_monitor job_queue
          (fun uu____4636  ->
             let uu____4637 = FStar_ST.op_Bang pending_jobs in
             let uu____4684 =
               let uu____4685 = FStar_ST.op_Bang job_queue in
               FStar_List.length uu____4685 in
             (uu____4637, uu____4684)) in
      match uu____4620 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list[@@deriving
                                                                  show]
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let mk_fresh_scope: Prims.unit -> scope_t =
  fun uu____4824  -> FStar_ST.op_Bang fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____4897 =
       let uu____4902 = FStar_ST.op_Bang fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____4902 in
     FStar_ST.op_Colon_Equals fresh_scope uu____4897);
    (let uu____5017 =
       let uu____5020 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____5020
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.op_Colon_Equals bg_scope uu____5017)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____5128 =
       let uu____5133 = FStar_ST.op_Bang fresh_scope in
       FStar_List.tl uu____5133 in
     FStar_ST.op_Colon_Equals fresh_scope uu____5128);
    (let uu____5248 =
       let uu____5251 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____5251
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.op_Colon_Equals bg_scope uu____5248)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___126_5366  ->
            match uu___126_5366 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____5367 -> ()));
    (let uu____5369 = FStar_ST.op_Bang fresh_scope in
     match uu____5369 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____5494 -> failwith "Impossible");
    (let uu____5499 =
       let uu____5502 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____5502 decls in
     FStar_ST.op_Colon_Equals bg_scope uu____5499)
let refresh: Prims.unit -> Prims.unit =
  fun uu____5608  ->
    (let uu____5610 =
       let uu____5611 = FStar_Options.n_cores () in
       uu____5611 < (Prims.parse_int "2") in
     if uu____5610 then bg_z3_proc.refresh () else ());
    (let uu____5613 =
       let uu____5616 =
         let uu____5621 = FStar_ST.op_Bang fresh_scope in
         FStar_List.rev uu____5621 in
       FStar_List.flatten uu____5616 in
     FStar_ST.op_Colon_Equals bg_scope uu____5613)
let mk_input:
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun theory  ->
    let options = z3_options () in
    let uu____5747 =
      let uu____5754 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())) in
      if uu____5754
      then
        let uu____5761 =
          let uu____5772 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___127_5800  ->
                    match uu___127_5800 with
                    | FStar_SMTEncoding_Term.CheckSat  -> true
                    | uu____5801 -> false)) in
          FStar_All.pipe_right uu____5772 FStar_Option.get in
        match uu____5761 with
        | (prefix1,check_sat,suffix) ->
            let pp =
              FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) in
            let pp_no_cap =
              FStar_List.map
                (FStar_SMTEncoding_Term.declToSmt_no_caps options) in
            let suffix1 = check_sat :: suffix in
            let ps_lines = pp prefix1 in
            let ss_lines = pp suffix1 in
            let ps = FStar_String.concat "\n" ps_lines in
            let ss = FStar_String.concat "\n" ss_lines in
            let uncaption uu___128_5879 =
              match uu___128_5879 with
              | FStar_SMTEncoding_Term.Caption uu____5880 ->
                  FStar_SMTEncoding_Term.Caption ""
              | FStar_SMTEncoding_Term.Assume a ->
                  FStar_SMTEncoding_Term.Assume
                    (let uu___133_5884 = a in
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         (uu___133_5884.FStar_SMTEncoding_Term.assumption_term);
                       FStar_SMTEncoding_Term.assumption_caption =
                         FStar_Pervasives_Native.None;
                       FStar_SMTEncoding_Term.assumption_name =
                         (uu___133_5884.FStar_SMTEncoding_Term.assumption_name);
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         (uu___133_5884.FStar_SMTEncoding_Term.assumption_fact_ids)
                     })
              | FStar_SMTEncoding_Term.DeclFun (n1,a,s,uu____5888) ->
                  FStar_SMTEncoding_Term.DeclFun
                    (n1, a, s, FStar_Pervasives_Native.None)
              | FStar_SMTEncoding_Term.DefineFun (n1,a,s,b,uu____5901) ->
                  FStar_SMTEncoding_Term.DefineFun
                    (n1, a, s, b, FStar_Pervasives_Native.None)
              | d -> d in
            let hs =
              let uu____5912 =
                let uu____5915 =
                  let uu____5918 =
                    FStar_All.pipe_right prefix1 (FStar_List.map uncaption) in
                  FStar_All.pipe_right uu____5918 pp_no_cap in
                FStar_All.pipe_right uu____5915
                  (FStar_List.filter (fun s  -> s <> "")) in
              FStar_All.pipe_right uu____5912 (FStar_String.concat "\n") in
            let uu____5937 =
              let uu____5940 = FStar_Util.digest_of_string hs in
              FStar_Pervasives_Native.Some uu____5940 in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____5937)
      else
        (let uu____5944 =
           let uu____5945 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory in
           FStar_All.pipe_right uu____5945 (FStar_String.concat "\n") in
         (uu____5944, FStar_Pervasives_Native.None)) in
    match uu____5747 with
    | (r,hash) ->
        ((let uu____5965 = FStar_Options.log_queries () in
          if uu____5965 then query_logging.write_to_log r else ());
         (r, hash))
type cb = z3result -> Prims.unit[@@deriving show]
let cache_hit:
  (Prims.string FStar_Pervasives_Native.option,unsat_core)
    FStar_Pervasives_Native.tuple2 ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool
  =
  fun cache  ->
    fun qhash  ->
      fun cb  ->
        let uu____6001 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()) in
        if uu____6001
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when
              qhash = (FStar_Pervasives_Native.fst cache) ->
              let stats = FStar_Util.smap_create (Prims.parse_int "0") in
              (FStar_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status =
                      (UNSAT (FStar_Pervasives_Native.snd cache));
                    z3result_time = (Prims.parse_int "0");
                    z3result_statistics = stats;
                    z3result_query_hash = qhash
                  } in
                cb result; true))
          | uu____6014 -> false
        else false
let ask_1_core:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    (Prims.string FStar_Pervasives_Native.option,unsat_core)
      FStar_Pervasives_Native.tuple2 ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun cb  ->
            let theory =
              let uu____6068 = FStar_ST.op_Bang bg_scope in
              FStar_List.append uu____6068
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____6121 = filter_theory theory in
            match uu____6121 with
            | (theory1,used_unsat_core) ->
                let uu____6128 = mk_input theory1 in
                (match uu____6128 with
                 | (input,qhash) ->
                     (FStar_ST.op_Colon_Equals bg_scope [];
                      (let uu____6192 =
                         let uu____6193 = cache_hit cache qhash cb in
                         Prims.op_Negation uu____6193 in
                       if uu____6192
                       then
                         run_job
                           {
                             job = (z3_job false label_messages input qhash);
                             callback = cb
                           }
                       else ())))
let ask_n_cores:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    (Prims.string FStar_Pervasives_Native.option,unsat_core)
      FStar_Pervasives_Native.tuple2 ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decls_t ->
          scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun scope  ->
            fun cb  ->
              let theory =
                let uu____6257 =
                  match scope with
                  | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                  | FStar_Pervasives_Native.None  ->
                      (FStar_ST.op_Colon_Equals bg_scope [];
                       (let uu____6320 = FStar_ST.op_Bang fresh_scope in
                        FStar_List.rev uu____6320)) in
                FStar_List.flatten uu____6257 in
              let theory1 =
                FStar_List.append theory
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
              let uu____6384 = filter_theory theory1 in
              match uu____6384 with
              | (theory2,used_unsat_core) ->
                  let uu____6391 = mk_input theory2 in
                  (match uu____6391 with
                   | (input,qhash) ->
                       let uu____6404 =
                         let uu____6405 = cache_hit cache qhash cb in
                         Prims.op_Negation uu____6405 in
                       if uu____6404
                       then
                         enqueue
                           {
                             job = (z3_job true label_messages input qhash);
                             callback = cb
                           }
                       else ())
let ask:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    (Prims.string FStar_Pervasives_Native.option,unsat_core)
      FStar_Pervasives_Native.tuple2 ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decl Prims.list ->
          scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
  fun filter1  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun scope  ->
            fun cb  ->
              let uu____6468 =
                let uu____6469 = FStar_Options.n_cores () in
                uu____6469 = (Prims.parse_int "1") in
              if uu____6468
              then ask_1_core filter1 cache label_messages qry cb
              else ask_n_cores filter1 cache label_messages qry scope cb
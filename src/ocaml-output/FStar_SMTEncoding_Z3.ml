open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (_z3hash_expected : Prims.string) = "1f29cebd4df6"
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested"
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out ->
    match FStar_Util.splitlines out with
    | x::uu____48 ->
        let trimmed = FStar_Util.trim_string x in
        let parts = FStar_Util.split trimmed " " in
        let rec aux uu___41_64 =
          match uu___41_64 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash) in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1 in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____75 = FStar_Options.debug_any () in
                  if uu____75
                  then
                    let msg =
                      FStar_Util.format1
                        "Successfully found expected Z3 commit hash %s\n"
                        hash in
                    FStar_Util.print_string msg
                  else ());
                 FStar_Pervasives_Native.None)
              else
                (let msg =
                   FStar_Util.format2
                     "Expected Z3 commit hash \"%s\", got \"%s\""
                     _z3hash_expected trimmed in
                 FStar_Pervasives_Native.Some msg)
          | uu____80::q -> aux q
          | uu____84 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found" in
        aux parts
    | uu____87 -> FStar_Pervasives_Native.Some "No Z3 version string found"
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error, Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____100 ->
    let run_proc_result =
      try
        let uu____129 =
          let uu____136 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____136 "-version" "" in
        FStar_Pervasives_Native.Some uu____129
      with | uu____154 -> FStar_Pervasives_Native.None in
    match run_proc_result with
    | FStar_Pervasives_Native.None ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some (uu____177, out, uu____179) ->
        let uu____186 = parse_z3_version_lines out in
        (match uu____186 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
let (check_z3hash : unit -> unit) =
  fun uu____208 ->
    let uu____209 =
      let uu____210 = FStar_ST.op_Bang _z3hash_checked in
      Prims.op_Negation uu____210 in
    if uu____209
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____270 = z3hash_warning_message () in
        match uu____270 with
        | FStar_Pervasives_Native.None -> ()
        | FStar_Pervasives_Native.Some (e, msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH" in
            FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)))
    else ()
let (ini_params : unit -> Prims.string) =
  fun uu____293 ->
    check_z3hash ();
    (let uu____295 =
       let uu____298 =
         let uu____301 =
           let uu____304 =
             let uu____305 =
               let uu____306 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____306 in
             FStar_Util.format1 "smt.random_seed=%s" uu____305 in
           [uu____304] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2 smt.case_split=3"
           :: uu____301 in
       let uu____307 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____298 uu____307 in
     FStar_String.concat " " uu____295)
type label = Prims.string[@@deriving show]
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
[@@deriving show]
type z3status =
  | UNSAT of unsat_core 
  | SAT of (FStar_SMTEncoding_Term.error_labels,
  Prims.string FStar_Pervasives_Native.option) FStar_Pervasives_Native.tuple2
  
  | UNKNOWN of (FStar_SMTEncoding_Term.error_labels,
  Prims.string FStar_Pervasives_Native.option) FStar_Pervasives_Native.tuple2
  
  | TIMEOUT of (FStar_SMTEncoding_Term.error_labels,
  Prims.string FStar_Pervasives_Native.option) FStar_Pervasives_Native.tuple2
  
  | KILLED [@@deriving show]
let (uu___is_UNSAT : z3status -> Prims.bool) =
  fun projectee ->
    match projectee with | UNSAT _0 -> true | uu____358 -> false
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee -> match projectee with | UNSAT _0 -> _0
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee -> match projectee with | SAT _0 -> true | uu____378 -> false
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,
      Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | SAT _0 -> _0
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee ->
    match projectee with | UNKNOWN _0 -> true | uu____416 -> false
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,
      Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | UNKNOWN _0 -> _0
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee ->
    match projectee with | TIMEOUT _0 -> true | uu____454 -> false
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,
      Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee -> match projectee with | TIMEOUT _0 -> _0
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee -> match projectee with | KILLED -> true | uu____485 -> false
type z3statistics = Prims.string FStar_Util.smap[@@deriving show]
let (status_tag : z3status -> Prims.string) =
  fun uu___42_492 ->
    match uu___42_492 with
    | SAT uu____493 -> "sat"
    | UNSAT uu____500 -> "unsat"
    | UNKNOWN uu____501 -> "unknown"
    | TIMEOUT uu____508 -> "timeout"
    | KILLED -> "killed"
let (status_string_and_errors :
  z3status ->
    (Prims.string, FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2)
  =
  fun s ->
    match s with
    | KILLED -> ((status_tag s), [])
    | UNSAT uu____530 -> ((status_tag s), [])
    | SAT (errs, msg) ->
        let uu____539 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____539, errs)
    | UNKNOWN (errs, msg) ->
        let uu____547 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____547, errs)
    | TIMEOUT (errs, msg) ->
        let uu____555 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____555, errs)
let (tid : unit -> Prims.string) =
  fun uu____561 ->
    let uu____562 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____562 FStar_Util.string_of_int
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1 ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____580 = FStar_Options.z3_exe () in
    let uu____581 = ini_params () in
    FStar_Util.start_process false id1 uu____580 uu____581 cond
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit }[@@deriving show]
let (__proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string) =
  fun projectee ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__ask
let (__proj__Mkbgproc__item__refresh : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__refresh
let (__proj__Mkbgproc__item__restart : bgproc -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__restart
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.string -> unit ;
  close_log: unit -> unit ;
  log_file_name: unit -> Prims.string }[@@deriving show]
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
let (__proj__Mkquery_log__item__log_file_name :
  query_log -> unit -> Prims.string) =
  fun projectee ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
let (query_logging : query_log) =
  let query_number = FStar_Util.mk_ref (Prims.parse_int "0") in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n1 =
    FStar_ST.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n1) in
  let get_module_name uu____1051 =
    let uu____1052 = FStar_ST.op_Bang current_module_name in
    match uu____1052 with
    | FStar_Pervasives_Native.None -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____1164 =
    let uu____1165 = FStar_ST.op_Bang current_module_name in
    match uu____1165 with
    | FStar_Pervasives_Native.None -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____1273 =
            let uu____1280 = FStar_ST.op_Bang used_file_names in
            FStar_List.tryFind
              (fun uu____1405 ->
                 match uu____1405 with | (m, uu____1411) -> n1 = m)
              uu____1280 in
          match uu____1273 with
          | FStar_Pervasives_Native.None ->
              ((let uu____1417 =
                  let uu____1424 = FStar_ST.op_Bang used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____1424 in
                FStar_ST.op_Colon_Equals used_file_names uu____1417);
               n1)
          | FStar_Pervasives_Native.Some (uu____1657, k) ->
              ((let uu____1664 =
                  let uu____1671 = FStar_ST.op_Bang used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1671 in
                FStar_ST.op_Colon_Equals used_file_names uu____1664);
               (let uu____1904 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____1904)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh)) in
  let get_log_file uu____2120 =
    let uu____2121 = FStar_ST.op_Bang log_file_opt in
    match uu____2121 with
    | FStar_Pervasives_Native.None -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____2234 = get_log_file () in
    FStar_Util.append_to_file uu____2234 str in
  let write_to_new_log str =
    let dir_name =
      let uu____2242 = FStar_ST.op_Bang current_file_name in
      match uu____2242 with
      | FStar_Pervasives_Native.None ->
          let dir_name =
            let uu____2349 = FStar_ST.op_Bang current_module_name in
            match uu____2349 with
            | FStar_Pervasives_Native.None ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.op_Colon_Equals current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
      | FStar_Pervasives_Native.Some n1 -> n1 in
    let qnum = FStar_ST.op_Bang query_number in
    (let uu____2663 =
       let uu____2664 = FStar_ST.op_Bang query_number in
       uu____2664 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals query_number uu____2663);
    (let file_name =
       let uu____2864 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____2864 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____2872 =
      let uu____2873 = FStar_Options.n_cores () in
      uu____2873 > (Prims.parse_int "1") in
    if uu____2872 then write_to_new_log str else append_to_log str in
  let close_log uu____2880 =
    let uu____2881 = FStar_ST.op_Bang log_file_opt in
    match uu____2881 with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____3097 =
    let uu____3098 = FStar_ST.op_Bang current_file_name in
    match uu____3098 with
    | FStar_Pervasives_Native.None -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1")) in
    fun uu____3257 ->
      let uu____3258 =
        let uu____3259 =
          FStar_Util.incr ctr;
          (let uu____3366 = FStar_ST.op_Bang ctr in
           FStar_All.pipe_right uu____3366 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____3259 in
      new_z3proc uu____3258 in
  let z3proc uu____3471 =
    (let uu____3473 =
       let uu____3474 = FStar_ST.op_Bang the_z3proc in
       uu____3474 = FStar_Pervasives_Native.None in
     if uu____3473
     then
       let uu____3582 =
         let uu____3585 = new_proc () in
         FStar_Pervasives_Native.Some uu____3585 in
       FStar_ST.op_Colon_Equals the_z3proc uu____3582
     else ());
    (let uu____3690 = FStar_ST.op_Bang the_z3proc in
     FStar_Util.must uu____3690) in
  let x = [] in
  let grab uu____3804 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____3813 = FStar_Util.monitor_exit x in
  let ask input =
    let proc = grab () in
    let stdout1 = FStar_Util.ask_process proc input in release (); stdout1 in
  let refresh uu____3830 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____3834 =
       let uu____3837 = new_proc () in
       FStar_Pervasives_Native.Some uu____3837 in
     FStar_ST.op_Colon_Equals the_z3proc uu____3834);
    query_logging.close_log ();
    release () in
  let restart uu____3947 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____4055 =
       let uu____4058 = new_proc () in
       FStar_Pervasives_Native.Some uu____4058 in
     FStar_ST.op_Colon_Equals the_z3proc uu____4055);
    FStar_Util.monitor_exit () in
  FStar_Util.mk_ref { ask; refresh; restart }
let (set_bg_z3_proc : bgproc -> unit) =
  fun bgp -> FStar_ST.op_Colon_Equals bg_z3_proc bgp
let (at_log_file : unit -> Prims.string) =
  fun uu____4200 ->
    let uu____4201 = FStar_Options.log_queries () in
    if uu____4201
    then
      let uu____4202 = query_logging.log_file_name () in
      Prims.strcat "@" uu____4202
    else ""
type smt_output_section = Prims.string Prims.list[@@deriving show]
type smt_output =
  {
  smt_result: smt_output_section ;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option ;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option ;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option ;
  smt_labels: smt_output_section FStar_Pervasives_Native.option }[@@deriving
                                                                   show]
let (__proj__Mksmt_output__item__smt_result :
  smt_output -> smt_output_section) =
  fun projectee ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_result
let (__proj__Mksmt_output__item__smt_reason_unknown :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_reason_unknown
let (__proj__Mksmt_output__item__smt_unsat_core :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_unsat_core
let (__proj__Mksmt_output__item__smt_statistics :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_statistics
let (__proj__Mksmt_output__item__smt_labels :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_labels
let (smt_output_sections :
  FStar_Range.range -> Prims.string Prims.list -> smt_output) =
  fun r ->
    fun lines ->
      let rec until tag lines1 =
        match lines1 with
        | [] -> FStar_Pervasives_Native.None
        | l::lines2 ->
            if tag = l
            then FStar_Pervasives_Native.Some ([], lines2)
            else
              (let uu____4429 = until tag lines2 in
               FStar_Util.map_opt uu____4429
                 (fun uu____4459 ->
                    match uu____4459 with
                    | (until_tag, rest) -> ((l :: until_tag), rest))) in
      let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
      let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
      let find_section tag lines1 =
        let uu____4537 = until (start_tag tag) lines1 in
        match uu____4537 with
        | FStar_Pervasives_Native.None ->
            (FStar_Pervasives_Native.None, lines1)
        | FStar_Pervasives_Native.Some (prefix1, suffix) ->
            let uu____4592 = until (end_tag tag) suffix in
            (match uu____4592 with
             | FStar_Pervasives_Native.None ->
                 failwith
                   (Prims.strcat "Parse error: "
                      (Prims.strcat (end_tag tag) " not found"))
             | FStar_Pervasives_Native.Some (section, suffix1) ->
                 ((FStar_Pervasives_Native.Some section),
                   (FStar_List.append prefix1 suffix1))) in
      let uu____4657 = find_section "result" lines in
      match uu____4657 with
      | (result_opt, lines1) ->
          let result = FStar_Util.must result_opt in
          let uu____4687 = find_section "reason-unknown" lines1 in
          (match uu____4687 with
           | (reason_unknown, lines2) ->
               let uu____4712 = find_section "unsat-core" lines2 in
               (match uu____4712 with
                | (unsat_core, lines3) ->
                    let uu____4737 = find_section "statistics" lines3 in
                    (match uu____4737 with
                     | (statistics, lines4) ->
                         let uu____4762 = find_section "labels" lines4 in
                         (match uu____4762 with
                          | (labels, lines5) ->
                              let remaining =
                                let uu____4790 = until "Done!" lines5 in
                                match uu____4790 with
                                | FStar_Pervasives_Native.None -> lines5
                                | FStar_Pervasives_Native.Some
                                    (prefix1, suffix) ->
                                    FStar_List.append prefix1 suffix in
                              ((match remaining with
                                | [] -> ()
                                | uu____4830 ->
                                    let uu____4833 =
                                      let uu____4838 =
                                        FStar_Util.format1
                                          "Unexpected output from Z3: %s\n"
                                          (FStar_String.concat "\n" remaining) in
                                      (FStar_Errors.Warning_UnexpectedZ3Output,
                                        uu____4838) in
                                    FStar_Errors.log_issue r uu____4833);
                               (let uu____4839 = FStar_Util.must result_opt in
                                {
                                  smt_result = uu____4839;
                                  smt_reason_unknown = reason_unknown;
                                  smt_unsat_core = unsat_core;
                                  smt_statistics = statistics;
                                  smt_labels = labels
                                }))))))
let (doZ3Exe :
  FStar_Range.range ->
    Prims.bool ->
      Prims.string ->
        FStar_SMTEncoding_Term.error_labels ->
          (z3status, z3statistics) FStar_Pervasives_Native.tuple2)
  =
  fun r ->
    fun fresh ->
      fun input ->
        fun label_messages ->
          let parse z3out =
            let lines =
              FStar_All.pipe_right (FStar_String.split [10] z3out)
                (FStar_List.map FStar_Util.trim_string) in
            let smt_output = smt_output_sections r lines in
            let unsat_core =
              match smt_output.smt_unsat_core with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some s ->
                  let s1 = FStar_Util.trim_string (FStar_String.concat " " s) in
                  let s2 =
                    FStar_Util.substring s1 (Prims.parse_int "1")
                      ((FStar_String.length s1) - (Prims.parse_int "2")) in
                  if FStar_Util.starts_with s2 "error"
                  then FStar_Pervasives_Native.None
                  else
                    (let uu____4912 =
                       FStar_All.pipe_right (FStar_Util.split s2 " ")
                         (FStar_Util.sort_with FStar_String.compare) in
                     FStar_Pervasives_Native.Some uu____4912) in
            let labels =
              match smt_output.smt_labels with
              | FStar_Pervasives_Native.None -> []
              | FStar_Pervasives_Native.Some lines1 ->
                  let rec lblnegs lines2 =
                    match lines2 with
                    | lname::"false"::rest when
                        FStar_Util.starts_with lname "label_" ->
                        let uu____4975 = lblnegs rest in lname :: uu____4975
                    | lname::uu____4979::rest when
                        FStar_Util.starts_with lname "label_" -> lblnegs rest
                    | uu____4983 -> [] in
                  let lblnegs1 = lblnegs lines1 in
                  FStar_All.pipe_right lblnegs1
                    (FStar_List.collect
                       (fun l ->
                          let uu____5016 =
                            FStar_All.pipe_right label_messages
                              (FStar_List.tryFind
                                 (fun uu____5055 ->
                                    match uu____5055 with
                                    | (m, uu____5067, uu____5068) ->
                                        (FStar_Pervasives_Native.fst m) = l)) in
                          match uu____5016 with
                          | FStar_Pervasives_Native.None -> []
                          | FStar_Pervasives_Native.Some (lbl, msg, r1) ->
                              [(lbl, msg, r1)])) in
            let statistics =
              let statistics = FStar_Util.smap_create (Prims.parse_int "0") in
              match smt_output.smt_statistics with
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
                            ((FStar_List.length tokens) -
                               (Prims.parse_int "1")) in
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
                            ((FStar_List.length tokens) -
                               (Prims.parse_int "1")) in
                        let value =
                          if FStar_Util.ends_with ltok ")"
                          then
                            FStar_Util.substring ltok (Prims.parse_int "0")
                              ((FStar_String.length ltok) -
                                 (Prims.parse_int "1"))
                          else ltok in
                        FStar_Util.smap_add statistics key value
                    | uu____5182 -> () in
                  (FStar_List.iter parse_line lines1; statistics) in
            let reason_unknown =
              FStar_Util.map_opt smt_output.smt_reason_unknown
                (fun x ->
                   let ru = FStar_String.concat " " x in
                   if FStar_Util.starts_with ru "(:reason-unknown \""
                   then
                     let reason =
                       FStar_Util.substring_from ru
                         (FStar_String.length "(:reason-unknown \"") in
                     let res =
                       FStar_String.substring reason (Prims.parse_int "0")
                         ((FStar_String.length reason) -
                            (Prims.parse_int "2")) in
                     res
                   else ru) in
            let status =
              (let uu____5200 = FStar_Options.debug_any () in
               if uu____5200
               then
                 let uu____5201 =
                   FStar_Util.format1 "Z3 says: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result) in
                 FStar_All.pipe_left FStar_Util.print_string uu____5201
               else ());
              (match smt_output.smt_result with
               | "unsat"::[] -> UNSAT unsat_core
               | "sat"::[] -> SAT (labels, reason_unknown)
               | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
               | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
               | "killed"::[] ->
                   ((let uu____5246 =
                       let uu____5251 = FStar_ST.op_Bang bg_z3_proc in
                       uu____5251.restart in
                     uu____5246 ());
                    KILLED)
               | uu____5281 ->
                   let uu____5282 =
                     FStar_Util.format1
                       "Unexpected output from Z3: got output result: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result) in
                   failwith uu____5282) in
            (status, statistics) in
          let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
          let stdout1 =
            if fresh
            then
              let uu____5296 = tid () in
              let uu____5297 = FStar_Options.z3_exe () in
              let uu____5298 = ini_params () in
              FStar_Util.launch_process false uu____5296 uu____5297
                uu____5298 input cond
            else
              (let uu____5300 =
                 let uu____5305 = FStar_ST.op_Bang bg_z3_proc in
                 uu____5305.ask in
               uu____5300 input) in
          parse (FStar_Util.trim_string stdout1)
let (z3_options : Prims.string FStar_ST.ref) =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
let (set_z3_options : Prims.string -> unit) =
  fun opts -> FStar_ST.op_Colon_Equals z3_options opts
type 'a job = {
  job: unit -> 'a ;
  callback: 'a -> unit }[@@deriving show]
let __proj__Mkjob__item__job : 'a . 'a job -> unit -> 'a =
  fun projectee ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> unit =
  fun projectee ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
type z3result =
  {
  z3result_status: z3status ;
  z3result_time: Prims.int ;
  z3result_statistics: z3statistics ;
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option }[@@deriving
                                                                    show]
let (__proj__Mkz3result__item__z3result_status : z3result -> z3status) =
  fun projectee ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_status
let (__proj__Mkz3result__item__z3result_time : z3result -> Prims.int) =
  fun projectee ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_time
let (__proj__Mkz3result__item__z3result_statistics :
  z3result -> z3statistics) =
  fun projectee ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_statistics
let (__proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_query_hash
type z3job = z3result job[@@deriving show]
let (job_queue : z3job Prims.list FStar_ST.ref) = FStar_Util.mk_ref []
let (pending_jobs : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor :
  'Auu____5640 'Auu____5641 .
    'Auu____5640 -> (unit -> 'Auu____5641) -> 'Auu____5641
  =
  fun m ->
    fun f ->
      FStar_Util.monitor_enter m;
      (let res = f () in FStar_Util.monitor_exit m; res)
let (z3_job :
  FStar_Range.range ->
    Prims.bool ->
      FStar_SMTEncoding_Term.error_labels ->
        Prims.string ->
          Prims.string FStar_Pervasives_Native.option -> unit -> z3result)
  =
  fun r ->
    fun fresh ->
      fun label_messages ->
        fun input ->
          fun qhash ->
            fun uu____5691 ->
              let start = FStar_Util.now () in
              let uu____5695 =
                try doZ3Exe r fresh input label_messages
                with
                | uu____5719 when
                    let uu____5720 = FStar_Options.trace_error () in
                    Prims.op_Negation uu____5720 ->
                    ((let uu____5722 =
                        let uu____5727 = FStar_ST.op_Bang bg_z3_proc in
                        uu____5727.refresh in
                      uu____5722 ());
                     (let uu____5757 =
                        FStar_Util.smap_create (Prims.parse_int "0") in
                      ((UNKNOWN
                          ([],
                            (FStar_Pervasives_Native.Some
                               "Z3 raised an exception"))), uu____5757))) in
              match uu____5695 with
              | (status, statistics) ->
                  let uu____5768 =
                    let uu____5773 = FStar_Util.now () in
                    FStar_Util.time_diff start uu____5773 in
                  (match uu____5768 with
                   | (uu____5774, elapsed_time) ->
                       {
                         z3result_status = status;
                         z3result_time = elapsed_time;
                         z3result_statistics = statistics;
                         z3result_query_hash = qhash
                       })
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let rec (dequeue' : unit -> unit) =
  fun uu____5825 ->
    let j =
      let uu____5827 = FStar_ST.op_Bang job_queue in
      match uu____5827 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____5914 -> FStar_Util.decr pending_jobs);
    dequeue ()
and (dequeue : unit -> unit) =
  fun uu____5916 ->
    let uu____5917 = FStar_ST.op_Bang running in
    if uu____5917
    then
      let rec aux uu____5952 =
        FStar_Util.monitor_enter job_queue;
        (let uu____5958 = FStar_ST.op_Bang job_queue in
         match uu____5958 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____6000 -> dequeue' ()) in
      aux ()
    else ()
and (run_job : z3job -> unit) =
  fun j ->
    let uu____6004 = j.job () in FStar_All.pipe_left j.callback uu____6004
let (init : unit -> unit) =
  fun uu____6009 ->
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
let (enqueue : z3job -> unit) =
  fun j ->
    FStar_Util.monitor_enter job_queue;
    (let uu____6061 =
       let uu____6064 = FStar_ST.op_Bang job_queue in
       FStar_List.append uu____6064 [j] in
     FStar_ST.op_Colon_Equals job_queue uu____6061);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let (finish : unit -> unit) =
  fun uu____6146 ->
    let rec aux uu____6152 =
      let uu____6153 =
        with_monitor job_queue
          (fun uu____6169 ->
             let uu____6170 = FStar_ST.op_Bang pending_jobs in
             let uu____6200 =
               let uu____6201 = FStar_ST.op_Bang job_queue in
               FStar_List.length uu____6201 in
             (uu____6170, uu____6200)) in
      match uu____6153 with
      | (n1, m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list[@@deriving
                                                                  show]
let (fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]]
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____6335 -> FStar_ST.op_Bang fresh_scope
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref []
let (push : Prims.string -> unit) =
  fun msg ->
    (let uu____6420 =
       let uu____6425 = FStar_ST.op_Bang fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____6425 in
     FStar_ST.op_Colon_Equals fresh_scope uu____6420);
    (let uu____6506 =
       let uu____6509 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____6509
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.op_Colon_Equals bg_scope uu____6506)
let (pop : Prims.string -> unit) =
  fun msg ->
    (let uu____6584 =
       let uu____6589 = FStar_ST.op_Bang fresh_scope in
       FStar_List.tl uu____6589 in
     FStar_ST.op_Colon_Equals fresh_scope uu____6584);
    (let uu____6670 =
       let uu____6673 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____6673
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.op_Colon_Equals bg_scope uu____6670)
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___43_6755 ->
            match uu___43_6755 with
            | FStar_SMTEncoding_Term.Push -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop -> failwith "Unexpected push/pop"
            | uu____6756 -> ()));
    (let uu____6758 = FStar_ST.op_Bang fresh_scope in
     match uu____6758 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____6849 -> failwith "Impossible");
    (let uu____6854 =
       let uu____6857 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____6857 decls in
     FStar_ST.op_Colon_Equals bg_scope uu____6854)
let (refresh : unit -> unit) =
  fun uu____6930 ->
    (let uu____6932 =
       let uu____6933 = FStar_Options.n_cores () in
       uu____6933 < (Prims.parse_int "2") in
     if uu____6932
     then
       let uu____6934 =
         let uu____6939 = FStar_ST.op_Bang bg_z3_proc in uu____6939.refresh in
       uu____6934 ()
     else ());
    (let uu____6970 =
       let uu____6973 =
         let uu____6978 = FStar_ST.op_Bang fresh_scope in
         FStar_List.rev uu____6978 in
       FStar_List.flatten uu____6973 in
     FStar_ST.op_Colon_Equals bg_scope uu____6970)
let (mk_input :
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string, Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun theory ->
    let options = FStar_ST.op_Bang z3_options in
    let uu____7100 =
      let uu____7107 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())) in
      if uu____7107
      then
        let uu____7114 =
          let uu____7125 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___44_7153 ->
                    match uu___44_7153 with
                    | FStar_SMTEncoding_Term.CheckSat -> true
                    | uu____7154 -> false)) in
          FStar_All.pipe_right uu____7125 FStar_Option.get in
        match uu____7114 with
        | (prefix1, check_sat, suffix) ->
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
            let uncaption uu___45_7238 =
              match uu___45_7238 with
              | FStar_SMTEncoding_Term.Caption uu____7239 ->
                  FStar_SMTEncoding_Term.Caption ""
              | FStar_SMTEncoding_Term.Assume a ->
                  FStar_SMTEncoding_Term.Assume
                    (let uu___50_7243 = a in
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         (uu___50_7243.FStar_SMTEncoding_Term.assumption_term);
                       FStar_SMTEncoding_Term.assumption_caption =
                         FStar_Pervasives_Native.None;
                       FStar_SMTEncoding_Term.assumption_name =
                         (uu___50_7243.FStar_SMTEncoding_Term.assumption_name);
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         (uu___50_7243.FStar_SMTEncoding_Term.assumption_fact_ids)
                     })
              | FStar_SMTEncoding_Term.DeclFun (n1, a, s, uu____7247) ->
                  FStar_SMTEncoding_Term.DeclFun
                    (n1, a, s, FStar_Pervasives_Native.None)
              | FStar_SMTEncoding_Term.DefineFun (n1, a, s, b, uu____7260) ->
                  FStar_SMTEncoding_Term.DefineFun
                    (n1, a, s, b, FStar_Pervasives_Native.None)
              | d -> d in
            let hs =
              let uu____7271 =
                let uu____7274 =
                  let uu____7277 =
                    FStar_All.pipe_right prefix1 (FStar_List.map uncaption) in
                  FStar_All.pipe_right uu____7277 pp_no_cap in
                FStar_All.pipe_right uu____7274
                  (FStar_List.filter (fun s -> s <> "")) in
              FStar_All.pipe_right uu____7271 (FStar_String.concat "\n") in
            let uu____7296 =
              let uu____7299 = FStar_Util.digest_of_string hs in
              FStar_Pervasives_Native.Some uu____7299 in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____7296)
      else
        (let uu____7303 =
           let uu____7304 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory in
           FStar_All.pipe_right uu____7304 (FStar_String.concat "\n") in
         (uu____7303, FStar_Pervasives_Native.None)) in
    match uu____7100 with
    | (r, hash) ->
        ((let uu____7324 = FStar_Options.log_queries () in
          if uu____7324 then query_logging.write_to_log r else ());
         (r, hash))
type cb = z3result -> unit[@@deriving show]
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool)
  =
  fun cache ->
    fun qhash ->
      fun cb ->
        let uu____7358 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()) in
        if uu____7358
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Util.smap_create (Prims.parse_int "0") in
              (FStar_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status = (UNSAT FStar_Pervasives_Native.None);
                    z3result_time = (Prims.parse_int "0");
                    z3result_statistics = stats;
                    z3result_query_hash = qhash
                  } in
                cb result; true))
          | uu____7369 -> false
        else false
let (ask_1_core :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t, Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t -> cb -> unit)
  =
  fun r ->
    fun filter_theory ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun cb ->
              let theory =
                let uu____7427 = FStar_ST.op_Bang bg_scope in
                FStar_List.append uu____7427
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
              let uu____7463 = filter_theory theory in
              match uu____7463 with
              | (theory1, used_unsat_core) ->
                  let uu____7470 = mk_input theory1 in
                  (match uu____7470 with
                   | (input, qhash) ->
                       (FStar_ST.op_Colon_Equals bg_scope [];
                        (let uu____7517 =
                           let uu____7518 = cache_hit cache qhash cb in
                           Prims.op_Negation uu____7518 in
                         if uu____7517
                         then
                           run_job
                             {
                               job =
                                 (z3_job r false label_messages input qhash);
                               callback = cb
                             }
                         else ())))
let (ask_n_cores :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t, Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t ->
            scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun r ->
    fun filter_theory ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun scope ->
              fun cb ->
                let theory =
                  let uu____7587 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____7633 = FStar_ST.op_Bang fresh_scope in
                          FStar_List.rev uu____7633)) in
                  FStar_List.flatten uu____7587 in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
                let uu____7680 = filter_theory theory1 in
                match uu____7680 with
                | (theory2, used_unsat_core) ->
                    let uu____7687 = mk_input theory2 in
                    (match uu____7687 with
                     | (input, qhash) ->
                         let uu____7700 =
                           let uu____7701 = cache_hit cache qhash cb in
                           Prims.op_Negation uu____7701 in
                         if uu____7700
                         then
                           enqueue
                             {
                               job =
                                 (z3_job r true label_messages input qhash);
                               callback = cb
                             }
                         else ())
let (ask :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t, Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun r ->
    fun filter1 ->
      fun cache ->
        fun label_messages ->
          fun qry ->
            fun scope ->
              fun cb ->
                let uu____7769 =
                  let uu____7770 = FStar_Options.n_cores () in
                  uu____7770 = (Prims.parse_int "1") in
                if uu____7769
                then ask_1_core r filter1 cache label_messages qry cb
                else ask_n_cores r filter1 cache label_messages qry scope cb
open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____24 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___38_39 =
          match uu___38_39 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                let uu____49 =
                  let uu____50 = FStar_Options.debug_any ()  in
                  if uu____50
                  then
                    let msg =
                      FStar_Util.format1
                        "Successfully found expected Z3 commit hash %s\n"
                        hash
                       in
                    FStar_Util.print_string msg
                  else ()  in
                FStar_Pervasives_Native.None
              else
                (let msg =
                   FStar_Util.format2
                     "Expected Z3 commit hash \"%s\", got \"%s\""
                     _z3hash_expected trimmed
                    in
                 FStar_Pervasives_Native.Some msg)
          | uu____55::q -> aux q
          | uu____59 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____62 -> FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____75  ->
    let run_proc_result =
      try
        let uu____104 =
          let uu____111 = FStar_Options.z3_exe ()  in
          FStar_Util.run_proc uu____111 "-version" ""  in
        FStar_Pervasives_Native.Some uu____104
      with | uu____129 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some (uu____152,out,uu____154) ->
        let uu____161 = parse_z3_version_lines out  in
        (match uu____161 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : unit -> unit) =
  fun uu____183  ->
    let uu____184 =
      let uu____185 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____185  in
    if uu____184
    then
      let uu____209 = FStar_ST.op_Colon_Equals _z3hash_checked true  in
      let uu____233 = z3hash_warning_message ()  in
      match uu____233 with
      | FStar_Pervasives_Native.None  -> ()
      | FStar_Pervasives_Native.Some (e,msg) ->
          let msg1 =
            FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
              "Please download the version of Z3 corresponding to your platform from:"
              _z3url "and add the bin/ subdirectory into your PATH"
             in
          FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)
    else ()
  
let (ini_params : unit -> Prims.string) =
  fun uu____256  ->
    let uu____257 = check_z3hash ()  in
    let uu____258 =
      let uu____261 =
        let uu____264 =
          let uu____267 =
            let uu____268 =
              let uu____269 = FStar_Options.z3_seed ()  in
              FStar_Util.string_of_int uu____269  in
            FStar_Util.format1 "smt.random_seed=%s" uu____268  in
          [uu____267]  in
        "-smt2 -in auto_config=false model=true smt.relevancy=2 smt.case_split=3"
          :: uu____264
         in
      let uu____270 = FStar_Options.z3_cliopt ()  in
      FStar_List.append uu____261 uu____270  in
    FStar_String.concat " " uu____258
  
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
  | KILLED [@@deriving show]
let (uu___is_UNSAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____317 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____337 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____375 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____413 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____444 -> false
  
type z3statistics = Prims.string FStar_Util.smap[@@deriving show]
let (status_tag : z3status -> Prims.string) =
  fun uu___39_451  ->
    match uu___39_451 with
    | SAT uu____452 -> "sat"
    | UNSAT uu____459 -> "unsat"
    | UNKNOWN uu____460 -> "unknown"
    | TIMEOUT uu____467 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____489 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____498 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____498, errs)
    | UNKNOWN (errs,msg) ->
        let uu____506 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____506, errs)
    | TIMEOUT (errs,msg) ->
        let uu____514 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____514, errs)
  
let (tid : unit -> Prims.string) =
  fun uu____520  ->
    let uu____521 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____521 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let uu____537 = FStar_Options.z3_exe ()  in
    let uu____538 = ini_params ()  in
    FStar_Util.start_process false id1 uu____537 uu____538 cond
  
type bgproc =
  {
  grab: unit -> FStar_Util.proc ;
  release: unit -> unit ;
  refresh: unit -> unit ;
  restart: unit -> unit }[@@deriving show]
let (__proj__Mkbgproc__item__grab : bgproc -> unit -> FStar_Util.proc) =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__grab
  
let (__proj__Mkbgproc__item__release : bgproc -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__release
  
let (__proj__Mkbgproc__item__refresh : bgproc -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__refresh
  
let (__proj__Mkbgproc__item__restart : bgproc -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__restart
  
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.string -> unit ;
  close_log: unit -> unit ;
  log_file_name: unit -> Prims.string }[@@deriving show]
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
  
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
  
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
  
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
  
let (__proj__Mkquery_log__item__log_file_name :
  query_log -> unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
  
let (query_logging : query_log) =
  let query_number = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let used_file_names = FStar_Util.mk_ref []  in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None
     in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set_module_name n1 =
    FStar_ST.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n1)
     in
  let get_module_name uu____984 =
    let uu____985 = FStar_ST.op_Bang current_module_name  in
    match uu____985 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____1042 =
    let uu____1043 = FStar_ST.op_Bang current_module_name  in
    match uu____1043 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____1097 =
            let uu____1104 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____1175  ->
                 match uu____1175 with | (m,uu____1181) -> n1 = m) uu____1104
             in
          match uu____1097 with
          | FStar_Pervasives_Native.None  ->
              let uu____1186 =
                let uu____1187 =
                  let uu____1194 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____1194  in
                FStar_ST.op_Colon_Equals used_file_names uu____1187  in
              n1
          | FStar_Pervasives_Native.Some (uu____1319,k) ->
              let uu____1325 =
                let uu____1326 =
                  let uu____1333 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1333  in
                FStar_ST.op_Colon_Equals used_file_names uu____1326  in
              let uu____1458 =
                FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
              FStar_Util.format2 "%s-%s" n1 uu____1458
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        let uu____1460 =
          FStar_ST.op_Colon_Equals current_file_name
            (FStar_Pervasives_Native.Some file_name1)
           in
        let fh = FStar_Util.open_file_for_writing file_name1  in
        let uu____1511 =
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh)
           in
        fh
     in
  let get_log_file uu____1565 =
    let uu____1566 = FStar_ST.op_Bang log_file_opt  in
    match uu____1566 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1624 = get_log_file ()  in
    FStar_Util.append_to_file uu____1624 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1631 = FStar_ST.op_Bang current_file_name  in
      match uu____1631 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1684 = FStar_ST.op_Bang current_module_name  in
            match uu____1684 with
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1
             in
          let uu____1737 = FStar_Util.mkdir true dir_name  in
          let uu____1738 =
            FStar_ST.op_Colon_Equals current_file_name
              (FStar_Pervasives_Native.Some dir_name)
             in
          dir_name
      | FStar_Pervasives_Native.Some n1 -> n1  in
    let qnum = FStar_ST.op_Bang query_number  in
    let uu____1835 =
      let uu____1836 =
        let uu____1837 = FStar_ST.op_Bang query_number  in
        uu____1837 + (Prims.parse_int "1")  in
      FStar_ST.op_Colon_Equals query_number uu____1836  in
    let file_name =
      let uu____1929 = FStar_Util.string_of_int qnum  in
      FStar_Util.format1 "query-%s.smt2" uu____1929  in
    let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
    FStar_Util.write_file file_name1 str  in
  let write_to_log str =
    let uu____1936 =
      let uu____1937 = FStar_Options.n_cores ()  in
      uu____1937 > (Prims.parse_int "1")  in
    if uu____1936 then write_to_new_log str else append_to_log str  in
  let close_log uu____1943 =
    let uu____1944 = FStar_ST.op_Bang log_file_opt  in
    match uu____1944 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        let uu____1997 = FStar_Util.close_file fh  in
        FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None
     in
  let log_file_name uu____2051 =
    let uu____2052 = FStar_ST.op_Bang current_file_name  in
    match uu____2052 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let (bg_z3_proc : bgproc) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____2119  ->
      let uu____2120 =
        let uu____2121 =
          let uu____2122 = FStar_Util.incr ctr  in
          let uu____2156 = FStar_ST.op_Bang ctr  in
          FStar_All.pipe_right uu____2156 FStar_Util.string_of_int  in
        FStar_Util.format1 "bg-%s" uu____2121  in
      new_z3proc uu____2120
     in
  let z3proc uu____2206 =
    let uu____2207 =
      let uu____2208 =
        let uu____2209 = FStar_ST.op_Bang the_z3proc  in
        uu____2209 = FStar_Pervasives_Native.None  in
      if uu____2208
      then
        let uu____2263 =
          let uu____2266 = new_proc ()  in
          FStar_Pervasives_Native.Some uu____2266  in
        FStar_ST.op_Colon_Equals the_z3proc uu____2263
      else ()  in
    let uu____2317 = FStar_ST.op_Bang the_z3proc  in
    FStar_Util.must uu____2317  in
  let x = []  in
  let grab uu____2376 =
    let uu____2377 = FStar_Util.monitor_enter x  in z3proc ()  in
  let release uu____2384 = FStar_Util.monitor_exit x  in
  let refresh uu____2391 =
    let proc = grab ()  in
    let uu____2393 = FStar_Util.kill_process proc  in
    let uu____2394 =
      let uu____2395 =
        let uu____2398 = new_proc ()  in
        FStar_Pervasives_Native.Some uu____2398  in
      FStar_ST.op_Colon_Equals the_z3proc uu____2395  in
    let uu____2448 = query_logging.close_log ()  in release ()  in
  let restart uu____2453 =
    let uu____2454 = FStar_Util.monitor_enter ()  in
    let uu____2455 = query_logging.close_log ()  in
    let uu____2456 =
      FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None  in
    let uu____2506 =
      let uu____2507 =
        let uu____2510 = new_proc ()  in
        FStar_Pervasives_Native.Some uu____2510  in
      FStar_ST.op_Colon_Equals the_z3proc uu____2507  in
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let (at_log_file : unit -> Prims.string) =
  fun uu____2564  ->
    let uu____2565 = FStar_Options.log_queries ()  in
    if uu____2565
    then
      let uu____2566 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____2566
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
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_result
  
let (__proj__Mksmt_output__item__smt_reason_unknown :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_reason_unknown
  
let (__proj__Mksmt_output__item__smt_unsat_core :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_unsat_core
  
let (__proj__Mksmt_output__item__smt_statistics :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_statistics
  
let (__proj__Mksmt_output__item__smt_labels :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_labels
  
let (smt_output_sections : Prims.string Prims.list -> smt_output) =
  fun lines  ->
    let rec until tag lines1 =
      match lines1 with
      | [] -> FStar_Pervasives_Native.None
      | l::lines2 ->
          if tag = l
          then FStar_Pervasives_Native.Some ([], lines2)
          else
            (let uu____2781 = until tag lines2  in
             FStar_Util.map_opt uu____2781
               (fun uu____2811  ->
                  match uu____2811 with
                  | (until_tag,rest) -> ((l :: until_tag), rest)))
       in
    let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">")  in
    let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">")  in
    let find_section tag lines1 =
      let uu____2885 = until (start_tag tag) lines1  in
      match uu____2885 with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, lines1)
      | FStar_Pervasives_Native.Some (prefix1,suffix) ->
          let uu____2940 = until (end_tag tag) suffix  in
          (match uu____2940 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.strcat "Parse error: "
                    (Prims.strcat (end_tag tag) " not found"))
           | FStar_Pervasives_Native.Some (section,suffix1) ->
               ((FStar_Pervasives_Native.Some section),
                 (FStar_List.append prefix1 suffix1)))
       in
    let uu____3005 = find_section "result" lines  in
    match uu____3005 with
    | (result_opt,lines1) ->
        let result = FStar_Util.must result_opt  in
        let uu____3035 = find_section "reason-unknown" lines1  in
        (match uu____3035 with
         | (reason_unknown,lines2) ->
             let uu____3060 = find_section "unsat-core" lines2  in
             (match uu____3060 with
              | (unsat_core,lines3) ->
                  let uu____3085 = find_section "statistics" lines3  in
                  (match uu____3085 with
                   | (statistics,lines4) ->
                       let uu____3110 = find_section "labels" lines4  in
                       (match uu____3110 with
                        | (labels,lines5) ->
                            let remaining =
                              let uu____3138 = until "Done!" lines5  in
                              match uu____3138 with
                              | FStar_Pervasives_Native.None  -> lines5
                              | FStar_Pervasives_Native.Some (prefix1,suffix)
                                  -> FStar_List.append prefix1 suffix
                               in
                            let uu____3177 =
                              match remaining with
                              | [] -> ()
                              | uu____3178 ->
                                  let uu____3181 =
                                    let uu____3186 =
                                      let uu____3187 =
                                        query_logging.get_module_name ()  in
                                      FStar_Util.format2
                                        "%s: Unexpected output from Z3: %s\n"
                                        uu____3187
                                        (FStar_String.concat "\n" remaining)
                                       in
                                    (FStar_Errors.Warning_UnexpectedZ3Output,
                                      uu____3186)
                                     in
                                  FStar_Errors.log_issue
                                    FStar_Range.dummyRange uu____3181
                               in
                            let uu____3188 = FStar_Util.must result_opt  in
                            {
                              smt_result = uu____3188;
                              smt_reason_unknown = reason_unknown;
                              smt_unsat_core = unsat_core;
                              smt_statistics = statistics;
                              smt_labels = labels
                            }))))
  
let (doZ3Exe :
  Prims.bool ->
    Prims.string ->
      FStar_SMTEncoding_Term.error_labels ->
        (z3status,z3statistics) FStar_Pervasives_Native.tuple2)
  =
  fun fresh  ->
    fun input  ->
      fun label_messages  ->
        let parse z3out =
          let lines =
            FStar_All.pipe_right (FStar_String.split [10] z3out)
              (FStar_List.map FStar_Util.trim_string)
             in
          let smt_output = smt_output_sections lines  in
          let unsat_core =
            match smt_output.smt_unsat_core with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some s ->
                let s1 = FStar_Util.trim_string (FStar_String.concat " " s)
                   in
                let s2 =
                  FStar_Util.substring s1 (Prims.parse_int "1")
                    ((FStar_String.length s1) - (Prims.parse_int "2"))
                   in
                if FStar_Util.starts_with s2 "error"
                then FStar_Pervasives_Native.None
                else
                  (let uu____3255 =
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_Util.sort_with FStar_String.compare)
                      in
                   FStar_Pervasives_Native.Some uu____3255)
             in
          let labels =
            match smt_output.smt_labels with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some lines1 ->
                let rec lblnegs lines2 =
                  match lines2 with
                  | lname::"false"::rest when
                      FStar_Util.starts_with lname "label_" ->
                      let uu____3317 = lblnegs rest  in lname :: uu____3317
                  | lname::uu____3321::rest when
                      FStar_Util.starts_with lname "label_" -> lblnegs rest
                  | uu____3325 -> []  in
                let lblnegs1 = lblnegs lines1  in
                FStar_All.pipe_right lblnegs1
                  (FStar_List.collect
                     (fun l  ->
                        let uu____3358 =
                          FStar_All.pipe_right label_messages
                            (FStar_List.tryFind
                               (fun uu____3397  ->
                                  match uu____3397 with
                                  | (m,uu____3409,uu____3410) ->
                                      (FStar_Pervasives_Native.fst m) = l))
                           in
                        match uu____3358 with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some (lbl,msg,r) ->
                            [(lbl, msg, r)]))
             in
          let statistics =
            let statistics = FStar_Util.smap_create (Prims.parse_int "0")  in
            match smt_output.smt_statistics with
            | FStar_Pervasives_Native.None  -> statistics
            | FStar_Pervasives_Native.Some lines1 ->
                let parse_line line =
                  let pline =
                    FStar_Util.split (FStar_Util.trim_string line) ":"  in
                  match pline with
                  | "("::entry::[] ->
                      let tokens = FStar_Util.split entry " "  in
                      let key = FStar_List.hd tokens  in
                      let ltok =
                        FStar_List.nth tokens
                          ((FStar_List.length tokens) - (Prims.parse_int "1"))
                         in
                      let value =
                        if FStar_Util.ends_with ltok ")"
                        then
                          FStar_Util.substring ltok (Prims.parse_int "0")
                            ((FStar_String.length ltok) -
                               (Prims.parse_int "1"))
                        else ltok  in
                      FStar_Util.smap_add statistics key value
                  | ""::entry::[] ->
                      let tokens = FStar_Util.split entry " "  in
                      let key = FStar_List.hd tokens  in
                      let ltok =
                        FStar_List.nth tokens
                          ((FStar_List.length tokens) - (Prims.parse_int "1"))
                         in
                      let value =
                        if FStar_Util.ends_with ltok ")"
                        then
                          FStar_Util.substring ltok (Prims.parse_int "0")
                            ((FStar_String.length ltok) -
                               (Prims.parse_int "1"))
                        else ltok  in
                      FStar_Util.smap_add statistics key value
                  | uu____3523 -> ()  in
                let uu____3526 = FStar_List.iter parse_line lines1  in
                statistics
             in
          let reason_unknown =
            FStar_Util.map_opt smt_output.smt_reason_unknown
              (fun x  ->
                 let ru = FStar_String.concat " " x  in
                 if FStar_Util.starts_with ru "(:reason-unknown \""
                 then
                   let reason =
                     FStar_Util.substring_from ru
                       (FStar_String.length "(:reason-unknown \"")
                      in
                   let res =
                     FStar_String.substring reason (Prims.parse_int "0")
                       ((FStar_String.length reason) - (Prims.parse_int "2"))
                      in
                   res
                 else ru)
             in
          let status =
            let uu____3540 =
              let uu____3541 = FStar_Options.debug_any ()  in
              if uu____3541
              then
                let uu____3542 =
                  FStar_Util.format1 "Z3 says: %s\n"
                    (FStar_String.concat "\n" smt_output.smt_result)
                   in
                FStar_All.pipe_left FStar_Util.print_string uu____3542
              else ()  in
            match smt_output.smt_result with
            | "unsat"::[] -> UNSAT unsat_core
            | "sat"::[] -> SAT (labels, reason_unknown)
            | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
            | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
            | "killed"::[] ->
                let uu____3586 = bg_z3_proc.restart ()  in KILLED
            | uu____3587 ->
                let uu____3588 =
                  FStar_Util.format1
                    "Unexpected output from Z3: got output result: %s\n"
                    (FStar_String.concat "\n" smt_output.smt_result)
                   in
                failwith uu____3588
             in
          (status, statistics)  in
        let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x
           in
        let stdout1 =
          if fresh
          then
            let uu____3600 = tid ()  in
            let uu____3601 = FStar_Options.z3_exe ()  in
            let uu____3602 = ini_params ()  in
            FStar_Util.launch_process false uu____3600 uu____3601 uu____3602
              input cond
          else
            (let proc = bg_z3_proc.grab ()  in
             let stdout1 = FStar_Util.ask_process proc input  in
             let uu____3606 = bg_z3_proc.release ()  in stdout1)
           in
        parse (FStar_Util.trim_string stdout1)
  
let (z3_options : unit -> Prims.string) =
  fun uu____3611  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
type 'a job = {
  job: unit -> 'a ;
  callback: 'a -> unit }[@@deriving show]
let __proj__Mkjob__item__job : 'a . 'a job -> unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
  
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> unit =
  fun projectee  ->
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
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_status
  
let (__proj__Mkz3result__item__z3result_time : z3result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_time
  
let (__proj__Mkz3result__item__z3result_statistics :
  z3result -> z3statistics) =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_statistics
  
let (__proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
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
  'Auu____3790 'Auu____3791 .
    'Auu____3790 -> (unit -> 'Auu____3791) -> 'Auu____3791
  =
  fun m  ->
    fun f  ->
      let uu____3807 = FStar_Util.monitor_enter m  in
      let res = f ()  in let uu____3809 = FStar_Util.monitor_exit m  in res
  
let (z3_job :
  Prims.bool ->
    FStar_SMTEncoding_Term.error_labels ->
      Prims.string ->
        Prims.string FStar_Pervasives_Native.option -> unit -> z3result)
  =
  fun fresh  ->
    fun label_messages  ->
      fun input  ->
        fun qhash  ->
          fun uu____3836  ->
            let start = FStar_Util.now ()  in
            let uu____3840 =
              try doZ3Exe fresh input label_messages
              with
              | uu____3864 when
                  let uu____3865 = FStar_Options.trace_error ()  in
                  Prims.op_Negation uu____3865 ->
                  let uu____3866 = bg_z3_proc.refresh ()  in
                  let uu____3867 =
                    FStar_Util.smap_create (Prims.parse_int "0")  in
                  ((UNKNOWN
                      ([],
                        (FStar_Pervasives_Native.Some
                           "Z3 raised an exception"))), uu____3867)
               in
            match uu____3840 with
            | (status,statistics) ->
                let uu____3878 =
                  let uu____3883 = FStar_Util.now ()  in
                  FStar_Util.time_diff start uu____3883  in
                (match uu____3878 with
                 | (uu____3884,elapsed_time) ->
                     {
                       z3result_status = status;
                       z3result_time = elapsed_time;
                       z3result_statistics = statistics;
                       z3result_query_hash = qhash
                     })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : unit -> unit) =
  fun uu____3911  ->
    let j =
      let uu____3913 = FStar_ST.op_Bang job_queue  in
      match uu____3913 with
      | [] -> failwith "Impossible"
      | hd1::tl1 ->
          let uu____3947 = FStar_ST.op_Colon_Equals job_queue tl1  in hd1
       in
    let uu____3975 = FStar_Util.incr pending_jobs  in
    let uu____3976 = FStar_Util.monitor_exit job_queue  in
    let uu____3981 = run_job j  in
    let uu____3982 =
      with_monitor job_queue
        (fun uu____3988  -> FStar_Util.decr pending_jobs)
       in
    let uu____3989 = dequeue ()  in ()

and (dequeue : unit -> unit) =
  fun uu____3990  ->
    let uu____3991 = FStar_ST.op_Bang running  in
    if uu____3991
    then
      let rec aux uu____4019 =
        let uu____4020 = FStar_Util.monitor_enter job_queue  in
        let uu____4025 = FStar_ST.op_Bang job_queue  in
        match uu____4025 with
        | [] ->
            let uu____4055 = FStar_Util.monitor_exit job_queue  in
            let uu____4060 = FStar_Util.sleep (Prims.parse_int "50")  in
            aux ()
        | uu____4061 -> dequeue' ()  in
      aux ()
    else ()

and (run_job : z3job -> unit) =
  fun j  ->
    let uu____4065 = j.job ()  in FStar_All.pipe_left j.callback uu____4065

let (init : unit -> unit) =
  fun uu____4070  ->
    let uu____4071 = FStar_ST.op_Colon_Equals running true  in
    let n_cores1 = FStar_Options.n_cores ()  in
    if n_cores1 > (Prims.parse_int "1")
    then
      let rec aux n1 =
        if n1 = (Prims.parse_int "0")
        then ()
        else
          (let uu____4102 = FStar_Util.spawn dequeue  in
           aux (n1 - (Prims.parse_int "1")))
         in
      aux n_cores1
    else ()
  
let (enqueue : z3job -> unit) =
  fun j  ->
    let uu____4109 = FStar_Util.monitor_enter job_queue  in
    let uu____4114 =
      let uu____4115 =
        let uu____4118 = FStar_ST.op_Bang job_queue  in
        FStar_List.append uu____4118 [j]  in
      FStar_ST.op_Colon_Equals job_queue uu____4115  in
    let uu____4175 = FStar_Util.monitor_pulse job_queue  in
    FStar_Util.monitor_exit job_queue
  
let (finish : unit -> unit) =
  fun uu____4188  ->
    let rec aux uu____4193 =
      let uu____4194 =
        with_monitor job_queue
          (fun uu____4210  ->
             let uu____4211 = FStar_ST.op_Bang pending_jobs  in
             let uu____4235 =
               let uu____4236 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____4236  in
             (uu____4211, uu____4235))
         in
      match uu____4194 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else
            (let uu____4300 = FStar_Util.sleep (Prims.parse_int "500")  in
             aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list[@@deriving
                                                                  show]
let (fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____4334  -> FStar_ST.op_Bang fresh_scope 
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> unit) =
  fun msg  ->
    let uu____4388 =
      let uu____4389 =
        let uu____4394 = FStar_ST.op_Bang fresh_scope  in
        [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
          uu____4394
         in
      FStar_ST.op_Colon_Equals fresh_scope uu____4389  in
    let uu____4463 =
      let uu____4466 = FStar_ST.op_Bang bg_scope  in
      FStar_List.append uu____4466
        [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
       in
    FStar_ST.op_Colon_Equals bg_scope uu____4463
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    let uu____4528 =
      let uu____4529 =
        let uu____4534 = FStar_ST.op_Bang fresh_scope  in
        FStar_List.tl uu____4534  in
      FStar_ST.op_Colon_Equals fresh_scope uu____4529  in
    let uu____4603 =
      let uu____4606 = FStar_ST.op_Bang bg_scope  in
      FStar_List.append uu____4606
        [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
       in
    FStar_ST.op_Colon_Equals bg_scope uu____4603
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls  ->
    let uu____4672 =
      FStar_All.pipe_right decls
        (FStar_List.iter
           (fun uu___40_4676  ->
              match uu___40_4676 with
              | FStar_SMTEncoding_Term.Push  ->
                  failwith "Unexpected push/pop"
              | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
              | uu____4677 -> ()))
       in
    let uu____4678 =
      let uu____4679 = FStar_ST.op_Bang fresh_scope  in
      match uu____4679 with
      | hd1::tl1 ->
          FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
            :: tl1)
      | uu____4758 -> failwith "Impossible"  in
    let uu____4763 =
      let uu____4766 = FStar_ST.op_Bang bg_scope  in
      FStar_List.append uu____4766 decls  in
    FStar_ST.op_Colon_Equals bg_scope uu____4763
  
let (refresh : unit -> unit) =
  fun uu____4827  ->
    let uu____4828 =
      let uu____4829 =
        let uu____4830 = FStar_Options.n_cores ()  in
        uu____4830 < (Prims.parse_int "2")  in
      if uu____4829 then bg_z3_proc.refresh () else ()  in
    let uu____4832 =
      let uu____4835 =
        let uu____4840 = FStar_ST.op_Bang fresh_scope  in
        FStar_List.rev uu____4840  in
      FStar_List.flatten uu____4835  in
    FStar_ST.op_Colon_Equals bg_scope uu____4832
  
let (mk_input :
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun theory  ->
    let options = z3_options ()  in
    let uu____4921 =
      let uu____4928 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
         in
      if uu____4928
      then
        let uu____4935 =
          let uu____4946 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___41_4974  ->
                    match uu___41_4974 with
                    | FStar_SMTEncoding_Term.CheckSat  -> true
                    | uu____4975 -> false))
             in
          FStar_All.pipe_right uu____4946 FStar_Option.get  in
        match uu____4935 with
        | (prefix1,check_sat,suffix) ->
            let pp =
              FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)  in
            let pp_no_cap =
              FStar_List.map
                (FStar_SMTEncoding_Term.declToSmt_no_caps options)
               in
            let suffix1 = check_sat :: suffix  in
            let ps_lines = pp prefix1  in
            let ss_lines = pp suffix1  in
            let ps = FStar_String.concat "\n" ps_lines  in
            let ss = FStar_String.concat "\n" ss_lines  in
            let uncaption uu___42_5056 =
              match uu___42_5056 with
              | FStar_SMTEncoding_Term.Caption uu____5057 ->
                  FStar_SMTEncoding_Term.Caption ""
              | FStar_SMTEncoding_Term.Assume a ->
                  FStar_SMTEncoding_Term.Assume
                    (let uu___47_5061 = a  in
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         (uu___47_5061.FStar_SMTEncoding_Term.assumption_term);
                       FStar_SMTEncoding_Term.assumption_caption =
                         FStar_Pervasives_Native.None;
                       FStar_SMTEncoding_Term.assumption_name =
                         (uu___47_5061.FStar_SMTEncoding_Term.assumption_name);
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         (uu___47_5061.FStar_SMTEncoding_Term.assumption_fact_ids)
                     })
              | FStar_SMTEncoding_Term.DeclFun (n1,a,s,uu____5065) ->
                  FStar_SMTEncoding_Term.DeclFun
                    (n1, a, s, FStar_Pervasives_Native.None)
              | FStar_SMTEncoding_Term.DefineFun (n1,a,s,b,uu____5078) ->
                  FStar_SMTEncoding_Term.DefineFun
                    (n1, a, s, b, FStar_Pervasives_Native.None)
              | d -> d  in
            let hs =
              let uu____5089 =
                let uu____5092 =
                  let uu____5095 =
                    FStar_All.pipe_right prefix1 (FStar_List.map uncaption)
                     in
                  FStar_All.pipe_right uu____5095 pp_no_cap  in
                FStar_All.pipe_right uu____5092
                  (FStar_List.filter (fun s  -> s <> ""))
                 in
              FStar_All.pipe_right uu____5089 (FStar_String.concat "\n")  in
            let uu____5114 =
              let uu____5117 = FStar_Util.digest_of_string hs  in
              FStar_Pervasives_Native.Some uu____5117  in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____5114)
      else
        (let uu____5121 =
           let uu____5122 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory
              in
           FStar_All.pipe_right uu____5122 (FStar_String.concat "\n")  in
         (uu____5121, FStar_Pervasives_Native.None))
       in
    match uu____4921 with
    | (r,hash) ->
        let uu____5141 =
          let uu____5142 = FStar_Options.log_queries ()  in
          if uu____5142 then query_logging.write_to_log r else ()  in
        (r, hash)
  
type cb = z3result -> unit[@@deriving show]
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool)
  =
  fun cache  ->
    fun qhash  ->
      fun cb  ->
        let uu____5175 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())
           in
        if uu____5175
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Util.smap_create (Prims.parse_int "0")  in
              let uu____5180 =
                FStar_Util.smap_add stats "fstar_cache_hit" "1"  in
              let result =
                {
                  z3result_status = (UNSAT FStar_Pervasives_Native.None);
                  z3result_time = (Prims.parse_int "0");
                  z3result_statistics = stats;
                  z3result_query_hash = qhash
                }  in
              let uu____5184 = cb result  in true
          | uu____5186 -> false
        else false
  
let (ask_1_core :
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    Prims.string FStar_Pervasives_Native.option ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decls_t -> cb -> unit)
  =
  fun filter_theory  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun cb  ->
            let theory =
              let uu____5239 = FStar_ST.op_Bang bg_scope  in
              FStar_List.append uu____5239
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
               in
            let uu____5269 = filter_theory theory  in
            match uu____5269 with
            | (theory1,used_unsat_core) ->
                let uu____5276 = mk_input theory1  in
                (match uu____5276 with
                 | (input,qhash) ->
                     let uu____5289 = FStar_ST.op_Colon_Equals bg_scope []
                        in
                     let uu____5317 =
                       let uu____5318 = cache_hit cache qhash cb  in
                       Prims.op_Negation uu____5318  in
                     if uu____5317
                     then
                       run_job
                         {
                           job = (z3_job false label_messages input qhash);
                           callback = cb
                         }
                     else ())
  
let (ask_n_cores :
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    Prims.string FStar_Pervasives_Native.option ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decls_t ->
          scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun filter_theory  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun scope  ->
            fun cb  ->
              let theory =
                let uu____5382 =
                  match scope with
                  | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                  | FStar_Pervasives_Native.None  ->
                      let uu____5394 = FStar_ST.op_Colon_Equals bg_scope []
                         in
                      let uu____5422 = FStar_ST.op_Bang fresh_scope  in
                      FStar_List.rev uu____5422
                   in
                FStar_List.flatten uu____5382  in
              let theory1 =
                FStar_List.append theory
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                 in
              let uu____5463 = filter_theory theory1  in
              match uu____5463 with
              | (theory2,used_unsat_core) ->
                  let uu____5470 = mk_input theory2  in
                  (match uu____5470 with
                   | (input,qhash) ->
                       let uu____5483 =
                         let uu____5484 = cache_hit cache qhash cb  in
                         Prims.op_Negation uu____5484  in
                       if uu____5483
                       then
                         enqueue
                           {
                             job = (z3_job true label_messages input qhash);
                             callback = cb
                           }
                       else ())
  
let (ask :
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    Prims.string FStar_Pervasives_Native.option ->
      FStar_SMTEncoding_Term.error_labels ->
        FStar_SMTEncoding_Term.decl Prims.list ->
          scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun filter1  ->
    fun cache  ->
      fun label_messages  ->
        fun qry  ->
          fun scope  ->
            fun cb  ->
              let uu____5547 =
                let uu____5548 = FStar_Options.n_cores ()  in
                uu____5548 = (Prims.parse_int "1")  in
              if uu____5547
              then ask_1_core filter1 cache label_messages qry cb
              else ask_n_cores filter1 cache label_messages qry scope cb
  
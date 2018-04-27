open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____22 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___38_36 =
          match uu___38_36 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____47 = FStar_Options.debug_any ()  in
                  if uu____47
                  then
                    let msg =
                      FStar_Util.format1
                        "Successfully found expected Z3 commit hash %s\n"
                        hash
                       in
                    FStar_Util.print_string msg
                  else ());
                 FStar_Pervasives_Native.None)
              else
                (let msg =
                   FStar_Util.format2
                     "Expected Z3 commit hash \"%s\", got \"%s\""
                     _z3hash_expected trimmed
                    in
                 FStar_Pervasives_Native.Some msg)
          | uu____52::q -> aux q
          | uu____56 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____59 -> FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  Prims.unit ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____70  ->
    let run_proc_result =
      try
        let uu____81 =
          let uu____82 = FStar_Options.z3_exe ()  in
          FStar_Util.run_process "z3_version" uu____82 ["-version"]
            FStar_Pervasives_Native.None
           in
        FStar_Pervasives_Native.Some uu____81
      with | uu____88 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____100 = parse_z3_version_lines out  in
        (match uu____100 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : Prims.unit -> Prims.unit) =
  fun uu____120  ->
    let uu____121 =
      let uu____122 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____122  in
    if uu____121
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____162 = z3hash_warning_message ()  in
        match uu____162 with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some (e,msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH"
               in
            FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)))
    else ()
  
let (ini_params : Prims.unit -> Prims.string Prims.list) =
  fun uu____185  ->
    check_z3hash ();
    (let uu____187 =
       let uu____190 =
         let uu____193 =
           let uu____196 =
             let uu____199 =
               let uu____202 =
                 let uu____205 =
                   let uu____208 =
                     let uu____209 =
                       let uu____210 = FStar_Options.z3_seed ()  in
                       FStar_Util.string_of_int uu____210  in
                     FStar_Util.format1 "smt.random_seed=%s" uu____209  in
                   [uu____208]  in
                 "smt.case_split=3" :: uu____205  in
               "smt.relevancy=2" :: uu____202  in
             "model=true" :: uu____199  in
           "auto_config=false" :: uu____196  in
         "-in" :: uu____193  in
       "-smt2" :: uu____190  in
     let uu____211 = FStar_Options.z3_cliopt ()  in
     FStar_List.append uu____187 uu____211)
  
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
    match projectee with | UNSAT _0 -> true | uu____256 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____274 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____310 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____346 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____375 -> false
  
type z3statistics = Prims.string FStar_Util.smap[@@deriving show]
let (status_tag : z3status -> Prims.string) =
  fun uu___39_380  ->
    match uu___39_380 with
    | SAT uu____381 -> "sat"
    | UNSAT uu____388 -> "unsat"
    | UNKNOWN uu____389 -> "unknown"
    | TIMEOUT uu____396 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____416 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____425 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____425, errs)
    | UNKNOWN (errs,msg) ->
        let uu____433 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____433, errs)
    | TIMEOUT (errs,msg) ->
        let uu____441 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____441, errs)
  
let (tid : Prims.unit -> Prims.string) =
  fun uu____445  ->
    let uu____446 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____446 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let uu____450 = FStar_Options.z3_exe ()  in
    let uu____451 = ini_params ()  in
    FStar_Util.start_process id1 uu____450 uu____451 (fun s  -> s = "Done!")
  
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: Prims.unit -> Prims.unit ;
  restart: Prims.unit -> Prims.unit }[@@deriving show]
let (__proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__ask
  
let (__proj__Mkbgproc__item__refresh : bgproc -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__refresh
  
let (__proj__Mkbgproc__item__restart : bgproc -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__restart
  
type query_log =
  {
  get_module_name: Prims.unit -> Prims.string ;
  set_module_name: Prims.string -> Prims.unit ;
  write_to_log: Prims.string -> Prims.unit ;
  close_log: Prims.unit -> Prims.unit ;
  log_file_name: Prims.unit -> Prims.string }[@@deriving show]
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> Prims.unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
  
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
  
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
  
let (__proj__Mkquery_log__item__close_log :
  query_log -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
  
let (__proj__Mkquery_log__item__log_file_name :
  query_log -> Prims.unit -> Prims.string) =
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
  let get_module_name uu____773 =
    let uu____774 = FStar_ST.op_Bang current_module_name  in
    match uu____774 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____826 =
    let uu____827 = FStar_ST.op_Bang current_module_name  in
    match uu____827 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____877 =
            let uu____884 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____951  ->
                 match uu____951 with | (m,uu____957) -> n1 = m) uu____884
             in
          match uu____877 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____963 =
                  let uu____970 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____970  in
                FStar_ST.op_Colon_Equals used_file_names uu____963);
               n1)
          | FStar_Pervasives_Native.Some (uu____1087,k) ->
              ((let uu____1094 =
                  let uu____1101 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1101  in
                FStar_ST.op_Colon_Equals used_file_names uu____1094);
               (let uu____1218 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____1218))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh))
     in
  let get_log_file uu____1316 =
    let uu____1317 = FStar_ST.op_Bang log_file_opt  in
    match uu____1317 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1370 = get_log_file ()  in
    FStar_Util.append_to_file uu____1370 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1376 = FStar_ST.op_Bang current_file_name  in
      match uu____1376 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1425 = FStar_ST.op_Bang current_module_name  in
            match uu____1425 with
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1
             in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.op_Colon_Equals current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
      | FStar_Pervasives_Native.Some n1 -> n1  in
    let qnum = FStar_ST.op_Bang query_number  in
    (let uu____1565 =
       let uu____1566 = FStar_ST.op_Bang query_number  in
       uu____1566 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals query_number uu____1565);
    (let file_name =
       let uu____1650 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____1650  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____1656 =
      let uu____1657 = FStar_Options.n_cores ()  in
      uu____1657 > (Prims.parse_int "1")  in
    if uu____1656 then write_to_new_log str else append_to_log str  in
  let close_log uu____1662 =
    let uu____1663 = FStar_ST.op_Bang log_file_opt  in
    match uu____1663 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____1761 =
    let uu____1762 = FStar_ST.op_Bang current_file_name  in
    match uu____1762 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____1837  ->
      let uu____1838 =
        let uu____1839 =
          FStar_Util.incr ctr;
          (let uu____1874 = FStar_ST.op_Bang ctr  in
           FStar_All.pipe_right uu____1874 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____1839  in
      new_z3proc uu____1838
     in
  let z3proc uu____1919 =
    (let uu____1921 =
       let uu____1922 = FStar_ST.op_Bang the_z3proc  in
       uu____1922 = FStar_Pervasives_Native.None  in
     if uu____1921
     then
       let uu____1972 =
         let uu____1975 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____1975  in
       FStar_ST.op_Colon_Equals the_z3proc uu____1972
     else ());
    (let uu____2022 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____2022)
     in
  let x = []  in
  let ask input =
    let kill_handler uu____2080 = "\nkilled\n"  in
    let uu____2081 = z3proc ()  in
    FStar_Util.ask_process uu____2081 input kill_handler  in
  let refresh uu____2085 =
    (let uu____2087 = z3proc ()  in FStar_Util.kill_process uu____2087);
    (let uu____2089 =
       let uu____2092 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2092  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2089);
    query_logging.close_log ()  in
  let restart uu____2141 =
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2189 =
       let uu____2192 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2192  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2189)
     in
  FStar_Util.mk_ref
    {
      ask = (FStar_Util.with_monitor x ask);
      refresh = (FStar_Util.with_monitor x refresh);
      restart = (FStar_Util.with_monitor x restart)
    }
  
let (set_bg_z3_proc : bgproc -> Prims.unit) =
  fun bgp  -> FStar_ST.op_Colon_Equals bg_z3_proc bgp 
let (at_log_file : Prims.unit -> Prims.string) =
  fun uu____2268  ->
    let uu____2269 = FStar_Options.log_queries ()  in
    if uu____2269
    then
      let uu____2270 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____2270
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
  
let (smt_output_sections :
  FStar_Range.range -> Prims.string Prims.list -> smt_output) =
  fun r  ->
    fun lines  ->
      let rec until tag lines1 =
        match lines1 with
        | [] -> FStar_Pervasives_Native.None
        | l::lines2 ->
            if tag = l
            then FStar_Pervasives_Native.Some ([], lines2)
            else
              (let uu____2474 = until tag lines2  in
               FStar_Util.map_opt uu____2474
                 (fun uu____2504  ->
                    match uu____2504 with
                    | (until_tag,rest) -> ((l :: until_tag), rest)))
         in
      let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">")  in
      let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">")  in
      let find_section tag lines1 =
        let uu____2574 = until (start_tag tag) lines1  in
        match uu____2574 with
        | FStar_Pervasives_Native.None  ->
            (FStar_Pervasives_Native.None, lines1)
        | FStar_Pervasives_Native.Some (prefix1,suffix) ->
            let uu____2629 = until (end_tag tag) suffix  in
            (match uu____2629 with
             | FStar_Pervasives_Native.None  ->
                 failwith
                   (Prims.strcat "Parse error: "
                      (Prims.strcat (end_tag tag) " not found"))
             | FStar_Pervasives_Native.Some (section,suffix1) ->
                 ((FStar_Pervasives_Native.Some section),
                   (FStar_List.append prefix1 suffix1)))
         in
      let uu____2694 = find_section "result" lines  in
      match uu____2694 with
      | (result_opt,lines1) ->
          let result = FStar_Util.must result_opt  in
          let uu____2724 = find_section "reason-unknown" lines1  in
          (match uu____2724 with
           | (reason_unknown,lines2) ->
               let uu____2749 = find_section "unsat-core" lines2  in
               (match uu____2749 with
                | (unsat_core,lines3) ->
                    let uu____2774 = find_section "statistics" lines3  in
                    (match uu____2774 with
                     | (statistics,lines4) ->
                         let uu____2799 = find_section "labels" lines4  in
                         (match uu____2799 with
                          | (labels,lines5) ->
                              let remaining =
                                let uu____2827 = until "Done!" lines5  in
                                match uu____2827 with
                                | FStar_Pervasives_Native.None  -> lines5
                                | FStar_Pervasives_Native.Some
                                    (prefix1,suffix) ->
                                    FStar_List.append prefix1 suffix
                                 in
                              ((match remaining with
                                | [] -> ()
                                | uu____2867 ->
                                    let uu____2870 =
                                      let uu____2875 =
                                        FStar_Util.format1
                                          "Unexpected output from Z3: %s\n"
                                          (FStar_String.concat "\n" remaining)
                                         in
                                      (FStar_Errors.Warning_UnexpectedZ3Output,
                                        uu____2875)
                                       in
                                    FStar_Errors.log_issue r uu____2870);
                               (let uu____2876 = FStar_Util.must result_opt
                                   in
                                {
                                  smt_result = uu____2876;
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
          (z3status,z3statistics) FStar_Pervasives_Native.tuple2)
  =
  fun r  ->
    fun fresh  ->
      fun input  ->
        fun label_messages  ->
          let parse z3out =
            let lines =
              FStar_All.pipe_right (FStar_String.split [10] z3out)
                (FStar_List.map FStar_Util.trim_string)
               in
            let smt_output = smt_output_sections r lines  in
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
                    (let uu____2939 =
                       FStar_All.pipe_right (FStar_Util.split s2 " ")
                         (FStar_Util.sort_with FStar_String.compare)
                        in
                     FStar_Pervasives_Native.Some uu____2939)
               in
            let labels =
              match smt_output.smt_labels with
              | FStar_Pervasives_Native.None  -> []
              | FStar_Pervasives_Native.Some lines1 ->
                  let rec lblnegs lines2 =
                    match lines2 with
                    | lname::"false"::rest when
                        FStar_Util.starts_with lname "label_" ->
                        let uu____3000 = lblnegs rest  in lname :: uu____3000
                    | lname::uu____3004::rest when
                        FStar_Util.starts_with lname "label_" -> lblnegs rest
                    | uu____3008 -> []  in
                  let lblnegs1 = lblnegs lines1  in
                  FStar_All.pipe_right lblnegs1
                    (FStar_List.collect
                       (fun l  ->
                          let uu____3041 =
                            FStar_All.pipe_right label_messages
                              (FStar_List.tryFind
                                 (fun uu____3080  ->
                                    match uu____3080 with
                                    | (m,uu____3092,uu____3093) ->
                                        (FStar_Pervasives_Native.fst m) = l))
                             in
                          match uu____3041 with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some (lbl,msg,r1) ->
                              [(lbl, msg, r1)]))
               in
            let statistics =
              let statistics = FStar_Util.smap_create (Prims.parse_int "0")
                 in
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
                            ((FStar_List.length tokens) -
                               (Prims.parse_int "1"))
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
                            ((FStar_List.length tokens) -
                               (Prims.parse_int "1"))
                           in
                        let value =
                          if FStar_Util.ends_with ltok ")"
                          then
                            FStar_Util.substring ltok (Prims.parse_int "0")
                              ((FStar_String.length ltok) -
                                 (Prims.parse_int "1"))
                          else ltok  in
                        FStar_Util.smap_add statistics key value
                    | uu____3205 -> ()  in
                  (FStar_List.iter parse_line lines1; statistics)
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
                         ((FStar_String.length reason) -
                            (Prims.parse_int "2"))
                        in
                     res
                   else ru)
               in
            let status =
              (let uu____3223 = FStar_Options.debug_any ()  in
               if uu____3223
               then
                 let uu____3224 =
                   FStar_Util.format1 "Z3 says: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result)
                    in
                 FStar_All.pipe_left FStar_Util.print_string uu____3224
               else ());
              (match smt_output.smt_result with
               | "unsat"::[] -> UNSAT unsat_core
               | "sat"::[] -> SAT (labels, reason_unknown)
               | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
               | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
               | "killed"::[] ->
                   ((let uu____3269 =
                       let uu____3272 = FStar_ST.op_Bang bg_z3_proc  in
                       uu____3272.restart  in
                     uu____3269 ());
                    KILLED)
               | uu____3292 ->
                   let uu____3293 =
                     FStar_Util.format1
                       "Unexpected output from Z3: got output result: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   failwith uu____3293)
               in
            (status, statistics)  in
          let stdout1 =
            if fresh
            then
              let uu____3295 = tid ()  in
              let uu____3296 = FStar_Options.z3_exe ()  in
              let uu____3297 = ini_params ()  in
              FStar_Util.run_process uu____3295 uu____3296 uu____3297
                (FStar_Pervasives_Native.Some input)
            else
              (let uu____3301 =
                 let uu____3304 = FStar_ST.op_Bang bg_z3_proc  in
                 uu____3304.ask  in
               uu____3301 input)
             in
          parse (FStar_Util.trim_string stdout1)
  
let (z3_options : Prims.string FStar_ST.ref) =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
let (set_z3_options : Prims.string -> Prims.unit) =
  fun opts  -> FStar_ST.op_Colon_Equals z3_options opts 
type 'a job = {
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }[@@deriving show]
let __proj__Mkjob__item__job : 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
  
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> Prims.unit =
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
let (z3_job :
  FStar_Range.range ->
    Prims.bool ->
      FStar_SMTEncoding_Term.error_labels ->
        Prims.string ->
          Prims.string FStar_Pervasives_Native.option ->
            Prims.unit -> z3result)
  =
  fun r  ->
    fun fresh  ->
      fun label_messages  ->
        fun input  ->
          fun qhash  ->
            fun uu____3526  ->
              let start = FStar_Util.now ()  in
              let uu____3530 =
                try doZ3Exe r fresh input label_messages
                with
                | e when
                    let uu____3554 = FStar_Options.trace_error ()  in
                    Prims.op_Negation uu____3554 ->
                    ((let uu____3556 =
                        let uu____3559 = FStar_ST.op_Bang bg_z3_proc  in
                        uu____3559.refresh  in
                      uu____3556 ());
                     FStar_Exn.raise e)
                 in
              match uu____3530 with
              | (status,statistics) ->
                  let uu____3585 =
                    let uu____3590 = FStar_Util.now ()  in
                    FStar_Util.time_diff start uu____3590  in
                  (match uu____3585 with
                   | (uu____3591,elapsed_time) ->
                       {
                         z3result_status = status;
                         z3result_time = elapsed_time;
                         z3result_statistics = statistics;
                         z3result_query_hash = qhash
                       })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : Prims.unit -> Prims.unit) =
  fun uu____3612  ->
    let j =
      let uu____3614 = FStar_ST.op_Bang job_queue  in
      match uu____3614 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    FStar_Util.with_monitor job_queue
      (fun uu____3681  -> FStar_Util.decr pending_jobs) ();
    dequeue ()

and (dequeue : Prims.unit -> Prims.unit) =
  fun uu____3683  ->
    let uu____3684 = FStar_ST.op_Bang running  in
    if uu____3684
    then
      let rec aux uu____3707 =
        FStar_Util.monitor_enter job_queue;
        (let uu____3713 = FStar_ST.op_Bang job_queue  in
         match uu____3713 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____3745 -> dequeue' ())
         in
      aux ()
    else ()

and (run_job : z3job -> Prims.unit) =
  fun j  ->
    let uu____3749 = j.job ()  in FStar_All.pipe_left j.callback uu____3749

let (init : Prims.unit -> Prims.unit) =
  fun uu____3752  ->
    FStar_ST.op_Colon_Equals running true;
    (let n_cores1 = FStar_Options.n_cores ()  in
     if n_cores1 > (Prims.parse_int "1")
     then
       let rec aux n1 =
         if n1 = (Prims.parse_int "0")
         then ()
         else (FStar_Util.spawn dequeue; aux (n1 - (Prims.parse_int "1")))
          in
       aux n_cores1
     else ())
  
let (enqueue : z3job -> Prims.unit) =
  fun j  ->
    FStar_Util.with_monitor job_queue
      (fun uu____3790  ->
         (let uu____3792 =
            let uu____3795 = FStar_ST.op_Bang job_queue  in
            FStar_List.append uu____3795 [j]  in
          FStar_ST.op_Colon_Equals job_queue uu____3792);
         FStar_Util.monitor_pulse job_queue) ()
  
let (finish : Prims.unit -> Prims.unit) =
  fun uu____3850  ->
    let rec aux uu____3854 =
      let uu____3855 =
        FStar_Util.with_monitor job_queue
          (fun uu____3871  ->
             let uu____3872 = FStar_ST.op_Bang pending_jobs  in
             let uu____3892 =
               let uu____3893 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____3893  in
             (uu____3872, uu____3892)) ()
         in
      match uu____3855 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list[@@deriving
                                                                  show]
let (fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : Prims.unit -> scope_t) =
  fun uu____3981  -> FStar_ST.op_Bang fresh_scope 
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> Prims.unit) =
  fun msg  ->
    (let uu____4030 =
       let uu____4035 = FStar_ST.op_Bang fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____4035
        in
     FStar_ST.op_Colon_Equals fresh_scope uu____4030);
    (let uu____4096 =
       let uu____4099 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4099
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4096)
  
let (pop : Prims.string -> Prims.unit) =
  fun msg  ->
    (let uu____4152 =
       let uu____4157 = FStar_ST.op_Bang fresh_scope  in
       FStar_List.tl uu____4157  in
     FStar_ST.op_Colon_Equals fresh_scope uu____4152);
    (let uu____4218 =
       let uu____4221 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4221
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4218)
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit) =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___40_4281  ->
            match uu___40_4281 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____4282 -> ()));
    (let uu____4284 = FStar_ST.op_Bang fresh_scope  in
     match uu____4284 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____4355 -> failwith "Impossible");
    (let uu____4360 =
       let uu____4363 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4363 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____4360)
  
let (refresh : Prims.unit -> Prims.unit) =
  fun uu____4414  ->
    (let uu____4416 =
       let uu____4417 = FStar_Options.n_cores ()  in
       uu____4417 < (Prims.parse_int "2")  in
     if uu____4416
     then
       let uu____4418 =
         let uu____4421 = FStar_ST.op_Bang bg_z3_proc  in uu____4421.refresh
          in
       uu____4418 ()
     else ());
    (let uu____4442 =
       let uu____4445 =
         let uu____4450 = FStar_ST.op_Bang fresh_scope  in
         FStar_List.rev uu____4450  in
       FStar_List.flatten uu____4445  in
     FStar_ST.op_Colon_Equals bg_scope uu____4442)
  
let (mk_input :
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun theory  ->
    let options = FStar_ST.op_Bang z3_options  in
    let uu____4540 =
      let uu____4547 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
         in
      if uu____4547
      then
        let uu____4554 =
          let uu____4565 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___41_4593  ->
                    match uu___41_4593 with
                    | FStar_SMTEncoding_Term.CheckSat  -> true
                    | uu____4594 -> false))
             in
          FStar_All.pipe_right uu____4565 FStar_Option.get  in
        match uu____4554 with
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
            let uncaption uu___42_4672 =
              match uu___42_4672 with
              | FStar_SMTEncoding_Term.Caption uu____4673 ->
                  FStar_SMTEncoding_Term.Caption ""
              | FStar_SMTEncoding_Term.Assume a ->
                  FStar_SMTEncoding_Term.Assume
                    (let uu___47_4677 = a  in
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         (uu___47_4677.FStar_SMTEncoding_Term.assumption_term);
                       FStar_SMTEncoding_Term.assumption_caption =
                         FStar_Pervasives_Native.None;
                       FStar_SMTEncoding_Term.assumption_name =
                         (uu___47_4677.FStar_SMTEncoding_Term.assumption_name);
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         (uu___47_4677.FStar_SMTEncoding_Term.assumption_fact_ids)
                     })
              | FStar_SMTEncoding_Term.DeclFun (n1,a,s,uu____4681) ->
                  FStar_SMTEncoding_Term.DeclFun
                    (n1, a, s, FStar_Pervasives_Native.None)
              | FStar_SMTEncoding_Term.DefineFun (n1,a,s,b,uu____4694) ->
                  FStar_SMTEncoding_Term.DefineFun
                    (n1, a, s, b, FStar_Pervasives_Native.None)
              | d -> d  in
            let hs =
              let uu____4705 =
                let uu____4708 =
                  let uu____4711 =
                    FStar_All.pipe_right prefix1 (FStar_List.map uncaption)
                     in
                  FStar_All.pipe_right uu____4711 pp_no_cap  in
                FStar_All.pipe_right uu____4708
                  (FStar_List.filter (fun s  -> s <> ""))
                 in
              FStar_All.pipe_right uu____4705 (FStar_String.concat "\n")  in
            let uu____4730 =
              let uu____4733 = FStar_Util.digest_of_string hs  in
              FStar_Pervasives_Native.Some uu____4733  in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____4730)
      else
        (let uu____4737 =
           let uu____4738 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory
              in
           FStar_All.pipe_right uu____4738 (FStar_String.concat "\n")  in
         (uu____4737, FStar_Pervasives_Native.None))
       in
    match uu____4540 with
    | (r,hash) ->
        ((let uu____4758 = FStar_Options.log_queries ()  in
          if uu____4758 then query_logging.write_to_log r else ());
         (r, hash))
  
type cb = z3result -> Prims.unit[@@deriving show]
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool)
  =
  fun cache  ->
    fun qhash  ->
      fun cb  ->
        let uu____4783 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())
           in
        if uu____4783
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Util.smap_create (Prims.parse_int "0")  in
              (FStar_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status = (UNSAT FStar_Pervasives_Native.None);
                    z3result_time = (Prims.parse_int "0");
                    z3result_statistics = stats;
                    z3result_query_hash = qhash
                  }  in
                cb result; true))
          | uu____4794 -> false
        else false
  
let (ask_1_core :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit)
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun cb  ->
              let theory =
                let uu____4838 = FStar_ST.op_Bang bg_scope  in
                FStar_List.append uu____4838
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                 in
              let uu____4864 = filter_theory theory  in
              match uu____4864 with
              | (theory1,used_unsat_core) ->
                  let uu____4871 = mk_input theory1  in
                  (match uu____4871 with
                   | (input,qhash) ->
                       (FStar_ST.op_Colon_Equals bg_scope [];
                        (let uu____4908 =
                           let uu____4909 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____4909  in
                         if uu____4908
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
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t ->
            scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit)
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let theory =
                  let uu____4962 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____4998 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____4998))
                     in
                  FStar_List.flatten uu____4962  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____5035 = filter_theory theory1  in
                match uu____5035 with
                | (theory2,used_unsat_core) ->
                    let uu____5042 = mk_input theory2  in
                    (match uu____5042 with
                     | (input,qhash) ->
                         let uu____5055 =
                           let uu____5056 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____5056  in
                         if uu____5055
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
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit)
  =
  fun r  ->
    fun filter1  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let uu____5108 =
                  let uu____5109 = FStar_Options.n_cores ()  in
                  uu____5109 = (Prims.parse_int "1")  in
                if uu____5108
                then ask_1_core r filter1 cache label_messages qry cb
                else ask_n_cores r filter1 cache label_messages qry scope cb
  
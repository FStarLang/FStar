open Prims
let _z3hash_checked : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let _z3hash_expected : Prims.string = "1f29cebd4df6" 
let _z3url : Prims.string =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____24 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___38_40 =
          match uu___38_40 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.lift_native_int (0)) n1
                 in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____51 = FStar_Options.debug_any ()  in
                  if uu____51
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
          | uu____56::q -> aux q
          | uu____60 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____63 -> FStar_Pervasives_Native.Some "No Z3 version string found"
  
let z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option
  =
  fun uu____76  ->
    let run_proc_result =
      try
        let uu____105 =
          let uu____112 = FStar_Options.z3_exe ()  in
          FStar_Util.run_proc uu____112 "-version" ""  in
        FStar_Pervasives_Native.Some uu____105
      with | uu____130 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some (uu____153,out,uu____155) ->
        let uu____162 = parse_z3_version_lines out  in
        (match uu____162 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let check_z3hash : unit -> unit =
  fun uu____184  ->
    let uu____185 =
      let uu____186 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____186  in
    if uu____185
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____234 = z3hash_warning_message ()  in
        match uu____234 with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some (e,msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH"
               in
            FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)))
    else ()
  
let ini_params : unit -> Prims.string =
  fun uu____257  ->
    check_z3hash ();
    (let uu____259 =
       let uu____262 =
         let uu____265 =
           let uu____268 =
             let uu____269 =
               let uu____270 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____270  in
             FStar_Util.format1 "smt.random_seed=%s" uu____269  in
           [uu____268]  in
         "-smt2 -in auto_config=false model=true smt.relevancy=2 smt.case_split=3"
           :: uu____265
          in
       let uu____271 = FStar_Options.z3_cliopt ()  in
       FStar_List.append uu____262 uu____271  in
     FStar_String.concat " " uu____259)
  
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
let uu___is_UNSAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____322 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____342 -> false
  
let __proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____380 -> false
  
let __proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____418 -> false
  
let __proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____449 -> false
  
type z3statistics = Prims.string FStar_Util.smap[@@deriving show]
let status_tag : z3status -> Prims.string =
  fun uu___39_456  ->
    match uu___39_456 with
    | SAT uu____457 -> "sat"
    | UNSAT uu____464 -> "unsat"
    | UNKNOWN uu____465 -> "unknown"
    | TIMEOUT uu____472 -> "timeout"
    | KILLED  -> "killed"
  
let status_string_and_errors :
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____494 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____503 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____503, errs)
    | UNKNOWN (errs,msg) ->
        let uu____511 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____511, errs)
    | TIMEOUT (errs,msg) ->
        let uu____519 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____519, errs)
  
let tid : unit -> Prims.string =
  fun uu____525  ->
    let uu____526 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____526 FStar_Util.string_of_int
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id1  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let uu____544 = FStar_Options.z3_exe ()  in
    let uu____545 = ini_params ()  in
    FStar_Util.start_process false id1 uu____544 uu____545 cond
  
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit }[@@deriving show]
let __proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__ask
  
let __proj__Mkbgproc__item__refresh : bgproc -> unit -> unit =
  fun projectee  ->
    match projectee with
    | { ask = __fname__ask; refresh = __fname__refresh;
        restart = __fname__restart;_} -> __fname__refresh
  
let __proj__Mkbgproc__item__restart : bgproc -> unit -> unit =
  fun projectee  ->
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
let __proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
  
let __proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
  
let __proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
  
let __proj__Mkquery_log__item__close_log : query_log -> unit -> unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
  
let __proj__Mkquery_log__item__log_file_name :
  query_log -> unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
  
let query_logging : query_log =
  let query_number = FStar_Util.mk_ref (Prims.lift_native_int (0))  in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let used_file_names = FStar_Util.mk_ref []  in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None
     in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let set_module_name n1 =
    FStar_ST.op_Colon_Equals current_module_name
      (FStar_Pervasives_Native.Some n1)
     in
  let get_module_name uu____961 =
    let uu____962 = FStar_ST.op_Bang current_module_name  in
    match uu____962 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____1020 =
    let uu____1021 = FStar_ST.op_Bang current_module_name  in
    match uu____1021 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____1075 =
            let uu____1082 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____1153  ->
                 match uu____1153 with | (m,uu____1159) -> n1 = m) uu____1082
             in
          match uu____1075 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1165 =
                  let uu____1172 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.lift_native_int (0))) :: uu____1172  in
                FStar_ST.op_Colon_Equals used_file_names uu____1165);
               n1)
          | FStar_Pervasives_Native.Some (uu____1297,k) ->
              ((let uu____1304 =
                  let uu____1311 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.lift_native_int (1)))) :: uu____1311  in
                FStar_ST.op_Colon_Equals used_file_names uu____1304);
               (let uu____1436 =
                  FStar_Util.string_of_int (k + (Prims.lift_native_int (1)))
                   in
                FStar_Util.format2 "%s-%s" n1 uu____1436))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh))
     in
  let get_log_file uu____1544 =
    let uu____1545 = FStar_ST.op_Bang log_file_opt  in
    match uu____1545 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1604 = get_log_file ()  in
    FStar_Util.append_to_file uu____1604 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1612 = FStar_ST.op_Bang current_file_name  in
      match uu____1612 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1665 = FStar_ST.op_Bang current_module_name  in
            match uu____1665 with
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
    (let uu____1817 =
       let uu____1818 = FStar_ST.op_Bang query_number  in
       uu____1818 + (Prims.lift_native_int (1))  in
     FStar_ST.op_Colon_Equals query_number uu____1817);
    (let file_name =
       let uu____1910 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____1910  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____1918 =
      let uu____1919 = FStar_Options.n_cores ()  in
      uu____1919 > (Prims.lift_native_int (1))  in
    if uu____1918 then write_to_new_log str else append_to_log str  in
  let close_log uu____1926 =
    let uu____1927 = FStar_ST.op_Bang log_file_opt  in
    match uu____1927 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____2035 =
    let uu____2036 = FStar_ST.op_Bang current_file_name  in
    match uu____2036 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let bg_z3_proc : bgproc FStar_ST.ref =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.lift_native_int (1)))  in
    fun uu____2117  ->
      let uu____2118 =
        let uu____2119 =
          FStar_Util.incr ctr;
          (let uu____2154 = FStar_ST.op_Bang ctr  in
           FStar_All.pipe_right uu____2154 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____2119  in
      new_z3proc uu____2118
     in
  let z3proc uu____2205 =
    (let uu____2207 =
       let uu____2208 = FStar_ST.op_Bang the_z3proc  in
       uu____2208 = FStar_Pervasives_Native.None  in
     if uu____2207
     then
       let uu____2262 =
         let uu____2265 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____2265  in
       FStar_ST.op_Colon_Equals the_z3proc uu____2262
     else ());
    (let uu____2316 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____2316)
     in
  let x = []  in
  let grab uu____2376 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____2385 = FStar_Util.monitor_exit x  in
  let ask input =
    let proc = grab ()  in
    let stdout1 = FStar_Util.ask_process proc input  in release (); stdout1
     in
  let refresh uu____2402 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let uu____2406 =
       let uu____2409 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2409  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2406);
    query_logging.close_log ();
    release ()  in
  let restart uu____2465 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2519 =
       let uu____2522 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2522  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2519);
    FStar_Util.monitor_exit ()  in
  FStar_Util.mk_ref { ask; refresh; restart } 
let set_bg_z3_proc : bgproc -> unit =
  fun bgp  -> FStar_ST.op_Colon_Equals bg_z3_proc bgp 
let at_log_file : unit -> Prims.string =
  fun uu____2604  ->
    let uu____2605 = FStar_Options.log_queries ()  in
    if uu____2605
    then
      let uu____2606 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____2606
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
let __proj__Mksmt_output__item__smt_result : smt_output -> smt_output_section
  =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_result
  
let __proj__Mksmt_output__item__smt_reason_unknown :
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_reason_unknown
  
let __proj__Mksmt_output__item__smt_unsat_core :
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_unsat_core
  
let __proj__Mksmt_output__item__smt_statistics :
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_statistics
  
let __proj__Mksmt_output__item__smt_labels :
  smt_output -> smt_output_section FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_labels
  
let smt_output_sections :
  FStar_Range.range -> Prims.string Prims.list -> smt_output =
  fun r  ->
    fun lines  ->
      let rec until tag lines1 =
        match lines1 with
        | [] -> FStar_Pervasives_Native.None
        | l::lines2 ->
            if tag = l
            then FStar_Pervasives_Native.Some ([], lines2)
            else
              (let uu____2833 = until tag lines2  in
               FStar_Util.map_opt uu____2833
                 (fun uu____2863  ->
                    match uu____2863 with
                    | (until_tag,rest) -> ((l :: until_tag), rest)))
         in
      let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">")  in
      let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">")  in
      let find_section tag lines1 =
        let uu____2941 = until (start_tag tag) lines1  in
        match uu____2941 with
        | FStar_Pervasives_Native.None  ->
            (FStar_Pervasives_Native.None, lines1)
        | FStar_Pervasives_Native.Some (prefix1,suffix) ->
            let uu____2996 = until (end_tag tag) suffix  in
            (match uu____2996 with
             | FStar_Pervasives_Native.None  ->
                 failwith
                   (Prims.strcat "Parse error: "
                      (Prims.strcat (end_tag tag) " not found"))
             | FStar_Pervasives_Native.Some (section,suffix1) ->
                 ((FStar_Pervasives_Native.Some section),
                   (FStar_List.append prefix1 suffix1)))
         in
      let uu____3061 = find_section "result" lines  in
      match uu____3061 with
      | (result_opt,lines1) ->
          let result = FStar_Util.must result_opt  in
          let uu____3091 = find_section "reason-unknown" lines1  in
          (match uu____3091 with
           | (reason_unknown,lines2) ->
               let uu____3116 = find_section "unsat-core" lines2  in
               (match uu____3116 with
                | (unsat_core,lines3) ->
                    let uu____3141 = find_section "statistics" lines3  in
                    (match uu____3141 with
                     | (statistics,lines4) ->
                         let uu____3166 = find_section "labels" lines4  in
                         (match uu____3166 with
                          | (labels,lines5) ->
                              let remaining =
                                let uu____3194 = until "Done!" lines5  in
                                match uu____3194 with
                                | FStar_Pervasives_Native.None  -> lines5
                                | FStar_Pervasives_Native.Some
                                    (prefix1,suffix) ->
                                    FStar_List.append prefix1 suffix
                                 in
                              ((match remaining with
                                | [] -> ()
                                | uu____3234 ->
                                    let uu____3237 =
                                      let uu____3242 =
                                        FStar_Util.format1
                                          "Unexpected output from Z3: %s\n"
                                          (FStar_String.concat "\n" remaining)
                                         in
                                      (FStar_Errors.Warning_UnexpectedZ3Output,
                                        uu____3242)
                                       in
                                    FStar_Errors.log_issue r uu____3237);
                               (let uu____3243 = FStar_Util.must result_opt
                                   in
                                {
                                  smt_result = uu____3243;
                                  smt_reason_unknown = reason_unknown;
                                  smt_unsat_core = unsat_core;
                                  smt_statistics = statistics;
                                  smt_labels = labels
                                }))))))
  
let doZ3Exe :
  FStar_Range.range ->
    Prims.bool ->
      Prims.string ->
        FStar_SMTEncoding_Term.error_labels ->
          (z3status,z3statistics) FStar_Pervasives_Native.tuple2
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
                    FStar_Util.substring s1 (Prims.lift_native_int (1))
                      ((FStar_String.length s1) - (Prims.lift_native_int (2)))
                     in
                  if FStar_Util.starts_with s2 "error"
                  then FStar_Pervasives_Native.None
                  else
                    (let uu____3316 =
                       FStar_All.pipe_right (FStar_Util.split s2 " ")
                         (FStar_Util.sort_with FStar_String.compare)
                        in
                     FStar_Pervasives_Native.Some uu____3316)
               in
            let labels =
              match smt_output.smt_labels with
              | FStar_Pervasives_Native.None  -> []
              | FStar_Pervasives_Native.Some lines1 ->
                  let rec lblnegs lines2 =
                    match lines2 with
                    | lname::"false"::rest when
                        FStar_Util.starts_with lname "label_" ->
                        let uu____3379 = lblnegs rest  in lname :: uu____3379
                    | lname::uu____3383::rest when
                        FStar_Util.starts_with lname "label_" -> lblnegs rest
                    | uu____3387 -> []  in
                  let lblnegs1 = lblnegs lines1  in
                  FStar_All.pipe_right lblnegs1
                    (FStar_List.collect
                       (fun l  ->
                          let uu____3420 =
                            FStar_All.pipe_right label_messages
                              (FStar_List.tryFind
                                 (fun uu____3459  ->
                                    match uu____3459 with
                                    | (m,uu____3471,uu____3472) ->
                                        (FStar_Pervasives_Native.fst m) = l))
                             in
                          match uu____3420 with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some (lbl,msg,r1) ->
                              [(lbl, msg, r1)]))
               in
            let statistics =
              let statistics =
                FStar_Util.smap_create (Prims.lift_native_int (0))  in
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
                               (Prims.lift_native_int (1)))
                           in
                        let value =
                          if FStar_Util.ends_with ltok ")"
                          then
                            FStar_Util.substring ltok
                              (Prims.lift_native_int (0))
                              ((FStar_String.length ltok) -
                                 (Prims.lift_native_int (1)))
                          else ltok  in
                        FStar_Util.smap_add statistics key value
                    | ""::entry::[] ->
                        let tokens = FStar_Util.split entry " "  in
                        let key = FStar_List.hd tokens  in
                        let ltok =
                          FStar_List.nth tokens
                            ((FStar_List.length tokens) -
                               (Prims.lift_native_int (1)))
                           in
                        let value =
                          if FStar_Util.ends_with ltok ")"
                          then
                            FStar_Util.substring ltok
                              (Prims.lift_native_int (0))
                              ((FStar_String.length ltok) -
                                 (Prims.lift_native_int (1)))
                          else ltok  in
                        FStar_Util.smap_add statistics key value
                    | uu____3586 -> ()  in
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
                       FStar_String.substring reason
                         (Prims.lift_native_int (0))
                         ((FStar_String.length reason) -
                            (Prims.lift_native_int (2)))
                        in
                     res
                   else ru)
               in
            let status =
              (let uu____3604 = FStar_Options.debug_any ()  in
               if uu____3604
               then
                 let uu____3605 =
                   FStar_Util.format1 "Z3 says: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result)
                    in
                 FStar_All.pipe_left FStar_Util.print_string uu____3605
               else ());
              (match smt_output.smt_result with
               | "unsat"::[] -> UNSAT unsat_core
               | "sat"::[] -> SAT (labels, reason_unknown)
               | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
               | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
               | "killed"::[] ->
                   ((let uu____3650 =
                       let uu____3655 = FStar_ST.op_Bang bg_z3_proc  in
                       uu____3655.restart  in
                     uu____3650 ());
                    KILLED)
               | uu____3679 ->
                   let uu____3680 =
                     FStar_Util.format1
                       "Unexpected output from Z3: got output result: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   failwith uu____3680)
               in
            (status, statistics)  in
          let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x
             in
          let stdout1 =
            if fresh
            then
              let uu____3694 = tid ()  in
              let uu____3695 = FStar_Options.z3_exe ()  in
              let uu____3696 = ini_params ()  in
              FStar_Util.launch_process false uu____3694 uu____3695
                uu____3696 input cond
            else
              (let uu____3698 =
                 let uu____3703 = FStar_ST.op_Bang bg_z3_proc  in
                 uu____3703.ask  in
               uu____3698 input)
             in
          parse (FStar_Util.trim_string stdout1)
  
let z3_options : Prims.string FStar_ST.ref =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
let set_z3_options : Prims.string -> unit =
  fun opts  -> FStar_ST.op_Colon_Equals z3_options opts 
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
let __proj__Mkz3result__item__z3result_status : z3result -> z3status =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_status
  
let __proj__Mkz3result__item__z3result_time : z3result -> Prims.int =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_time
  
let __proj__Mkz3result__item__z3result_statistics : z3result -> z3statistics
  =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_statistics
  
let __proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { z3result_status = __fname__z3result_status;
        z3result_time = __fname__z3result_time;
        z3result_statistics = __fname__z3result_statistics;
        z3result_query_hash = __fname__z3result_query_hash;_} ->
        __fname__z3result_query_hash
  
type z3job = z3result job[@@deriving show]
let job_queue : z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let pending_jobs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.lift_native_int (0)) 
let with_monitor :
  'Auu____3954 'Auu____3955 .
    'Auu____3954 -> (unit -> 'Auu____3955) -> 'Auu____3955
  =
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f ()  in FStar_Util.monitor_exit m; res)
  
let z3_job :
  FStar_Range.range ->
    Prims.bool ->
      FStar_SMTEncoding_Term.error_labels ->
        Prims.string ->
          Prims.string FStar_Pervasives_Native.option -> unit -> z3result
  =
  fun r  ->
    fun fresh  ->
      fun label_messages  ->
        fun input  ->
          fun qhash  ->
            fun uu____4005  ->
              let start = FStar_Util.now ()  in
              let uu____4009 =
                try doZ3Exe r fresh input label_messages
                with
                | uu____4033 when
                    let uu____4034 = FStar_Options.trace_error ()  in
                    Prims.op_Negation uu____4034 ->
                    ((let uu____4036 =
                        let uu____4041 = FStar_ST.op_Bang bg_z3_proc  in
                        uu____4041.refresh  in
                      uu____4036 ());
                     (let uu____4065 =
                        FStar_Util.smap_create (Prims.lift_native_int (0))
                         in
                      ((UNKNOWN
                          ([],
                            (FStar_Pervasives_Native.Some
                               "Z3 raised an exception"))), uu____4065)))
                 in
              match uu____4009 with
              | (status,statistics) ->
                  let uu____4076 =
                    let uu____4081 = FStar_Util.now ()  in
                    FStar_Util.time_diff start uu____4081  in
                  (match uu____4076 with
                   | (uu____4082,elapsed_time) ->
                       {
                         z3result_status = status;
                         z3result_time = elapsed_time;
                         z3result_statistics = statistics;
                         z3result_query_hash = qhash
                       })
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : unit -> unit =
  fun uu____4109  ->
    let j =
      let uu____4111 = FStar_ST.op_Bang job_queue  in
      match uu____4111 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____4186  -> FStar_Util.decr pending_jobs);
    dequeue ()

and dequeue : unit -> unit =
  fun uu____4188  ->
    let uu____4189 = FStar_ST.op_Bang running  in
    if uu____4189
    then
      let rec aux uu____4218 =
        FStar_Util.monitor_enter job_queue;
        (let uu____4224 = FStar_ST.op_Bang job_queue  in
         match uu____4224 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.lift_native_int (50));
              aux ())
         | uu____4260 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> unit =
  fun j  ->
    let uu____4264 = j.job ()  in FStar_All.pipe_left j.callback uu____4264

let init : unit -> unit =
  fun uu____4269  ->
    FStar_ST.op_Colon_Equals running true;
    (let n_cores1 = FStar_Options.n_cores ()  in
     if n_cores1 > (Prims.lift_native_int (1))
     then
       let rec aux n1 =
         if n1 = (Prims.lift_native_int (0))
         then ()
         else
           (FStar_Util.spawn dequeue; aux (n1 - (Prims.lift_native_int (1))))
          in
       aux n_cores1
     else ())
  
let enqueue : z3job -> unit =
  fun j  ->
    FStar_Util.monitor_enter job_queue;
    (let uu____4315 =
       let uu____4318 = FStar_ST.op_Bang job_queue  in
       FStar_List.append uu____4318 [j]  in
     FStar_ST.op_Colon_Equals job_queue uu____4315);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
  
let finish : unit -> unit =
  fun uu____4388  ->
    let rec aux uu____4394 =
      let uu____4395 =
        with_monitor job_queue
          (fun uu____4411  ->
             let uu____4412 = FStar_ST.op_Bang pending_jobs  in
             let uu____4436 =
               let uu____4437 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____4437  in
             (uu____4412, uu____4436))
         in
      match uu____4395 with
      | (n1,m) ->
          if (n1 + m) = (Prims.lift_native_int (0))
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.lift_native_int (500)); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list[@@deriving
                                                                  show]
let fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let mk_fresh_scope : unit -> scope_t =
  fun uu____4535  -> FStar_ST.op_Bang fresh_scope 
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let push : Prims.string -> unit =
  fun msg  ->
    (let uu____4590 =
       let uu____4595 = FStar_ST.op_Bang fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____4595
        in
     FStar_ST.op_Colon_Equals fresh_scope uu____4590);
    (let uu____4664 =
       let uu____4667 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4667
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4664)
  
let pop : Prims.string -> unit =
  fun msg  ->
    (let uu____4730 =
       let uu____4735 = FStar_ST.op_Bang fresh_scope  in
       FStar_List.tl uu____4735  in
     FStar_ST.op_Colon_Equals fresh_scope uu____4730);
    (let uu____4804 =
       let uu____4807 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4807
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4804)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___40_4877  ->
            match uu___40_4877 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____4878 -> ()));
    (let uu____4880 = FStar_ST.op_Bang fresh_scope  in
     match uu____4880 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____4959 -> failwith "Impossible");
    (let uu____4964 =
       let uu____4967 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4967 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____4964)
  
let refresh : unit -> unit =
  fun uu____5028  ->
    (let uu____5030 =
       let uu____5031 = FStar_Options.n_cores ()  in
       uu____5031 < (Prims.lift_native_int (2))  in
     if uu____5030
     then
       let uu____5032 =
         let uu____5037 = FStar_ST.op_Bang bg_z3_proc  in uu____5037.refresh
          in
       uu____5032 ()
     else ());
    (let uu____5062 =
       let uu____5065 =
         let uu____5070 = FStar_ST.op_Bang fresh_scope  in
         FStar_List.rev uu____5070  in
       FStar_List.flatten uu____5065  in
     FStar_ST.op_Colon_Equals bg_scope uu____5062)
  
let mk_input :
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  =
  fun theory  ->
    let options = FStar_ST.op_Bang z3_options  in
    let uu____5174 =
      let uu____5181 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
         in
      if uu____5181
      then
        let uu____5188 =
          let uu____5199 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___41_5227  ->
                    match uu___41_5227 with
                    | FStar_SMTEncoding_Term.CheckSat  -> true
                    | uu____5228 -> false))
             in
          FStar_All.pipe_right uu____5199 FStar_Option.get  in
        match uu____5188 with
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
            let uncaption uu___42_5312 =
              match uu___42_5312 with
              | FStar_SMTEncoding_Term.Caption uu____5313 ->
                  FStar_SMTEncoding_Term.Caption ""
              | FStar_SMTEncoding_Term.Assume a ->
                  FStar_SMTEncoding_Term.Assume
                    (let uu___47_5317 = a  in
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         (uu___47_5317.FStar_SMTEncoding_Term.assumption_term);
                       FStar_SMTEncoding_Term.assumption_caption =
                         FStar_Pervasives_Native.None;
                       FStar_SMTEncoding_Term.assumption_name =
                         (uu___47_5317.FStar_SMTEncoding_Term.assumption_name);
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         (uu___47_5317.FStar_SMTEncoding_Term.assumption_fact_ids)
                     })
              | FStar_SMTEncoding_Term.DeclFun (n1,a,s,uu____5321) ->
                  FStar_SMTEncoding_Term.DeclFun
                    (n1, a, s, FStar_Pervasives_Native.None)
              | FStar_SMTEncoding_Term.DefineFun (n1,a,s,b,uu____5334) ->
                  FStar_SMTEncoding_Term.DefineFun
                    (n1, a, s, b, FStar_Pervasives_Native.None)
              | d -> d  in
            let hs =
              let uu____5345 =
                let uu____5348 =
                  let uu____5351 =
                    FStar_All.pipe_right prefix1 (FStar_List.map uncaption)
                     in
                  FStar_All.pipe_right uu____5351 pp_no_cap  in
                FStar_All.pipe_right uu____5348
                  (FStar_List.filter (fun s  -> s <> ""))
                 in
              FStar_All.pipe_right uu____5345 (FStar_String.concat "\n")  in
            let uu____5370 =
              let uu____5373 = FStar_Util.digest_of_string hs  in
              FStar_Pervasives_Native.Some uu____5373  in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____5370)
      else
        (let uu____5377 =
           let uu____5378 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory
              in
           FStar_All.pipe_right uu____5378 (FStar_String.concat "\n")  in
         (uu____5377, FStar_Pervasives_Native.None))
       in
    match uu____5174 with
    | (r,hash) ->
        ((let uu____5398 = FStar_Options.log_queries ()  in
          if uu____5398 then query_logging.write_to_log r else ());
         (r, hash))
  
type cb = z3result -> unit[@@deriving show]
let cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool
  =
  fun cache  ->
    fun qhash  ->
      fun cb  ->
        let uu____5432 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())
           in
        if uu____5432
        then
          match qhash with
          | FStar_Pervasives_Native.Some x when qhash = cache ->
              let stats = FStar_Util.smap_create (Prims.lift_native_int (0))
                 in
              (FStar_Util.smap_add stats "fstar_cache_hit" "1";
               (let result =
                  {
                    z3result_status = (UNSAT FStar_Pervasives_Native.None);
                    z3result_time = (Prims.lift_native_int (0));
                    z3result_statistics = stats;
                    z3result_query_hash = qhash
                  }  in
                cb result; true))
          | uu____5443 -> false
        else false
  
let ask_1_core :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t -> cb -> unit
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun cb  ->
              let theory =
                let uu____5501 = FStar_ST.op_Bang bg_scope  in
                FStar_List.append uu____5501
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                 in
              let uu____5531 = filter_theory theory  in
              match uu____5531 with
              | (theory1,used_unsat_core) ->
                  let uu____5538 = mk_input theory1  in
                  (match uu____5538 with
                   | (input,qhash) ->
                       (FStar_ST.op_Colon_Equals bg_scope [];
                        (let uu____5579 =
                           let uu____5580 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____5580  in
                         if uu____5579
                         then
                           run_job
                             {
                               job =
                                 (z3_job r false label_messages input qhash);
                               callback = cb
                             }
                         else ())))
  
let ask_n_cores :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t ->
            scope_t FStar_Pervasives_Native.option -> cb -> unit
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let theory =
                  let uu____5649 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____5689 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____5689))
                     in
                  FStar_List.flatten uu____5649  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____5730 = filter_theory theory1  in
                match uu____5730 with
                | (theory2,used_unsat_core) ->
                    let uu____5737 = mk_input theory2  in
                    (match uu____5737 with
                     | (input,qhash) ->
                         let uu____5750 =
                           let uu____5751 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____5751  in
                         if uu____5750
                         then
                           enqueue
                             {
                               job =
                                 (z3_job r true label_messages input qhash);
                               callback = cb
                             }
                         else ())
  
let ask :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            scope_t FStar_Pervasives_Native.option -> cb -> unit
  =
  fun r  ->
    fun filter1  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let uu____5819 =
                  let uu____5820 = FStar_Options.n_cores ()  in
                  uu____5820 = (Prims.lift_native_int (1))  in
                if uu____5819
                then ask_1_core r filter1 cache label_messages qry cb
                else ask_n_cores r filter1 cache label_messages qry scope cb
  
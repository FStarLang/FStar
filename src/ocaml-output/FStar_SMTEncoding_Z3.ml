open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____38 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___123_62 =
          match uu___123_62 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____84 = FStar_Options.debug_any ()  in
                  if uu____84
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
          | uu____99::q -> aux q
          | uu____106 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____112 -> FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error,Prims.string) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____130  ->
    let run_proc_result =
      try
        (fun uu___128_140  ->
           match () with
           | () ->
               let uu____144 =
                 let uu____146 = FStar_Options.z3_exe ()  in
                 FStar_Util.run_process "z3_version" uu____146 ["-version"]
                   FStar_Pervasives_Native.None
                  in
               FStar_Pervasives_Native.Some uu____144) ()
      with | uu___127_155 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____178 = parse_z3_version_lines out  in
        (match uu____178 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : unit -> unit) =
  fun uu____209  ->
    let uu____210 =
      let uu____212 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____212  in
    if uu____210
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____259 = z3hash_warning_message ()  in
        match uu____259 with
        | FStar_Pervasives_Native.None  -> ()
        | FStar_Pervasives_Native.Some (e,msg) ->
            let msg1 =
              FStar_Util.format4 "%s\n%s\n%s\n%s\n" msg
                "Please download the version of Z3 corresponding to your platform from:"
                _z3url "and add the bin/ subdirectory into your PATH"
               in
            FStar_Errors.log_issue FStar_Range.dummyRange (e, msg1)))
    else ()
  
let (ini_params : unit -> Prims.string Prims.list) =
  fun uu____297  ->
    check_z3hash ();
    (let uu____299 =
       let uu____303 =
         let uu____307 =
           let uu____311 =
             let uu____315 =
               let uu____319 =
                 let uu____323 =
                   let uu____327 =
                     let uu____329 =
                       let uu____331 = FStar_Options.z3_seed ()  in
                       FStar_Util.string_of_int uu____331  in
                     FStar_Util.format1 "smt.random_seed=%s" uu____329  in
                   [uu____327]  in
                 "smt.case_split=3" :: uu____323  in
               "smt.relevancy=2" :: uu____319  in
             "model=true" :: uu____315  in
           "auto_config=false" :: uu____311  in
         "-in" :: uu____307  in
       "-smt2" :: uu____303  in
     let uu____348 = FStar_Options.z3_cliopt ()  in
     FStar_List.append uu____299 uu____348)
  
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
let (uu___is_UNSAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____412 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____439 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____487 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____535 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____575 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let (status_tag : z3status -> Prims.string) =
  fun uu___124_586  ->
    match uu___124_586 with
    | SAT uu____588 -> "sat"
    | UNSAT uu____597 -> "unsat"
    | UNKNOWN uu____599 -> "unknown"
    | TIMEOUT uu____608 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2)
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____635 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____645 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____645, errs)
    | UNKNOWN (errs,msg) ->
        let uu____664 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____664, errs)
    | TIMEOUT (errs,msg) ->
        let uu____683 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____683, errs)
  
let (tid : unit -> Prims.string) =
  fun uu____700  ->
    let uu____701 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____701 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let uu____713 = FStar_Options.z3_exe ()  in
    let uu____715 = ini_params ()  in
    FStar_Util.start_process id1 uu____713 uu____715 (fun s  -> s = "Done!")
  
type bgproc =
  {
  ask: Prims.string -> Prims.string ;
  refresh: unit -> unit ;
  restart: unit -> unit }
let (__proj__Mkbgproc__item__ask : bgproc -> Prims.string -> Prims.string) =
  fun projectee  -> match projectee with | { ask; refresh; restart;_} -> ask 
let (__proj__Mkbgproc__item__refresh : bgproc -> unit -> unit) =
  fun projectee  ->
    match projectee with | { ask; refresh; restart;_} -> refresh
  
let (__proj__Mkbgproc__item__restart : bgproc -> unit -> unit) =
  fun projectee  ->
    match projectee with | { ask; refresh; restart;_} -> restart
  
type query_log =
  {
  get_module_name: unit -> Prims.string ;
  set_module_name: Prims.string -> unit ;
  write_to_log: Prims.string -> unit ;
  close_log: unit -> unit ;
  log_file_name: unit -> Prims.string }
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;
        log_file_name;_} -> get_module_name
  
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;
        log_file_name;_} -> set_module_name
  
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;
        log_file_name;_} -> write_to_log
  
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;
        log_file_name;_} -> close_log
  
let (__proj__Mkquery_log__item__log_file_name :
  query_log -> unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;
        log_file_name;_} -> log_file_name
  
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
  let get_module_name uu____1209 =
    let uu____1210 = FStar_ST.op_Bang current_module_name  in
    match uu____1210 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____1273 =
    let uu____1274 = FStar_ST.op_Bang current_module_name  in
    match uu____1274 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____1332 =
            let uu____1341 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____1416  ->
                 match uu____1416 with | (m,uu____1425) -> n1 = m) uu____1341
             in
          match uu____1332 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1439 =
                  let uu____1448 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____1448  in
                FStar_ST.op_Colon_Equals used_file_names uu____1439);
               n1)
          | FStar_Pervasives_Native.Some (uu____1580,k) ->
              ((let uu____1593 =
                  let uu____1602 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1602  in
                FStar_ST.op_Colon_Equals used_file_names uu____1593);
               (let uu____1734 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____1734))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh))
     in
  let get_log_file uu____1842 =
    let uu____1843 = FStar_ST.op_Bang log_file_opt  in
    match uu____1843 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1900 = get_log_file ()  in
    FStar_Util.append_to_file uu____1900 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1911 = FStar_ST.op_Bang current_file_name  in
      match uu____1911 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1966 = FStar_ST.op_Bang current_module_name  in
            match uu____1966 with
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
    (let uu____2125 =
       let uu____2127 = FStar_ST.op_Bang query_number  in
       uu____2127 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals query_number uu____2125);
    (let file_name =
       let uu____2218 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____2218  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____2231 =
      let uu____2233 = FStar_Options.n_cores ()  in
      uu____2233 > (Prims.parse_int "1")  in
    if uu____2231 then write_to_new_log str else append_to_log str  in
  let close_log uu____2244 =
    let uu____2245 = FStar_ST.op_Bang log_file_opt  in
    match uu____2245 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____2346 =
    let uu____2347 = FStar_ST.op_Bang current_file_name  in
    match uu____2347 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____2437  ->
      let uu____2438 =
        let uu____2440 =
          FStar_Util.incr ctr;
          (let uu____2476 = FStar_ST.op_Bang ctr  in
           FStar_All.pipe_right uu____2476 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____2440  in
      new_z3proc uu____2438
     in
  let z3proc uu____2529 =
    (let uu____2531 =
       let uu____2533 = FStar_ST.op_Bang the_z3proc  in
       uu____2533 = FStar_Pervasives_Native.None  in
     if uu____2531
     then
       let uu____2584 =
         let uu____2587 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____2587  in
       FStar_ST.op_Colon_Equals the_z3proc uu____2584
     else ());
    (let uu____2635 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____2635)
     in
  let x = []  in
  let ask input =
    let kill_handler uu____2701 = "\nkilled\n"  in
    let uu____2703 = z3proc ()  in
    FStar_Util.ask_process uu____2703 input kill_handler  in
  let refresh uu____2709 =
    (let uu____2711 = z3proc ()  in FStar_Util.kill_process uu____2711);
    (let uu____2713 =
       let uu____2716 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2716  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2713);
    query_logging.close_log ()  in
  let restart uu____2767 =
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2815 =
       let uu____2818 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2818  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2815)
     in
  FStar_Util.mk_ref
    {
      ask = (FStar_Util.with_monitor x ask);
      refresh = (FStar_Util.with_monitor x refresh);
      restart = (FStar_Util.with_monitor x restart)
    }
  
let (set_bg_z3_proc : bgproc -> unit) =
  fun bgp  -> FStar_ST.op_Colon_Equals bg_z3_proc bgp 
let (at_log_file : unit -> Prims.string) =
  fun uu____2903  ->
    let uu____2904 = FStar_Options.log_queries ()  in
    if uu____2904
    then
      let uu____2908 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____2908
    else ""
  
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
  fun projectee  ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_result
  
let (__proj__Mksmt_output__item__smt_reason_unknown :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_reason_unknown
  
let (__proj__Mksmt_output__item__smt_unsat_core :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_unsat_core
  
let (__proj__Mksmt_output__item__smt_statistics :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_statistics
  
let (__proj__Mksmt_output__item__smt_labels :
  smt_output -> smt_output_section FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { smt_result; smt_reason_unknown; smt_unsat_core; smt_statistics;
        smt_labels;_} -> smt_labels
  
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
              (let uu____3172 = until tag lines2  in
               FStar_Util.map_opt uu____3172
                 (fun uu____3208  ->
                    match uu____3208 with
                    | (until_tag,rest) -> ((l :: until_tag), rest)))
         in
      let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">")  in
      let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">")  in
      let find_section tag lines1 =
        let uu____3315 = until (start_tag tag) lines1  in
        match uu____3315 with
        | FStar_Pervasives_Native.None  ->
            (FStar_Pervasives_Native.None, lines1)
        | FStar_Pervasives_Native.Some (prefix1,suffix) ->
            let uu____3385 = until (end_tag tag) suffix  in
            (match uu____3385 with
             | FStar_Pervasives_Native.None  ->
                 failwith
                   (Prims.strcat "Parse error: "
                      (Prims.strcat (end_tag tag) " not found"))
             | FStar_Pervasives_Native.Some (section,suffix1) ->
                 ((FStar_Pervasives_Native.Some section),
                   (FStar_List.append prefix1 suffix1)))
         in
      let uu____3470 = find_section "result" lines  in
      match uu____3470 with
      | (result_opt,lines1) ->
          let result = FStar_Util.must result_opt  in
          let uu____3509 = find_section "reason-unknown" lines1  in
          (match uu____3509 with
           | (reason_unknown,lines2) ->
               let uu____3541 = find_section "unsat-core" lines2  in
               (match uu____3541 with
                | (unsat_core,lines3) ->
                    let uu____3573 = find_section "statistics" lines3  in
                    (match uu____3573 with
                     | (statistics,lines4) ->
                         let uu____3605 = find_section "labels" lines4  in
                         (match uu____3605 with
                          | (labels,lines5) ->
                              let remaining =
                                let uu____3641 = until "Done!" lines5  in
                                match uu____3641 with
                                | FStar_Pervasives_Native.None  -> lines5
                                | FStar_Pervasives_Native.Some
                                    (prefix1,suffix) ->
                                    FStar_List.append prefix1 suffix
                                 in
                              ((match remaining with
                                | [] -> ()
                                | uu____3695 ->
                                    let uu____3699 =
                                      let uu____3705 =
                                        FStar_Util.format1
                                          "Unexpected output from Z3: %s\n"
                                          (FStar_String.concat "\n" remaining)
                                         in
                                      (FStar_Errors.Warning_UnexpectedZ3Output,
                                        uu____3705)
                                       in
                                    FStar_Errors.log_issue r uu____3699);
                               (let uu____3710 = FStar_Util.must result_opt
                                   in
                                {
                                  smt_result = uu____3710;
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
                    (let uu____3794 =
                       FStar_All.pipe_right (FStar_Util.split s2 " ")
                         (FStar_Util.sort_with FStar_String.compare)
                        in
                     FStar_Pervasives_Native.Some uu____3794)
               in
            let labels =
              match smt_output.smt_labels with
              | FStar_Pervasives_Native.None  -> []
              | FStar_Pervasives_Native.Some lines1 ->
                  let rec lblnegs lines2 =
                    match lines2 with
                    | lname::"false"::rest when
                        FStar_Util.starts_with lname "label_" ->
                        let uu____3839 = lblnegs rest  in lname :: uu____3839
                    | lname::uu____3845::rest when
                        FStar_Util.starts_with lname "label_" -> lblnegs rest
                    | uu____3855 -> []  in
                  let lblnegs1 = lblnegs lines1  in
                  FStar_All.pipe_right lblnegs1
                    (FStar_List.collect
                       (fun l  ->
                          let uu____3884 =
                            FStar_All.pipe_right label_messages
                              (FStar_List.tryFind
                                 (fun uu____3943  ->
                                    match uu____3943 with
                                    | (m,uu____3958,uu____3959) ->
                                        (FStar_Pervasives_Native.fst m) = l))
                             in
                          match uu____3884 with
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
                    | uu____4145 -> ()  in
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
              (let uu____4178 = FStar_Options.debug_any ()  in
               if uu____4178
               then
                 let uu____4181 =
                   FStar_Util.format1 "Z3 says: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result)
                    in
                 FStar_All.pipe_left FStar_Util.print_string uu____4181
               else ());
              (match smt_output.smt_result with
               | "unsat"::[] -> UNSAT unsat_core
               | "sat"::[] -> SAT (labels, reason_unknown)
               | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
               | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
               | "killed"::[] ->
                   ((let uu____4213 =
                       let uu____4218 = FStar_ST.op_Bang bg_z3_proc  in
                       uu____4218.restart  in
                     uu____4213 ());
                    KILLED)
               | uu____4238 ->
                   let uu____4239 =
                     FStar_Util.format1
                       "Unexpected output from Z3: got output result: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   failwith uu____4239)
               in
            (status, statistics)  in
          let stdout1 =
            if fresh
            then
              let uu____4247 = tid ()  in
              let uu____4249 = FStar_Options.z3_exe ()  in
              let uu____4251 = ini_params ()  in
              FStar_Util.run_process uu____4247 uu____4249 uu____4251
                (FStar_Pervasives_Native.Some input)
            else
              (let uu____4258 =
                 let uu____4265 = FStar_ST.op_Bang bg_z3_proc  in
                 uu____4265.ask  in
               uu____4258 input)
             in
          parse (FStar_Util.trim_string stdout1)
  
let (z3_options : Prims.string FStar_ST.ref) =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
let (set_z3_options : Prims.string -> unit) =
  fun opts  -> FStar_ST.op_Colon_Equals z3_options opts 
type 'a job_t = {
  job: unit -> 'a ;
  callback: 'a -> unit }
let __proj__Mkjob_t__item__job : 'a . 'a job_t -> unit -> 'a =
  fun projectee  -> match projectee with | { job; callback;_} -> job 
let __proj__Mkjob_t__item__callback : 'a . 'a job_t -> 'a -> unit =
  fun projectee  -> match projectee with | { job; callback;_} -> callback 
type z3result =
  {
  z3result_status: z3status ;
  z3result_time: Prims.int ;
  z3result_statistics: z3statistics ;
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkz3result__item__z3result_status : z3result -> z3status) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash;_} -> z3result_status
  
let (__proj__Mkz3result__item__z3result_time : z3result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash;_} -> z3result_time
  
let (__proj__Mkz3result__item__z3result_statistics :
  z3result -> z3statistics) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash;_} -> z3result_statistics
  
let (__proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash;_} -> z3result_query_hash
  
type z3job = z3result job_t
let (job_queue : z3job Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (pending_jobs : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (z3_job :
  FStar_Range.range ->
    Prims.bool ->
      FStar_SMTEncoding_Term.error_labels ->
        Prims.string ->
          Prims.string FStar_Pervasives_Native.option -> unit -> z3result)
  =
  fun r  ->
    fun fresh  ->
      fun label_messages  ->
        fun input  ->
          fun qhash  ->
            fun uu____4569  ->
              let start = FStar_Util.now ()  in
              let uu____4576 =
                try
                  (fun uu___130_4586  ->
                     match () with
                     | () -> doZ3Exe r fresh input label_messages) ()
                with
                | uu___129_4593 ->
                    if
                      let uu____4598 = FStar_Options.trace_error ()  in
                      Prims.op_Negation uu____4598
                    then
                      Obj.magic
                        (Obj.repr
                           ((let uu____4601 =
                               let uu____4606 = FStar_ST.op_Bang bg_z3_proc
                                  in
                               uu____4606.refresh  in
                             uu____4601 ());
                            FStar_Exn.raise uu___129_4593))
                    else Obj.magic (Obj.repr (failwith "unreachable"))
                 in
              match uu____4576 with
              | (status,statistics) ->
                  let uu____4632 =
                    let uu____4638 = FStar_Util.now ()  in
                    FStar_Util.time_diff start uu____4638  in
                  (match uu____4632 with
                   | (uu____4639,elapsed_time) ->
                       {
                         z3result_status = status;
                         z3result_time = elapsed_time;
                         z3result_statistics = statistics;
                         z3result_query_hash = qhash
                       })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : unit -> unit) =
  fun uu____4673  ->
    let j =
      let uu____4675 = FStar_ST.op_Bang job_queue  in
      match uu____4675 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    FStar_Util.with_monitor job_queue
      (fun uu____4743  -> FStar_Util.decr pending_jobs) ();
    dequeue ()

and (dequeue : unit -> unit) =
  fun uu____4745  ->
    let uu____4746 = FStar_ST.op_Bang running  in
    if uu____4746
    then
      let rec aux uu____4774 =
        FStar_Util.monitor_enter job_queue;
        (let uu____4780 = FStar_ST.op_Bang job_queue  in
         match uu____4780 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____4813 -> dequeue' ())
         in
      aux ()
    else ()

and (run_job : z3job -> unit) =
  fun j  ->
    let uu____4817 = j.job ()  in FStar_All.pipe_left j.callback uu____4817

let (init : unit -> unit) =
  fun uu____4823  ->
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
  
let (enqueue : z3job -> unit) =
  fun j  ->
    FStar_Util.with_monitor job_queue
      (fun uu____4880  ->
         (let uu____4882 =
            let uu____4885 = FStar_ST.op_Bang job_queue  in
            FStar_List.append uu____4885 [j]  in
          FStar_ST.op_Colon_Equals job_queue uu____4882);
         FStar_Util.monitor_pulse job_queue) ()
  
let (finish : unit -> unit) =
  fun uu____4943  ->
    let rec aux uu____4949 =
      let uu____4950 =
        FStar_Util.with_monitor job_queue
          (fun uu____4968  ->
             let uu____4969 = FStar_ST.op_Bang pending_jobs  in
             let uu____4992 =
               let uu____4993 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____4993  in
             (uu____4969, uu____4992)) ()
         in
      match uu____4950 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let (fresh_scope : scope_t FStar_ST.ref) = FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____5088  -> FStar_ST.op_Bang fresh_scope 
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____5137  ->
         (let uu____5139 =
            let uu____5140 = FStar_ST.op_Bang fresh_scope  in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu____5140
             in
          FStar_ST.op_Colon_Equals fresh_scope uu____5139);
         (let uu____5185 =
            let uu____5188 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____5188
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____5185))
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____5248  ->
         (let uu____5250 =
            let uu____5251 = FStar_ST.op_Bang fresh_scope  in
            FStar_List.tl uu____5251  in
          FStar_ST.op_Colon_Equals fresh_scope uu____5250);
         (let uu____5296 =
            let uu____5299 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____5299
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____5296))
  
let (snapshot :
  Prims.string -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun msg  -> FStar_Common.snapshot push fresh_scope msg 
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg  ->
    fun depth  ->
      FStar_Common.rollback (fun uu____5386  -> pop msg) fresh_scope depth
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___125_5401  ->
            match uu___125_5401 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____5404 -> ()));
    (let uu____5406 = FStar_ST.op_Bang fresh_scope  in
     match uu____5406 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____5457 -> failwith "Impossible");
    (let uu____5459 =
       let uu____5462 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____5462 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____5459)
  
let (refresh : unit -> unit) =
  fun uu____5516  ->
    (let uu____5518 =
       let uu____5520 = FStar_Options.n_cores ()  in
       uu____5520 < (Prims.parse_int "2")  in
     if uu____5518
     then
       let uu____5524 =
         let uu____5529 = FStar_ST.op_Bang bg_z3_proc  in uu____5529.refresh
          in
       uu____5524 ()
     else ());
    (let uu____5551 =
       let uu____5554 =
         let uu____5559 = FStar_ST.op_Bang fresh_scope  in
         FStar_List.rev uu____5559  in
       FStar_List.flatten uu____5554  in
     FStar_ST.op_Colon_Equals bg_scope uu____5551)
  
let (mk_input :
  FStar_SMTEncoding_Term.decl Prims.list ->
    (Prims.string,Prims.string FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  =
  fun theory  ->
    let options = FStar_ST.op_Bang z3_options  in
    let uu____5649 =
      let uu____5658 =
        (FStar_Options.record_hints ()) ||
          ((FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ()))
         in
      if uu____5658
      then
        let uu____5669 =
          let uu____5680 =
            FStar_All.pipe_right theory
              (FStar_Util.prefix_until
                 (fun uu___126_5708  ->
                    match uu___126_5708 with
                    | FStar_SMTEncoding_Term.CheckSat  -> true
                    | uu____5711 -> false))
             in
          FStar_All.pipe_right uu____5680 FStar_Option.get  in
        match uu____5669 with
        | (prefix1,check_sat,suffix) ->
            let pp =
              FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)  in
            let suffix1 = check_sat :: suffix  in
            let ps_lines = pp prefix1  in
            let ss_lines = pp suffix1  in
            let ps = FStar_String.concat "\n" ps_lines  in
            let ss = FStar_String.concat "\n" ss_lines  in
            let hs =
              let uu____5794 = FStar_Options.keep_query_captions ()  in
              if uu____5794
              then
                let uu____5798 =
                  FStar_All.pipe_right prefix1
                    (FStar_List.map
                       (FStar_SMTEncoding_Term.declToSmt_no_caps options))
                   in
                FStar_All.pipe_right uu____5798 (FStar_String.concat "\n")
              else ps  in
            let uu____5815 =
              let uu____5819 = FStar_Util.digest_of_string hs  in
              FStar_Pervasives_Native.Some uu____5819  in
            ((Prims.strcat ps (Prims.strcat "\n" ss)), uu____5815)
      else
        (let uu____5829 =
           let uu____5831 =
             FStar_List.map (FStar_SMTEncoding_Term.declToSmt options) theory
              in
           FStar_All.pipe_right uu____5831 (FStar_String.concat "\n")  in
         (uu____5829, FStar_Pervasives_Native.None))
       in
    match uu____5649 with
    | (r,hash) ->
        ((let uu____5865 = FStar_Options.log_queries ()  in
          if uu____5865 then query_logging.write_to_log r else ());
         (r, hash))
  
type cb = z3result -> unit
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool)
  =
  fun cache  ->
    fun qhash  ->
      fun cb  ->
        let uu____5910 =
          (FStar_Options.use_hints ()) && (FStar_Options.use_hint_hashes ())
           in
        if uu____5910
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
          | uu____5936 -> false
        else false
  
let (ask_1_core :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decls_t,Prims.bool)
         FStar_Pervasives_Native.tuple2)
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decls_t -> cb -> unit)
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun cb  ->
              let theory =
                let uu____6003 = FStar_ST.op_Bang bg_scope  in
                FStar_List.append uu____6003
                  (FStar_List.append [FStar_SMTEncoding_Term.Push]
                     (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                 in
              let uu____6029 = filter_theory theory  in
              match uu____6029 with
              | (theory1,used_unsat_core) ->
                  let uu____6039 = mk_input theory1  in
                  (match uu____6039 with
                   | (input,qhash) ->
                       (FStar_ST.op_Colon_Equals bg_scope [];
                        (let uu____6082 =
                           let uu____6084 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____6084  in
                         if uu____6082
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
            scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let theory =
                  let uu____6162 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____6198 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____6198))
                     in
                  FStar_List.flatten uu____6162  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____6227 = filter_theory theory1  in
                match uu____6227 with
                | (theory2,used_unsat_core) ->
                    let uu____6237 = mk_input theory2  in
                    (match uu____6237 with
                     | (input,qhash) ->
                         let uu____6256 =
                           let uu____6258 = cache_hit cache qhash cb  in
                           Prims.op_Negation uu____6258  in
                         if uu____6256
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
            scope_t FStar_Pervasives_Native.option -> cb -> unit)
  =
  fun r  ->
    fun filter1  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                let uu____6335 =
                  let uu____6337 = FStar_Options.n_cores ()  in
                  uu____6337 = (Prims.parse_int "1")  in
                if uu____6335
                then ask_1_core r filter1 cache label_messages qry cb
                else ask_n_cores r filter1 cache label_messages qry scope cb
  
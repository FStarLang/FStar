open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____46890 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___413_46914 =
          match uu___413_46914 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____46936 = FStar_Options.debug_any ()  in
                  if uu____46936
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
          | uu____46951::q -> aux q
          | uu____46958 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____46964 ->
        FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____46982  ->
    let run_proc_result =
      try
        (fun uu___442_46992  ->
           match () with
           | () ->
               let uu____46996 =
                 let uu____46998 = FStar_Options.z3_exe ()  in
                 FStar_Util.run_process "z3_version" uu____46998 ["-version"]
                   FStar_Pervasives_Native.None
                  in
               FStar_Pervasives_Native.Some uu____46996) ()
      with | uu___441_47007 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____47030 = parse_z3_version_lines out  in
        (match uu____47030 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : unit -> unit) =
  fun uu____47061  ->
    let uu____47062 =
      let uu____47064 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____47064  in
    if uu____47062
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____47111 = z3hash_warning_message ()  in
        match uu____47111 with
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
  fun uu____47149  ->
    check_z3hash ();
    (let uu____47151 =
       let uu____47155 =
         let uu____47159 =
           let uu____47163 =
             let uu____47165 =
               let uu____47167 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____47167  in
             FStar_Util.format1 "smt.random_seed=%s" uu____47165  in
           [uu____47163]  in
         "-in" :: uu____47159  in
       "-smt2" :: uu____47155  in
     let uu____47176 = FStar_Options.z3_cliopt ()  in
     FStar_List.append uu____47151 uu____47176)
  
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
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____47240 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____47267 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____47315 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____47363 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____47403 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let (status_tag : z3status -> Prims.string) =
  fun uu___414_47414  ->
    match uu___414_47414 with
    | SAT uu____47416 -> "sat"
    | UNSAT uu____47425 -> "unsat"
    | UNKNOWN uu____47427 -> "unknown"
    | TIMEOUT uu____47436 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status -> (Prims.string * FStar_SMTEncoding_Term.error_labels)) =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____47463 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____47473 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47473, errs)
    | UNKNOWN (errs,msg) ->
        let uu____47492 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47492, errs)
    | TIMEOUT (errs,msg) ->
        let uu____47511 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47511, errs)
  
let (tid : unit -> Prims.string) =
  fun uu____47528  ->
    let uu____47529 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____47529 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let uu____47541 = FStar_Options.z3_exe ()  in
    let uu____47543 = ini_params ()  in
    FStar_Util.start_process id1 uu____47541 uu____47543
      (fun s  -> s = "Done!")
  
let (new_z3proc_with_id : unit -> FStar_Util.proc) =
  let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
  fun uu____47563  ->
    let uu____47564 =
      let uu____47566 =
        FStar_Util.incr ctr;
        (let uu____47602 = FStar_ST.op_Bang ctr  in
         FStar_All.pipe_right uu____47602 FStar_Util.string_of_int)
         in
      FStar_Util.format1 "bg-%s" uu____47566  in
    new_z3proc uu____47564
  
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
  write_to_log: Prims.bool -> Prims.string -> Prims.string ;
  close_log: unit -> unit }
let (__proj__Mkquery_log__item__get_module_name :
  query_log -> unit -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        get_module_name
  
let (__proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        set_module_name
  
let (__proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.bool -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        write_to_log
  
let (__proj__Mkquery_log__item__close_log : query_log -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { get_module_name; set_module_name; write_to_log; close_log;_} ->
        close_log
  
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
  let get_module_name uu____48118 =
    let uu____48119 = FStar_ST.op_Bang current_module_name  in
    match uu____48119 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let next_file_name uu____48183 =
    let n1 = get_module_name ()  in
    let file_name =
      let uu____48188 =
        let uu____48197 = FStar_ST.op_Bang used_file_names  in
        FStar_List.tryFind
          (fun uu____48272  ->
             match uu____48272 with | (m,uu____48281) -> n1 = m) uu____48197
         in
      match uu____48188 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____48295 =
              let uu____48304 = FStar_ST.op_Bang used_file_names  in
              (n1, (Prims.parse_int "0")) :: uu____48304  in
            FStar_ST.op_Colon_Equals used_file_names uu____48295);
           n1)
      | FStar_Pervasives_Native.Some (uu____48436,k) ->
          ((let uu____48449 =
              let uu____48458 = FStar_ST.op_Bang used_file_names  in
              (n1, (k + (Prims.parse_int "1"))) :: uu____48458  in
            FStar_ST.op_Colon_Equals used_file_names uu____48449);
           (let uu____48590 =
              FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
            FStar_Util.format2 "%s-%s" n1 uu____48590))
       in
    FStar_Util.format1 "queries-%s.smt2" file_name  in
  let new_log_file uu____48605 =
    let file_name = next_file_name ()  in
    FStar_ST.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let fh = FStar_Util.open_file_for_writing file_name  in
     FStar_ST.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (fh, file_name));
     (fh, file_name))
     in
  let get_log_file uu____48731 =
    let uu____48732 = FStar_ST.op_Bang log_file_opt  in
    match uu____48732 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____48825 = get_log_file ()  in
    match uu____48825 with | (f,nm) -> (FStar_Util.append_to_file f str; nm)
     in
  let write_to_new_log str =
    let file_name = next_file_name ()  in
    FStar_Util.write_file file_name str; file_name  in
  let write_to_log fresh str =
    let uu____48865 =
      fresh ||
        (let uu____48868 = FStar_Options.n_cores ()  in
         uu____48868 > (Prims.parse_int "1"))
       in
    if uu____48865 then write_to_new_log str else append_to_log str  in
  let close_log uu____48880 =
    let uu____48881 = FStar_ST.op_Bang log_file_opt  in
    match uu____48881 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some (fh,uu____48950) ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____49025 =
    let uu____49026 = FStar_ST.op_Bang current_file_name  in
    match uu____49026 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log } 
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let z3proc uu____49110 =
    (let uu____49112 =
       let uu____49114 = FStar_ST.op_Bang the_z3proc  in
       uu____49114 = FStar_Pervasives_Native.None  in
     if uu____49112
     then
       let uu____49165 =
         let uu____49168 = new_z3proc_with_id ()  in
         FStar_Pervasives_Native.Some uu____49168  in
       FStar_ST.op_Colon_Equals the_z3proc uu____49165
     else ());
    (let uu____49216 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____49216)
     in
  let x = []  in
  let ask input =
    let kill_handler uu____49282 = "\nkilled\n"  in
    let uu____49284 = z3proc ()  in
    FStar_Util.ask_process uu____49284 input kill_handler  in
  let refresh uu____49290 =
    (let uu____49292 = z3proc ()  in FStar_Util.kill_process uu____49292);
    (let uu____49294 =
       let uu____49297 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____49297  in
     FStar_ST.op_Colon_Equals the_z3proc uu____49294);
    query_logging.close_log ()  in
  let restart uu____49348 =
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____49396 =
       let uu____49399 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____49399  in
     FStar_ST.op_Colon_Equals the_z3proc uu____49396)
     in
  FStar_Util.mk_ref
    {
      ask = (FStar_Util.with_monitor x ask);
      refresh = (FStar_Util.with_monitor x refresh);
      restart = (FStar_Util.with_monitor x restart)
    }
  
let (set_bg_z3_proc : bgproc -> unit) =
  fun bgp  -> FStar_ST.op_Colon_Equals bg_z3_proc bgp 
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
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Range.range -> Prims.string Prims.list -> smt_output)
  =
  fun log_file  ->
    fun r  ->
      fun lines  ->
        let rec until tag lines1 =
          match lines1 with
          | [] -> FStar_Pervasives_Native.None
          | l::lines2 ->
              if tag = l
              then FStar_Pervasives_Native.Some ([], lines2)
              else
                (let uu____49747 = until tag lines2  in
                 FStar_Util.map_opt uu____49747
                   (fun uu____49783  ->
                      match uu____49783 with
                      | (until_tag,rest) -> ((l :: until_tag), rest)))
           in
        let start_tag tag = Prims.op_Hat "<" (Prims.op_Hat tag ">")  in
        let end_tag tag = Prims.op_Hat "</" (Prims.op_Hat tag ">")  in
        let find_section tag lines1 =
          let uu____49890 = until (start_tag tag) lines1  in
          match uu____49890 with
          | FStar_Pervasives_Native.None  ->
              (FStar_Pervasives_Native.None, lines1)
          | FStar_Pervasives_Native.Some (prefix1,suffix) ->
              let uu____49960 = until (end_tag tag) suffix  in
              (match uu____49960 with
               | FStar_Pervasives_Native.None  ->
                   failwith
                     (Prims.op_Hat "Parse error: "
                        (Prims.op_Hat (end_tag tag) " not found"))
               | FStar_Pervasives_Native.Some (section,suffix1) ->
                   ((FStar_Pervasives_Native.Some section),
                     (FStar_List.append prefix1 suffix1)))
           in
        let uu____50045 = find_section "result" lines  in
        match uu____50045 with
        | (result_opt,lines1) ->
            let result = FStar_Util.must result_opt  in
            let uu____50084 = find_section "reason-unknown" lines1  in
            (match uu____50084 with
             | (reason_unknown,lines2) ->
                 let uu____50116 = find_section "unsat-core" lines2  in
                 (match uu____50116 with
                  | (unsat_core,lines3) ->
                      let uu____50148 = find_section "statistics" lines3  in
                      (match uu____50148 with
                       | (statistics,lines4) ->
                           let uu____50180 = find_section "labels" lines4  in
                           (match uu____50180 with
                            | (labels,lines5) ->
                                let remaining =
                                  let uu____50216 = until "Done!" lines5  in
                                  match uu____50216 with
                                  | FStar_Pervasives_Native.None  -> lines5
                                  | FStar_Pervasives_Native.Some
                                      (prefix1,suffix) ->
                                      FStar_List.append prefix1 suffix
                                   in
                                ((match remaining with
                                  | [] -> ()
                                  | uu____50270 ->
                                      let msg =
                                        FStar_Util.format2
                                          "%sUnexpected output from Z3: %s\n"
                                          (match log_file with
                                           | FStar_Pervasives_Native.None  ->
                                               ""
                                           | FStar_Pervasives_Native.Some f
                                               -> Prims.op_Hat f ": ")
                                          (FStar_String.concat "\n" remaining)
                                         in
                                      FStar_Errors.log_issue r
                                        (FStar_Errors.Warning_UnexpectedZ3Output,
                                          msg));
                                 (let uu____50286 =
                                    FStar_Util.must result_opt  in
                                  {
                                    smt_result = uu____50286;
                                    smt_reason_unknown = reason_unknown;
                                    smt_unsat_core = unsat_core;
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
  fun log_file  ->
    fun r  ->
      fun fresh  ->
        fun input  ->
          fun label_messages  ->
            let parse z3out =
              let lines =
                FStar_All.pipe_right (FStar_String.split [10] z3out)
                  (FStar_List.map FStar_Util.trim_string)
                 in
              let smt_output = smt_output_sections log_file r lines  in
              let unsat_core =
                match smt_output.smt_unsat_core with
                | FStar_Pervasives_Native.None  ->
                    FStar_Pervasives_Native.None
                | FStar_Pervasives_Native.Some s ->
                    let s1 =
                      FStar_Util.trim_string (FStar_String.concat " " s)  in
                    let s2 =
                      FStar_Util.substring s1 (Prims.parse_int "1")
                        ((FStar_String.length s1) - (Prims.parse_int "2"))
                       in
                    if FStar_Util.starts_with s2 "error"
                    then FStar_Pervasives_Native.None
                    else
                      (let uu____50381 =
                         FStar_All.pipe_right (FStar_Util.split s2 " ")
                           (FStar_Util.sort_with FStar_String.compare)
                          in
                       FStar_Pervasives_Native.Some uu____50381)
                 in
              let labels =
                match smt_output.smt_labels with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some lines1 ->
                    let rec lblnegs lines2 =
                      match lines2 with
                      | lname::"false"::rest when
                          FStar_Util.starts_with lname "label_" ->
                          let uu____50426 = lblnegs rest  in lname ::
                            uu____50426
                      | lname::uu____50432::rest when
                          FStar_Util.starts_with lname "label_" ->
                          lblnegs rest
                      | uu____50442 -> []  in
                    let lblnegs1 = lblnegs lines1  in
                    FStar_All.pipe_right lblnegs1
                      (FStar_List.collect
                         (fun l  ->
                            let uu____50466 =
                              FStar_All.pipe_right label_messages
                                (FStar_List.tryFind
                                   (fun uu____50506  ->
                                      match uu____50506 with
                                      | (m,uu____50516,uu____50517) ->
                                          let uu____50520 =
                                            FStar_SMTEncoding_Term.fv_name m
                                             in
                                          uu____50520 = l))
                               in
                            match uu____50466 with
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
                        FStar_Util.split (FStar_Util.trim_string line) ":"
                         in
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
                      | uu____50649 -> ()  in
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
                (let uu____50682 = FStar_Options.debug_any ()  in
                 if uu____50682
                 then
                   let uu____50685 =
                     FStar_Util.format1 "Z3 says: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   FStar_All.pipe_left FStar_Util.print_string uu____50685
                 else ());
                (match smt_output.smt_result with
                 | "unsat"::[] -> UNSAT unsat_core
                 | "sat"::[] -> SAT (labels, reason_unknown)
                 | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
                 | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
                 | "killed"::[] ->
                     ((let uu____50717 =
                         let uu____50722 = FStar_ST.op_Bang bg_z3_proc  in
                         uu____50722.restart  in
                       uu____50717 ());
                      KILLED)
                 | uu____50742 ->
                     let uu____50743 =
                       FStar_Util.format1
                         "Unexpected output from Z3: got output result: %s\n"
                         (FStar_String.concat "\n" smt_output.smt_result)
                        in
                     failwith uu____50743)
                 in
              (status, statistics)  in
            let stdout1 =
              if fresh
              then
                let proc = new_z3proc_with_id ()  in
                let kill_handler uu____50758 = "\nkilled\n"  in
                let out = FStar_Util.ask_process proc input kill_handler  in
                (FStar_Util.kill_process proc; out)
              else
                (let uu____50765 =
                   let uu____50772 = FStar_ST.op_Bang bg_z3_proc  in
                   uu____50772.ask  in
                 uu____50765 input)
               in
            parse (FStar_Util.trim_string stdout1)
  
let (z3_options : Prims.string FStar_ST.ref) =
  FStar_Util.mk_ref
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n(set-option :model true)\n(set-option :smt.case_split 3)\n(set-option :smt.relevancy 2)\n"
  
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
  z3result_query_hash: Prims.string FStar_Pervasives_Native.option ;
  z3result_log_file: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkz3result__item__z3result_status : z3result -> z3status) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_status
  
let (__proj__Mkz3result__item__z3result_time : z3result -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_time
  
let (__proj__Mkz3result__item__z3result_statistics :
  z3result -> z3statistics) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_statistics
  
let (__proj__Mkz3result__item__z3result_query_hash :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_query_hash
  
let (__proj__Mkz3result__item__z3result_log_file :
  z3result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { z3result_status; z3result_time; z3result_statistics;
        z3result_query_hash; z3result_log_file;_} -> z3result_log_file
  
type z3job = z3result job_t
let (job_queue : z3job Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (pending_jobs : Prims.int FStar_ST.ref) =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let (z3_job :
  Prims.string FStar_Pervasives_Native.option ->
    FStar_Range.range ->
      Prims.bool ->
        FStar_SMTEncoding_Term.error_labels ->
          Prims.string ->
            Prims.string FStar_Pervasives_Native.option -> unit -> z3result)
  =
  fun log_file  ->
    fun r  ->
      fun fresh  ->
        fun label_messages  ->
          fun input  ->
            fun qhash  ->
              fun uu____51132  ->
                let start = FStar_Util.now ()  in
                let uu____51142 =
                  try
                    (fun uu___811_51152  ->
                       match () with
                       | () -> doZ3Exe log_file r fresh input label_messages)
                      ()
                  with
                  | uu___810_51159 ->
                      if
                        let uu____51164 = FStar_Options.trace_error ()  in
                        Prims.op_Negation uu____51164
                      then
                        Obj.magic
                          (Obj.repr
                             ((let uu____51167 =
                                 let uu____51172 =
                                   FStar_ST.op_Bang bg_z3_proc  in
                                 uu____51172.refresh  in
                               uu____51167 ());
                              FStar_Exn.raise uu___810_51159))
                      else Obj.magic (Obj.repr (failwith "unreachable"))
                   in
                match uu____51142 with
                | (status,statistics) ->
                    let uu____51198 =
                      let uu____51204 = FStar_Util.now ()  in
                      FStar_Util.time_diff start uu____51204  in
                    (match uu____51198 with
                     | (uu____51205,elapsed_time) ->
                         {
                           z3result_status = status;
                           z3result_time = elapsed_time;
                           z3result_statistics = statistics;
                           z3result_query_hash = qhash;
                           z3result_log_file = log_file
                         })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : unit -> unit) =
  fun uu____51239  ->
    let j =
      let uu____51241 = FStar_ST.op_Bang job_queue  in
      match uu____51241 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    FStar_Util.with_monitor job_queue
      (fun uu____51309  -> FStar_Util.decr pending_jobs) ();
    dequeue ()

and (dequeue : unit -> unit) =
  fun uu____51311  ->
    let uu____51312 = FStar_ST.op_Bang running  in
    if uu____51312
    then
      let rec aux uu____51340 =
        FStar_Util.monitor_enter job_queue;
        (let uu____51346 = FStar_ST.op_Bang job_queue  in
         match uu____51346 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____51379 -> dequeue' ())
         in
      aux ()
    else ()

and (run_job : z3job -> unit) =
  fun j  ->
    let uu____51383 = j.job ()  in FStar_All.pipe_left j.callback uu____51383

let (init : unit -> unit) =
  fun uu____51389  ->
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
      (fun uu____51446  ->
         (let uu____51448 =
            let uu____51451 = FStar_ST.op_Bang job_queue  in
            FStar_List.append uu____51451 [j]  in
          FStar_ST.op_Colon_Equals job_queue uu____51448);
         FStar_Util.monitor_pulse job_queue) ()
  
let (finish : unit -> unit) =
  fun uu____51509  ->
    let rec aux uu____51515 =
      let uu____51516 =
        FStar_Util.with_monitor job_queue
          (fun uu____51534  ->
             let uu____51535 = FStar_ST.op_Bang pending_jobs  in
             let uu____51558 =
               let uu____51559 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____51559  in
             (uu____51535, uu____51558)) ()
         in
      match uu____51516 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let (fresh_scope : scope_t FStar_ST.ref) = FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____51654  -> FStar_ST.op_Bang fresh_scope 
let (flatten_fresh_scope : unit -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun uu____51681  ->
    let uu____51682 =
      let uu____51687 = FStar_ST.op_Bang fresh_scope  in
      FStar_List.rev uu____51687  in
    FStar_List.flatten uu____51682
  
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____51742  ->
         (let uu____51744 =
            let uu____51745 = FStar_ST.op_Bang fresh_scope  in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu____51745
             in
          FStar_ST.op_Colon_Equals fresh_scope uu____51744);
         (let uu____51790 =
            let uu____51793 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____51793
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____51790))
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____51853  ->
         (let uu____51855 =
            let uu____51856 = FStar_ST.op_Bang fresh_scope  in
            FStar_List.tl uu____51856  in
          FStar_ST.op_Colon_Equals fresh_scope uu____51855);
         (let uu____51901 =
            let uu____51904 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____51904
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____51901))
  
let (snapshot : Prims.string -> (Prims.int * unit)) =
  fun msg  -> FStar_Common.snapshot push fresh_scope msg 
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg  ->
    fun depth  ->
      FStar_Common.rollback (fun uu____51991  -> pop msg) fresh_scope depth
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___415_52006  ->
            match uu___415_52006 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____52009 -> ()));
    (let uu____52011 = FStar_ST.op_Bang fresh_scope  in
     match uu____52011 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____52062 -> failwith "Impossible");
    (let uu____52064 =
       let uu____52067 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____52067 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____52064)
  
let (refresh : unit -> unit) =
  fun uu____52121  ->
    (let uu____52123 =
       let uu____52125 = FStar_Options.n_cores ()  in
       uu____52125 < (Prims.parse_int "2")  in
     if uu____52123
     then
       let uu____52129 =
         let uu____52134 = FStar_ST.op_Bang bg_z3_proc  in
         uu____52134.refresh  in
       uu____52129 ()
     else ());
    (let uu____52156 = flatten_fresh_scope ()  in
     FStar_ST.op_Colon_Equals bg_scope uu____52156)
  
let (context_profile : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun theory  ->
    let uu____52192 =
      FStar_List.fold_left
        (fun uu____52225  ->
           fun d  ->
             match uu____52225 with
             | (out,_total) ->
                 (match d with
                  | FStar_SMTEncoding_Term.Module (name,decls) ->
                      let decls1 =
                        FStar_List.filter
                          (fun uu___416_52294  ->
                             match uu___416_52294 with
                             | FStar_SMTEncoding_Term.Assume uu____52296 ->
                                 true
                             | uu____52298 -> false) decls
                         in
                      let n1 = FStar_List.length decls1  in
                      (((name, n1) :: out), (n1 + _total))
                  | uu____52325 -> (out, _total)))
        ([], (Prims.parse_int "0")) theory
       in
    match uu____52192 with
    | (modules,total_decls) ->
        let modules1 =
          FStar_List.sortWith
            (fun uu____52387  ->
               fun uu____52388  ->
                 match (uu____52387, uu____52388) with
                 | ((uu____52414,n1),(uu____52416,m)) -> m - n1) modules
           in
        (if modules1 <> []
         then
           (let uu____52454 = FStar_Util.string_of_int total_decls  in
            FStar_Util.print1
              "Z3 Proof Stats: context_profile with %s assertions\n"
              uu____52454)
         else ();
         FStar_List.iter
           (fun uu____52469  ->
              match uu____52469 with
              | (m,n1) ->
                  if n1 <> (Prims.parse_int "0")
                  then
                    let uu____52485 = FStar_Util.string_of_int n1  in
                    FStar_Util.print2
                      "Z3 Proof Stats: %s produced %s SMT decls\n" m
                      uu____52485
                  else ()) modules1)
  
let (mk_input :
  Prims.bool ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (Prims.string * Prims.string FStar_Pervasives_Native.option *
        Prims.string FStar_Pervasives_Native.option))
  =
  fun fresh  ->
    fun theory  ->
      let options = FStar_ST.op_Bang z3_options  in
      (let uu____52544 = FStar_Options.print_z3_statistics ()  in
       if uu____52544 then context_profile theory else ());
      (let uu____52549 =
         let uu____52558 =
           (FStar_Options.record_hints ()) ||
             ((FStar_Options.use_hints ()) &&
                (FStar_Options.use_hint_hashes ()))
            in
         if uu____52558
         then
           let uu____52569 =
             let uu____52580 =
               FStar_All.pipe_right theory
                 (FStar_Util.prefix_until
                    (fun uu___417_52608  ->
                       match uu___417_52608 with
                       | FStar_SMTEncoding_Term.CheckSat  -> true
                       | uu____52611 -> false))
                in
             FStar_All.pipe_right uu____52580 FStar_Option.get  in
           match uu____52569 with
           | (prefix1,check_sat,suffix) ->
               let pp =
                 FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)
                  in
               let suffix1 = check_sat :: suffix  in
               let ps_lines = pp prefix1  in
               let ss_lines = pp suffix1  in
               let ps = FStar_String.concat "\n" ps_lines  in
               let ss = FStar_String.concat "\n" ss_lines  in
               let hs =
                 let uu____52694 = FStar_Options.keep_query_captions ()  in
                 if uu____52694
                 then
                   let uu____52698 =
                     FStar_All.pipe_right prefix1
                       (FStar_List.map
                          (FStar_SMTEncoding_Term.declToSmt_no_caps options))
                      in
                   FStar_All.pipe_right uu____52698
                     (FStar_String.concat "\n")
                 else ps  in
               let uu____52715 =
                 let uu____52719 = FStar_Util.digest_of_string hs  in
                 FStar_Pervasives_Native.Some uu____52719  in
               ((Prims.op_Hat ps (Prims.op_Hat "\n" ss)), uu____52715)
         else
           (let uu____52729 =
              let uu____52731 =
                FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)
                  theory
                 in
              FStar_All.pipe_right uu____52731 (FStar_String.concat "\n")  in
            (uu____52729, FStar_Pervasives_Native.None))
          in
       match uu____52549 with
       | (r,hash) ->
           let log_file_name =
             let uu____52773 = FStar_Options.log_queries ()  in
             if uu____52773
             then
               let uu____52779 = query_logging.write_to_log fresh r  in
               FStar_Pervasives_Native.Some uu____52779
             else FStar_Pervasives_Native.None  in
           (r, hash, log_file_name))
  
type cb = z3result -> unit
let (cache_hit :
  Prims.string FStar_Pervasives_Native.option ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string FStar_Pervasives_Native.option -> cb -> Prims.bool)
  =
  fun log_file  ->
    fun cache  ->
      fun qhash  ->
        fun cb  ->
          let uu____52839 =
            (FStar_Options.use_hints ()) &&
              (FStar_Options.use_hint_hashes ())
             in
          if uu____52839
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
                      z3result_query_hash = qhash;
                      z3result_log_file = log_file
                    }  in
                  cb result; true))
            | uu____52865 -> false
          else false
  
let (ask_1_core :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list -> cb -> Prims.bool -> unit)
  =
  fun r  ->
    fun filter_theory  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun cb  ->
              fun fresh  ->
                let theory =
                  if fresh
                  then flatten_fresh_scope ()
                  else
                    (let theory = FStar_ST.op_Bang bg_scope  in
                     FStar_ST.op_Colon_Equals bg_scope []; theory)
                   in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____53009 = filter_theory theory1  in
                match uu____53009 with
                | (theory2,_used_unsat_core) ->
                    let uu____53025 = mk_input fresh theory2  in
                    (match uu____53025 with
                     | (input,qhash,log_file_name) ->
                         let uu____53056 =
                           let uu____53058 =
                             fresh &&
                               (cache_hit log_file_name cache qhash cb)
                              in
                           Prims.op_Negation uu____53058  in
                         if uu____53056
                         then
                           run_job
                             {
                               job =
                                 (z3_job log_file_name r fresh label_messages
                                    input qhash);
                               callback = cb
                             }
                         else ())
  
let (ask_n_cores :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
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
                  let uu____53147 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____53183 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____53183))
                     in
                  FStar_List.flatten uu____53147  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____53212 = filter_theory theory1  in
                match uu____53212 with
                | (theory2,used_unsat_core) ->
                    let uu____53228 = mk_input true theory2  in
                    (match uu____53228 with
                     | (input,qhash,log_file_name) ->
                         let uu____53260 =
                           let uu____53262 =
                             cache_hit log_file_name cache qhash cb  in
                           Prims.op_Negation uu____53262  in
                         if uu____53260
                         then
                           enqueue
                             {
                               job =
                                 (z3_job log_file_name r true label_messages
                                    input qhash);
                               callback = cb
                             }
                         else ())
  
let (ask :
  FStar_Range.range ->
    (FStar_SMTEncoding_Term.decl Prims.list ->
       (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
      ->
      Prims.string FStar_Pervasives_Native.option ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            scope_t FStar_Pervasives_Native.option ->
              cb -> Prims.bool -> unit)
  =
  fun r  ->
    fun filter1  ->
      fun cache  ->
        fun label_messages  ->
          fun qry  ->
            fun scope  ->
              fun cb  ->
                fun fresh  ->
                  let uu____53356 =
                    let uu____53358 = FStar_Options.n_cores ()  in
                    uu____53358 = (Prims.parse_int "1")  in
                  if uu____53356
                  then ask_1_core r filter1 cache label_messages qry cb fresh
                  else
                    ask_n_cores r filter1 cache label_messages qry scope cb
  
open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____46896 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___413_46920 =
          match uu___413_46920 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____46942 = FStar_Options.debug_any ()  in
                  if uu____46942
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
          | uu____46957::q -> aux q
          | uu____46964 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____46970 ->
        FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____46988  ->
    let run_proc_result =
      try
        (fun uu___442_46998  ->
           match () with
           | () ->
               let uu____47002 =
                 let uu____47004 = FStar_Options.z3_exe ()  in
                 FStar_Util.run_process "z3_version" uu____47004 ["-version"]
                   FStar_Pervasives_Native.None
                  in
               FStar_Pervasives_Native.Some uu____47002) ()
      with | uu___441_47013 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____47036 = parse_z3_version_lines out  in
        (match uu____47036 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : unit -> unit) =
  fun uu____47067  ->
    let uu____47068 =
      let uu____47070 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____47070  in
    if uu____47068
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____47117 = z3hash_warning_message ()  in
        match uu____47117 with
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
  fun uu____47155  ->
    check_z3hash ();
    (let uu____47157 =
       let uu____47161 =
         let uu____47165 =
           let uu____47169 =
             let uu____47171 =
               let uu____47173 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____47173  in
             FStar_Util.format1 "smt.random_seed=%s" uu____47171  in
           [uu____47169]  in
         "-in" :: uu____47165  in
       "-smt2" :: uu____47161  in
     let uu____47182 = FStar_Options.z3_cliopt ()  in
     FStar_List.append uu____47157 uu____47182)
  
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
    match projectee with | UNSAT _0 -> true | uu____47246 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____47273 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____47321 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____47369 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____47409 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let (status_tag : z3status -> Prims.string) =
  fun uu___414_47420  ->
    match uu___414_47420 with
    | SAT uu____47422 -> "sat"
    | UNSAT uu____47431 -> "unsat"
    | UNKNOWN uu____47433 -> "unknown"
    | TIMEOUT uu____47442 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status -> (Prims.string * FStar_SMTEncoding_Term.error_labels)) =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____47469 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____47479 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47479, errs)
    | UNKNOWN (errs,msg) ->
        let uu____47498 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47498, errs)
    | TIMEOUT (errs,msg) ->
        let uu____47517 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.op_Hat " because " msg1)
           in
        (uu____47517, errs)
  
let (tid : unit -> Prims.string) =
  fun uu____47534  ->
    let uu____47535 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____47535 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let uu____47547 = FStar_Options.z3_exe ()  in
    let uu____47549 = ini_params ()  in
    FStar_Util.start_process id1 uu____47547 uu____47549
      (fun s  -> s = "Done!")
  
let (new_z3proc_with_id : unit -> FStar_Util.proc) =
  let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
  fun uu____47569  ->
    let uu____47570 =
      let uu____47572 =
        FStar_Util.incr ctr;
        (let uu____47608 = FStar_ST.op_Bang ctr  in
         FStar_All.pipe_right uu____47608 FStar_Util.string_of_int)
         in
      FStar_Util.format1 "bg-%s" uu____47572  in
    new_z3proc uu____47570
  
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
  let get_module_name uu____48124 =
    let uu____48125 = FStar_ST.op_Bang current_module_name  in
    match uu____48125 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let next_file_name uu____48189 =
    let n1 = get_module_name ()  in
    let file_name =
      let uu____48194 =
        let uu____48203 = FStar_ST.op_Bang used_file_names  in
        FStar_List.tryFind
          (fun uu____48278  ->
             match uu____48278 with | (m,uu____48287) -> n1 = m) uu____48203
         in
      match uu____48194 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____48301 =
              let uu____48310 = FStar_ST.op_Bang used_file_names  in
              (n1, (Prims.parse_int "0")) :: uu____48310  in
            FStar_ST.op_Colon_Equals used_file_names uu____48301);
           n1)
      | FStar_Pervasives_Native.Some (uu____48442,k) ->
          ((let uu____48455 =
              let uu____48464 = FStar_ST.op_Bang used_file_names  in
              (n1, (k + (Prims.parse_int "1"))) :: uu____48464  in
            FStar_ST.op_Colon_Equals used_file_names uu____48455);
           (let uu____48596 =
              FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
            FStar_Util.format2 "%s-%s" n1 uu____48596))
       in
    FStar_Util.format1 "queries-%s.smt2" file_name  in
  let new_log_file uu____48611 =
    let file_name = next_file_name ()  in
    FStar_ST.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let fh = FStar_Util.open_file_for_writing file_name  in
     FStar_ST.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (fh, file_name));
     (fh, file_name))
     in
  let get_log_file uu____48737 =
    let uu____48738 = FStar_ST.op_Bang log_file_opt  in
    match uu____48738 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____48831 = get_log_file ()  in
    match uu____48831 with | (f,nm) -> (FStar_Util.append_to_file f str; nm)
     in
  let write_to_new_log str =
    let file_name = next_file_name ()  in
    FStar_Util.write_file file_name str; file_name  in
  let write_to_log fresh str =
    let uu____48871 =
      fresh ||
        (let uu____48874 = FStar_Options.n_cores ()  in
         uu____48874 > (Prims.parse_int "1"))
       in
    if uu____48871 then write_to_new_log str else append_to_log str  in
  let close_log uu____48886 =
    let uu____48887 = FStar_ST.op_Bang log_file_opt  in
    match uu____48887 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some (fh,uu____48956) ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____49031 =
    let uu____49032 = FStar_ST.op_Bang current_file_name  in
    match uu____49032 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log } 
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let z3proc uu____49116 =
    (let uu____49118 =
       let uu____49120 = FStar_ST.op_Bang the_z3proc  in
       uu____49120 = FStar_Pervasives_Native.None  in
     if uu____49118
     then
       let uu____49171 =
         let uu____49174 = new_z3proc_with_id ()  in
         FStar_Pervasives_Native.Some uu____49174  in
       FStar_ST.op_Colon_Equals the_z3proc uu____49171
     else ());
    (let uu____49222 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____49222)
     in
  let x = []  in
  let ask input =
    let kill_handler uu____49288 = "\nkilled\n"  in
    let uu____49290 = z3proc ()  in
    FStar_Util.ask_process uu____49290 input kill_handler  in
  let refresh uu____49296 =
    (let uu____49298 = z3proc ()  in FStar_Util.kill_process uu____49298);
    (let uu____49300 =
       let uu____49303 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____49303  in
     FStar_ST.op_Colon_Equals the_z3proc uu____49300);
    query_logging.close_log ()  in
  let restart uu____49354 =
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____49402 =
       let uu____49405 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____49405  in
     FStar_ST.op_Colon_Equals the_z3proc uu____49402)
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
                (let uu____49753 = until tag lines2  in
                 FStar_Util.map_opt uu____49753
                   (fun uu____49789  ->
                      match uu____49789 with
                      | (until_tag,rest) -> ((l :: until_tag), rest)))
           in
        let start_tag tag = Prims.op_Hat "<" (Prims.op_Hat tag ">")  in
        let end_tag tag = Prims.op_Hat "</" (Prims.op_Hat tag ">")  in
        let find_section tag lines1 =
          let uu____49896 = until (start_tag tag) lines1  in
          match uu____49896 with
          | FStar_Pervasives_Native.None  ->
              (FStar_Pervasives_Native.None, lines1)
          | FStar_Pervasives_Native.Some (prefix1,suffix) ->
              let uu____49966 = until (end_tag tag) suffix  in
              (match uu____49966 with
               | FStar_Pervasives_Native.None  ->
                   failwith
                     (Prims.op_Hat "Parse error: "
                        (Prims.op_Hat (end_tag tag) " not found"))
               | FStar_Pervasives_Native.Some (section,suffix1) ->
                   ((FStar_Pervasives_Native.Some section),
                     (FStar_List.append prefix1 suffix1)))
           in
        let uu____50051 = find_section "result" lines  in
        match uu____50051 with
        | (result_opt,lines1) ->
            let result = FStar_Util.must result_opt  in
            let uu____50090 = find_section "reason-unknown" lines1  in
            (match uu____50090 with
             | (reason_unknown,lines2) ->
                 let uu____50122 = find_section "unsat-core" lines2  in
                 (match uu____50122 with
                  | (unsat_core,lines3) ->
                      let uu____50154 = find_section "statistics" lines3  in
                      (match uu____50154 with
                       | (statistics,lines4) ->
                           let uu____50186 = find_section "labels" lines4  in
                           (match uu____50186 with
                            | (labels,lines5) ->
                                let remaining =
                                  let uu____50222 = until "Done!" lines5  in
                                  match uu____50222 with
                                  | FStar_Pervasives_Native.None  -> lines5
                                  | FStar_Pervasives_Native.Some
                                      (prefix1,suffix) ->
                                      FStar_List.append prefix1 suffix
                                   in
                                ((match remaining with
                                  | [] -> ()
                                  | uu____50276 ->
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
                                 (let uu____50292 =
                                    FStar_Util.must result_opt  in
                                  {
                                    smt_result = uu____50292;
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
                      (let uu____50387 =
                         FStar_All.pipe_right (FStar_Util.split s2 " ")
                           (FStar_Util.sort_with FStar_String.compare)
                          in
                       FStar_Pervasives_Native.Some uu____50387)
                 in
              let labels =
                match smt_output.smt_labels with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some lines1 ->
                    let rec lblnegs lines2 =
                      match lines2 with
                      | lname::"false"::rest when
                          FStar_Util.starts_with lname "label_" ->
                          let uu____50432 = lblnegs rest  in lname ::
                            uu____50432
                      | lname::uu____50438::rest when
                          FStar_Util.starts_with lname "label_" ->
                          lblnegs rest
                      | uu____50448 -> []  in
                    let lblnegs1 = lblnegs lines1  in
                    FStar_All.pipe_right lblnegs1
                      (FStar_List.collect
                         (fun l  ->
                            let uu____50472 =
                              FStar_All.pipe_right label_messages
                                (FStar_List.tryFind
                                   (fun uu____50512  ->
                                      match uu____50512 with
                                      | (m,uu____50522,uu____50523) ->
                                          let uu____50526 =
                                            FStar_SMTEncoding_Term.fv_name m
                                             in
                                          uu____50526 = l))
                               in
                            match uu____50472 with
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
                      | uu____50655 -> ()  in
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
                (let uu____50688 = FStar_Options.debug_any ()  in
                 if uu____50688
                 then
                   let uu____50691 =
                     FStar_Util.format1 "Z3 says: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   FStar_All.pipe_left FStar_Util.print_string uu____50691
                 else ());
                (match smt_output.smt_result with
                 | "unsat"::[] -> UNSAT unsat_core
                 | "sat"::[] -> SAT (labels, reason_unknown)
                 | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
                 | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
                 | "killed"::[] ->
                     ((let uu____50723 =
                         let uu____50728 = FStar_ST.op_Bang bg_z3_proc  in
                         uu____50728.restart  in
                       uu____50723 ());
                      KILLED)
                 | uu____50748 ->
                     let uu____50749 =
                       FStar_Util.format1
                         "Unexpected output from Z3: got output result: %s\n"
                         (FStar_String.concat "\n" smt_output.smt_result)
                        in
                     failwith uu____50749)
                 in
              (status, statistics)  in
            let stdout1 =
              if fresh
              then
                let proc = new_z3proc_with_id ()  in
                let kill_handler uu____50764 = "\nkilled\n"  in
                let out = FStar_Util.ask_process proc input kill_handler  in
                (FStar_Util.kill_process proc; out)
              else
                (let uu____50771 =
                   let uu____50778 = FStar_ST.op_Bang bg_z3_proc  in
                   uu____50778.ask  in
                 uu____50771 input)
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
              fun uu____51138  ->
                let start = FStar_Util.now ()  in
                let uu____51148 =
                  try
                    (fun uu___811_51158  ->
                       match () with
                       | () -> doZ3Exe log_file r fresh input label_messages)
                      ()
                  with
                  | uu___810_51165 ->
                      if
                        let uu____51170 = FStar_Options.trace_error ()  in
                        Prims.op_Negation uu____51170
                      then
                        Obj.magic
                          (Obj.repr
                             ((let uu____51173 =
                                 let uu____51178 =
                                   FStar_ST.op_Bang bg_z3_proc  in
                                 uu____51178.refresh  in
                               uu____51173 ());
                              FStar_Exn.raise uu___810_51165))
                      else Obj.magic (Obj.repr (failwith "unreachable"))
                   in
                match uu____51148 with
                | (status,statistics) ->
                    let uu____51204 =
                      let uu____51210 = FStar_Util.now ()  in
                      FStar_Util.time_diff start uu____51210  in
                    (match uu____51204 with
                     | (uu____51211,elapsed_time) ->
                         {
                           z3result_status = status;
                           z3result_time = elapsed_time;
                           z3result_statistics = statistics;
                           z3result_query_hash = qhash;
                           z3result_log_file = log_file
                         })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : unit -> unit) =
  fun uu____51245  ->
    let j =
      let uu____51247 = FStar_ST.op_Bang job_queue  in
      match uu____51247 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    FStar_Util.with_monitor job_queue
      (fun uu____51315  -> FStar_Util.decr pending_jobs) ();
    dequeue ()

and (dequeue : unit -> unit) =
  fun uu____51317  ->
    let uu____51318 = FStar_ST.op_Bang running  in
    if uu____51318
    then
      let rec aux uu____51346 =
        FStar_Util.monitor_enter job_queue;
        (let uu____51352 = FStar_ST.op_Bang job_queue  in
         match uu____51352 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____51385 -> dequeue' ())
         in
      aux ()
    else ()

and (run_job : z3job -> unit) =
  fun j  ->
    let uu____51389 = j.job ()  in FStar_All.pipe_left j.callback uu____51389

let (init : unit -> unit) =
  fun uu____51395  ->
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
      (fun uu____51452  ->
         (let uu____51454 =
            let uu____51457 = FStar_ST.op_Bang job_queue  in
            FStar_List.append uu____51457 [j]  in
          FStar_ST.op_Colon_Equals job_queue uu____51454);
         FStar_Util.monitor_pulse job_queue) ()
  
let (finish : unit -> unit) =
  fun uu____51515  ->
    let rec aux uu____51521 =
      let uu____51522 =
        FStar_Util.with_monitor job_queue
          (fun uu____51540  ->
             let uu____51541 = FStar_ST.op_Bang pending_jobs  in
             let uu____51564 =
               let uu____51565 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____51565  in
             (uu____51541, uu____51564)) ()
         in
      match uu____51522 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let (fresh_scope : scope_t FStar_ST.ref) = FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____51660  -> FStar_ST.op_Bang fresh_scope 
let (flatten_fresh_scope : unit -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun uu____51687  ->
    let uu____51688 =
      let uu____51693 = FStar_ST.op_Bang fresh_scope  in
      FStar_List.rev uu____51693  in
    FStar_List.flatten uu____51688
  
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____51748  ->
         (let uu____51750 =
            let uu____51751 = FStar_ST.op_Bang fresh_scope  in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu____51751
             in
          FStar_ST.op_Colon_Equals fresh_scope uu____51750);
         (let uu____51796 =
            let uu____51799 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____51799
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____51796))
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____51859  ->
         (let uu____51861 =
            let uu____51862 = FStar_ST.op_Bang fresh_scope  in
            FStar_List.tl uu____51862  in
          FStar_ST.op_Colon_Equals fresh_scope uu____51861);
         (let uu____51907 =
            let uu____51910 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____51910
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____51907))
  
let (snapshot : Prims.string -> (Prims.int * unit)) =
  fun msg  -> FStar_Common.snapshot push fresh_scope msg 
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg  ->
    fun depth  ->
      FStar_Common.rollback (fun uu____51997  -> pop msg) fresh_scope depth
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___415_52012  ->
            match uu___415_52012 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____52015 -> ()));
    (let uu____52017 = FStar_ST.op_Bang fresh_scope  in
     match uu____52017 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____52068 -> failwith "Impossible");
    (let uu____52070 =
       let uu____52073 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____52073 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____52070)
  
let (refresh : unit -> unit) =
  fun uu____52127  ->
    (let uu____52129 =
       let uu____52131 = FStar_Options.n_cores ()  in
       uu____52131 < (Prims.parse_int "2")  in
     if uu____52129
     then
       let uu____52135 =
         let uu____52140 = FStar_ST.op_Bang bg_z3_proc  in
         uu____52140.refresh  in
       uu____52135 ()
     else ());
    (let uu____52162 = flatten_fresh_scope ()  in
     FStar_ST.op_Colon_Equals bg_scope uu____52162)
  
let (context_profile : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun theory  ->
    let uu____52198 =
      FStar_List.fold_left
        (fun uu____52231  ->
           fun d  ->
             match uu____52231 with
             | (out,_total) ->
                 (match d with
                  | FStar_SMTEncoding_Term.Module (name,decls) ->
                      let decls1 =
                        FStar_List.filter
                          (fun uu___416_52300  ->
                             match uu___416_52300 with
                             | FStar_SMTEncoding_Term.Assume uu____52302 ->
                                 true
                             | uu____52304 -> false) decls
                         in
                      let n1 = FStar_List.length decls1  in
                      (((name, n1) :: out), (n1 + _total))
                  | uu____52331 -> (out, _total)))
        ([], (Prims.parse_int "0")) theory
       in
    match uu____52198 with
    | (modules,total_decls) ->
        let modules1 =
          FStar_List.sortWith
            (fun uu____52393  ->
               fun uu____52394  ->
                 match (uu____52393, uu____52394) with
                 | ((uu____52420,n1),(uu____52422,m)) -> m - n1) modules
           in
        (if modules1 <> []
         then
           (let uu____52460 = FStar_Util.string_of_int total_decls  in
            FStar_Util.print1
              "Z3 Proof Stats: context_profile with %s assertions\n"
              uu____52460)
         else ();
         FStar_List.iter
           (fun uu____52475  ->
              match uu____52475 with
              | (m,n1) ->
                  if n1 <> (Prims.parse_int "0")
                  then
                    let uu____52491 = FStar_Util.string_of_int n1  in
                    FStar_Util.print2
                      "Z3 Proof Stats: %s produced %s SMT decls\n" m
                      uu____52491
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
      (let uu____52550 = FStar_Options.print_z3_statistics ()  in
       if uu____52550 then context_profile theory else ());
      (let uu____52555 =
         let uu____52564 =
           (FStar_Options.record_hints ()) ||
             ((FStar_Options.use_hints ()) &&
                (FStar_Options.use_hint_hashes ()))
            in
         if uu____52564
         then
           let uu____52575 =
             let uu____52586 =
               FStar_All.pipe_right theory
                 (FStar_Util.prefix_until
                    (fun uu___417_52614  ->
                       match uu___417_52614 with
                       | FStar_SMTEncoding_Term.CheckSat  -> true
                       | uu____52617 -> false))
                in
             FStar_All.pipe_right uu____52586 FStar_Option.get  in
           match uu____52575 with
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
                 let uu____52700 = FStar_Options.keep_query_captions ()  in
                 if uu____52700
                 then
                   let uu____52704 =
                     FStar_All.pipe_right prefix1
                       (FStar_List.map
                          (FStar_SMTEncoding_Term.declToSmt_no_caps options))
                      in
                   FStar_All.pipe_right uu____52704
                     (FStar_String.concat "\n")
                 else ps  in
               let uu____52721 =
                 let uu____52725 = FStar_Util.digest_of_string hs  in
                 FStar_Pervasives_Native.Some uu____52725  in
               ((Prims.op_Hat ps (Prims.op_Hat "\n" ss)), uu____52721)
         else
           (let uu____52735 =
              let uu____52737 =
                FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)
                  theory
                 in
              FStar_All.pipe_right uu____52737 (FStar_String.concat "\n")  in
            (uu____52735, FStar_Pervasives_Native.None))
          in
       match uu____52555 with
       | (r,hash) ->
           let log_file_name =
             let uu____52779 = FStar_Options.log_queries ()  in
             if uu____52779
             then
               let uu____52785 = query_logging.write_to_log fresh r  in
               FStar_Pervasives_Native.Some uu____52785
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
          let uu____52845 =
            (FStar_Options.use_hints ()) &&
              (FStar_Options.use_hint_hashes ())
             in
          if uu____52845
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
            | uu____52871 -> false
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
                let uu____53015 = filter_theory theory1  in
                match uu____53015 with
                | (theory2,_used_unsat_core) ->
                    let uu____53031 = mk_input fresh theory2  in
                    (match uu____53031 with
                     | (input,qhash,log_file_name) ->
                         let uu____53062 =
                           let uu____53064 =
                             fresh &&
                               (cache_hit log_file_name cache qhash cb)
                              in
                           Prims.op_Negation uu____53064  in
                         if uu____53062
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
                  let uu____53153 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____53189 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____53189))
                     in
                  FStar_List.flatten uu____53153  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____53218 = filter_theory theory1  in
                match uu____53218 with
                | (theory2,used_unsat_core) ->
                    let uu____53234 = mk_input true theory2  in
                    (match uu____53234 with
                     | (input,qhash,log_file_name) ->
                         let uu____53266 =
                           let uu____53268 =
                             cache_hit log_file_name cache qhash cb  in
                           Prims.op_Negation uu____53268  in
                         if uu____53266
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
                  let uu____53362 =
                    let uu____53364 = FStar_Options.n_cores ()  in
                    uu____53364 = (Prims.parse_int "1")  in
                  if uu____53362
                  then ask_1_core r filter1 cache label_messages qry cb fresh
                  else
                    ask_n_cores r filter1 cache label_messages qry scope cb
  
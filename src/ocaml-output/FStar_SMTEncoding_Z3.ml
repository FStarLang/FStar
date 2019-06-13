open Prims
let (_z3hash_checked : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (_z3hash_expected : Prims.string) = "1f29cebd4df6" 
let (_z3url : Prims.string) =
  "https://github.com/FStarLang/binaries/tree/master/z3-tested" 
let (parse_z3_version_lines :
  Prims.string -> Prims.string FStar_Pervasives_Native.option) =
  fun out  ->
    match FStar_Util.splitlines out with
    | x::uu____46 ->
        let trimmed = FStar_Util.trim_string x  in
        let parts = FStar_Util.split trimmed " "  in
        let rec aux uu___0_70 =
          match uu___0_70 with
          | hash::[] ->
              let n1 =
                Prims.min (FStar_String.strlen _z3hash_expected)
                  (FStar_String.strlen hash)
                 in
              let hash_prefix =
                FStar_String.substring hash (Prims.parse_int "0") n1  in
              if hash_prefix = _z3hash_expected
              then
                ((let uu____92 = FStar_Options.debug_any ()  in
                  if uu____92
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
          | uu____107::q -> aux q
          | uu____114 ->
              FStar_Pervasives_Native.Some "No Z3 commit hash found"
           in
        aux parts
    | uu____120 -> FStar_Pervasives_Native.Some "No Z3 version string found"
  
let (z3hash_warning_message :
  unit ->
    (FStar_Errors.raw_error * Prims.string) FStar_Pervasives_Native.option)
  =
  fun uu____138  ->
    let run_proc_result =
      try
        (fun uu___29_148  ->
           match () with
           | () ->
               let uu____152 =
                 let uu____154 = FStar_Options.z3_exe ()  in
                 FStar_Util.run_process "z3_version" uu____154 ["-version"]
                   FStar_Pervasives_Native.None
                  in
               FStar_Pervasives_Native.Some uu____152) ()
      with | uu___28_163 -> FStar_Pervasives_Native.None  in
    match run_proc_result with
    | FStar_Pervasives_Native.None  ->
        FStar_Pervasives_Native.Some
          (FStar_Errors.Error_Z3InvocationError, "Could not run Z3")
    | FStar_Pervasives_Native.Some out ->
        let uu____186 = parse_z3_version_lines out  in
        (match uu____186 with
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some msg ->
             FStar_Pervasives_Native.Some
               (FStar_Errors.Warning_Z3InvocationWarning, msg))
  
let (check_z3hash : unit -> unit) =
  fun uu____217  ->
    let uu____218 =
      let uu____220 = FStar_ST.op_Bang _z3hash_checked  in
      Prims.op_Negation uu____220  in
    if uu____218
    then
      (FStar_ST.op_Colon_Equals _z3hash_checked true;
       (let uu____267 = z3hash_warning_message ()  in
        match uu____267 with
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
  fun uu____305  ->
    check_z3hash ();
    (let uu____307 =
       let uu____311 =
         let uu____315 =
           let uu____319 =
             let uu____321 =
               let uu____323 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____323  in
             FStar_Util.format1 "smt.random_seed=%s" uu____321  in
           [uu____319]  in
         "-in" :: uu____315  in
       "-smt2" :: uu____311  in
     let uu____332 = FStar_Options.z3_cliopt ()  in
     FStar_List.append uu____307 uu____332)
  
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
    match projectee with | UNSAT _0 -> true | uu____395 -> false
  
let (__proj__UNSAT__item___0 : z3status -> unsat_core) =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let (uu___is_SAT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____421 -> false
  
let (__proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let (uu___is_UNKNOWN : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____468 -> false
  
let (__proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let (uu___is_TIMEOUT : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____515 -> false
  
let (__proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels * Prims.string
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let (uu___is_KILLED : z3status -> Prims.bool) =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____554 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let (status_tag : z3status -> Prims.string) =
  fun uu___1_565  ->
    match uu___1_565 with
    | SAT uu____567 -> "sat"
    | UNSAT uu____576 -> "unsat"
    | UNKNOWN uu____578 -> "unknown"
    | TIMEOUT uu____587 -> "timeout"
    | KILLED  -> "killed"
  
let (status_string_and_errors :
  z3status -> (Prims.string * FStar_SMTEncoding_Term.error_labels)) =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____614 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        (((match msg with
           | FStar_Pervasives_Native.None  -> "unknown"
           | FStar_Pervasives_Native.Some msg1 -> msg1)), errs)
    | UNKNOWN (errs,msg) ->
        (((match msg with
           | FStar_Pervasives_Native.None  -> "unknown"
           | FStar_Pervasives_Native.Some msg1 -> msg1)), errs)
    | TIMEOUT (errs,msg) ->
        (((match msg with
           | FStar_Pervasives_Native.None  -> "unknown"
           | FStar_Pervasives_Native.Some msg1 -> msg1)), errs)
  
let (tid : unit -> Prims.string) =
  fun uu____667  ->
    let uu____668 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____668 FStar_Util.string_of_int
  
let (new_z3proc : Prims.string -> FStar_Util.proc) =
  fun id1  ->
    let uu____680 = FStar_Options.z3_exe ()  in
    let uu____682 = ini_params ()  in
    FStar_Util.start_process id1 uu____680 uu____682 (fun s  -> s = "Done!")
  
let (new_z3proc_with_id : unit -> FStar_Util.proc) =
  let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
  fun uu____702  ->
    let uu____703 =
      let uu____705 =
        FStar_Util.incr ctr;
        (let uu____708 = FStar_ST.op_Bang ctr  in
         FStar_All.pipe_right uu____708 FStar_Util.string_of_int)
         in
      FStar_Util.format1 "bg-%s" uu____705  in
    new_z3proc uu____703
  
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
  let get_module_name uu____1180 =
    let uu____1181 = FStar_ST.op_Bang current_module_name  in
    match uu____1181 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let next_file_name uu____1223 =
    let n1 = get_module_name ()  in
    let file_name =
      let uu____1228 =
        let uu____1237 = FStar_ST.op_Bang used_file_names  in
        FStar_List.tryFind
          (fun uu____1290  ->
             match uu____1290 with | (m,uu____1299) -> n1 = m) uu____1237
         in
      match uu____1228 with
      | FStar_Pervasives_Native.None  ->
          ((let uu____1313 =
              let uu____1322 = FStar_ST.op_Bang used_file_names  in
              (n1, (Prims.parse_int "0")) :: uu____1322  in
            FStar_ST.op_Colon_Equals used_file_names uu____1313);
           n1)
      | FStar_Pervasives_Native.Some (uu____1410,k) ->
          ((let uu____1423 =
              let uu____1432 = FStar_ST.op_Bang used_file_names  in
              (n1, (k + (Prims.parse_int "1"))) :: uu____1432  in
            FStar_ST.op_Colon_Equals used_file_names uu____1423);
           (let uu____1520 =
              FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
            FStar_Util.format2 "%s-%s" n1 uu____1520))
       in
    FStar_Util.format1 "queries-%s.smt2" file_name  in
  let new_log_file uu____1535 =
    let file_name = next_file_name ()  in
    FStar_ST.op_Colon_Equals current_file_name
      (FStar_Pervasives_Native.Some file_name);
    (let fh = FStar_Util.open_file_for_writing file_name  in
     FStar_ST.op_Colon_Equals log_file_opt
       (FStar_Pervasives_Native.Some (fh, file_name));
     (fh, file_name))
     in
  let get_log_file uu____1617 =
    let uu____1618 = FStar_ST.op_Bang log_file_opt  in
    match uu____1618 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1689 = get_log_file ()  in
    match uu____1689 with | (f,nm) -> (FStar_Util.append_to_file f str; nm)
     in
  let write_to_new_log str =
    let file_name = next_file_name ()  in
    FStar_Util.write_file file_name str; file_name  in
  let write_to_log fresh str =
    let uu____1729 =
      fresh ||
        (let uu____1732 = FStar_Options.n_cores ()  in
         uu____1732 > (Prims.parse_int "1"))
       in
    if uu____1729 then write_to_new_log str else append_to_log str  in
  let close_log uu____1744 =
    let uu____1745 = FStar_ST.op_Bang log_file_opt  in
    match uu____1745 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some (fh,uu____1792) ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____1845 =
    let uu____1846 = FStar_ST.op_Bang current_file_name  in
    match uu____1846 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log } 
let (bg_z3_proc : bgproc FStar_ST.ref) =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let z3proc uu____1897 =
    (let uu____1899 =
       let uu____1901 = FStar_ST.op_Bang the_z3proc  in
       uu____1901 = FStar_Pervasives_Native.None  in
     if uu____1899
     then
       let uu____1930 =
         let uu____1933 = new_z3proc_with_id ()  in
         FStar_Pervasives_Native.Some uu____1933  in
       FStar_ST.op_Colon_Equals the_z3proc uu____1930
     else ());
    (let uu____1959 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____1959)
     in
  let x = []  in
  let ask input =
    let kill_handler uu____2003 = "\nkilled\n"  in
    let uu____2005 = z3proc ()  in
    FStar_Util.ask_process uu____2005 input kill_handler  in
  let refresh uu____2011 =
    (let uu____2013 = z3proc ()  in FStar_Util.kill_process uu____2013);
    (let uu____2015 =
       let uu____2018 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____2018  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2015);
    query_logging.close_log ()  in
  let restart uu____2047 =
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2073 =
       let uu____2076 = new_z3proc_with_id ()  in
       FStar_Pervasives_Native.Some uu____2076  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2073)
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
                (let uu____2402 = until tag lines2  in
                 FStar_Util.map_opt uu____2402
                   (fun uu____2438  ->
                      match uu____2438 with
                      | (until_tag,rest) -> ((l :: until_tag), rest)))
           in
        let start_tag tag = Prims.op_Hat "<" (Prims.op_Hat tag ">")  in
        let end_tag tag = Prims.op_Hat "</" (Prims.op_Hat tag ">")  in
        let find_section tag lines1 =
          let uu____2545 = until (start_tag tag) lines1  in
          match uu____2545 with
          | FStar_Pervasives_Native.None  ->
              (FStar_Pervasives_Native.None, lines1)
          | FStar_Pervasives_Native.Some (prefix1,suffix) ->
              let uu____2615 = until (end_tag tag) suffix  in
              (match uu____2615 with
               | FStar_Pervasives_Native.None  ->
                   failwith
                     (Prims.op_Hat "Parse error: "
                        (Prims.op_Hat (end_tag tag) " not found"))
               | FStar_Pervasives_Native.Some (section,suffix1) ->
                   ((FStar_Pervasives_Native.Some section),
                     (FStar_List.append prefix1 suffix1)))
           in
        let uu____2700 = find_section "result" lines  in
        match uu____2700 with
        | (result_opt,lines1) ->
            let result = FStar_Util.must result_opt  in
            let uu____2739 = find_section "reason-unknown" lines1  in
            (match uu____2739 with
             | (reason_unknown,lines2) ->
                 let uu____2771 = find_section "unsat-core" lines2  in
                 (match uu____2771 with
                  | (unsat_core,lines3) ->
                      let uu____2803 = find_section "statistics" lines3  in
                      (match uu____2803 with
                       | (statistics,lines4) ->
                           let uu____2835 = find_section "labels" lines4  in
                           (match uu____2835 with
                            | (labels,lines5) ->
                                let remaining =
                                  let uu____2871 = until "Done!" lines5  in
                                  match uu____2871 with
                                  | FStar_Pervasives_Native.None  -> lines5
                                  | FStar_Pervasives_Native.Some
                                      (prefix1,suffix) ->
                                      FStar_List.append prefix1 suffix
                                   in
                                ((match remaining with
                                  | [] -> ()
                                  | uu____2925 ->
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
                                 (let uu____2941 = FStar_Util.must result_opt
                                     in
                                  {
                                    smt_result = uu____2941;
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
                      (let uu____3036 =
                         FStar_All.pipe_right (FStar_Util.split s2 " ")
                           (FStar_Util.sort_with FStar_String.compare)
                          in
                       FStar_Pervasives_Native.Some uu____3036)
                 in
              let labels =
                match smt_output.smt_labels with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some lines1 ->
                    let rec lblnegs lines2 =
                      match lines2 with
                      | lname::"false"::rest when
                          FStar_Util.starts_with lname "label_" ->
                          let uu____3081 = lblnegs rest  in lname ::
                            uu____3081
                      | lname::uu____3087::rest when
                          FStar_Util.starts_with lname "label_" ->
                          lblnegs rest
                      | uu____3097 -> []  in
                    let lblnegs1 = lblnegs lines1  in
                    FStar_All.pipe_right lblnegs1
                      (FStar_List.collect
                         (fun l  ->
                            let uu____3121 =
                              FStar_All.pipe_right label_messages
                                (FStar_List.tryFind
                                   (fun uu____3161  ->
                                      match uu____3161 with
                                      | (m,uu____3171,uu____3172) ->
                                          let uu____3175 =
                                            FStar_SMTEncoding_Term.fv_name m
                                             in
                                          uu____3175 = l))
                               in
                            match uu____3121 with
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
                      | uu____3304 -> ()  in
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
                (let uu____3337 = FStar_Options.debug_any ()  in
                 if uu____3337
                 then
                   let uu____3340 =
                     FStar_Util.format1 "Z3 says: %s\n"
                       (FStar_String.concat "\n" smt_output.smt_result)
                      in
                   FStar_All.pipe_left FStar_Util.print_string uu____3340
                 else ());
                (match smt_output.smt_result with
                 | "unsat"::[] -> UNSAT unsat_core
                 | "sat"::[] -> SAT (labels, reason_unknown)
                 | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
                 | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
                 | "killed"::[] ->
                     ((let uu____3372 =
                         let uu____3377 = FStar_ST.op_Bang bg_z3_proc  in
                         uu____3377.restart  in
                       uu____3372 ());
                      KILLED)
                 | uu____3397 ->
                     let uu____3398 =
                       FStar_Util.format1
                         "Unexpected output from Z3: got output result: %s\n"
                         (FStar_String.concat "\n" smt_output.smt_result)
                        in
                     failwith uu____3398)
                 in
              (status, statistics)  in
            let stdout1 =
              if fresh
              then
                let proc = new_z3proc_with_id ()  in
                let kill_handler uu____3413 = "\nkilled\n"  in
                let out = FStar_Util.ask_process proc input kill_handler  in
                (FStar_Util.kill_process proc; out)
              else
                (let uu____3420 =
                   let uu____3427 = FStar_ST.op_Bang bg_z3_proc  in
                   uu____3427.ask  in
                 uu____3420 input)
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
              fun uu____3754  ->
                let start = FStar_Util.now ()  in
                let uu____3764 =
                  try
                    (fun uu___398_3774  ->
                       match () with
                       | () -> doZ3Exe log_file r fresh input label_messages)
                      ()
                  with
                  | uu___397_3781 ->
                      if
                        let uu____3786 = FStar_Options.trace_error ()  in
                        Prims.op_Negation uu____3786
                      then
                        Obj.magic
                          (Obj.repr
                             ((let uu____3789 =
                                 let uu____3794 = FStar_ST.op_Bang bg_z3_proc
                                    in
                                 uu____3794.refresh  in
                               uu____3789 ());
                              FStar_Exn.raise uu___397_3781))
                      else Obj.magic (Obj.repr (failwith "unreachable"))
                   in
                match uu____3764 with
                | (status,statistics) ->
                    let uu____3820 =
                      let uu____3826 = FStar_Util.now ()  in
                      FStar_Util.time_diff start uu____3826  in
                    (match uu____3820 with
                     | (uu____3827,elapsed_time) ->
                         {
                           z3result_status = status;
                           z3result_time = elapsed_time;
                           z3result_statistics = statistics;
                           z3result_query_hash = qhash;
                           z3result_log_file = log_file
                         })
  
let (running : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let rec (dequeue' : unit -> unit) =
  fun uu____3850  ->
    let j =
      let uu____3852 = FStar_ST.op_Bang job_queue  in
      match uu____3852 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    FStar_Util.with_monitor job_queue
      (fun uu____3920  -> FStar_Util.decr pending_jobs) ();
    dequeue ()

and (dequeue : unit -> unit) =
  fun uu____3922  ->
    let uu____3923 = FStar_ST.op_Bang running  in
    if uu____3923
    then
      let rec aux uu____3951 =
        FStar_Util.monitor_enter job_queue;
        (let uu____3957 = FStar_ST.op_Bang job_queue  in
         match uu____3957 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____3990 -> dequeue' ())
         in
      aux ()
    else ()

and (run_job : z3job -> unit) =
  fun j  ->
    let uu____3994 = j.job ()  in FStar_All.pipe_left j.callback uu____3994

let (init : unit -> unit) =
  fun uu____4000  ->
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
      (fun uu____4057  ->
         (let uu____4059 =
            let uu____4062 = FStar_ST.op_Bang job_queue  in
            FStar_List.append uu____4062 [j]  in
          FStar_ST.op_Colon_Equals job_queue uu____4059);
         FStar_Util.monitor_pulse job_queue) ()
  
let (finish : unit -> unit) =
  fun uu____4120  ->
    let rec aux uu____4126 =
      let uu____4127 =
        FStar_Util.with_monitor job_queue
          (fun uu____4145  ->
             let uu____4146 = FStar_ST.op_Bang pending_jobs  in
             let uu____4169 =
               let uu____4170 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____4170  in
             (uu____4146, uu____4169)) ()
         in
      match uu____4127 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let (fresh_scope : scope_t FStar_ST.ref) = FStar_Util.mk_ref [[]] 
let (mk_fresh_scope : unit -> scope_t) =
  fun uu____4246  -> FStar_ST.op_Bang fresh_scope 
let (flatten_fresh_scope : unit -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun uu____4273  ->
    let uu____4274 =
      let uu____4279 = FStar_ST.op_Bang fresh_scope  in
      FStar_List.rev uu____4279  in
    FStar_List.flatten uu____4274
  
let (bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let (push : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____4323  ->
         (let uu____4325 =
            let uu____4326 = FStar_ST.op_Bang fresh_scope  in
            [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
              :: uu____4326
             in
          FStar_ST.op_Colon_Equals fresh_scope uu____4325);
         (let uu____4371 =
            let uu____4374 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____4374
              [FStar_SMTEncoding_Term.Push;
              FStar_SMTEncoding_Term.Caption msg]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____4371))
  
let (pop : Prims.string -> unit) =
  fun msg  ->
    FStar_Util.atomically
      (fun uu____4434  ->
         (let uu____4436 =
            let uu____4437 = FStar_ST.op_Bang fresh_scope  in
            FStar_List.tl uu____4437  in
          FStar_ST.op_Colon_Equals fresh_scope uu____4436);
         (let uu____4482 =
            let uu____4485 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____4485
              [FStar_SMTEncoding_Term.Caption msg;
              FStar_SMTEncoding_Term.Pop]
             in
          FStar_ST.op_Colon_Equals bg_scope uu____4482))
  
let (snapshot : Prims.string -> (Prims.int * unit)) =
  fun msg  -> FStar_Common.snapshot push fresh_scope msg 
let (rollback :
  Prims.string -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun msg  ->
    fun depth  ->
      FStar_Common.rollback (fun uu____4572  -> pop msg) fresh_scope depth
  
let (giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___2_4587  ->
            match uu___2_4587 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____4590 -> ()));
    (let uu____4592 = FStar_ST.op_Bang fresh_scope  in
     match uu____4592 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____4643 -> failwith "Impossible");
    (let uu____4645 =
       let uu____4648 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4648 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____4645)
  
let (refresh : unit -> unit) =
  fun uu____4702  ->
    (let uu____4704 =
       let uu____4706 = FStar_Options.n_cores ()  in
       uu____4706 < (Prims.parse_int "2")  in
     if uu____4704
     then
       let uu____4710 =
         let uu____4715 = FStar_ST.op_Bang bg_z3_proc  in uu____4715.refresh
          in
       uu____4710 ()
     else ());
    (let uu____4737 = flatten_fresh_scope ()  in
     FStar_ST.op_Colon_Equals bg_scope uu____4737)
  
let (context_profile : FStar_SMTEncoding_Term.decl Prims.list -> unit) =
  fun theory  ->
    let uu____4773 =
      FStar_List.fold_left
        (fun uu____4806  ->
           fun d  ->
             match uu____4806 with
             | (out,_total) ->
                 (match d with
                  | FStar_SMTEncoding_Term.Module (name,decls) ->
                      let decls1 =
                        FStar_List.filter
                          (fun uu___3_4875  ->
                             match uu___3_4875 with
                             | FStar_SMTEncoding_Term.Assume uu____4877 ->
                                 true
                             | uu____4879 -> false) decls
                         in
                      let n1 = FStar_List.length decls1  in
                      (((name, n1) :: out), (n1 + _total))
                  | uu____4896 -> (out, _total))) ([], (Prims.parse_int "0"))
        theory
       in
    match uu____4773 with
    | (modules,total_decls) ->
        let modules1 =
          FStar_List.sortWith
            (fun uu____4958  ->
               fun uu____4959  ->
                 match (uu____4958, uu____4959) with
                 | ((uu____4985,n1),(uu____4987,m)) -> m - n1) modules
           in
        (if modules1 <> []
         then
           (let uu____5025 = FStar_Util.string_of_int total_decls  in
            FStar_Util.print1
              "Z3 Proof Stats: context_profile with %s assertions\n"
              uu____5025)
         else ();
         FStar_List.iter
           (fun uu____5040  ->
              match uu____5040 with
              | (m,n1) ->
                  if n1 <> (Prims.parse_int "0")
                  then
                    let uu____5056 = FStar_Util.string_of_int n1  in
                    FStar_Util.print2
                      "Z3 Proof Stats: %s produced %s SMT decls\n" m
                      uu____5056
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
      (let uu____5115 = FStar_Options.print_z3_statistics ()  in
       if uu____5115 then context_profile theory else ());
      (let uu____5120 =
         let uu____5129 =
           (FStar_Options.record_hints ()) ||
             ((FStar_Options.use_hints ()) &&
                (FStar_Options.use_hint_hashes ()))
            in
         if uu____5129
         then
           let uu____5140 =
             let uu____5151 =
               FStar_All.pipe_right theory
                 (FStar_Util.prefix_until
                    (fun uu___4_5179  ->
                       match uu___4_5179 with
                       | FStar_SMTEncoding_Term.CheckSat  -> true
                       | uu____5182 -> false))
                in
             FStar_All.pipe_right uu____5151 FStar_Option.get  in
           match uu____5140 with
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
                 let uu____5265 = FStar_Options.keep_query_captions ()  in
                 if uu____5265
                 then
                   let uu____5269 =
                     FStar_All.pipe_right prefix1
                       (FStar_List.map
                          (FStar_SMTEncoding_Term.declToSmt_no_caps options))
                      in
                   FStar_All.pipe_right uu____5269 (FStar_String.concat "\n")
                 else ps  in
               let uu____5286 =
                 let uu____5290 = FStar_Util.digest_of_string hs  in
                 FStar_Pervasives_Native.Some uu____5290  in
               ((Prims.op_Hat ps (Prims.op_Hat "\n" ss)), uu____5286)
         else
           (let uu____5300 =
              let uu____5302 =
                FStar_List.map (FStar_SMTEncoding_Term.declToSmt options)
                  theory
                 in
              FStar_All.pipe_right uu____5302 (FStar_String.concat "\n")  in
            (uu____5300, FStar_Pervasives_Native.None))
          in
       match uu____5120 with
       | (r,hash) ->
           let log_file_name =
             let uu____5344 = FStar_Options.log_queries ()  in
             if uu____5344
             then
               let uu____5350 = query_logging.write_to_log fresh r  in
               FStar_Pervasives_Native.Some uu____5350
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
          let uu____5408 =
            (FStar_Options.use_hints ()) &&
              (FStar_Options.use_hint_hashes ())
             in
          if uu____5408
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
            | uu____5433 -> false
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
                let uu____5575 = filter_theory theory1  in
                match uu____5575 with
                | (theory2,_used_unsat_core) ->
                    let uu____5591 = mk_input fresh theory2  in
                    (match uu____5591 with
                     | (input,qhash,log_file_name) ->
                         let uu____5622 =
                           let uu____5624 =
                             fresh &&
                               (cache_hit log_file_name cache qhash cb)
                              in
                           Prims.op_Negation uu____5624  in
                         if uu____5622
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
                  let uu____5707 =
                    match scope with
                    | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                    | FStar_Pervasives_Native.None  ->
                        (FStar_ST.op_Colon_Equals bg_scope [];
                         (let uu____5743 = FStar_ST.op_Bang fresh_scope  in
                          FStar_List.rev uu____5743))
                     in
                  FStar_List.flatten uu____5707  in
                let theory1 =
                  FStar_List.append theory
                    (FStar_List.append [FStar_SMTEncoding_Term.Push]
                       (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
                   in
                let uu____5772 = filter_theory theory1  in
                match uu____5772 with
                | (theory2,used_unsat_core) ->
                    let uu____5788 = mk_input true theory2  in
                    (match uu____5788 with
                     | (input,qhash,log_file_name) ->
                         let uu____5820 =
                           let uu____5822 =
                             cache_hit log_file_name cache qhash cb  in
                           Prims.op_Negation uu____5822  in
                         if uu____5820
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
                  let uu____5910 =
                    let uu____5912 = FStar_Options.n_cores ()  in
                    uu____5912 = (Prims.parse_int "1")  in
                  if uu____5910
                  then ask_1_core r filter1 cache label_messages qry cb fresh
                  else
                    ask_n_cores r filter1 cache label_messages qry scope cb
  
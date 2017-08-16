open Prims
type z3version =
  | Z3V_Unknown of Prims.string 
  | Z3V of (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 
let uu___is_Z3V_Unknown : z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____20 -> false
  
let __proj__Z3V_Unknown__item___0 : z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0 
let uu___is_Z3V : z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____40 -> false 
let __proj__Z3V__item___0 :
  z3version -> (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Z3V _0 -> _0 
let z3version_as_string : z3version -> Prims.string =
  fun uu___95_70  ->
    match uu___95_70 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____75 = FStar_Util.string_of_int i  in
        let uu____76 = FStar_Util.string_of_int j  in
        let uu____77 = FStar_Util.string_of_int k  in
        FStar_Util.format3 "%s.%s.%s" uu____75 uu____76 uu____77
  
let z3v_compare :
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.int FStar_Pervasives_Native.option
  =
  fun known  ->
    fun uu____93  ->
      match uu____93 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____107 -> FStar_Pervasives_Native.None
           | Z3V (k1,k2,k3) ->
               FStar_Pervasives_Native.Some
                 (if k1 <> w1
                  then w1 - k1
                  else if k2 <> w2 then w2 - k2 else w3 - k3))
  
let z3v_le :
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.bool
  =
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some i -> i >= (Prims.parse_int "0")
  
let _z3version : z3version FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let get_z3version : Prims.unit -> z3version =
  fun uu____150  ->
    let prefix1 = "Z3 version "  in
    let uu____152 = FStar_ST.op_Bang _z3version  in
    match uu____152 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____174 =
          let uu____181 = FStar_Options.solver_exe ()  in
          FStar_Util.run_proc uu____181 "-version" ""  in
        (match uu____174 with
         | (uu____182,out,uu____184) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____187 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____191 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1)
                        in
                     FStar_Util.trim_string uu____191  in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____206 -> []  in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____210 -> Z3V_Unknown out)
               | uu____213 -> Z3V_Unknown out  in
             (FStar_ST.op_Colon_Equals _z3version
                (FStar_Pervasives_Native.Some out1);
              out1))
  
let ini_params : Prims.unit -> Prims.string =
  fun uu____238  ->
    let uu____239 = FStar_Options.smt_solver ()  in
    match uu____239 with
    | FStar_Options.Z3  ->
        let z3_v = get_z3version ()  in
        ((let uu____242 =
            let uu____243 = get_z3version ()  in
            z3v_le uu____243
              ((Prims.parse_int "4"), (Prims.parse_int "4"),
                (Prims.parse_int "0"))
             in
          if uu____242
          then
            let uu____244 =
              let uu____245 =
                let uu____246 = z3version_as_string z3_v  in
                FStar_Util.format1
                  "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
                  uu____246
                 in
              FStar_Util.Failure uu____245  in
            FStar_All.pipe_left FStar_Exn.raise uu____244
          else ());
         (let uu____248 =
            let uu____251 =
              let uu____254 =
                let uu____257 =
                  let uu____260 =
                    let uu____263 =
                      let uu____266 =
                        let uu____269 =
                          let uu____272 =
                            let uu____273 =
                              let uu____274 = FStar_Options.z3_seed ()  in
                              FStar_Util.string_of_int uu____274  in
                            FStar_Util.format1 "smt.random_seed=%s" uu____273
                             in
                          [uu____272]  in
                        "smtlib2_compliant=true" :: uu____269  in
                      "smt.relevancy=2" :: uu____266  in
                    "model=true" :: uu____263  in
                  "auto_config=false" :: uu____260  in
                "-in" :: uu____257  in
              "-smt2" :: uu____254  in
            let uu____275 = FStar_Options.z3_cliopt ()  in
            FStar_List.append uu____251 uu____275  in
          FStar_All.pipe_right uu____248 (FStar_String.concat " ")))
    | FStar_Options.CVC4  ->
        let uu____280 =
          let uu____283 = FStar_Options.z3_cliopt ()  in
          FStar_List.append
            ["--incremental"; "--mbqi=none"; "--lang smt2"; "--incremental"]
            uu____283
           in
        FStar_All.pipe_right uu____280 (FStar_String.concat " ")
  
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
let uu___is_UNSAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____331 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____351 -> false
  
let __proj__SAT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____389 -> false
  
let __proj__UNKNOWN__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____427 -> false
  
let __proj__TIMEOUT__item___0 :
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____458 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let status_tag : z3status -> Prims.string =
  fun uu___96_464  ->
    match uu___96_464 with
    | SAT uu____465 -> "sat"
    | UNSAT uu____472 -> "unsat"
    | UNKNOWN uu____473 -> "unknown"
    | TIMEOUT uu____480 -> "timeout"
    | KILLED  -> "killed"
  
let status_string_and_errors :
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____501 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____510 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____510, errs)
    | UNKNOWN (errs,msg) ->
        let uu____518 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____518, errs)
    | TIMEOUT (errs,msg) ->
        let uu____526 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1)
           in
        (uu____526, errs)
  
let tid : Prims.unit -> Prims.string =
  fun uu____531  ->
    let uu____532 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____532 FStar_Util.string_of_int
  
let smt_cond : 'Auu____539 . 'Auu____539 -> Prims.string -> Prims.bool =
  fun uu____546  ->
    fun s  ->
      let s1 = FStar_Util.trim_string s  in
      (s1 = "Done!") || (s1 = "\"Done!\"")
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id  ->
    let uu____553 = FStar_Options.solver_exe ()  in
    let uu____554 = ini_params ()  in
    FStar_Util.start_process id uu____553 uu____554 smt_cond
  
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc ;
  release: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit ;
  restart: Prims.unit -> Prims.unit }
let __proj__Mkbgproc__item__grab : bgproc -> Prims.unit -> FStar_Util.proc =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__grab
  
let __proj__Mkbgproc__item__release : bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__release
  
let __proj__Mkbgproc__item__refresh : bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__refresh
  
let __proj__Mkbgproc__item__restart : bgproc -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__restart
  
type query_log =
  {
  get_module_name: Prims.unit -> Prims.string ;
  set_module_name: Prims.string -> Prims.unit ;
  write_to_log: Prims.string -> Prims.unit ;
  close_log: Prims.unit -> Prims.unit ;
  log_file_name: Prims.unit -> Prims.string }
let __proj__Mkquery_log__item__get_module_name :
  query_log -> Prims.unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
  
let __proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
  
let __proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
  
let __proj__Mkquery_log__item__close_log :
  query_log -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
  
let __proj__Mkquery_log__item__log_file_name :
  query_log -> Prims.unit -> Prims.string =
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
  
let query_logging : query_log =
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
  let get_module_name uu____913 =
    let uu____914 = FStar_ST.op_Bang current_module_name  in
    match uu____914 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____953 =
    let uu____954 = FStar_ST.op_Bang current_module_name  in
    match uu____954 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____991 =
            let uu____998 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____1060  ->
                 match uu____1060 with | (m,uu____1066) -> n1 = m) uu____998
             in
          match uu____991 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1072 =
                  let uu____1079 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____1079  in
                FStar_ST.op_Colon_Equals used_file_names uu____1072);
               n1)
          | FStar_Pervasives_Native.Some (uu____1186,k) ->
              ((let uu____1193 =
                  let uu____1200 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1200  in
                FStar_ST.op_Colon_Equals used_file_names uu____1193);
               (let uu____1307 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____1307))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh))
     in
  let get_log_file uu____1379 =
    let uu____1380 = FStar_ST.op_Bang log_file_opt  in
    match uu____1380 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____1420 = get_log_file ()  in
    FStar_Util.append_to_file uu____1420 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1426 = FStar_ST.op_Bang current_file_name  in
      match uu____1426 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1462 = FStar_ST.op_Bang current_module_name  in
            match uu____1462 with
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
    (let uu____1559 =
       let uu____1560 = FStar_ST.op_Bang query_number  in
       uu____1560 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals query_number uu____1559);
    (let file_name =
       let uu____1610 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____1610  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____1616 =
      let uu____1617 = FStar_Options.n_cores ()  in
      uu____1617 > (Prims.parse_int "1")  in
    if uu____1616 then write_to_new_log str else append_to_log str  in
  let close_log uu____1622 =
    let uu____1623 = FStar_ST.op_Bang log_file_opt  in
    match uu____1623 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____1695 =
    let uu____1696 = FStar_ST.op_Bang current_file_name  in
    match uu____1696 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let bg_z3_proc : bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____1745  ->
      let uu____1746 =
        let uu____1747 =
          FStar_Util.incr ctr;
          (let uu____1770 = FStar_ST.op_Bang ctr  in
           FStar_All.pipe_right uu____1770 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____1747  in
      new_z3proc uu____1746
     in
  let z3proc uu____1798 =
    (let uu____1800 =
       let uu____1801 = FStar_ST.op_Bang the_z3proc  in
       uu____1801 = FStar_Pervasives_Native.None  in
     if uu____1800
     then
       let uu____1838 =
         let uu____1841 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____1841  in
       FStar_ST.op_Colon_Equals the_z3proc uu____1838
     else ());
    (let uu____1875 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____1875)
     in
  let x = []  in
  let grab uu____1916 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____1923 = FStar_Util.monitor_exit x  in
  let refresh uu____1929 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let uu____1933 =
       let uu____1936 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____1936  in
     FStar_ST.op_Colon_Equals the_z3proc uu____1933);
    query_logging.close_log ();
    release ()  in
  let restart uu____1973 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____2010 =
       let uu____2013 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____2013  in
     FStar_ST.op_Colon_Equals the_z3proc uu____2010);
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let at_log_file : Prims.unit -> Prims.string =
  fun uu____2049  ->
    let uu____2050 = FStar_Options.log_queries ()  in
    if uu____2050
    then
      let uu____2051 = query_logging.log_file_name ()  in
      Prims.strcat "__" uu____2051
    else ""
  
type smt_output_section = Prims.string Prims.list
type smt_output =
  {
  smt_result: smt_output_section ;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option ;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option ;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option ;
  smt_labels: smt_output_section FStar_Pervasives_Native.option }
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
  
let smt_output_sections : Prims.string Prims.list -> smt_output =
  fun lines  ->
    let until tag lines1 =
      let tag' = Prims.strcat "\"" (Prims.strcat tag "\"")  in
      let rec aux lines2 =
        match lines2 with
        | [] -> FStar_Pervasives_Native.None
        | l::lines3 ->
            if (tag = l) || (tag' = l)
            then FStar_Pervasives_Native.Some ([], lines3)
            else
              (let uu____2277 = aux lines3  in
               FStar_Util.map_opt uu____2277
                 (fun uu____2307  ->
                    match uu____2307 with
                    | (until_tag,rest) -> ((l :: until_tag), rest)))
         in
      aux lines1  in
    let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">")  in
    let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">")  in
    let find_section tag lines1 =
      let uu____2377 = until (start_tag tag) lines1  in
      match uu____2377 with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, lines1)
      | FStar_Pervasives_Native.Some (prefix1,suffix) ->
          let uu____2432 = until (end_tag tag) suffix  in
          (match uu____2432 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.strcat "Parse error: "
                    (Prims.strcat (end_tag tag) " not found"))
           | FStar_Pervasives_Native.Some (section,suffix1) ->
               ((FStar_Pervasives_Native.Some section),
                 (FStar_List.append prefix1 suffix1)))
       in
    let uu____2497 = find_section "result" lines  in
    match uu____2497 with
    | (result_opt,lines1) ->
        let result = FStar_Util.must result_opt  in
        let uu____2527 = find_section "reason-unknown" lines1  in
        (match uu____2527 with
         | (reason_unknown,lines2) ->
             let uu____2552 = find_section "unsat-core" lines2  in
             (match uu____2552 with
              | (unsat_core,lines3) ->
                  let uu____2577 = find_section "statistics" lines3  in
                  (match uu____2577 with
                   | (statistics,lines4) ->
                       let uu____2602 = find_section "labels" lines4  in
                       (match uu____2602 with
                        | (labels,lines5) ->
                            let remaining =
                              let uu____2630 = until "Done!" lines5  in
                              match uu____2630 with
                              | FStar_Pervasives_Native.None  -> lines5
                              | FStar_Pervasives_Native.Some (prefix1,suffix)
                                  -> FStar_List.append prefix1 suffix
                               in
                            ((match remaining with
                              | [] -> ()
                              | uu____2670 ->
                                  let uu____2673 =
                                    let uu____2674 =
                                      query_logging.get_module_name ()  in
                                    FStar_Util.format2
                                      "%s: Unexpected output from Z3: %s\n"
                                      uu____2674
                                      (FStar_String.concat "\n" remaining)
                                     in
                                  FStar_Errors.warn FStar_Range.dummyRange
                                    uu____2673);
                             (let uu____2675 = FStar_Util.must result_opt  in
                              {
                                smt_result = uu____2675;
                                smt_reason_unknown = reason_unknown;
                                smt_unsat_core = unsat_core;
                                smt_statistics = statistics;
                                smt_labels = labels
                              }))))))
  
let doZ3Exe :
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
                  (let uu____2735 =
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_Util.sort_with FStar_String.compare)
                      in
                   FStar_Pervasives_Native.Some uu____2735)
             in
          let labels =
            match smt_output.smt_labels with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some lines1 ->
                let rec lblnegs lines2 =
                  match lines2 with
                  | lname::"false"::rest when
                      FStar_Util.starts_with lname "label_" ->
                      let uu____2796 = lblnegs rest  in lname :: uu____2796
                  | lname::uu____2800::rest when
                      FStar_Util.starts_with lname "label_" -> lblnegs rest
                  | uu____2804 -> []  in
                let lblnegs1 = lblnegs lines1  in
                FStar_All.pipe_right lblnegs1
                  (FStar_List.collect
                     (fun l  ->
                        let uu____2837 =
                          FStar_All.pipe_right label_messages
                            (FStar_List.tryFind
                               (fun uu____2876  ->
                                  match uu____2876 with
                                  | (m,uu____2888,uu____2889) ->
                                      (FStar_Pervasives_Native.fst m) = l))
                           in
                        match uu____2837 with
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
                  | uu____3001 -> ()  in
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
                       ((FStar_String.length reason) - (Prims.parse_int "2"))
                      in
                   res
                 else ru)
             in
          let status =
            (let uu____3019 = FStar_Options.debug_any ()  in
             if uu____3019
             then
               let uu____3020 =
                 FStar_Util.format1 "Z3 says: %s\n"
                   (FStar_String.concat "\n" smt_output.smt_result)
                  in
               FStar_All.pipe_left FStar_Util.print_string uu____3020
             else ());
            (match smt_output.smt_result with
             | "unsat"::[] -> UNSAT unsat_core
             | "sat"::[] -> SAT (labels, reason_unknown)
             | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
             | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
             | "killed"::[] -> (bg_z3_proc.restart (); KILLED)
             | uu____3065 ->
                 let uu____3066 =
                   FStar_Util.format1
                     "Unexpected output from Z3: got output result: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result)
                    in
                 failwith uu____3066)
             in
          (status, statistics)  in
        let stdout1 =
          if fresh1
          then
            let uu____3068 = tid ()  in
            let uu____3069 = FStar_Options.solver_exe ()  in
            let uu____3070 = ini_params ()  in
            FStar_Util.launch_process uu____3068 uu____3069 uu____3070 input
              smt_cond
          else
            (let proc = bg_z3_proc.grab ()  in
             let stdout1 = FStar_Util.ask_process proc input  in
             bg_z3_proc.release (); stdout1)
           in
        parse (FStar_Util.trim_string stdout1)
  
type 'a job = {
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }
let __proj__Mkjob__item__job : 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
  
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
  
type z3job =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3 job
let job_queue : z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let pending_jobs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let with_monitor :
  'Auu____3177 'Auu____3178 .
    'Auu____3178 -> (Prims.unit -> 'Auu____3177) -> 'Auu____3177
  =
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f ()  in FStar_Util.monitor_exit m; res)
  
let z3_job :
  Prims.bool ->
    FStar_SMTEncoding_Term.error_labels ->
      Prims.string ->
        Prims.unit ->
          (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____3216  ->
          let start = FStar_Util.now ()  in
          let uu____3224 = doZ3Exe fresh1 input label_messages  in
          match uu____3224 with
          | (status,statistics) ->
              let uu____3237 =
                let uu____3242 = FStar_Util.now ()  in
                FStar_Util.time_diff start uu____3242  in
              (match uu____3237 with
               | (uu____3249,elapsed_time) ->
                   (status, elapsed_time, statistics))
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : Prims.unit -> Prims.unit =
  fun uu____3266  ->
    let j =
      let uu____3268 = FStar_ST.op_Bang job_queue  in
      match uu____3268 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____3325  -> FStar_Util.decr pending_jobs);
    dequeue ()

and dequeue : Prims.unit -> Prims.unit =
  fun uu____3327  ->
    let uu____3328 = FStar_ST.op_Bang running  in
    if uu____3328
    then
      let rec aux uu____3342 =
        FStar_Util.monitor_enter job_queue;
        (let uu____3348 = FStar_ST.op_Bang job_queue  in
         match uu____3348 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____3375 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> Prims.unit =
  fun j  ->
    let uu____3379 = j.job ()  in FStar_All.pipe_left j.callback uu____3379

let init : Prims.unit -> Prims.unit =
  fun uu____3407  ->
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
  
let enqueue : z3job -> Prims.unit =
  fun j  ->
    FStar_Util.monitor_enter job_queue;
    (let uu____3437 =
       let uu____3440 = FStar_ST.op_Bang job_queue  in
       FStar_List.append uu____3440 [j]  in
     FStar_ST.op_Colon_Equals job_queue uu____3437);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
  
let finish : Prims.unit -> Prims.unit =
  fun uu____3491  ->
    let rec aux uu____3495 =
      let uu____3496 =
        with_monitor job_queue
          (fun uu____3512  ->
             let uu____3513 = FStar_ST.op_Bang pending_jobs  in
             let uu____3524 =
               let uu____3525 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____3525  in
             (uu____3513, uu____3524))
         in
      match uu____3496 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let mk_fresh_scope : Prims.unit -> scope_t =
  fun uu____3596  -> FStar_ST.op_Bang fresh_scope 
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let push : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3641 =
       let uu____3646 = FStar_ST.op_Bang fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____3646
        in
     FStar_ST.op_Colon_Equals fresh_scope uu____3641);
    (let uu____3705 =
       let uu____3708 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____3708
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____3705)
  
let pop : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3752 =
       let uu____3757 = FStar_ST.op_Bang fresh_scope  in
       FStar_List.tl uu____3757  in
     FStar_ST.op_Colon_Equals fresh_scope uu____3752);
    (let uu____3816 =
       let uu____3819 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____3819
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____3816)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___97_3870  ->
            match uu___97_3870 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____3871 -> ()));
    (let uu____3873 = FStar_ST.op_Bang fresh_scope  in
     match uu____3873 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____3942 -> failwith "Impossible");
    (let uu____3947 =
       let uu____3950 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____3950 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____3947)
  
let refresh : Prims.unit -> Prims.unit =
  fun uu____3992  ->
    (let uu____3994 =
       let uu____3995 = FStar_Options.n_cores ()  in
       uu____3995 < (Prims.parse_int "2")  in
     if uu____3994 then bg_z3_proc.refresh () else ());
    (let uu____3997 =
       let uu____4000 =
         let uu____4005 = FStar_ST.op_Bang fresh_scope  in
         FStar_List.rev uu____4005  in
       FStar_List.flatten uu____4000  in
     FStar_ST.op_Colon_Equals bg_scope uu____3997)
  
let mark : Prims.string -> Prims.unit = fun msg  -> push msg 
let reset_mark : Prims.string -> Prims.unit = fun msg  -> pop msg; refresh () 
let commit_mark : Prims.string -> Prims.unit =
  fun msg  ->
    let uu____4069 = FStar_ST.op_Bang fresh_scope  in
    match uu____4069 with
    | hd1::s::tl1 ->
        FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 s) ::
          tl1)
    | uu____4143 -> failwith "Impossible"
  
let mk_input : FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____4157 = FStar_List.map FStar_SMTEncoding_Term.declToSmt theory
         in
      FStar_All.pipe_right uu____4157 (FStar_String.concat "\n")  in
    (let uu____4163 = FStar_Options.log_queries ()  in
     if uu____4163 then query_logging.write_to_log r else ());
    r
  
type z3result =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
type cb = z3result -> Prims.unit
let ask_1_core :
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
            let uu____4207 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____4207
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
             in
          let uu____4228 = filter_theory theory  in
          match uu____4228 with
          | (theory1,used_unsat_core) ->
              let input = mk_input theory1  in
              (FStar_ST.op_Colon_Equals bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb })
  
let ask_n_cores :
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
              let uu____4305 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.op_Colon_Equals bg_scope [];
                     (let uu____4336 = FStar_ST.op_Bang fresh_scope  in
                      FStar_List.rev uu____4336))
                 in
              FStar_List.flatten uu____4305  in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
               in
            let uu____4372 = filter_theory theory1  in
            match uu____4372 with
            | (theory2,used_unsat_core) ->
                let input = mk_input theory2  in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb }
  
let ask :
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
            let uu____4429 =
              let uu____4430 = FStar_Options.n_cores ()  in
              uu____4430 = (Prims.parse_int "1")  in
            if uu____4429
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
  
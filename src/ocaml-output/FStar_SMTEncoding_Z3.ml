open Prims
type z3version =
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
let uu___is_Z3V_Unknown: z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____20 -> false
let __proj__Z3V_Unknown__item___0: z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let uu___is_Z3V: z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____40 -> false
let __proj__Z3V__item___0:
  z3version -> (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Z3V _0 -> _0
let z3version_as_string: z3version -> Prims.string =
  fun uu___95_70  ->
    match uu___95_70 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____75 = FStar_Util.string_of_int i in
        let uu____76 = FStar_Util.string_of_int j in
        let uu____77 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____75 uu____76 uu____77
let z3v_compare:
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
let z3v_le:
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.bool
  =
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some i -> i >= (Prims.parse_int "0")
let _z3version: z3version FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let get_z3version: Prims.unit -> z3version =
  fun uu____150  ->
    let prefix1 = "Z3 version " in
    let uu____152 = FStar_ST.op_Bang _z3version in
    match uu____152 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____174 =
          let uu____181 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____181 "-version" "" in
        (match uu____174 with
         | (uu____182,out,uu____184) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____187 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____191 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____191 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____206 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____210 -> Z3V_Unknown out)
               | uu____213 -> Z3V_Unknown out in
             (FStar_ST.op_Colon_Equals _z3version
                (FStar_Pervasives_Native.Some out1);
              out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____238  ->
    let z3_v = get_z3version () in
    (let uu____241 =
       let uu____242 = get_z3version () in
       z3v_le uu____242
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____241
     then
       let uu____243 =
         let uu____244 =
           let uu____245 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____245 in
         FStar_Util.Failure uu____244 in
       FStar_All.pipe_left FStar_Exn.raise uu____243
     else ());
    (let uu____247 =
       let uu____250 =
         let uu____253 =
           let uu____256 =
             let uu____257 =
               let uu____258 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____258 in
             FStar_Util.format1 "smt.random_seed=%s" uu____257 in
           [uu____256] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____253 in
       let uu____259 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____250 uu____259 in
     FStar_String.concat " " uu____247)
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
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____305 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____325 -> false
let __proj__SAT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____363 -> false
let __proj__UNKNOWN__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____401 -> false
let __proj__TIMEOUT__item___0:
  z3status ->
    (FStar_SMTEncoding_Term.error_labels,Prims.string
                                           FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____432 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_tag: z3status -> Prims.string =
  fun uu___96_438  ->
    match uu___96_438 with
    | SAT uu____439 -> "sat"
    | UNSAT uu____446 -> "unsat"
    | UNKNOWN uu____447 -> "unknown"
    | TIMEOUT uu____454 -> "timeout"
    | KILLED  -> "killed"
let status_string_and_errors:
  z3status ->
    (Prims.string,FStar_SMTEncoding_Term.error_labels)
      FStar_Pervasives_Native.tuple2
  =
  fun s  ->
    match s with
    | KILLED  -> ((status_tag s), [])
    | UNSAT uu____475 -> ((status_tag s), [])
    | SAT (errs,msg) ->
        let uu____484 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____484, errs)
    | UNKNOWN (errs,msg) ->
        let uu____492 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____492, errs)
    | TIMEOUT (errs,msg) ->
        let uu____500 =
          FStar_Util.format2 "%s%s" (status_tag s)
            (match msg with
             | FStar_Pervasives_Native.None  -> ""
             | FStar_Pervasives_Native.Some msg1 ->
                 Prims.strcat " because " msg1) in
        (uu____500, errs)
let tid: Prims.unit -> Prims.string =
  fun uu____505  ->
    let uu____506 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____506 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____519 = FStar_Options.z3_exe () in
    let uu____520 = ini_params () in
    FStar_Util.start_process false id uu____519 uu____520 cond
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc;
  release: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;
  restart: Prims.unit -> Prims.unit;}
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
  log_file_name: Prims.unit -> Prims.string;}
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
  let get_module_name uu____879 =
    let uu____880 = FStar_ST.op_Bang current_module_name in
    match uu____880 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____919 =
    let uu____920 = FStar_ST.op_Bang current_module_name in
    match uu____920 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____957 =
            let uu____964 = FStar_ST.op_Bang used_file_names in
            FStar_List.tryFind
              (fun uu____1026  ->
                 match uu____1026 with | (m,uu____1032) -> n1 = m) uu____964 in
          match uu____957 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____1038 =
                  let uu____1045 = FStar_ST.op_Bang used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____1045 in
                FStar_ST.op_Colon_Equals used_file_names uu____1038);
               n1)
          | FStar_Pervasives_Native.Some (uu____1152,k) ->
              ((let uu____1159 =
                  let uu____1166 = FStar_ST.op_Bang used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1166 in
                FStar_ST.op_Colon_Equals used_file_names uu____1159);
               (let uu____1273 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____1273)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
          fh)) in
  let get_log_file uu____1345 =
    let uu____1346 = FStar_ST.op_Bang log_file_opt in
    match uu____1346 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____1386 = get_log_file () in
    FStar_Util.append_to_file uu____1386 str in
  let write_to_new_log str =
    let dir_name =
      let uu____1392 = FStar_ST.op_Bang current_file_name in
      match uu____1392 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1428 = FStar_ST.op_Bang current_module_name in
            match uu____1428 with
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
    (let uu____1525 =
       let uu____1526 = FStar_ST.op_Bang query_number in
       uu____1526 + (Prims.parse_int "1") in
     FStar_ST.op_Colon_Equals query_number uu____1525);
    (let file_name =
       let uu____1576 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____1576 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____1582 =
      let uu____1583 = FStar_Options.n_cores () in
      uu____1583 > (Prims.parse_int "1") in
    if uu____1582 then write_to_new_log str else append_to_log str in
  let close_log uu____1588 =
    let uu____1589 = FStar_ST.op_Bang log_file_opt in
    match uu____1589 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____1661 =
    let uu____1662 = FStar_ST.op_Bang current_file_name in
    match uu____1662 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____1711  ->
      let uu____1712 =
        let uu____1713 =
          FStar_Util.incr ctr;
          (let uu____1736 = FStar_ST.op_Bang ctr in
           FStar_All.pipe_right uu____1736 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____1713 in
      new_z3proc uu____1712 in
  let z3proc uu____1764 =
    (let uu____1766 =
       let uu____1767 = FStar_ST.op_Bang the_z3proc in
       uu____1767 = FStar_Pervasives_Native.None in
     if uu____1766
     then
       let uu____1804 =
         let uu____1807 = new_proc () in
         FStar_Pervasives_Native.Some uu____1807 in
       FStar_ST.op_Colon_Equals the_z3proc uu____1804
     else ());
    (let uu____1841 = FStar_ST.op_Bang the_z3proc in
     FStar_Util.must uu____1841) in
  let x = [] in
  let grab uu____1882 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____1889 = FStar_Util.monitor_exit x in
  let refresh uu____1895 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____1899 =
       let uu____1902 = new_proc () in
       FStar_Pervasives_Native.Some uu____1902 in
     FStar_ST.op_Colon_Equals the_z3proc uu____1899);
    query_logging.close_log ();
    release () in
  let restart uu____1939 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____1976 =
       let uu____1979 = new_proc () in
       FStar_Pervasives_Native.Some uu____1979 in
     FStar_ST.op_Colon_Equals the_z3proc uu____1976);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____2015  ->
    let uu____2016 = FStar_Options.log_queries () in
    if uu____2016
    then
      let uu____2017 = query_logging.log_file_name () in
      Prims.strcat "@" uu____2017
    else ""
type smt_output_section = Prims.string Prims.list
type smt_output =
  {
  smt_result: smt_output_section;
  smt_reason_unknown: smt_output_section FStar_Pervasives_Native.option;
  smt_unsat_core: smt_output_section FStar_Pervasives_Native.option;
  smt_statistics: smt_output_section FStar_Pervasives_Native.option;
  smt_labels: smt_output_section FStar_Pervasives_Native.option;}
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
            (let uu____2224 = until tag lines2 in
             FStar_Util.map_opt uu____2224
               (fun uu____2254  ->
                  match uu____2254 with
                  | (until_tag,rest) -> ((l :: until_tag), rest))) in
    let start_tag tag = Prims.strcat "<" (Prims.strcat tag ">") in
    let end_tag tag = Prims.strcat "</" (Prims.strcat tag ">") in
    let find_section tag lines1 =
      let uu____2324 = until (start_tag tag) lines1 in
      match uu____2324 with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, lines1)
      | FStar_Pervasives_Native.Some (prefix1,suffix) ->
          let uu____2379 = until (end_tag tag) suffix in
          (match uu____2379 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.strcat "Parse error: "
                    (Prims.strcat (end_tag tag) " not found"))
           | FStar_Pervasives_Native.Some (section,suffix1) ->
               ((FStar_Pervasives_Native.Some section),
                 (FStar_List.append prefix1 suffix1))) in
    let uu____2444 = find_section "result" lines in
    match uu____2444 with
    | (result_opt,lines1) ->
        let result = FStar_Util.must result_opt in
        let uu____2474 = find_section "reason-unknown" lines1 in
        (match uu____2474 with
         | (reason_unknown,lines2) ->
             let uu____2499 = find_section "unsat-core" lines2 in
             (match uu____2499 with
              | (unsat_core,lines3) ->
                  let uu____2524 = find_section "statistics" lines3 in
                  (match uu____2524 with
                   | (statistics,lines4) ->
                       let uu____2549 = find_section "labels" lines4 in
                       (match uu____2549 with
                        | (labels,lines5) ->
                            let remaining =
                              let uu____2577 = until "Done!" lines5 in
                              match uu____2577 with
                              | FStar_Pervasives_Native.None  -> lines5
                              | FStar_Pervasives_Native.Some (prefix1,suffix)
                                  -> FStar_List.append prefix1 suffix in
                            ((match remaining with
                              | [] -> ()
                              | uu____2617 ->
                                  let uu____2620 =
                                    let uu____2621 =
                                      query_logging.get_module_name () in
                                    FStar_Util.format2
                                      "%s: Unexpected output from Z3: %s\n"
                                      uu____2621
                                      (FStar_String.concat "\n" remaining) in
                                  FStar_Errors.warn FStar_Range.dummyRange
                                    uu____2620);
                             (let uu____2622 = FStar_Util.must result_opt in
                              {
                                smt_result = uu____2622;
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
                  (let uu____2682 =
                     FStar_All.pipe_right (FStar_Util.split s2 " ")
                       (FStar_Util.sort_with FStar_String.compare) in
                   FStar_Pervasives_Native.Some uu____2682) in
          let labels =
            match smt_output.smt_labels with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some lines1 ->
                let rec lblnegs lines2 =
                  match lines2 with
                  | lname::"false"::rest when
                      FStar_Util.starts_with lname "label_" ->
                      let uu____2743 = lblnegs rest in lname :: uu____2743
                  | lname::uu____2747::rest when
                      FStar_Util.starts_with lname "label_" -> lblnegs rest
                  | uu____2751 -> [] in
                let lblnegs1 = lblnegs lines1 in
                FStar_All.pipe_right lblnegs1
                  (FStar_List.collect
                     (fun l  ->
                        let uu____2784 =
                          FStar_All.pipe_right label_messages
                            (FStar_List.tryFind
                               (fun uu____2823  ->
                                  match uu____2823 with
                                  | (m,uu____2835,uu____2836) ->
                                      (FStar_Pervasives_Native.fst m) = l)) in
                        match uu____2784 with
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
                  | uu____2948 -> () in
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
            (let uu____2966 = FStar_Options.debug_any () in
             if uu____2966
             then
               let uu____2967 =
                 FStar_Util.format1 "Z3 says: %s\n"
                   (FStar_String.concat "\n" smt_output.smt_result) in
               FStar_All.pipe_left FStar_Util.print_string uu____2967
             else ());
            (match smt_output.smt_result with
             | "unsat"::[] -> UNSAT unsat_core
             | "sat"::[] -> SAT (labels, reason_unknown)
             | "unknown"::[] -> UNKNOWN (labels, reason_unknown)
             | "timeout"::[] -> TIMEOUT (labels, reason_unknown)
             | "killed"::[] -> (bg_z3_proc.restart (); KILLED)
             | uu____3012 ->
                 let uu____3013 =
                   FStar_Util.format1
                     "Unexpected output from Z3: got output result: %s\n"
                     (FStar_String.concat "\n" smt_output.smt_result) in
                 failwith uu____3013) in
          (status, statistics) in
        let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
        let stdout1 =
          if fresh1
          then
            let uu____3023 = tid () in
            let uu____3024 = FStar_Options.z3_exe () in
            let uu____3025 = ini_params () in
            FStar_Util.launch_process false uu____3023 uu____3024 uu____3025
              input cond
          else
            (let proc = bg_z3_proc.grab () in
             let stdout1 = FStar_Util.ask_process proc input in
             bg_z3_proc.release (); stdout1) in
        parse (FStar_Util.trim_string stdout1)
let z3_options: Prims.unit -> Prims.string =
  fun uu____3033  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
let __proj__Mkjob__item__job: 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback: 'a . 'a job -> 'a -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
type z3job =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3 job
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor:
  'Auu____3136 'Auu____3137 .
    'Auu____3137 -> (Prims.unit -> 'Auu____3136) -> 'Auu____3136
  =
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f () in FStar_Util.monitor_exit m; res)
let z3_job:
  Prims.bool ->
    FStar_SMTEncoding_Term.error_labels ->
      Prims.string ->
        Prims.unit ->
          (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____3175  ->
          let start = FStar_Util.now () in
          let uu____3183 = doZ3Exe fresh1 input label_messages in
          match uu____3183 with
          | (status,statistics) ->
              let uu____3196 =
                let uu____3201 = FStar_Util.now () in
                FStar_Util.time_diff start uu____3201 in
              (match uu____3196 with
               | (uu____3208,elapsed_time) ->
                   (status, elapsed_time, statistics))
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____3225  ->
    let j =
      let uu____3227 = FStar_ST.op_Bang job_queue in
      match uu____3227 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____3284  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____3286  ->
    let uu____3287 = FStar_ST.op_Bang running in
    if uu____3287
    then
      let rec aux uu____3301 =
        FStar_Util.monitor_enter job_queue;
        (let uu____3307 = FStar_ST.op_Bang job_queue in
         match uu____3307 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____3334 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____3338 = j.job () in FStar_All.pipe_left j.callback uu____3338
let init: Prims.unit -> Prims.unit =
  fun uu____3366  ->
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
    (let uu____3396 =
       let uu____3399 = FStar_ST.op_Bang job_queue in
       FStar_List.append uu____3399 [j] in
     FStar_ST.op_Colon_Equals job_queue uu____3396);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____3450  ->
    let rec aux uu____3454 =
      let uu____3455 =
        with_monitor job_queue
          (fun uu____3471  ->
             let uu____3472 = FStar_ST.op_Bang pending_jobs in
             let uu____3483 =
               let uu____3484 = FStar_ST.op_Bang job_queue in
               FStar_List.length uu____3484 in
             (uu____3472, uu____3483)) in
      match uu____3455 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let mk_fresh_scope: Prims.unit -> scope_t =
  fun uu____3555  -> FStar_ST.op_Bang fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3600 =
       let uu____3605 = FStar_ST.op_Bang fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____3605 in
     FStar_ST.op_Colon_Equals fresh_scope uu____3600);
    (let uu____3664 =
       let uu____3667 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3667
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.op_Colon_Equals bg_scope uu____3664)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____3711 =
       let uu____3716 = FStar_ST.op_Bang fresh_scope in
       FStar_List.tl uu____3716 in
     FStar_ST.op_Colon_Equals fresh_scope uu____3711);
    (let uu____3775 =
       let uu____3778 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3778
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.op_Colon_Equals bg_scope uu____3775)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___97_3829  ->
            match uu___97_3829 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____3830 -> ()));
    (let uu____3832 = FStar_ST.op_Bang fresh_scope in
     match uu____3832 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____3901 -> failwith "Impossible");
    (let uu____3906 =
       let uu____3909 = FStar_ST.op_Bang bg_scope in
       FStar_List.append uu____3909 decls in
     FStar_ST.op_Colon_Equals bg_scope uu____3906)
let refresh: Prims.unit -> Prims.unit =
  fun uu____3951  ->
    (let uu____3953 =
       let uu____3954 = FStar_Options.n_cores () in
       uu____3954 < (Prims.parse_int "2") in
     if uu____3953 then bg_z3_proc.refresh () else ());
    (let uu____3956 =
       let uu____3959 =
         let uu____3964 = FStar_ST.op_Bang fresh_scope in
         FStar_List.rev uu____3964 in
       FStar_List.flatten uu____3959 in
     FStar_ST.op_Colon_Equals bg_scope uu____3956)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____4028 = FStar_ST.op_Bang fresh_scope in
    match uu____4028 with
    | hd1::s::tl1 ->
        FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 s) ::
          tl1)
    | uu____4102 -> failwith "Impossible"
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____4116 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____4116 (FStar_String.concat "\n") in
    (let uu____4122 = FStar_Options.log_queries () in
     if uu____4122 then query_logging.write_to_log r else ());
    r
type z3result =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
type cb = z3result -> Prims.unit
let ask_1_core:
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
            let uu____4166 = FStar_ST.op_Bang bg_scope in
            FStar_List.append uu____4166
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____4187 = filter_theory theory in
          match uu____4187 with
          | (theory1,used_unsat_core) ->
              let input = mk_input theory1 in
              (FStar_ST.op_Colon_Equals bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb })
let ask_n_cores:
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
              let uu____4264 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.op_Colon_Equals bg_scope [];
                     (let uu____4295 = FStar_ST.op_Bang fresh_scope in
                      FStar_List.rev uu____4295)) in
              FStar_List.flatten uu____4264 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____4331 = filter_theory theory1 in
            match uu____4331 with
            | (theory2,used_unsat_core) ->
                let input = mk_input theory2 in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb }
let ask:
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
            let uu____4388 =
              let uu____4389 = FStar_Options.n_cores () in
              uu____4389 = (Prims.parse_int "1") in
            if uu____4388
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
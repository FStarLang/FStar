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
  fun uu___96_70  ->
    match uu___96_70 with
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
  fun uu____144  ->
    let prefix1 = "Z3 version " in
    let uu____146 = FStar_ST.read _z3version in
    match uu____146 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____152 =
          let uu____159 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____159 "-version" "" in
        (match uu____152 with
         | (uu____160,out,uu____162) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____165 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____169 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____169 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____184 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____188 -> Z3V_Unknown out)
               | uu____191 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (FStar_Pervasives_Native.Some out1);
              out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____200  ->
    let z3_v = get_z3version () in
    (let uu____203 =
       let uu____204 = get_z3version () in
       z3v_le uu____204
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____203
     then
       let uu____205 =
         let uu____206 =
           let uu____207 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____207 in
         FStar_Util.Failure uu____206 in
       FStar_All.pipe_left FStar_Pervasives.raise uu____205
     else ());
    (let uu____209 =
       let uu____212 =
         let uu____215 =
           let uu____218 =
             let uu____219 =
               let uu____220 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____220 in
             FStar_Util.format1 "smt.random_seed=%s" uu____219 in
           [uu____218] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____215 in
       let uu____221 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____212 uu____221 in
     FStar_String.concat " " uu____209)
type label = Prims.string
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
type z3status =
  | UNSAT of unsat_core
  | SAT of label Prims.list
  | UNKNOWN of label Prims.list
  | TIMEOUT of label Prims.list
  | KILLED
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____255 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____271 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____293 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____315 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____334 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___97_340  ->
    match uu___97_340 with
    | SAT uu____341 -> "sat"
    | UNSAT uu____344 -> "unsat"
    | UNKNOWN uu____345 -> "unknown"
    | TIMEOUT uu____348 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____354  ->
    let uu____355 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____355 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____368 = FStar_Options.z3_exe () in
    let uu____369 = ini_params () in
    FStar_Util.start_process id uu____368 uu____369 cond
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
    FStar_ST.write current_module_name (FStar_Pervasives_Native.Some n1) in
  let get_module_name uu____700 =
    let uu____701 = FStar_ST.read current_module_name in
    match uu____701 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____712 =
    let uu____713 = FStar_ST.read current_module_name in
    match uu____713 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____722 =
            let uu____729 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____751  ->
                 match uu____751 with | (m,uu____757) -> n1 = m) uu____729 in
          match uu____722 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____763 =
                  let uu____770 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____770 in
                FStar_ST.write used_file_names uu____763);
               n1)
          | FStar_Pervasives_Native.Some (uu____797,k) ->
              ((let uu____804 =
                  let uu____811 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____811 in
                FStar_ST.write used_file_names uu____804);
               (let uu____838 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____838)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (FStar_Pervasives_Native.Some fh); fh)) in
  let get_log_file uu____854 =
    let uu____855 = FStar_ST.read log_file_opt in
    match uu____855 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____867 = get_log_file () in
    FStar_Util.append_to_file uu____867 str in
  let write_to_new_log str =
    let dir_name =
      let uu____873 = FStar_ST.read current_file_name in
      match uu____873 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____881 = FStar_ST.read current_module_name in
            match uu____881 with
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
      | FStar_Pervasives_Native.Some n1 -> n1 in
    let qnum = FStar_ST.read query_number in
    (let uu____900 =
       let uu____901 = FStar_ST.read query_number in
       uu____901 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____900);
    (let file_name =
       let uu____907 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____907 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____913 =
      let uu____914 = FStar_Options.n_cores () in
      uu____914 > (Prims.parse_int "1") in
    if uu____913 then write_to_new_log str else append_to_log str in
  let close_log uu____919 =
    let uu____920 = FStar_ST.read log_file_opt in
    match uu____920 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.write log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____936 =
    let uu____937 = FStar_ST.read current_file_name in
    match uu____937 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____958  ->
      let uu____959 =
        let uu____960 =
          FStar_Util.incr ctr;
          (let uu____965 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____965 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____960 in
      new_z3proc uu____959 in
  let z3proc uu____971 =
    (let uu____973 =
       let uu____974 = FStar_ST.read the_z3proc in
       uu____974 = FStar_Pervasives_Native.None in
     if uu____973
     then
       let uu____983 =
         let uu____986 = new_proc () in
         FStar_Pervasives_Native.Some uu____986 in
       FStar_ST.write the_z3proc uu____983
     else ());
    (let uu____992 = FStar_ST.read the_z3proc in FStar_Util.must uu____992) in
  let x = [] in
  let grab uu____1005 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____1012 = FStar_Util.monitor_exit x in
  let refresh uu____1018 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____1022 =
       let uu____1025 = new_proc () in
       FStar_Pervasives_Native.Some uu____1025 in
     FStar_ST.write the_z3proc uu____1022);
    query_logging.close_log ();
    release () in
  let restart uu____1034 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc FStar_Pervasives_Native.None;
    (let uu____1043 =
       let uu____1046 = new_proc () in
       FStar_Pervasives_Native.Some uu____1046 in
     FStar_ST.write the_z3proc uu____1043);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____1054  ->
    let uu____1055 = FStar_Options.log_queries () in
    if uu____1055
    then
      let uu____1056 = query_logging.log_file_name () in
      Prims.strcat "@" uu____1056
    else ""
let doZ3Exe':
  Prims.bool ->
    Prims.string -> (z3status,z3statistics) FStar_Pervasives_Native.tuple2
  =
  fun fresh1  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string) in
        let get_data lines1 =
          let parse_core s =
            let s1 = FStar_Util.trim_string s in
            let s2 =
              FStar_Util.substring s1 (Prims.parse_int "1")
                ((FStar_String.length s1) - (Prims.parse_int "2")) in
            if FStar_Util.starts_with s2 "error"
            then FStar_Pervasives_Native.None
            else
              (let uu____1116 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____1116
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38)) in
          let core = FStar_Util.mk_ref FStar_Pervasives_Native.None in
          let statistics = FStar_Util.smap_create (Prims.parse_int "0") in
          let reason_unknown = FStar_Util.mk_ref "" in
          let in_core = FStar_Util.mk_ref false in
          let in_statistics = FStar_Util.mk_ref false in
          let in_reason_unknown = FStar_Util.mk_ref false in
          let parse line =
            match line with
            | "<unsat-core>" -> FStar_ST.write in_core true
            | "<statistics>" -> FStar_ST.write in_statistics true
            | "<reason-unknown>" -> FStar_ST.write in_reason_unknown true
            | "</unsat-core>" -> FStar_ST.write in_core false
            | "</statistics>" -> FStar_ST.write in_statistics false
            | "</reason-unknown>" -> FStar_ST.write in_reason_unknown false
            | uu____1173 ->
                let uu____1174 = FStar_ST.read in_core in
                if uu____1174
                then
                  let uu____1177 = parse_core line in
                  FStar_ST.write core uu____1177
                else
                  (let uu____1189 = FStar_ST.read in_statistics in
                   if uu____1189
                   then
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
                     | uu____1211 -> ()
                   else
                     (let uu____1215 = FStar_ST.read in_reason_unknown in
                      if uu____1215
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____1222::txt::uu____1224::[] -> txt
                          | uu____1225 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             (Prims.strcat "\"" (Prims.strcat rsn "\""))
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____1233 = FStar_ST.read core in
           let uu____1244 = FStar_ST.read reason_unknown in
           (uu____1233, statistics, uu____1244)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____1267 = lblnegs rest in lname :: uu____1267
          | lname::uu____1271::rest when
              FStar_Util.starts_with lname "label_" -> lblnegs rest
          | uu____1275 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____1295 = lblnegs tl1 in UNKNOWN uu____1295
          | "sat"::tl1 -> let uu____1301 = lblnegs tl1 in SAT uu____1301
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____1316 =
                  let uu____1317 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____1317 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____1316);
               result tl1 core)
          | uu____1318 ->
              let uu____1321 =
                let uu____1322 =
                  let uu____1323 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____1323 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____1322 in
              FStar_All.pipe_left failwith uu____1321 in
        let uu____1328 = get_data lines in
        match uu____1328 with
        | (core,statistics,reason_unknown) ->
            let uu____1354 = result lines core in (uu____1354, statistics) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____1364 = tid () in
          let uu____1365 = FStar_Options.z3_exe () in
          let uu____1366 = ini_params () in
          FStar_Util.launch_process uu____1364 uu____1365 uu____1366 input
            cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout1 = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout1) in
      parse (FStar_Util.trim_string stdout1)
let doZ3Exe:
  Prims.bool ->
    Prims.string -> (z3status,z3statistics) FStar_Pervasives_Native.tuple2
  = fun fresh1  -> fun input  -> doZ3Exe' fresh1 input
let z3_options: Prims.unit -> Prims.string =
  fun uu____1386  ->
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
type error_kind =
  | Timeout
  | Kill
  | Default
let uu___is_Timeout: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____1455 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1460 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1465 -> false
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3 job
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor:
  'Auu____1500 'Auu____1501 .
    'Auu____1501 -> (Prims.unit -> 'Auu____1500) -> 'Auu____1500
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
          ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                         FStar_Pervasives_Native.tuple2)
             FStar_Util.either,Prims.int,z3statistics)
            FStar_Pervasives_Native.tuple3
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____1547  ->
          let ekind uu___98_1565 =
            match uu___98_1565 with
            | TIMEOUT uu____1566 -> Timeout
            | SAT uu____1569 -> Default
            | UNKNOWN uu____1572 -> Default
            | KILLED  -> Kill
            | uu____1575 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1577 = doZ3Exe fresh1 input in
          match uu____1577 with
          | (status,statistics) ->
              let uu____1598 =
                let uu____1603 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1603 in
              (match uu____1598 with
               | (uu____1618,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1772 = FStar_Options.debug_any () in
                           if uu____1772
                           then
                             let uu____1773 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1773
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1815 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1854  ->
                                               match uu____1854 with
                                               | (m,uu____1866,uu____1867) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____1815 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1953 =
                             let uu____1974 =
                               let uu____1991 = ekind status in
                               (failing_assertions, uu____1991) in
                             FStar_Util.Inr uu____1974 in
                           (uu____1953, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____2044 = FStar_Options.debug_any () in
                           if uu____2044
                           then
                             let uu____2045 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____2045
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____2087 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____2126  ->
                                               match uu____2126 with
                                               | (m,uu____2138,uu____2139) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____2087 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____2225 =
                             let uu____2246 =
                               let uu____2263 = ekind status in
                               (failing_assertions, uu____2263) in
                             FStar_Util.Inr uu____2246 in
                           (uu____2225, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____2316 = FStar_Options.debug_any () in
                           if uu____2316
                           then
                             let uu____2317 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____2317
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____2359 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____2398  ->
                                               match uu____2398 with
                                               | (m,uu____2410,uu____2411) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____2359 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____2497 =
                             let uu____2518 =
                               let uu____2535 = ekind status in
                               (failing_assertions, uu____2535) in
                             FStar_Util.Inr uu____2518 in
                           (uu____2497, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____2593  ->
    let j =
      let uu____2595 = FStar_ST.read job_queue in
      match uu____2595 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____2620  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____2622  ->
    let uu____2623 = FStar_ST.read running in
    if uu____2623
    then
      let rec aux uu____2627 =
        FStar_Util.monitor_enter job_queue;
        (let uu____2633 = FStar_ST.read job_queue in
         match uu____2633 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____2644 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____2648 = j.job () in FStar_All.pipe_left j.callback uu____2648
let init: Prims.unit -> Prims.unit =
  fun uu____2708  ->
    FStar_ST.write running true;
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
    (let uu____2728 =
       let uu____2731 = FStar_ST.read job_queue in
       FStar_List.append uu____2731 [j] in
     FStar_ST.write job_queue uu____2728);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____2750  ->
    let rec aux uu____2754 =
      let uu____2755 =
        with_monitor job_queue
          (fun uu____2771  ->
             let uu____2772 = FStar_ST.read pending_jobs in
             let uu____2773 =
               let uu____2774 = FStar_ST.read job_queue in
               FStar_List.length uu____2774 in
             (uu____2772, uu____2773)) in
      match uu____2755 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.write running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let mk_fresh_scope: Prims.unit -> scope_t =
  fun uu____2813  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2830 =
       let uu____2835 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____2835 in
     FStar_ST.write fresh_scope uu____2830);
    (let uu____2850 =
       let uu____2853 = FStar_ST.read bg_scope in
       FStar_List.append uu____2853
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____2850)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2865 =
       let uu____2870 = FStar_ST.read fresh_scope in FStar_List.tl uu____2870 in
     FStar_ST.write fresh_scope uu____2865);
    (let uu____2885 =
       let uu____2888 = FStar_ST.read bg_scope in
       FStar_List.append uu____2888
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____2885)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___99_2907  ->
            match uu___99_2907 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____2908 -> ()));
    (let uu____2910 = FStar_ST.read fresh_scope in
     match uu____2910 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____2935 -> failwith "Impossible");
    (let uu____2940 =
       let uu____2943 = FStar_ST.read bg_scope in
       FStar_List.append uu____2943 decls in
     FStar_ST.write bg_scope uu____2940)
let refresh: Prims.unit -> Prims.unit =
  fun uu____2953  ->
    (let uu____2955 =
       let uu____2956 = FStar_Options.n_cores () in
       uu____2956 < (Prims.parse_int "2") in
     if uu____2955 then bg_z3_proc.refresh () else ());
    (let uu____2958 =
       let uu____2961 =
         let uu____2966 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____2966 in
       FStar_List.flatten uu____2961 in
     FStar_ST.write bg_scope uu____2958)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____2992 = FStar_ST.read fresh_scope in
    match uu____2992 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____3022 -> failwith "Impossible"
let mk_cb:
  'Auu____3045 'Auu____3046 'Auu____3047 'Auu____3048 'Auu____3049
    'Auu____3050 .
    Prims.bool ->
      ((('Auu____3050,('Auu____3049 Prims.list,'Auu____3048)
                        FStar_Pervasives_Native.tuple2)
          FStar_Util.either,'Auu____3047,'Auu____3046)
         FStar_Pervasives_Native.tuple3 -> 'Auu____3045)
        ->
        (('Auu____3050,('Auu____3049 Prims.list,'Auu____3048)
                         FStar_Pervasives_Native.tuple2)
           FStar_Util.either,'Auu____3047,'Auu____3046)
          FStar_Pervasives_Native.tuple3 -> 'Auu____3045
  =
  fun used_unsat_core  ->
    fun cb  ->
      fun uu____3097  ->
        match uu____3097 with
        | (uc_errs,time,statistics) ->
            if used_unsat_core
            then
              (match uc_errs with
               | FStar_Util.Inl uu____3155 -> cb (uc_errs, time, statistics)
               | FStar_Util.Inr (uu____3172,ek) ->
                   cb ((FStar_Util.Inr ([], ek)), time, statistics))
            else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____3222 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____3222 (FStar_String.concat "\n") in
    (let uu____3228 = FStar_Options.log_queries () in
     if uu____3228 then query_logging.write_to_log r else ());
    r
type z3result =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3
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
            let uu____3280 = FStar_ST.read bg_scope in
            FStar_List.append uu____3280
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____3285 = filter_theory theory in
          match uu____3285 with
          | (theory1,used_unsat_core) ->
              let cb1 = mk_cb used_unsat_core cb in
              let input = mk_input theory1 in
              (FStar_ST.write bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb1
                 })
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
              let uu____3373 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____3388 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____3388)) in
              FStar_List.flatten uu____3373 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____3402 = filter_theory theory1 in
            match uu____3402 with
            | (theory2,used_unsat_core) ->
                let cb1 = mk_cb used_unsat_core cb in
                let input = mk_input theory2 in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb1
                  }
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
            let uu____3486 =
              let uu____3487 = FStar_Options.n_cores () in
              uu____3487 = (Prims.parse_int "1") in
            if uu____3486
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
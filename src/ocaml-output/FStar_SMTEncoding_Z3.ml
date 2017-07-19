open Prims
type z3version =
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
let uu___is_Z3V_Unknown: z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____19 -> false
let __proj__Z3V_Unknown__item___0: z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let uu___is_Z3V: z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____37 -> false
let __proj__Z3V__item___0:
  z3version -> (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Z3V _0 -> _0
let z3version_as_string: z3version -> Prims.string =
  fun uu___94_65  ->
    match uu___94_65 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____70 = FStar_Util.string_of_int i in
        let uu____71 = FStar_Util.string_of_int j in
        let uu____72 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____70 uu____71 uu____72
let z3v_compare:
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.int FStar_Pervasives_Native.option
  =
  fun known  ->
    fun uu____86  ->
      match uu____86 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____100 -> FStar_Pervasives_Native.None
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
  fun uu____134  ->
    let prefix1 = "Z3 version " in
    let uu____136 = FStar_ST.read _z3version in
    match uu____136 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____142 =
          let uu____149 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____149 "-version" "" in
        (match uu____142 with
         | (uu____150,out,uu____152) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____155 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____159 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____159 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____171 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____175 -> Z3V_Unknown out)
               | uu____178 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (FStar_Pervasives_Native.Some out1);
              out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____186  ->
    let z3_v = get_z3version () in
    (let uu____189 =
       let uu____190 = get_z3version () in
       z3v_le uu____190
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____189
     then
       let uu____191 =
         let uu____192 =
           let uu____193 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____193 in
         FStar_Util.Failure uu____192 in
       FStar_All.pipe_left FStar_Pervasives.raise uu____191
     else ());
    (let uu____195 =
       let uu____198 =
         let uu____201 =
           let uu____204 =
             let uu____205 =
               let uu____206 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____206 in
             FStar_Util.format1 "smt.random_seed=%s" uu____205 in
           [uu____204] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____201 in
       let uu____207 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____198 uu____207 in
     FStar_String.concat " " uu____195)
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
    match projectee with | UNSAT _0 -> true | uu____240 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____254 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____274 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____294 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____311 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___95_316  ->
    match uu___95_316 with
    | SAT uu____317 -> "sat"
    | UNSAT uu____320 -> "unsat"
    | UNKNOWN uu____321 -> "unknown"
    | TIMEOUT uu____324 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____329  ->
    let uu____330 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____330 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____342 = FStar_Options.z3_exe () in
    let uu____343 = ini_params () in
    FStar_Util.start_process id uu____342 uu____343 cond
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc;
  release: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;
  restart: Prims.unit -> Prims.unit;}
type query_log =
  {
  get_module_name: Prims.unit -> Prims.string;
  set_module_name: Prims.string -> Prims.unit;
  write_to_log: Prims.string -> Prims.unit;
  close_log: Prims.unit -> Prims.unit;
  log_file_name: Prims.unit -> Prims.string;}
let query_logging: query_log =
  let query_number = FStar_Util.mk_ref (Prims.parse_int "0") in
  let log_file_opt = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let current_file_name = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let set_module_name n1 =
    FStar_ST.write current_module_name (FStar_Pervasives_Native.Some n1) in
  let get_module_name uu____542 =
    let uu____543 = FStar_ST.read current_module_name in
    match uu____543 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  let new_log_file uu____554 =
    let uu____555 = FStar_ST.read current_module_name in
    match uu____555 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____564 =
            let uu____571 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____590  ->
                 match uu____590 with | (m,uu____596) -> n1 = m) uu____571 in
          match uu____564 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____602 =
                  let uu____609 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____609 in
                FStar_ST.write used_file_names uu____602);
               n1)
          | FStar_Pervasives_Native.Some (uu____636,k) ->
              ((let uu____643 =
                  let uu____650 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____650 in
                FStar_ST.write used_file_names uu____643);
               (let uu____677 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____677)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (FStar_Pervasives_Native.Some fh); fh)) in
  let get_log_file uu____693 =
    let uu____694 = FStar_ST.read log_file_opt in
    match uu____694 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh in
  let append_to_log str =
    let uu____706 = get_log_file () in
    FStar_Util.append_to_file uu____706 str in
  let write_to_new_log str =
    let dir_name =
      let uu____712 = FStar_ST.read current_file_name in
      match uu____712 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____720 = FStar_ST.read current_module_name in
            match uu____720 with
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
    (let uu____739 =
       let uu____740 = FStar_ST.read query_number in
       uu____740 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____739);
    (let file_name =
       let uu____746 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____746 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____752 =
      let uu____753 = FStar_Options.n_cores () in
      uu____753 > (Prims.parse_int "1") in
    if uu____752 then write_to_new_log str else append_to_log str in
  let close_log uu____758 =
    let uu____759 = FStar_ST.read log_file_opt in
    match uu____759 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.write log_file_opt FStar_Pervasives_Native.None) in
  let log_file_name uu____775 =
    let uu____776 = FStar_ST.read current_file_name in
    match uu____776 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____797  ->
      let uu____798 =
        let uu____799 =
          FStar_Util.incr ctr;
          (let uu____804 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____804 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____799 in
      new_z3proc uu____798 in
  let z3proc uu____810 =
    (let uu____812 =
       let uu____813 = FStar_ST.read the_z3proc in
       uu____813 = FStar_Pervasives_Native.None in
     if uu____812
     then
       let uu____822 =
         let uu____825 = new_proc () in
         FStar_Pervasives_Native.Some uu____825 in
       FStar_ST.write the_z3proc uu____822
     else ());
    (let uu____831 = FStar_ST.read the_z3proc in FStar_Util.must uu____831) in
  let x = [] in
  let grab uu____844 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____851 = FStar_Util.monitor_exit x in
  let refresh uu____857 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____861 =
       let uu____864 = new_proc () in FStar_Pervasives_Native.Some uu____864 in
     FStar_ST.write the_z3proc uu____861);
    query_logging.close_log ();
    release () in
  let restart uu____873 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc FStar_Pervasives_Native.None;
    (let uu____882 =
       let uu____885 = new_proc () in FStar_Pervasives_Native.Some uu____885 in
     FStar_ST.write the_z3proc uu____882);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____892  ->
    let uu____893 = FStar_Options.log_queries () in
    if uu____893
    then
      let uu____894 = query_logging.log_file_name () in
      Prims.strcat "@" uu____894
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
              (let uu____952 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____952
                 (fun _0_28  -> FStar_Pervasives_Native.Some _0_28)) in
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
            | uu____1009 ->
                let uu____1010 = FStar_ST.read in_core in
                if uu____1010
                then
                  let uu____1013 = parse_core line in
                  FStar_ST.write core uu____1013
                else
                  (let uu____1025 = FStar_ST.read in_statistics in
                   if uu____1025
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
                     | uu____1047 -> ()
                   else
                     (let uu____1051 = FStar_ST.read in_reason_unknown in
                      if uu____1051
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____1058::txt::uu____1060::[] -> txt
                          | uu____1061 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             (Prims.strcat "\"" (Prims.strcat rsn "\""))
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____1068 = FStar_ST.read core in
           let uu____1079 = FStar_ST.read reason_unknown in
           (uu____1068, statistics, uu____1079)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____1102 = lblnegs rest in lname :: uu____1102
          | lname::uu____1106::rest when
              FStar_Util.starts_with lname "label_" -> lblnegs rest
          | uu____1110 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____1130 = lblnegs tl1 in UNKNOWN uu____1130
          | "sat"::tl1 -> let uu____1136 = lblnegs tl1 in SAT uu____1136
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____1151 =
                  let uu____1152 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____1152 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____1151);
               result tl1 core)
          | uu____1153 ->
              let uu____1156 =
                let uu____1157 =
                  let uu____1158 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____1158 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____1157 in
              FStar_All.pipe_left failwith uu____1156 in
        let uu____1162 = get_data lines in
        match uu____1162 with
        | (core,statistics,reason_unknown) ->
            let uu____1188 = result lines core in (uu____1188, statistics) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____1198 = tid () in
          let uu____1199 = FStar_Options.z3_exe () in
          let uu____1200 = ini_params () in
          FStar_Util.launch_process uu____1198 uu____1199 uu____1200 input
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
  fun uu____1217  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
type error_kind =
  | Timeout
  | Kill
  | Default
let uu___is_Timeout: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____1277 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1281 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1285 -> false
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3 job
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor m f =
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
        fun uu____1359  ->
          let ekind uu___96_1377 =
            match uu___96_1377 with
            | TIMEOUT uu____1378 -> Timeout
            | SAT uu____1381 -> Default
            | UNKNOWN uu____1384 -> Default
            | KILLED  -> Kill
            | uu____1387 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1389 = doZ3Exe fresh1 input in
          match uu____1389 with
          | (status,statistics) ->
              let uu____1410 =
                let uu____1415 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1415 in
              (match uu____1410 with
               | (uu____1430,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1584 = FStar_Options.debug_any () in
                           if uu____1584
                           then
                             let uu____1585 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1585
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1625 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1660  ->
                                               match uu____1660 with
                                               | (m,uu____1672,uu____1673) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____1625 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1759 =
                             let uu____1780 =
                               let uu____1797 = ekind status in
                               (failing_assertions, uu____1797) in
                             FStar_Util.Inr uu____1780 in
                           (uu____1759, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____1850 = FStar_Options.debug_any () in
                           if uu____1850
                           then
                             let uu____1851 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1851
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1891 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1926  ->
                                               match uu____1926 with
                                               | (m,uu____1938,uu____1939) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____1891 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____2025 =
                             let uu____2046 =
                               let uu____2063 = ekind status in
                               (failing_assertions, uu____2063) in
                             FStar_Util.Inr uu____2046 in
                           (uu____2025, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____2116 = FStar_Options.debug_any () in
                           if uu____2116
                           then
                             let uu____2117 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____2117
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____2157 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____2192  ->
                                               match uu____2192 with
                                               | (m,uu____2204,uu____2205) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l)) in
                                     match uu____2157 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____2291 =
                             let uu____2312 =
                               let uu____2329 = ekind status in
                               (failing_assertions, uu____2329) in
                             FStar_Util.Inr uu____2312 in
                           (uu____2291, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____2387  ->
    let j =
      let uu____2389 = FStar_ST.read job_queue in
      match uu____2389 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____2413  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____2415  ->
    let uu____2416 = FStar_ST.read running in
    if uu____2416
    then
      let rec aux uu____2420 =
        FStar_Util.monitor_enter job_queue;
        (let uu____2426 = FStar_ST.read job_queue in
         match uu____2426 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____2437 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____2441 = j.job () in FStar_All.pipe_left j.callback uu____2441
let init: Prims.unit -> Prims.unit =
  fun uu____2500  ->
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
    (let uu____2519 =
       let uu____2522 = FStar_ST.read job_queue in
       FStar_List.append uu____2522 [j] in
     FStar_ST.write job_queue uu____2519);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____2540  ->
    let rec aux uu____2544 =
      let uu____2545 =
        with_monitor job_queue
          (fun uu____2558  ->
             let uu____2559 = FStar_ST.read pending_jobs in
             let uu____2560 =
               let uu____2561 = FStar_ST.read job_queue in
               FStar_List.length uu____2561 in
             (uu____2559, uu____2560)) in
      match uu____2545 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.write running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let mk_fresh_scope:
  Prims.unit -> FStar_SMTEncoding_Term.decl Prims.list Prims.list =
  fun uu____2595  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2611 =
       let uu____2616 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____2616 in
     FStar_ST.write fresh_scope uu____2611);
    (let uu____2631 =
       let uu____2634 = FStar_ST.read bg_scope in
       FStar_List.append uu____2634
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____2631)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2645 =
       let uu____2650 = FStar_ST.read fresh_scope in FStar_List.tl uu____2650 in
     FStar_ST.write fresh_scope uu____2645);
    (let uu____2665 =
       let uu____2668 = FStar_ST.read bg_scope in
       FStar_List.append uu____2668
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____2665)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___97_2685  ->
            match uu___97_2685 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____2686 -> ()));
    (let uu____2688 = FStar_ST.read fresh_scope in
     match uu____2688 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____2713 -> failwith "Impossible");
    (let uu____2718 =
       let uu____2721 = FStar_ST.read bg_scope in
       FStar_List.append uu____2721 decls in
     FStar_ST.write bg_scope uu____2718)
let refresh: Prims.unit -> Prims.unit =
  fun uu____2730  ->
    (let uu____2732 =
       let uu____2733 = FStar_Options.n_cores () in
       uu____2733 < (Prims.parse_int "2") in
     if uu____2732 then bg_z3_proc.refresh () else ());
    (let uu____2735 =
       let uu____2738 =
         let uu____2743 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____2743 in
       FStar_List.flatten uu____2738 in
     FStar_ST.write bg_scope uu____2735)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____2766 = FStar_ST.read fresh_scope in
    match uu____2766 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____2796 -> failwith "Impossible"
let mk_cb used_unsat_core cb uu____2862 =
  match uu____2862 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____2920 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____2937,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____2986 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____2986 (FStar_String.concat "\n") in
    (let uu____2992 = FStar_Options.log_queries () in
     if uu____2992 then query_logging.write_to_log r else ());
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
            let uu____3040 = FStar_ST.read bg_scope in
            FStar_List.append uu____3040
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____3045 = filter_theory theory in
          match uu____3045 with
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
              let uu____3128 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____3143 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____3143)) in
              FStar_List.flatten uu____3128 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____3157 = filter_theory theory1 in
            match uu____3157 with
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
      FStar_SMTEncoding_Term.decls_t ->
        scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
  fun filter1  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let uu____3236 =
              let uu____3237 = FStar_Options.n_cores () in
              uu____3237 = (Prims.parse_int "1") in
            if uu____3236
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
open Prims
type z3version =
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int* Prims.int* Prims.int)
let uu___is_Z3V_Unknown: z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____17 -> false
let __proj__Z3V_Unknown__item___0: z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let uu___is_Z3V: z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____34 -> false
let __proj__Z3V__item___0: z3version -> (Prims.int* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Z3V _0 -> _0
let z3version_as_string: z3version -> Prims.string =
  fun uu___95_55  ->
    match uu___95_55 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____60 = FStar_Util.string_of_int i in
        let uu____61 = FStar_Util.string_of_int j in
        let uu____62 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____60 uu____61 uu____62
let z3v_compare:
  z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.int option =
  fun known  ->
    fun uu____74  ->
      match uu____74 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____83 -> None
           | Z3V (k1,k2,k3) ->
               Some
                 (if k1 <> w1
                  then w1 - k1
                  else if k2 <> w2 then w2 - k2 else w3 - k3))
let z3v_le: z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.bool =
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | None  -> false
      | Some i -> i >= (Prims.parse_int "0")
let _z3version: z3version option FStar_ST.ref = FStar_Util.mk_ref None
let get_z3version: Prims.unit -> z3version =
  fun uu____112  ->
    let prefix1 = "Z3 version " in
    let uu____114 = FStar_ST.read _z3version in
    match uu____114 with
    | Some version -> version
    | None  ->
        let uu____120 =
          let uu____124 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____124 "-version" "" in
        (match uu____120 with
         | (uu____125,out,uu____127) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____130 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____133 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____133 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____145 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____149 -> Z3V_Unknown out)
               | uu____151 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (Some out1); out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____160  ->
    let z3_v = get_z3version () in
    (let uu____163 =
       let uu____164 = get_z3version () in
       z3v_le uu____164
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____163
     then
       let uu____165 =
         let uu____166 =
           let uu____167 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____167 in
         FStar_Util.Failure uu____166 in
       FStar_All.pipe_left FStar_Pervasives.raise uu____165
     else ());
    (let uu____169 =
       let uu____171 =
         let uu____173 =
           let uu____175 =
             let uu____176 =
               let uu____177 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____177 in
             FStar_Util.format1 "smt.random_seed=%s" uu____176 in
           [uu____175] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____173 in
       let uu____178 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____171 uu____178 in
     FStar_String.concat " " uu____169)
type label = Prims.string
type unsat_core = Prims.string Prims.list option
type z3status =
  | UNSAT of unsat_core
  | SAT of label Prims.list
  | UNKNOWN of label Prims.list
  | TIMEOUT of label Prims.list
  | KILLED
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____206 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____221 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____239 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____257 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____273 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___96_278  ->
    match uu___96_278 with
    | SAT uu____279 -> "sat"
    | UNSAT uu____281 -> "unsat"
    | UNKNOWN uu____282 -> "unknown"
    | TIMEOUT uu____284 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____289  ->
    let uu____290 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____290 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____303 = FStar_Options.z3_exe () in
    let uu____304 = ini_params () in
    FStar_Util.start_process id uu____303 uu____304 cond
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
  let log_file_opt = FStar_Util.mk_ref None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref None in
  let current_file_name = FStar_Util.mk_ref None in
  let set_module_name n1 = FStar_ST.write current_module_name (Some n1) in
  let get_module_name uu____506 =
    let uu____507 = FStar_ST.read current_module_name in
    match uu____507 with
    | None  -> failwith "Module name not set"
    | Some n1 -> n1 in
  let new_log_file uu____516 =
    let uu____517 = FStar_ST.read current_module_name in
    match uu____517 with
    | None  -> failwith "current module not set"
    | Some n1 ->
        let file_name =
          let uu____524 =
            let uu____528 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____539  ->
                 match uu____539 with | (m,uu____543) -> n1 = m) uu____528 in
          match uu____524 with
          | None  ->
              ((let uu____547 =
                  let uu____551 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____551 in
                FStar_ST.write used_file_names uu____547);
               n1)
          | Some (uu____567,k) ->
              ((let uu____572 =
                  let uu____576 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____576 in
                FStar_ST.write used_file_names uu____572);
               (let uu____592 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____592)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name (Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (Some fh); fh)) in
  let get_log_file uu____606 =
    let uu____607 = FStar_ST.read log_file_opt in
    match uu____607 with | None  -> new_log_file () | Some fh -> fh in
  let append_to_log str =
    let uu____617 = get_log_file () in
    FStar_Util.append_to_file uu____617 str in
  let write_to_new_log str =
    let dir_name =
      let uu____623 = FStar_ST.read current_file_name in
      match uu____623 with
      | None  ->
          let dir_name =
            let uu____629 = FStar_ST.read current_module_name in
            match uu____629 with
            | None  -> failwith "current module not set"
            | Some n1 -> FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n1 -> n1 in
    let qnum = FStar_ST.read query_number in
    (let uu____645 =
       let uu____646 = FStar_ST.read query_number in
       uu____646 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____645);
    (let file_name =
       let uu____652 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____652 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____658 =
      let uu____659 = FStar_Options.n_cores () in
      uu____659 > (Prims.parse_int "1") in
    if uu____658 then write_to_new_log str else append_to_log str in
  let close_log uu____664 =
    let uu____665 = FStar_ST.read log_file_opt in
    match uu____665 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None) in
  let log_file_name uu____678 =
    let uu____679 = FStar_ST.read current_file_name in
    match uu____679 with | None  -> failwith "no log file" | Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____696  ->
      let uu____697 =
        let uu____698 =
          FStar_Util.incr ctr;
          (let uu____703 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____703 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____698 in
      new_z3proc uu____697 in
  let z3proc uu____709 =
    (let uu____711 =
       let uu____712 = FStar_ST.read the_z3proc in uu____712 = None in
     if uu____711
     then
       let uu____718 = let uu____720 = new_proc () in Some uu____720 in
       FStar_ST.write the_z3proc uu____718
     else ());
    (let uu____725 = FStar_ST.read the_z3proc in FStar_Util.must uu____725) in
  let x = [] in
  let grab uu____735 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____741 = FStar_Util.monitor_exit x in
  let refresh uu____746 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____750 = let uu____752 = new_proc () in Some uu____752 in
     FStar_ST.write the_z3proc uu____750);
    query_logging.close_log ();
    release () in
  let restart uu____760 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let uu____768 = let uu____770 = new_proc () in Some uu____770 in
     FStar_ST.write the_z3proc uu____768);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____777  ->
    let uu____778 = FStar_Options.log_queries () in
    if uu____778
    then
      let uu____779 = query_logging.log_file_name () in
      Prims.strcat "@" uu____779
    else ""
let doZ3Exe': Prims.bool -> Prims.string -> (z3status* z3statistics) =
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
            then None
            else
              (let uu____828 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____828 (fun _0_38  -> Some _0_38)) in
          let core = FStar_Util.mk_ref None in
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
            | uu____873 ->
                let uu____874 = FStar_ST.read in_core in
                if uu____874
                then
                  let uu____877 = parse_core line in
                  FStar_ST.write core uu____877
                else
                  (let uu____885 = FStar_ST.read in_statistics in
                   if uu____885
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
                     | uu____928 -> ()
                   else
                     (let uu____931 = FStar_ST.read in_reason_unknown in
                      if uu____931
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____937::txt::uu____939::[] -> txt
                          | uu____940 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             rsn
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____946 = FStar_ST.read core in
           let uu____953 = FStar_ST.read reason_unknown in
           (uu____946, statistics, uu____953)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____969 = lblnegs rest in lname :: uu____969
          | lname::uu____972::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest
          | uu____975 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____990 = lblnegs tl1 in UNKNOWN uu____990
          | "sat"::tl1 -> let uu____994 = lblnegs tl1 in SAT uu____994
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____1005 =
                  let uu____1006 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____1006 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____1005);
               result tl1 core)
          | uu____1007 ->
              let uu____1009 =
                let uu____1010 =
                  let uu____1011 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____1011 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____1010 in
              FStar_All.pipe_left failwith uu____1009 in
        let uu____1014 = get_data lines in
        match uu____1014 with
        | (core,statistics,reason_unknown) ->
            let uu____1029 = result lines core in (uu____1029, statistics) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____1039 = tid () in
          let uu____1040 = FStar_Options.z3_exe () in
          let uu____1041 = ini_params () in
          FStar_Util.launch_process uu____1039 uu____1040 uu____1041 input
            cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout1 = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout1) in
      parse (FStar_Util.trim_string stdout1)
let doZ3Exe: Prims.bool -> Prims.string -> (z3status* z3statistics) =
  fun fresh1  -> fun input  -> doZ3Exe' fresh1 input
let z3_options: Prims.unit -> Prims.string =
  fun uu____1059  ->
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
    match projectee with | Timeout  -> true | uu____1121 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1126 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1131 -> false
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
    FStar_Util.either* Prims.int* z3statistics) job
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
          ((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
            FStar_Util.either* Prims.int* z3statistics)
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____1196  ->
          let ekind uu___97_1207 =
            match uu___97_1207 with
            | TIMEOUT uu____1208 -> Timeout
            | SAT uu____1210 -> Default
            | UNKNOWN uu____1212 -> Default
            | KILLED  -> Kill
            | uu____1214 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1216 = doZ3Exe fresh1 input in
          match uu____1216 with
          | (status,statistics) ->
              let uu____1228 =
                let uu____1231 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1231 in
              (match uu____1228 with
               | (uu____1239,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1319 = FStar_Options.debug_any () in
                           if uu____1319
                           then
                             let uu____1320 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1320
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1342 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1360  ->
                                               match uu____1360 with
                                               | (m,uu____1367,uu____1368) ->
                                                   (fst m) = l)) in
                                     match uu____1342 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1413 =
                             let uu____1424 =
                               let uu____1433 = ekind status in
                               (failing_assertions, uu____1433) in
                             FStar_Util.Inr uu____1424 in
                           (uu____1413, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____1461 = FStar_Options.debug_any () in
                           if uu____1461
                           then
                             let uu____1462 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1462
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1484 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1502  ->
                                               match uu____1502 with
                                               | (m,uu____1509,uu____1510) ->
                                                   (fst m) = l)) in
                                     match uu____1484 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1555 =
                             let uu____1566 =
                               let uu____1575 = ekind status in
                               (failing_assertions, uu____1575) in
                             FStar_Util.Inr uu____1566 in
                           (uu____1555, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____1603 = FStar_Options.debug_any () in
                           if uu____1603
                           then
                             let uu____1604 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1604
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1626 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1644  ->
                                               match uu____1644 with
                                               | (m,uu____1651,uu____1652) ->
                                                   (fst m) = l)) in
                                     match uu____1626 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1697 =
                             let uu____1708 =
                               let uu____1717 = ekind status in
                               (failing_assertions, uu____1717) in
                             FStar_Util.Inr uu____1708 in
                           (uu____1697, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____1751  ->
    let j =
      let uu____1753 = FStar_ST.read job_queue in
      match uu____1753 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1780  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____1785  ->
    let uu____1786 = FStar_ST.read running in
    if uu____1786
    then
      let rec aux uu____1792 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1798 = FStar_ST.read job_queue in
         match uu____1798 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1809 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____1812 = j.job () in FStar_All.pipe_left j.callback uu____1812
let init: Prims.unit -> Prims.unit =
  fun uu____1844  ->
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
    (let uu____1866 =
       let uu____1868 = FStar_ST.read job_queue in
       FStar_List.append uu____1868 [j] in
     FStar_ST.write job_queue uu____1866);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____1888  ->
    let rec aux uu____1892 =
      let uu____1893 =
        with_monitor job_queue
          (fun uu____1902  ->
             let uu____1903 = FStar_ST.read pending_jobs in
             let uu____1906 =
               let uu____1907 = FStar_ST.read job_queue in
               FStar_List.length uu____1907 in
             (uu____1903, uu____1906)) in
      match uu____1893 with
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
  fun uu____1942  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1957 =
       let uu____1960 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____1960 in
     FStar_ST.write fresh_scope uu____1957);
    (let uu____1972 =
       let uu____1974 = FStar_ST.read bg_scope in
       FStar_List.append uu____1974
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____1972)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1987 =
       let uu____1990 = FStar_ST.read fresh_scope in FStar_List.tl uu____1990 in
     FStar_ST.write fresh_scope uu____1987);
    (let uu____2002 =
       let uu____2004 = FStar_ST.read bg_scope in
       FStar_List.append uu____2004
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____2002)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___98_2020  ->
            match uu___98_2020 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____2021 -> ()));
    (let uu____2023 = FStar_ST.read fresh_scope in
     match uu____2023 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____2041 -> failwith "Impossible");
    (let uu____2044 =
       let uu____2046 = FStar_ST.read bg_scope in
       FStar_List.append uu____2046 decls in
     FStar_ST.write bg_scope uu____2044)
let refresh: Prims.unit -> Prims.unit =
  fun uu____2057  ->
    (let uu____2059 =
       let uu____2060 = FStar_Options.n_cores () in
       uu____2060 < (Prims.parse_int "2") in
     if uu____2059 then bg_z3_proc.refresh () else ());
    (let uu____2062 =
       let uu____2064 =
         let uu____2067 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____2067 in
       FStar_List.flatten uu____2064 in
     FStar_ST.write bg_scope uu____2062)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____2091 = FStar_ST.read fresh_scope in
    match uu____2091 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____2112 -> failwith "Impossible"
let mk_cb used_unsat_core cb uu____2169 =
  match uu____2169 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____2201 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____2210,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____2239 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____2239 (FStar_String.concat "\n") in
    (let uu____2243 = FStar_Options.log_queries () in
     if uu____2243 then query_logging.write_to_log r else ());
    r
type z3result =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
    FStar_Util.either* Prims.int* z3statistics)
type cb = z3result -> Prims.unit
let ask_1_core:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t* Prims.bool))
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun cb  ->
          let theory =
            let uu____2283 = FStar_ST.read bg_scope in
            FStar_List.append uu____2283
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____2288 = filter_theory theory in
          match uu____2288 with
          | (theory1,used_unsat_core) ->
              let cb1 = mk_cb used_unsat_core cb in
              let input = mk_input theory1 in
              (FStar_ST.write bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb1
                 })
let ask_n_cores:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t* Prims.bool))
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t -> scope_t option -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let theory =
              let uu____2353 =
                match scope with
                | Some s -> FStar_List.rev s
                | None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____2364 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____2364)) in
              FStar_List.flatten uu____2353 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____2374 = filter_theory theory1 in
            match uu____2374 with
            | (theory2,used_unsat_core) ->
                let cb1 = mk_cb used_unsat_core cb in
                let input = mk_input theory2 in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb1
                  }
let ask:
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t* Prims.bool))
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t -> scope_t option -> cb -> Prims.unit
  =
  fun filter1  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let uu____2434 =
              let uu____2435 = FStar_Options.n_cores () in
              uu____2435 = (Prims.parse_int "1") in
            if uu____2434
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
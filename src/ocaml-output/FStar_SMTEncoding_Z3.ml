open Prims
type z3version =
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int* Prims.int* Prims.int)
let uu___is_Z3V_Unknown: z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____14 -> false
let __proj__Z3V_Unknown__item___0: z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let uu___is_Z3V: z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____29 -> false
let __proj__Z3V__item___0: z3version -> (Prims.int* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Z3V _0 -> _0
let z3version_as_string: z3version -> Prims.string =
  fun uu___95_48  ->
    match uu___95_48 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____53 = FStar_Util.string_of_int i in
        let uu____54 = FStar_Util.string_of_int j in
        let uu____55 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____53 uu____54 uu____55
let z3v_compare:
  z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.int option =
  fun known  ->
    fun uu____65  ->
      match uu____65 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____74 -> None
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
  fun uu____100  ->
    let prefix1 = "Z3 version " in
    let uu____102 = FStar_ST.read _z3version in
    match uu____102 with
    | Some version -> version
    | None  ->
        let uu____108 =
          let uu____112 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____112 "-version" "" in
        (match uu____108 with
         | (uu____113,out,uu____115) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____118 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____121 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____121 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____133 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____137 -> Z3V_Unknown out)
               | uu____139 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (Some out1); out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____147  ->
    let z3_v = get_z3version () in
    (let uu____150 =
       let uu____151 = get_z3version () in
       z3v_le uu____151
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____150
     then
       let uu____152 =
         let uu____153 =
           let uu____154 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____154 in
         FStar_Util.Failure uu____153 in
       FStar_All.pipe_left FStar_Pervasives.raise uu____152
     else ());
    (let uu____156 =
       let uu____158 =
         let uu____160 =
           let uu____162 =
             let uu____163 =
               let uu____164 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____164 in
             FStar_Util.format1 "smt.random_seed=%s" uu____163 in
           [uu____162] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____160 in
       let uu____165 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____158 uu____165 in
     FStar_String.concat " " uu____156)
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
    match projectee with | UNSAT _0 -> true | uu____188 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____201 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____217 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____233 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____247 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___96_251  ->
    match uu___96_251 with
    | SAT uu____252 -> "sat"
    | UNSAT uu____254 -> "unsat"
    | UNKNOWN uu____255 -> "unknown"
    | TIMEOUT uu____257 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____261  ->
    let uu____262 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____262 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____274 = FStar_Options.z3_exe () in
    let uu____275 = ini_params () in
    FStar_Util.start_process id uu____274 uu____275 cond
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
  let get_module_name uu____441 =
    let uu____442 = FStar_ST.read current_module_name in
    match uu____442 with
    | None  -> failwith "Module name not set"
    | Some n1 -> n1 in
  let new_log_file uu____451 =
    let uu____452 = FStar_ST.read current_module_name in
    match uu____452 with
    | None  -> failwith "current module not set"
    | Some n1 ->
        let file_name =
          let uu____459 =
            let uu____463 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____474  ->
                 match uu____474 with | (m,uu____478) -> n1 = m) uu____463 in
          match uu____459 with
          | None  ->
              ((let uu____482 =
                  let uu____486 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____486 in
                FStar_ST.write used_file_names uu____482);
               n1)
          | Some (uu____502,k) ->
              ((let uu____507 =
                  let uu____511 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____511 in
                FStar_ST.write used_file_names uu____507);
               (let uu____527 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____527)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name (Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (Some fh); fh)) in
  let get_log_file uu____541 =
    let uu____542 = FStar_ST.read log_file_opt in
    match uu____542 with | None  -> new_log_file () | Some fh -> fh in
  let append_to_log str =
    let uu____552 = get_log_file () in
    FStar_Util.append_to_file uu____552 str in
  let write_to_new_log str =
    let dir_name =
      let uu____558 = FStar_ST.read current_file_name in
      match uu____558 with
      | None  ->
          let dir_name =
            let uu____564 = FStar_ST.read current_module_name in
            match uu____564 with
            | None  -> failwith "current module not set"
            | Some n1 -> FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n1 -> n1 in
    let qnum = FStar_ST.read query_number in
    (let uu____580 =
       let uu____581 = FStar_ST.read query_number in
       uu____581 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____580);
    (let file_name =
       let uu____587 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____587 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____593 =
      let uu____594 = FStar_Options.n_cores () in
      uu____594 > (Prims.parse_int "1") in
    if uu____593 then write_to_new_log str else append_to_log str in
  let close_log uu____599 =
    let uu____600 = FStar_ST.read log_file_opt in
    match uu____600 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None) in
  let log_file_name uu____613 =
    let uu____614 = FStar_ST.read current_file_name in
    match uu____614 with | None  -> failwith "no log file" | Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____631  ->
      let uu____632 =
        let uu____633 =
          FStar_Util.incr ctr;
          (let uu____638 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____638 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____633 in
      new_z3proc uu____632 in
  let z3proc uu____644 =
    (let uu____646 =
       let uu____647 = FStar_ST.read the_z3proc in uu____647 = None in
     if uu____646
     then
       let uu____653 = let uu____655 = new_proc () in Some uu____655 in
       FStar_ST.write the_z3proc uu____653
     else ());
    (let uu____660 = FStar_ST.read the_z3proc in FStar_Util.must uu____660) in
  let x = [] in
  let grab uu____670 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____676 = FStar_Util.monitor_exit x in
  let refresh uu____681 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____685 = let uu____687 = new_proc () in Some uu____687 in
     FStar_ST.write the_z3proc uu____685);
    query_logging.close_log ();
    release () in
  let restart uu____695 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let uu____703 = let uu____705 = new_proc () in Some uu____705 in
     FStar_ST.write the_z3proc uu____703);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____711  ->
    let uu____712 = FStar_Options.log_queries () in
    if uu____712
    then
      let uu____713 = query_logging.log_file_name () in
      Prims.strcat "@" uu____713
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
              (let uu____760 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____760 (fun _0_28  -> Some _0_28)) in
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
            | uu____805 ->
                let uu____806 = FStar_ST.read in_core in
                if uu____806
                then
                  let uu____809 = parse_core line in
                  FStar_ST.write core uu____809
                else
                  (let uu____817 = FStar_ST.read in_statistics in
                   if uu____817
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
                     | uu____860 -> ()
                   else
                     (let uu____863 = FStar_ST.read in_reason_unknown in
                      if uu____863
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____869::txt::uu____871::[] -> txt
                          | uu____872 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             rsn
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____878 = FStar_ST.read core in
           let uu____885 = FStar_ST.read reason_unknown in
           (uu____878, statistics, uu____885)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____901 = lblnegs rest in lname :: uu____901
          | lname::uu____904::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest
          | uu____907 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____922 = lblnegs tl1 in UNKNOWN uu____922
          | "sat"::tl1 -> let uu____926 = lblnegs tl1 in SAT uu____926
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____937 =
                  let uu____938 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____938 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____937);
               result tl1 core)
          | uu____939 ->
              let uu____941 =
                let uu____942 =
                  let uu____943 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____943 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____942 in
              FStar_All.pipe_left failwith uu____941 in
        let uu____946 = get_data lines in
        match uu____946 with
        | (core,statistics,reason_unknown) ->
            let uu____961 = result lines core in (uu____961, statistics) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____971 = tid () in
          let uu____972 = FStar_Options.z3_exe () in
          let uu____973 = ini_params () in
          FStar_Util.launch_process uu____971 uu____972 uu____973 input cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout1 = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout1) in
      parse (FStar_Util.trim_string stdout1)
let doZ3Exe: Prims.bool -> Prims.string -> (z3status* z3statistics) =
  fun fresh1  -> fun input  -> doZ3Exe' fresh1 input
let z3_options: Prims.unit -> Prims.string =
  fun uu____988  ->
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
    match projectee with | Timeout  -> true | uu____1039 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1043 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1047 -> false
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
        fun uu____1104  ->
          let ekind uu___97_1115 =
            match uu___97_1115 with
            | TIMEOUT uu____1116 -> Timeout
            | SAT uu____1118 -> Default
            | UNKNOWN uu____1120 -> Default
            | KILLED  -> Kill
            | uu____1122 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1124 = doZ3Exe fresh1 input in
          match uu____1124 with
          | (status,statistics) ->
              let uu____1136 =
                let uu____1139 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1139 in
              (match uu____1136 with
               | (uu____1147,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1227 = FStar_Options.debug_any () in
                           if uu____1227
                           then
                             let uu____1228 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1228
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1250 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1268  ->
                                               match uu____1268 with
                                               | (m,uu____1275,uu____1276) ->
                                                   (fst m) = l)) in
                                     match uu____1250 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1321 =
                             let uu____1332 =
                               let uu____1341 = ekind status in
                               (failing_assertions, uu____1341) in
                             FStar_Util.Inr uu____1332 in
                           (uu____1321, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____1369 = FStar_Options.debug_any () in
                           if uu____1369
                           then
                             let uu____1370 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1370
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1392 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1410  ->
                                               match uu____1410 with
                                               | (m,uu____1417,uu____1418) ->
                                                   (fst m) = l)) in
                                     match uu____1392 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1463 =
                             let uu____1474 =
                               let uu____1483 = ekind status in
                               (failing_assertions, uu____1483) in
                             FStar_Util.Inr uu____1474 in
                           (uu____1463, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____1511 = FStar_Options.debug_any () in
                           if uu____1511
                           then
                             let uu____1512 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1512
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1534 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1552  ->
                                               match uu____1552 with
                                               | (m,uu____1559,uu____1560) ->
                                                   (fst m) = l)) in
                                     match uu____1534 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1605 =
                             let uu____1616 =
                               let uu____1625 = ekind status in
                               (failing_assertions, uu____1625) in
                             FStar_Util.Inr uu____1616 in
                           (uu____1605, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____1659  ->
    let j =
      let uu____1661 = FStar_ST.read job_queue in
      match uu____1661 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1688  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____1693  ->
    let uu____1694 = FStar_ST.read running in
    if uu____1694
    then
      let rec aux uu____1700 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1706 = FStar_ST.read job_queue in
         match uu____1706 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1717 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____1720 = j.job () in FStar_All.pipe_left j.callback uu____1720
let init: Prims.unit -> Prims.unit =
  fun uu____1751  ->
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
    (let uu____1772 =
       let uu____1774 = FStar_ST.read job_queue in
       FStar_List.append uu____1774 [j] in
     FStar_ST.write job_queue uu____1772);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____1793  ->
    let rec aux uu____1797 =
      let uu____1798 =
        with_monitor job_queue
          (fun uu____1807  ->
             let uu____1808 = FStar_ST.read pending_jobs in
             let uu____1811 =
               let uu____1812 = FStar_ST.read job_queue in
               FStar_List.length uu____1812 in
             (uu____1808, uu____1811)) in
      match uu____1798 with
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
  fun uu____1846  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1860 =
       let uu____1863 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____1863 in
     FStar_ST.write fresh_scope uu____1860);
    (let uu____1875 =
       let uu____1877 = FStar_ST.read bg_scope in
       FStar_List.append uu____1877
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____1875)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1889 =
       let uu____1892 = FStar_ST.read fresh_scope in FStar_List.tl uu____1892 in
     FStar_ST.write fresh_scope uu____1889);
    (let uu____1904 =
       let uu____1906 = FStar_ST.read bg_scope in
       FStar_List.append uu____1906
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____1904)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___98_1921  ->
            match uu___98_1921 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____1922 -> ()));
    (let uu____1924 = FStar_ST.read fresh_scope in
     match uu____1924 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____1942 -> failwith "Impossible");
    (let uu____1945 =
       let uu____1947 = FStar_ST.read bg_scope in
       FStar_List.append uu____1947 decls in
     FStar_ST.write bg_scope uu____1945)
let refresh: Prims.unit -> Prims.unit =
  fun uu____1957  ->
    (let uu____1959 =
       let uu____1960 = FStar_Options.n_cores () in
       uu____1960 < (Prims.parse_int "2") in
     if uu____1959 then bg_z3_proc.refresh () else ());
    (let uu____1962 =
       let uu____1964 =
         let uu____1967 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____1967 in
       FStar_List.flatten uu____1964 in
     FStar_ST.write bg_scope uu____1962)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____1988 = FStar_ST.read fresh_scope in
    match uu____1988 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____2009 -> failwith "Impossible"
let mk_cb used_unsat_core cb uu____2057 =
  match uu____2057 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____2089 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____2098,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____2126 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____2126 (FStar_String.concat "\n") in
    (let uu____2130 = FStar_Options.log_queries () in
     if uu____2130 then query_logging.write_to_log r else ());
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
            let uu____2166 = FStar_ST.read bg_scope in
            FStar_List.append uu____2166
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____2171 = filter_theory theory in
          match uu____2171 with
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
              let uu____2231 =
                match scope with
                | Some s -> FStar_List.rev s
                | None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____2242 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____2242)) in
              FStar_List.flatten uu____2231 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____2252 = filter_theory theory1 in
            match uu____2252 with
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
            let uu____2307 =
              let uu____2308 = FStar_Options.n_cores () in
              uu____2308 = (Prims.parse_int "1") in
            if uu____2307
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
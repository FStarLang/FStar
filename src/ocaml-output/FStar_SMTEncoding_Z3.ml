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
  fun uu___96_48  ->
    match uu___96_48 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____53 = FStar_Util.string_of_int i in
        let uu____54 = FStar_Util.string_of_int j in
        let uu____55 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____53 uu____54 uu____55
let z3v_compare:
  z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.int Prims.option =
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
let _z3version: z3version Prims.option FStar_ST.ref = FStar_Util.mk_ref None
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
                     with | uu____131 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____135 -> Z3V_Unknown out)
               | uu____137 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (Some out1); out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____145  ->
    let z3_v = get_z3version () in
    (let uu____148 =
       let uu____149 = get_z3version () in
       z3v_le uu____149
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____148
     then
       let uu____150 =
         let uu____151 =
           let uu____152 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____152 in
         FStar_Util.Failure uu____151 in
       FStar_All.pipe_left Prims.raise uu____150
     else ());
    (let uu____154 =
       let uu____156 =
         let uu____158 =
           let uu____160 =
             let uu____161 =
               let uu____162 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____162 in
             FStar_Util.format1 "smt.random_seed=%s" uu____161 in
           [uu____160] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____158 in
       let uu____163 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____156 uu____163 in
     FStar_String.concat " " uu____154)
type label = Prims.string
type unsat_core = Prims.string Prims.list Prims.option
type z3status =
  | UNSAT of unsat_core
  | SAT of label Prims.list
  | UNKNOWN of label Prims.list
  | TIMEOUT of label Prims.list
  | KILLED
let uu___is_UNSAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____186 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____199 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____215 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____231 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____245 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___97_249  ->
    match uu___97_249 with
    | SAT uu____250 -> "sat"
    | UNSAT uu____252 -> "unsat"
    | UNKNOWN uu____253 -> "unknown"
    | TIMEOUT uu____255 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____259  ->
    let uu____260 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____260 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____272 = FStar_Options.z3_exe () in
    let uu____273 = ini_params () in
    FStar_Util.start_process id uu____272 uu____273 cond
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
  let get_module_name uu____439 =
    let uu____440 = FStar_ST.read current_module_name in
    match uu____440 with
    | None  -> failwith "Module name not set"
    | Some n1 -> n1 in
  let new_log_file uu____449 =
    let uu____450 = FStar_ST.read current_module_name in
    match uu____450 with
    | None  -> failwith "current module not set"
    | Some n1 ->
        let file_name =
          let uu____457 =
            let uu____461 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____472  ->
                 match uu____472 with | (m,uu____476) -> n1 = m) uu____461 in
          match uu____457 with
          | None  ->
              ((let uu____480 =
                  let uu____484 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____484 in
                FStar_ST.write used_file_names uu____480);
               n1)
          | Some (uu____500,k) ->
              ((let uu____505 =
                  let uu____509 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____509 in
                FStar_ST.write used_file_names uu____505);
               (let uu____525 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____525)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name (Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (Some fh); fh)) in
  let get_log_file uu____539 =
    let uu____540 = FStar_ST.read log_file_opt in
    match uu____540 with | None  -> new_log_file () | Some fh -> fh in
  let append_to_log str =
    let uu____550 = get_log_file () in
    FStar_Util.append_to_file uu____550 str in
  let write_to_new_log str =
    let dir_name =
      let uu____556 = FStar_ST.read current_file_name in
      match uu____556 with
      | None  ->
          let dir_name =
            let uu____562 = FStar_ST.read current_module_name in
            match uu____562 with
            | None  -> failwith "current module not set"
            | Some n1 -> FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n1 -> n1 in
    let qnum = FStar_ST.read query_number in
    (let uu____578 =
       let uu____579 = FStar_ST.read query_number in
       uu____579 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____578);
    (let file_name =
       let uu____585 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____585 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____591 =
      let uu____592 = FStar_Options.n_cores () in
      uu____592 > (Prims.parse_int "1") in
    if uu____591 then write_to_new_log str else append_to_log str in
  let close_log uu____597 =
    let uu____598 = FStar_ST.read log_file_opt in
    match uu____598 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None) in
  let log_file_name uu____611 =
    let uu____612 = FStar_ST.read current_file_name in
    match uu____612 with | None  -> failwith "no log file" | Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____629  ->
      let uu____630 =
        let uu____631 =
          FStar_Util.incr ctr;
          (let uu____636 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____636 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____631 in
      new_z3proc uu____630 in
  let z3proc uu____642 =
    (let uu____644 =
       let uu____645 = FStar_ST.read the_z3proc in uu____645 = None in
     if uu____644
     then
       let uu____651 = let uu____653 = new_proc () in Some uu____653 in
       FStar_ST.write the_z3proc uu____651
     else ());
    (let uu____658 = FStar_ST.read the_z3proc in FStar_Util.must uu____658) in
  let x = [] in
  let grab uu____668 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____674 = FStar_Util.monitor_exit x in
  let refresh uu____679 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____683 = let uu____685 = new_proc () in Some uu____685 in
     FStar_ST.write the_z3proc uu____683);
    query_logging.close_log ();
    release () in
  let restart uu____693 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let uu____701 = let uu____703 = new_proc () in Some uu____703 in
     FStar_ST.write the_z3proc uu____701);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____709  ->
    let uu____710 = FStar_Options.log_queries () in
    if uu____710
    then
      let uu____711 = query_logging.log_file_name () in
      Prims.strcat "@" uu____711
    else ""
let doZ3Exe': Prims.bool -> Prims.string -> (z3status* z3statistics) =
  fun fresh1  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string) in
        let print_stats statistics =
          (let uu____740 =
             let uu____741 =
               let uu____742 = query_logging.get_module_name () in
               FStar_Util.format1 "BEGIN-STATS %s\n" uu____742 in
             let uu____743 = at_log_file () in
             Prims.strcat uu____741 uu____743 in
           FStar_Util.print_string uu____740);
          FStar_Util.print_string "(";
          FStar_Util.smap_fold statistics
            (fun k  ->
               fun v1  ->
                 fun a  ->
                   let uu____749 = FStar_Util.format2 ":%s %s\n" k v1 in
                   FStar_Util.print_string uu____749) ();
          FStar_Util.print_string ")\n";
          FStar_Util.print_string "END-STATS\n" in
        let get_data lines1 =
          let parse_core s =
            let s1 = FStar_Util.trim_string s in
            let s2 =
              FStar_Util.substring s1 (Prims.parse_int "1")
                ((FStar_String.length s1) - (Prims.parse_int "2")) in
            if FStar_Util.starts_with s2 "error"
            then None
            else
              (let uu____773 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____773 (fun _0_27  -> Some _0_27)) in
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
            | uu____818 ->
                let uu____819 = FStar_ST.read in_core in
                if uu____819
                then
                  let uu____822 = parse_core line in
                  FStar_ST.write core uu____822
                else
                  (let uu____830 = FStar_ST.read in_statistics in
                   if uu____830
                   then
                     let pline =
                       FStar_Util.split (FStar_Util.trim_string line) ":" in
                     match pline with
                     | "("::entry::[]|""::entry::[] ->
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
                     | uu____848 -> ()
                   else
                     (let uu____851 = FStar_ST.read in_reason_unknown in
                      if uu____851
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____857::txt::uu____859::[] -> txt
                          | uu____860 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             rsn
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____866 = FStar_ST.read core in
           let uu____873 = FStar_ST.read reason_unknown in
           (uu____866, statistics, uu____873)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____889 = lblnegs rest in lname :: uu____889
          | lname::uu____892::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest
          | uu____895 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____910 = lblnegs tl1 in UNKNOWN uu____910
          | "sat"::tl1 -> let uu____914 = lblnegs tl1 in SAT uu____914
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____925 =
                  let uu____926 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____926 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____925);
               result tl1 core)
          | uu____927 ->
              let uu____929 =
                let uu____930 =
                  let uu____931 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____931 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____930 in
              FStar_All.pipe_left failwith uu____929 in
        let uu____934 = get_data lines in
        match uu____934 with
        | (core,statistics,reason_unknown) ->
            ((let uu____950 = FStar_Options.print_z3_statistics () in
              if uu____950 then print_stats statistics else ());
             (let uu____952 = result lines core in (uu____952, statistics))) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____962 = tid () in
          let uu____963 = FStar_Options.z3_exe () in
          let uu____964 = ini_params () in
          FStar_Util.launch_process uu____962 uu____963 uu____964 input cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout1 = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout1) in
      parse (FStar_Util.trim_string stdout1)
let doZ3Exe: Prims.bool -> Prims.string -> (z3status* z3statistics) =
  fun fresh1  -> fun input  -> doZ3Exe' fresh1 input
let z3_options: Prims.unit -> Prims.string =
  fun uu____979  ->
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
    match projectee with | Timeout  -> true | uu____1030 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1034 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1038 -> false
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
        fun uu____1095  ->
          let ekind uu___98_1106 =
            match uu___98_1106 with
            | TIMEOUT uu____1107 -> Timeout
            | SAT _|UNKNOWN _ -> Default
            | KILLED  -> Kill
            | uu____1111 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1113 = doZ3Exe fresh1 input in
          match uu____1113 with
          | (status,statistics) ->
              let uu____1125 =
                let uu____1128 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1128 in
              (match uu____1125 with
               | (uu____1136,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs|SAT lblnegs|UNKNOWN lblnegs ->
                         ((let uu____1218 = FStar_Options.debug_any () in
                           if uu____1218
                           then
                             let uu____1219 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1219
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1241 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1259  ->
                                               match uu____1259 with
                                               | (m,uu____1266,uu____1267) ->
                                                   (Prims.fst m) = l)) in
                                     match uu____1241 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1312 =
                             let uu____1323 =
                               let uu____1332 = ekind status in
                               (failing_assertions, uu____1332) in
                             FStar_Util.Inr uu____1323 in
                           (uu____1312, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____1366  ->
    let j =
      let uu____1368 = FStar_ST.read job_queue in
      match uu____1368 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1395  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____1400  ->
    let uu____1401 = FStar_ST.read running in
    if uu____1401
    then
      let rec aux uu____1407 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1413 = FStar_ST.read job_queue in
         match uu____1413 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1424 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____1427 = j.job () in FStar_All.pipe_left j.callback uu____1427
let init: Prims.unit -> Prims.unit =
  fun uu____1458  ->
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
    (let uu____1479 =
       let uu____1481 = FStar_ST.read job_queue in
       FStar_List.append uu____1481 [j] in
     FStar_ST.write job_queue uu____1479);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____1500  ->
    let rec aux uu____1504 =
      let uu____1505 =
        with_monitor job_queue
          (fun uu____1514  ->
             let uu____1515 = FStar_ST.read pending_jobs in
             let uu____1518 =
               let uu____1519 = FStar_ST.read job_queue in
               FStar_List.length uu____1519 in
             (uu____1515, uu____1518)) in
      match uu____1505 with
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
  fun uu____1548  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1562 =
       let uu____1565 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____1565 in
     FStar_ST.write fresh_scope uu____1562);
    (let uu____1577 =
       let uu____1579 = FStar_ST.read bg_scope in
       FStar_List.append uu____1579
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____1577)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1591 =
       let uu____1594 = FStar_ST.read fresh_scope in FStar_List.tl uu____1594 in
     FStar_ST.write fresh_scope uu____1591);
    (let uu____1606 =
       let uu____1608 = FStar_ST.read bg_scope in
       FStar_List.append uu____1608
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____1606)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___99_1623  ->
            match uu___99_1623 with
            | FStar_SMTEncoding_Term.Push |FStar_SMTEncoding_Term.Pop  ->
                failwith "Unexpected push/pop"
            | uu____1624 -> ()));
    (let uu____1626 = FStar_ST.read fresh_scope in
     match uu____1626 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____1644 -> failwith "Impossible");
    (let uu____1647 =
       let uu____1649 = FStar_ST.read bg_scope in
       FStar_List.append uu____1649 decls in
     FStar_ST.write bg_scope uu____1647)
let refresh: Prims.unit -> Prims.unit =
  fun uu____1659  ->
    (let uu____1661 =
       let uu____1662 = FStar_Options.n_cores () in
       uu____1662 < (Prims.parse_int "2") in
     if uu____1661 then bg_z3_proc.refresh () else ());
    (let uu____1664 =
       let uu____1666 =
         let uu____1669 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____1669 in
       FStar_List.flatten uu____1666 in
     FStar_ST.write bg_scope uu____1664)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____1690 = FStar_ST.read fresh_scope in
    match uu____1690 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____1711 -> failwith "Impossible"
let mk_cb used_unsat_core cb uu____1759 =
  match uu____1759 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____1791 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____1800,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____1828 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____1828 (FStar_String.concat "\n") in
    (let uu____1832 = FStar_Options.log_queries () in
     if uu____1832 then query_logging.write_to_log r else ());
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
            let uu____1868 = FStar_ST.read bg_scope in
            FStar_List.append uu____1868
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____1873 = filter_theory theory in
          match uu____1873 with
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
      FStar_SMTEncoding_Term.decls_t ->
        scope_t Prims.option -> cb -> Prims.unit
  =
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let theory =
              let uu____1933 =
                match scope with
                | Some s -> FStar_List.rev s
                | None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____1944 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____1944)) in
              FStar_List.flatten uu____1933 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____1954 = filter_theory theory1 in
            match uu____1954 with
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
      FStar_SMTEncoding_Term.decls_t ->
        scope_t Prims.option -> cb -> Prims.unit
  =
  fun filter1  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let uu____2009 =
              let uu____2010 = FStar_Options.n_cores () in
              uu____2010 = (Prims.parse_int "1") in
            if uu____2009
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
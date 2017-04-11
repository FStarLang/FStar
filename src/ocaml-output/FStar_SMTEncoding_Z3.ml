open Prims
type z3version =
  | Z3V_Unknown of Prims.string 
  | Z3V of (Prims.int * Prims.int * Prims.int) 
let uu___is_Z3V_Unknown : z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____14 -> false
  
let __proj__Z3V_Unknown__item___0 : z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0 
let uu___is_Z3V : z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____29 -> false 
let __proj__Z3V__item___0 : z3version -> (Prims.int * Prims.int * Prims.int)
  = fun projectee  -> match projectee with | Z3V _0 -> _0 
let z3version_as_string : z3version -> Prims.string =
  fun uu___91_48  ->
    match uu___91_48 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____53 = FStar_Util.string_of_int i  in
        let uu____54 = FStar_Util.string_of_int j  in
        let uu____55 = FStar_Util.string_of_int k  in
        FStar_Util.format3 "%s.%s.%s" uu____53 uu____54 uu____55
  
let z3v_compare :
  z3version -> (Prims.int * Prims.int * Prims.int) -> Prims.int Prims.option
  =
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
  
let z3v_le : z3version -> (Prims.int * Prims.int * Prims.int) -> Prims.bool =
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | None  -> false
      | Some i -> i >= (Prims.parse_int "0")
  
let _z3version : z3version Prims.option FStar_ST.ref = FStar_Util.mk_ref None 
let get_z3version : Prims.unit -> z3version =
  fun uu____100  ->
    let prefix1 = "Z3 version "  in
    let uu____102 = FStar_ST.read _z3version  in
    match uu____102 with
    | Some version -> version
    | None  ->
        let uu____108 =
          let uu____112 = FStar_Options.z3_exe ()  in
          FStar_Util.run_proc uu____112 "-version" ""  in
        (match uu____108 with
         | (uu____113,out,uu____115) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____118 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____121 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1)
                        in
                     FStar_Util.trim_string uu____121  in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____131 -> []  in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____135 -> Z3V_Unknown out)
               | uu____137 -> Z3V_Unknown out  in
             (FStar_ST.write _z3version (Some out1); out1))
  
let ini_params : Prims.unit -> Prims.string =
  fun uu____145  ->
    let z3_v = get_z3version ()  in
    (let uu____148 =
       let uu____149 = get_z3version ()  in
       z3v_le uu____149
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0"))
        in
     if uu____148
     then
       let uu____150 =
         let uu____151 =
           let uu____152 = z3version_as_string z3_v  in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____152
            in
         FStar_Util.Failure uu____151  in
       FStar_All.pipe_left Prims.raise uu____150
     else ());
    (let uu____154 =
       let uu____156 =
         let uu____158 =
           let uu____160 =
             let uu____161 =
               let uu____162 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____162  in
             FStar_Util.format1 "smt.random_seed=%s" uu____161  in
           [uu____160]  in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____158
          in
       let uu____163 = FStar_Options.z3_cliopt ()  in
       FStar_List.append uu____156 uu____163  in
     FStar_String.concat " " uu____154)
  
type label = Prims.string
type unsat_core = Prims.string Prims.list Prims.option
type z3status =
  | UNSAT of unsat_core 
  | SAT of label Prims.list 
  | UNKNOWN of label Prims.list 
  | TIMEOUT of label Prims.list 
  | KILLED 
let uu___is_UNSAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____186 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____199 -> false
  
let __proj__SAT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____215 -> false
  
let __proj__UNKNOWN__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____231 -> false
  
let __proj__TIMEOUT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____245 -> false
  
let status_to_string : z3status -> Prims.string =
  fun uu___92_248  ->
    match uu___92_248 with
    | SAT uu____249 -> "sat"
    | UNSAT uu____251 -> "unsat"
    | UNKNOWN uu____252 -> "unknown"
    | TIMEOUT uu____254 -> "timeout"
    | KILLED  -> "killed"
  
let tid : Prims.unit -> Prims.string =
  fun uu____258  ->
    let uu____259 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____259 FStar_Util.string_of_int
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let uu____271 = FStar_Options.z3_exe ()  in
    let uu____272 = ini_params ()  in
    FStar_Util.start_process id uu____271 uu____272 cond
  
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc ;
  release: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit ;
  restart: Prims.unit -> Prims.unit }
type query_log =
  {
  get_module_name: Prims.unit -> Prims.string ;
  set_module_name: Prims.string -> Prims.unit ;
  write_to_log: Prims.string -> Prims.unit ;
  close_log: Prims.unit -> Prims.unit ;
  log_file_name: Prims.unit -> Prims.string }
let query_logging : query_log =
  let query_number = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let log_file_opt = FStar_Util.mk_ref None  in
  let used_file_names = FStar_Util.mk_ref []  in
  let current_module_name = FStar_Util.mk_ref None  in
  let current_file_name = FStar_Util.mk_ref None  in
  let set_module_name n1 = FStar_ST.write current_module_name (Some n1)  in
  let get_module_name uu____438 =
    let uu____439 = FStar_ST.read current_module_name  in
    match uu____439 with
    | None  -> failwith "Module name not set"
    | Some n1 -> n1  in
  let new_log_file uu____448 =
    let uu____449 = FStar_ST.read current_module_name  in
    match uu____449 with
    | None  -> failwith "current module not set"
    | Some n1 ->
        let file_name =
          let uu____456 =
            let uu____460 = FStar_ST.read used_file_names  in
            FStar_List.tryFind
              (fun uu____471  ->
                 match uu____471 with | (m,uu____475) -> n1 = m) uu____460
             in
          match uu____456 with
          | None  ->
              ((let uu____479 =
                  let uu____483 = FStar_ST.read used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____483  in
                FStar_ST.write used_file_names uu____479);
               n1)
          | Some (uu____499,k) ->
              ((let uu____504 =
                  let uu____508 = FStar_ST.read used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____508  in
                FStar_ST.write used_file_names uu____504);
               (let uu____524 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____524))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.write current_file_name (Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.write log_file_opt (Some fh); fh))
     in
  let get_log_file uu____538 =
    let uu____539 = FStar_ST.read log_file_opt  in
    match uu____539 with | None  -> new_log_file () | Some fh -> fh  in
  let append_to_log str =
    let uu____549 = get_log_file ()  in
    FStar_Util.append_to_file uu____549 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____555 = FStar_ST.read current_file_name  in
      match uu____555 with
      | None  ->
          let dir_name =
            let uu____561 = FStar_ST.read current_module_name  in
            match uu____561 with
            | None  -> failwith "current module not set"
            | Some n1 -> FStar_Util.format1 "queries-%s" n1  in
          (FStar_Util.mkdir_clean dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n1 -> n1  in
    let qnum = FStar_ST.read query_number  in
    (let uu____577 =
       let uu____578 = FStar_ST.read query_number  in
       uu____578 + (Prims.parse_int "1")  in
     FStar_ST.write query_number uu____577);
    (let file_name =
       let uu____584 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____584  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____590 =
      let uu____591 = FStar_Options.n_cores ()  in
      uu____591 > (Prims.parse_int "1")  in
    if uu____590 then write_to_new_log str else append_to_log str  in
  let close_log uu____596 =
    let uu____597 = FStar_ST.read log_file_opt  in
    match uu____597 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None)
     in
  let log_file_name uu____610 =
    let uu____611 = FStar_ST.read current_file_name  in
    match uu____611 with | None  -> failwith "no log file" | Some n1 -> n1
     in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let bg_z3_proc : bgproc =
  let the_z3proc = FStar_Util.mk_ref None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____628  ->
      let uu____629 =
        let uu____630 =
          FStar_Util.incr ctr;
          (let uu____635 = FStar_ST.read ctr  in
           FStar_All.pipe_right uu____635 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____630  in
      new_z3proc uu____629
     in
  let z3proc uu____641 =
    (let uu____643 =
       let uu____644 = FStar_ST.read the_z3proc  in uu____644 = None  in
     if uu____643
     then
       let uu____650 = let uu____652 = new_proc ()  in Some uu____652  in
       FStar_ST.write the_z3proc uu____650
     else ());
    (let uu____657 = FStar_ST.read the_z3proc  in FStar_Util.must uu____657)
     in
  let x = []  in
  let grab uu____667 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____673 = FStar_Util.monitor_exit x  in
  let refresh uu____678 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let uu____682 = let uu____684 = new_proc ()  in Some uu____684  in
     FStar_ST.write the_z3proc uu____682);
    query_logging.close_log ();
    release ()  in
  let restart uu____692 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let uu____700 = let uu____702 = new_proc ()  in Some uu____702  in
     FStar_ST.write the_z3proc uu____700);
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let at_log_file : Prims.unit -> Prims.string =
  fun uu____708  ->
    let uu____709 = FStar_Options.log_queries ()  in
    if uu____709
    then
      let uu____710 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____710
    else ""
  
let doZ3Exe' : Prims.bool -> Prims.string -> z3status =
  fun fresh1  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string)
           in
        let print_stats lines1 =
          let starts_with1 c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let uu____742 = FStar_String.get s (Prims.parse_int "0")  in
               uu____742 = c)
             in
          let ends_with1 c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let uu____753 =
                 FStar_String.get s
                   ((FStar_String.length s) - (Prims.parse_int "1"))
                  in
               uu____753 = c)
             in
          let last1 l =
            FStar_List.nth l ((FStar_List.length l) - (Prims.parse_int "1"))
             in
          let uu____766 = FStar_Options.print_z3_statistics ()  in
          if uu____766
          then
            let uu____767 =
              (((FStar_List.length lines1) >= (Prims.parse_int "2")) &&
                 (let uu____771 = FStar_List.hd lines1  in
                  starts_with1 '(' uu____771))
                &&
                (let uu____772 = last1 lines1  in ends_with1 ')' uu____772)
               in
            (if uu____767
             then
               ((let uu____774 =
                   let uu____775 =
                     let uu____776 = query_logging.get_module_name ()  in
                     FStar_Util.format1 "BEGIN-STATS %s\n" uu____776  in
                   let uu____777 = at_log_file ()  in
                   Prims.strcat uu____775 uu____777  in
                 FStar_Util.print_string uu____774);
                FStar_List.iter
                  (fun s  ->
                     let uu____780 = FStar_Util.format1 "%s\n" s  in
                     FStar_Util.print_string uu____780) lines1;
                FStar_Util.print_string "END-STATS\n")
             else
               failwith
                 "Unexpected output from Z3: could not find statistics\n")
          else ()  in
        let unsat_core lines1 =
          let parse_core s =
            let s1 = FStar_Util.trim_string s  in
            let s2 =
              FStar_Util.substring s1 (Prims.parse_int "1")
                ((FStar_String.length s1) - (Prims.parse_int "2"))
               in
            if FStar_Util.starts_with s2 "error"
            then None
            else
              (let uu____809 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare)
                  in
               FStar_All.pipe_right uu____809 (fun _0_27  -> Some _0_27))
             in
          match lines1 with
          | "<unsat-core>"::core::"</unsat-core>"::rest ->
              let uu____825 = parse_core core  in (uu____825, lines1)
          | uu____831 -> (None, lines1)  in
        let rec lblnegs lines1 succeeded =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              ->
              let uu____851 = lblnegs rest succeeded  in lname :: uu____851
          | lname::uu____854::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest succeeded
          | uu____857 -> (if succeeded then print_stats lines1 else (); [])
           in
        let unsat_core_and_lblnegs lines1 succeeded =
          let uu____875 = unsat_core lines1  in
          match uu____875 with
          | (core_opt,rest) ->
              let uu____894 = lblnegs rest succeeded  in
              (core_opt, uu____894)
           in
        let rec result x =
          match x with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____909 =
                let uu____911 = unsat_core_and_lblnegs tl1 false  in
                Prims.snd uu____911  in
              UNKNOWN uu____909
          | "sat"::tl1 ->
              let uu____922 =
                let uu____924 = unsat_core_and_lblnegs tl1 false  in
                Prims.snd uu____924  in
              SAT uu____922
          | "unsat"::tl1 ->
              let uu____935 =
                let uu____936 = unsat_core_and_lblnegs tl1 true  in
                Prims.fst uu____936  in
              UNSAT uu____935
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____952 =
                  let uu____953 = query_logging.get_module_name ()  in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____953 hd1
                   in
                FStar_Errors.warn FStar_Range.dummyRange uu____952);
               result tl1)
          | uu____954 ->
              let uu____956 =
                let uu____957 =
                  let uu____958 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines
                     in
                  FStar_String.concat "\n" uu____958  in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____957
                 in
              FStar_All.pipe_left failwith uu____956
           in
        result lines  in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
      let stdout1 =
        if fresh1
        then
          let uu____970 = tid ()  in
          let uu____971 = FStar_Options.z3_exe ()  in
          let uu____972 = ini_params ()  in
          FStar_Util.launch_process uu____970 uu____971 uu____972 input cond
        else
          (let proc = bg_z3_proc.grab ()  in
           let stdout1 = FStar_Util.ask_process proc input  in
           bg_z3_proc.release (); stdout1)
         in
      parse (FStar_Util.trim_string stdout1)
  
let doZ3Exe : Prims.bool -> Prims.string -> z3status =
  fun fresh1  -> fun input  -> doZ3Exe' fresh1 input 
let z3_options : Prims.unit -> Prims.string =
  fun uu____985  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
type 'a job = {
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }
type error_kind =
  | Timeout 
  | Kill 
  | Default 
let uu___is_Timeout : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____1036 -> false
  
let uu___is_Kill : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1040 -> false
  
let uu___is_Default : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1044 -> false
  
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels * error_kind))
    FStar_Util.either * Prims.int) job
let job_queue : z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let pending_jobs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let with_monitor m f =
  FStar_Util.monitor_enter m;
  (let res = f ()  in FStar_Util.monitor_exit m; res) 
let z3_job :
  Prims.bool ->
    ((label * FStar_SMTEncoding_Term.sort) * Prims.string *
      FStar_Range.range) Prims.list ->
      Prims.string ->
        Prims.unit ->
          ((unsat_core,(FStar_SMTEncoding_Term.error_labels * error_kind))
            FStar_Util.either * Prims.int)
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____1105  ->
          let ekind uu___93_1121 =
            match uu___93_1121 with
            | TIMEOUT uu____1122 -> Timeout
            | SAT _|UNKNOWN _ -> Default
            | KILLED  -> Kill
            | uu____1126 -> failwith "Impossible"  in
          let start = FStar_Util.now ()  in
          let status = doZ3Exe fresh1 input  in
          let uu____1129 =
            let uu____1132 = FStar_Util.now ()  in
            FStar_Util.time_diff start uu____1132  in
          match uu____1129 with
          | (uu____1139,elapsed_time) ->
              let result =
                match status with
                | UNSAT core -> ((FStar_Util.Inl core), elapsed_time)
                | KILLED  -> ((FStar_Util.Inr ([], Kill)), elapsed_time)
                | TIMEOUT lblnegs|SAT lblnegs|UNKNOWN lblnegs ->
                    ((let uu____1219 = FStar_Options.debug_any ()  in
                      if uu____1219
                      then
                        let uu____1220 =
                          FStar_Util.format1 "Z3 says: %s\n"
                            (status_to_string status)
                           in
                        FStar_All.pipe_left FStar_Util.print_string
                          uu____1220
                      else ());
                     (let failing_assertions =
                        FStar_All.pipe_right lblnegs
                          (FStar_List.collect
                             (fun l  ->
                                let uu____1242 =
                                  FStar_All.pipe_right label_messages
                                    (FStar_List.tryFind
                                       (fun uu____1266  ->
                                          match uu____1266 with
                                          | (m,uu____1273,uu____1274) ->
                                              (Prims.fst m) = l))
                                   in
                                match uu____1242 with
                                | None  -> []
                                | Some (lbl,msg,r) -> [(lbl, msg, r)]))
                         in
                      let uu____1319 =
                        let uu____1330 =
                          let uu____1339 = ekind status  in
                          (failing_assertions, uu____1339)  in
                        FStar_Util.Inr uu____1330  in
                      (uu____1319, elapsed_time)))
                 in
              result
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : Prims.unit -> Prims.unit =
  fun uu____1373  ->
    let j =
      let uu____1375 = FStar_ST.read job_queue  in
      match uu____1375 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1402  -> FStar_Util.decr pending_jobs);
    dequeue ()

and dequeue : Prims.unit -> Prims.unit =
  fun uu____1407  ->
    let uu____1408 = FStar_ST.read running  in
    if uu____1408
    then
      let rec aux uu____1414 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1420 = FStar_ST.read job_queue  in
         match uu____1420 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1431 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> Prims.unit =
  fun j  ->
    let uu____1434 = j.job ()  in FStar_All.pipe_left j.callback uu____1434

let init : Prims.unit -> Prims.unit =
  fun uu____1461  ->
    FStar_ST.write running true;
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
    (let uu____1482 =
       let uu____1484 = FStar_ST.read job_queue  in
       FStar_List.append uu____1484 [j]  in
     FStar_ST.write job_queue uu____1482);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
  
let finish : Prims.unit -> Prims.unit =
  fun uu____1503  ->
    let rec aux uu____1507 =
      let uu____1508 =
        with_monitor job_queue
          (fun uu____1517  ->
             let uu____1518 = FStar_ST.read pending_jobs  in
             let uu____1521 =
               let uu____1522 = FStar_ST.read job_queue  in
               FStar_List.length uu____1522  in
             (uu____1518, uu____1521))
         in
      match uu____1508 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then
            (FStar_ST.write running false;
             (let uu____1537 = FStar_Errors.report_all ()  in
              FStar_All.pipe_right uu____1537 Prims.ignore))
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let push : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1563 =
       let uu____1566 = FStar_ST.read fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____1566
        in
     FStar_ST.write fresh_scope uu____1563);
    (let uu____1578 =
       let uu____1580 = FStar_ST.read bg_scope  in
       FStar_List.append uu____1580
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.write bg_scope uu____1578)
  
let pop : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____1592 =
       let uu____1595 = FStar_ST.read fresh_scope  in
       FStar_List.tl uu____1595  in
     FStar_ST.write fresh_scope uu____1592);
    (let uu____1607 =
       let uu____1609 = FStar_ST.read bg_scope  in
       FStar_List.append uu____1609
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.write bg_scope uu____1607)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___94_1624  ->
            match uu___94_1624 with
            | FStar_SMTEncoding_Term.Push |FStar_SMTEncoding_Term.Pop  ->
                failwith "Unexpected push/pop"
            | uu____1625 -> ()));
    (let uu____1627 = FStar_ST.read fresh_scope  in
     match uu____1627 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____1645 -> failwith "Impossible");
    (let uu____1648 =
       let uu____1650 = FStar_ST.read bg_scope  in
       FStar_List.append uu____1650 decls  in
     FStar_ST.write bg_scope uu____1648)
  
let refresh : Prims.unit -> Prims.unit =
  fun uu____1660  ->
    (let uu____1662 =
       let uu____1663 = FStar_Options.n_cores ()  in
       uu____1663 < (Prims.parse_int "2")  in
     if uu____1662 then bg_z3_proc.refresh () else ());
    (let uu____1665 =
       let uu____1667 =
         let uu____1670 = FStar_ST.read fresh_scope  in
         FStar_List.rev uu____1670  in
       FStar_List.flatten uu____1667  in
     FStar_ST.write bg_scope uu____1665)
  
let mark : Prims.string -> Prims.unit = fun msg  -> push msg 
let reset_mark : Prims.string -> Prims.unit = fun msg  -> pop msg; refresh () 
let commit_mark msg =
  let uu____1695 = FStar_ST.read fresh_scope  in
  match uu____1695 with
  | hd1::s::tl1 ->
      FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
  | uu____1716 -> failwith "Impossible" 
let filter_assertions :
  Prims.string Prims.list Prims.option ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool)
  =
  fun core  ->
    fun theory  ->
      match core with
      | None  -> (theory, false)
      | Some core1 ->
          let uu____1742 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____1752  ->
                   match uu____1752 with
                   | (theory1,n_retained,n_pruned) ->
                       (match d with
                        | FStar_SMTEncoding_Term.Assume
                            (uu____1770,uu____1771,name) ->
                            if FStar_List.contains name core1
                            then
                              ((d :: theory1),
                                (n_retained + (Prims.parse_int "1")),
                                n_pruned)
                            else
                              if FStar_Util.starts_with name "@"
                              then ((d :: theory1), n_retained, n_pruned)
                              else
                                (theory1, n_retained,
                                  (n_pruned + (Prims.parse_int "1")))
                        | uu____1786 ->
                            ((d :: theory1), n_retained, n_pruned))) theory
              ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
             in
          (match uu____1742 with
           | (theory',n_retained,n_pruned) ->
               let missed_assertions th core2 =
                 let missed =
                   let uu____1809 =
                     FStar_All.pipe_right core2
                       (FStar_List.filter
                          (fun nm  ->
                             let uu____1814 =
                               FStar_All.pipe_right th
                                 (FStar_Util.for_some
                                    (fun uu___95_1816  ->
                                       match uu___95_1816 with
                                       | FStar_SMTEncoding_Term.Assume
                                           (uu____1817,uu____1818,nm') ->
                                           nm = nm'
                                       | uu____1820 -> false))
                                in
                             FStar_All.pipe_right uu____1814
                               Prims.op_Negation))
                      in
                   FStar_All.pipe_right uu____1809 (FStar_String.concat ", ")
                    in
                 let included =
                   let uu____1823 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___96_1827  ->
                             match uu___96_1827 with
                             | FStar_SMTEncoding_Term.Assume
                                 (uu____1829,uu____1830,nm) -> [nm]
                             | uu____1832 -> []))
                      in
                   FStar_All.pipe_right uu____1823 (FStar_String.concat ", ")
                    in
                 FStar_Util.format2 "missed={%s}; included={%s}" missed
                   included
                  in
               ((let uu____1835 =
                   (FStar_Options.hint_info ()) &&
                     (FStar_Options.debug_any ())
                    in
                 if uu____1835
                 then
                   let n1 = FStar_List.length core1  in
                   let missed =
                     if n1 <> n_retained
                     then missed_assertions theory' core1
                     else ""  in
                   let uu____1842 = FStar_Util.string_of_int n_retained  in
                   let uu____1843 =
                     if n1 <> n_retained
                     then
                       let uu____1846 = FStar_Util.string_of_int n1  in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____1846 missed
                     else ""  in
                   let uu____1851 = FStar_Util.string_of_int n_pruned  in
                   FStar_Util.print3
                     "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____1842 uu____1843 uu____1851
                 else ());
                (let uu____1853 =
                   let uu____1855 =
                     let uu____1857 =
                       let uu____1858 =
                         let uu____1859 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____1859  in
                       FStar_SMTEncoding_Term.Caption uu____1858  in
                     [uu____1857]  in
                   FStar_List.append theory' uu____1855  in
                 (uu____1853, true))))
  
let mk_cb used_unsat_core cb uu____1903 =
  match uu____1903 with
  | (uc_errs,time) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____1932 -> cb (uc_errs, time)
         | FStar_Util.Inr (uu____1941,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time))
      else cb (uc_errs, time)
  
let mk_input : FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____1969 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory
         in
      FStar_All.pipe_right uu____1969 (FStar_String.concat "\n")  in
    (let uu____1973 = FStar_Options.log_queries ()  in
     if uu____1973 then query_logging.write_to_log r else ());
    r
  
let ask_1_core :
  unsat_core ->
    ((label * FStar_SMTEncoding_Term.sort) * Prims.string *
      FStar_Range.range) Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (((unsat_core,(FStar_SMTEncoding_Term.error_labels * error_kind))
           FStar_Util.either * Prims.int) -> Prims.unit)
          -> Prims.unit
  =
  fun core  ->
    fun label_messages  ->
      fun qry  ->
        fun cb  ->
          let theory =
            let uu____2020 = FStar_ST.read bg_scope  in
            FStar_List.append uu____2020
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
             in
          let uu____2025 = filter_assertions core theory  in
          match uu____2025 with
          | (theory1,used_unsat_core) ->
              let cb1 = mk_cb used_unsat_core cb  in
              let input = mk_input theory1  in
              (FStar_ST.write bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb1
                 })
  
let ask_n_cores :
  unsat_core ->
    ((label * FStar_SMTEncoding_Term.sort) * Prims.string *
      FStar_Range.range) Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        scope_t Prims.option ->
          (((unsat_core,(FStar_SMTEncoding_Term.error_labels * error_kind))
             FStar_Util.either * Prims.int) -> Prims.unit)
            -> Prims.unit
  =
  fun core  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let theory =
              let uu____2104 =
                match scope with
                | Some s -> FStar_List.rev s
                | None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____2115 = FStar_ST.read fresh_scope  in
                      FStar_List.rev uu____2115))
                 in
              FStar_List.flatten uu____2104  in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
               in
            let uu____2125 = filter_assertions core theory1  in
            match uu____2125 with
            | (theory2,used_unsat_core) ->
                let cb1 = mk_cb used_unsat_core cb  in
                let input = mk_input theory2  in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb1
                  }
  
let ask :
  unsat_core ->
    ((label * FStar_SMTEncoding_Term.sort) * Prims.string *
      FStar_Range.range) Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        scope_t Prims.option ->
          (((unsat_core,(FStar_SMTEncoding_Term.error_labels * error_kind))
             FStar_Util.either * Prims.int) -> Prims.unit)
            -> Prims.unit
  =
  fun core  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
            let uu____2198 =
              let uu____2199 = FStar_Options.n_cores ()  in
              uu____2199 = (Prims.parse_int "1")  in
            if uu____2198
            then ask_1_core core label_messages qry cb
            else ask_n_cores core label_messages qry scope cb
  
open Prims
type z3version =
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int* Prims.int* Prims.int)
let uu___is_Z3V_Unknown: z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____16 -> false
let __proj__Z3V_Unknown__item___0: z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let uu___is_Z3V: z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____31 -> false
let __proj__Z3V__item___0: z3version -> (Prims.int* Prims.int* Prims.int) =
  fun projectee  -> match projectee with | Z3V _0 -> _0
let z3version_as_string: z3version -> Prims.string =
  fun uu___95_50  ->
    match uu___95_50 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____55 = FStar_Util.string_of_int i in
        let uu____56 = FStar_Util.string_of_int j in
        let uu____57 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" uu____55 uu____56 uu____57
let z3v_compare:
  z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.int option =
  fun known  ->
    fun uu____67  ->
      match uu____67 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____76 -> None
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
  fun uu____102  ->
    let prefix1 = "Z3 version " in
    let uu____104 = FStar_ST.read _z3version in
    match uu____104 with
    | Some version -> version
    | None  ->
        let uu____110 =
          let uu____114 = FStar_Options.z3_exe () in
          FStar_Util.run_proc uu____114 "-version" "" in
        (match uu____110 with
         | (uu____115,out,uu____117) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____120 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____123 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1) in
                     FStar_Util.trim_string uu____123 in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____135 -> [] in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____139 -> Z3V_Unknown out)
               | uu____141 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (Some out1); out1))
let ini_params: Prims.unit -> Prims.string =
  fun uu____149  ->
    let z3_v = get_z3version () in
    (let uu____152 =
       let uu____153 = get_z3version () in
       z3v_le uu____153
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____152
     then
       let uu____154 =
         let uu____155 =
           let uu____156 = z3version_as_string z3_v in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____156 in
         FStar_Util.Failure uu____155 in
       FStar_All.pipe_left FStar_Pervasives.raise uu____154
     else ());
    (let uu____158 =
       let uu____160 =
         let uu____162 =
           let uu____164 =
             let uu____165 =
               let uu____166 = FStar_Options.z3_seed () in
               FStar_Util.string_of_int uu____166 in
             FStar_Util.format1 "smt.random_seed=%s" uu____165 in
           [uu____164] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____162 in
       let uu____167 = FStar_Options.z3_cliopt () in
       FStar_List.append uu____160 uu____167 in
     FStar_String.concat " " uu____158)
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
    match projectee with | UNSAT _0 -> true | uu____194 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____207 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____223 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____239 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____253 -> false
type z3statistics = Prims.string FStar_Util.smap
let status_to_string: z3status -> Prims.string =
  fun uu___96_257  ->
    match uu___96_257 with
    | SAT uu____258 -> "sat"
    | UNSAT uu____260 -> "unsat"
    | UNKNOWN uu____261 -> "unknown"
    | TIMEOUT uu____263 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____267  ->
    let uu____268 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____268 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____280 = FStar_Options.z3_exe () in
    let uu____281 = ini_params () in
    FStar_Util.start_process id uu____280 uu____281 cond
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
  let log_file_opt = FStar_Util.mk_ref None in
  let used_file_names = FStar_Util.mk_ref [] in
  let current_module_name = FStar_Util.mk_ref None in
  let current_file_name = FStar_Util.mk_ref None in
  let set_module_name n1 = FStar_ST.write current_module_name (Some n1) in
  let get_module_name uu____579 =
    let uu____580 = FStar_ST.read current_module_name in
    match uu____580 with
    | None  -> failwith "Module name not set"
    | Some n1 -> n1 in
  let new_log_file uu____589 =
    let uu____590 = FStar_ST.read current_module_name in
    match uu____590 with
    | None  -> failwith "current module not set"
    | Some n1 ->
        let file_name =
          let uu____597 =
            let uu____601 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____612  ->
                 match uu____612 with | (m,uu____616) -> n1 = m) uu____601 in
          match uu____597 with
          | None  ->
              ((let uu____620 =
                  let uu____624 = FStar_ST.read used_file_names in
                  (n1, (Prims.parse_int "0")) :: uu____624 in
                FStar_ST.write used_file_names uu____620);
               n1)
          | Some (uu____640,k) ->
              ((let uu____645 =
                  let uu____649 = FStar_ST.read used_file_names in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____649 in
                FStar_ST.write used_file_names uu____645);
               (let uu____665 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n1 uu____665)) in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name (Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1 in
          FStar_ST.write log_file_opt (Some fh); fh)) in
  let get_log_file uu____679 =
    let uu____680 = FStar_ST.read log_file_opt in
    match uu____680 with | None  -> new_log_file () | Some fh -> fh in
  let append_to_log str =
    let uu____690 = get_log_file () in
    FStar_Util.append_to_file uu____690 str in
  let write_to_new_log str =
    let dir_name =
      let uu____696 = FStar_ST.read current_file_name in
      match uu____696 with
      | None  ->
          let dir_name =
            let uu____702 = FStar_ST.read current_module_name in
            match uu____702 with
            | None  -> failwith "current module not set"
            | Some n1 -> FStar_Util.format1 "queries-%s" n1 in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n1 -> n1 in
    let qnum = FStar_ST.read query_number in
    (let uu____718 =
       let uu____719 = FStar_ST.read query_number in
       uu____719 + (Prims.parse_int "1") in
     FStar_ST.write query_number uu____718);
    (let file_name =
       let uu____725 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" uu____725 in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name1 str) in
  let write_to_log str =
    let uu____731 =
      let uu____732 = FStar_Options.n_cores () in
      uu____732 > (Prims.parse_int "1") in
    if uu____731 then write_to_new_log str else append_to_log str in
  let close_log uu____737 =
    let uu____738 = FStar_ST.read log_file_opt in
    match uu____738 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None) in
  let log_file_name uu____751 =
    let uu____752 = FStar_ST.read current_file_name in
    match uu____752 with | None  -> failwith "no log file" | Some n1 -> n1 in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____769  ->
      let uu____770 =
        let uu____771 =
          FStar_Util.incr ctr;
          (let uu____776 = FStar_ST.read ctr in
           FStar_All.pipe_right uu____776 FStar_Util.string_of_int) in
        FStar_Util.format1 "bg-%s" uu____771 in
      new_z3proc uu____770 in
  let z3proc uu____782 =
    (let uu____784 =
       let uu____785 = FStar_ST.read the_z3proc in uu____785 = None in
     if uu____784
     then
       let uu____791 = let uu____793 = new_proc () in Some uu____793 in
       FStar_ST.write the_z3proc uu____791
     else ());
    (let uu____798 = FStar_ST.read the_z3proc in FStar_Util.must uu____798) in
  let x = [] in
  let grab uu____808 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____814 = FStar_Util.monitor_exit x in
  let refresh uu____819 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let uu____823 = let uu____825 = new_proc () in Some uu____825 in
     FStar_ST.write the_z3proc uu____823);
    query_logging.close_log ();
    release () in
  let restart uu____833 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let uu____841 = let uu____843 = new_proc () in Some uu____843 in
     FStar_ST.write the_z3proc uu____841);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____849  ->
    let uu____850 = FStar_Options.log_queries () in
    if uu____850
    then
      let uu____851 = query_logging.log_file_name () in
      Prims.strcat "@" uu____851
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
              (let uu____898 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right uu____898 (fun _0_38  -> Some _0_38)) in
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
            | uu____943 ->
                let uu____944 = FStar_ST.read in_core in
                if uu____944
                then
                  let uu____947 = parse_core line in
                  FStar_ST.write core uu____947
                else
                  (let uu____955 = FStar_ST.read in_statistics in
                   if uu____955
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
                     | uu____998 -> ()
                   else
                     (let uu____1001 = FStar_ST.read in_reason_unknown in
                      if uu____1001
                      then
                        let tkns = FStar_Util.split line "\"" in
                        let rsn =
                          match tkns with
                          | uu____1007::txt::uu____1009::[] -> txt
                          | uu____1010 -> line in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             rsn
                         else ())
                      else ())) in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____1016 = FStar_ST.read core in
           let uu____1023 = FStar_ST.read reason_unknown in
           (uu____1016, statistics, uu____1023)) in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____1039 = lblnegs rest in lname :: uu____1039
          | lname::uu____1042::rest when
              FStar_Util.starts_with lname "label_" -> lblnegs rest
          | uu____1045 -> [] in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____1060 = lblnegs tl1 in UNKNOWN uu____1060
          | "sat"::tl1 -> let uu____1064 = lblnegs tl1 in SAT uu____1064
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____1075 =
                  let uu____1076 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____1076 hd1 in
                FStar_Errors.warn FStar_Range.dummyRange uu____1075);
               result tl1 core)
          | uu____1077 ->
              let uu____1079 =
                let uu____1080 =
                  let uu____1081 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1 in
                  FStar_String.concat "\n" uu____1081 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____1080 in
              FStar_All.pipe_left failwith uu____1079 in
        let uu____1084 = get_data lines in
        match uu____1084 with
        | (core,statistics,reason_unknown) ->
            let uu____1099 = result lines core in (uu____1099, statistics) in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout1 =
        if fresh1
        then
          let uu____1109 = tid () in
          let uu____1110 = FStar_Options.z3_exe () in
          let uu____1111 = ini_params () in
          FStar_Util.launch_process uu____1109 uu____1110 uu____1111 input
            cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout1 = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout1) in
      parse (FStar_Util.trim_string stdout1)
let doZ3Exe: Prims.bool -> Prims.string -> (z3status* z3statistics) =
  fun fresh1  -> fun input  -> doZ3Exe' fresh1 input
let z3_options: Prims.unit -> Prims.string =
  fun uu____1126  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
let __proj__Mkjob__item__job projectee =
  match projectee with
  | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback projectee =
  match projectee with
  | { job = __fname__job; callback = __fname__callback;_} ->
      __fname__callback
type error_kind =
  | Timeout
  | Kill
  | Default
let uu___is_Timeout: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____1183 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1187 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1191 -> false
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
        fun uu____1248  ->
          let ekind uu___97_1259 =
            match uu___97_1259 with
            | TIMEOUT uu____1260 -> Timeout
            | SAT uu____1262 -> Default
            | UNKNOWN uu____1264 -> Default
            | KILLED  -> Kill
            | uu____1266 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let uu____1268 = doZ3Exe fresh1 input in
          match uu____1268 with
          | (status,statistics) ->
              let uu____1280 =
                let uu____1283 = FStar_Util.now () in
                FStar_Util.time_diff start uu____1283 in
              (match uu____1280 with
               | (uu____1291,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1371 = FStar_Options.debug_any () in
                           if uu____1371
                           then
                             let uu____1372 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1372
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1394 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1412  ->
                                               match uu____1412 with
                                               | (m,uu____1419,uu____1420) ->
                                                   (fst m) = l)) in
                                     match uu____1394 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1465 =
                             let uu____1476 =
                               let uu____1485 = ekind status in
                               (failing_assertions, uu____1485) in
                             FStar_Util.Inr uu____1476 in
                           (uu____1465, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____1513 = FStar_Options.debug_any () in
                           if uu____1513
                           then
                             let uu____1514 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1514
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1536 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1554  ->
                                               match uu____1554 with
                                               | (m,uu____1561,uu____1562) ->
                                                   (fst m) = l)) in
                                     match uu____1536 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1607 =
                             let uu____1618 =
                               let uu____1627 = ekind status in
                               (failing_assertions, uu____1627) in
                             FStar_Util.Inr uu____1618 in
                           (uu____1607, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____1655 = FStar_Options.debug_any () in
                           if uu____1655
                           then
                             let uu____1656 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status) in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1656
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1678 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1696  ->
                                               match uu____1696 with
                                               | (m,uu____1703,uu____1704) ->
                                                   (fst m) = l)) in
                                     match uu____1678 with
                                     | None  -> []
                                     | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                           let uu____1749 =
                             let uu____1760 =
                               let uu____1769 = ekind status in
                               (failing_assertions, uu____1769) in
                             FStar_Util.Inr uu____1760 in
                           (uu____1749, elapsed_time, statistics))) in
                   result)
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____1803  ->
    let j =
      let uu____1805 = FStar_ST.read job_queue in
      match uu____1805 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1832  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____1837  ->
    let uu____1838 = FStar_ST.read running in
    if uu____1838
    then
      let rec aux uu____1844 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1850 = FStar_ST.read job_queue in
         match uu____1850 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1861 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  ->
    let uu____1864 = j.job () in FStar_All.pipe_left j.callback uu____1864
let init: Prims.unit -> Prims.unit =
  fun uu____1895  ->
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
    (let uu____1916 =
       let uu____1918 = FStar_ST.read job_queue in
       FStar_List.append uu____1918 [j] in
     FStar_ST.write job_queue uu____1916);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let finish: Prims.unit -> Prims.unit =
  fun uu____1937  ->
    let rec aux uu____1941 =
      let uu____1942 =
        with_monitor job_queue
          (fun uu____1951  ->
             let uu____1952 = FStar_ST.read pending_jobs in
             let uu____1955 =
               let uu____1956 = FStar_ST.read job_queue in
               FStar_List.length uu____1956 in
             (uu____1952, uu____1955)) in
      match uu____1942 with
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
  fun uu____1990  -> FStar_ST.read fresh_scope
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2004 =
       let uu____2007 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____2007 in
     FStar_ST.write fresh_scope uu____2004);
    (let uu____2019 =
       let uu____2021 = FStar_ST.read bg_scope in
       FStar_List.append uu____2021
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg] in
     FStar_ST.write bg_scope uu____2019)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2033 =
       let uu____2036 = FStar_ST.read fresh_scope in FStar_List.tl uu____2036 in
     FStar_ST.write fresh_scope uu____2033);
    (let uu____2048 =
       let uu____2050 = FStar_ST.read bg_scope in
       FStar_List.append uu____2050
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop] in
     FStar_ST.write bg_scope uu____2048)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___98_2065  ->
            match uu___98_2065 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____2066 -> ()));
    (let uu____2068 = FStar_ST.read fresh_scope in
     match uu____2068 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____2086 -> failwith "Impossible");
    (let uu____2089 =
       let uu____2091 = FStar_ST.read bg_scope in
       FStar_List.append uu____2091 decls in
     FStar_ST.write bg_scope uu____2089)
let refresh: Prims.unit -> Prims.unit =
  fun uu____2101  ->
    (let uu____2103 =
       let uu____2104 = FStar_Options.n_cores () in
       uu____2104 < (Prims.parse_int "2") in
     if uu____2103 then bg_z3_proc.refresh () else ());
    (let uu____2106 =
       let uu____2108 =
         let uu____2111 = FStar_ST.read fresh_scope in
         FStar_List.rev uu____2111 in
       FStar_List.flatten uu____2108 in
     FStar_ST.write bg_scope uu____2106)
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    let uu____2132 = FStar_ST.read fresh_scope in
    match uu____2132 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____2153 -> failwith "Impossible"
let mk_cb used_unsat_core cb uu____2201 =
  match uu____2201 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____2233 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____2242,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
let mk_input: FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____2270 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory in
      FStar_All.pipe_right uu____2270 (FStar_String.concat "\n") in
    (let uu____2274 = FStar_Options.log_queries () in
     if uu____2274 then query_logging.write_to_log r else ());
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
            let uu____2310 = FStar_ST.read bg_scope in
            FStar_List.append uu____2310
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____2315 = filter_theory theory in
          match uu____2315 with
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
              let uu____2375 =
                match scope with
                | Some s -> FStar_List.rev s
                | None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____2386 = FStar_ST.read fresh_scope in
                      FStar_List.rev uu____2386)) in
              FStar_List.flatten uu____2375 in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
            let uu____2396 = filter_theory theory1 in
            match uu____2396 with
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
            let uu____2451 =
              let uu____2452 = FStar_Options.n_cores () in
              uu____2452 = (Prims.parse_int "1") in
            if uu____2451
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
open Prims
type z3version =
  | Z3V_Unknown of Prims.string 
  | Z3V of (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 
let uu___is_Z3V_Unknown : z3version -> Prims.bool =
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____17 -> false
  
let __proj__Z3V_Unknown__item___0 : z3version -> Prims.string =
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0 
let uu___is_Z3V : z3version -> Prims.bool =
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____34 -> false 
let __proj__Z3V__item___0 :
  z3version -> (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Z3V _0 -> _0 
let z3version_as_string : z3version -> Prims.string =
  fun uu___96_55  ->
    match uu___96_55 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____60 = FStar_Util.string_of_int i  in
        let uu____61 = FStar_Util.string_of_int j  in
        let uu____62 = FStar_Util.string_of_int k  in
        FStar_Util.format3 "%s.%s.%s" uu____60 uu____61 uu____62
  
let z3v_compare :
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.int FStar_Pervasives_Native.option
  =
  fun known  ->
    fun uu____74  ->
      match uu____74 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____83 -> FStar_Pervasives_Native.None
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
  fun uu____112  ->
    let prefix1 = "Z3 version "  in
    let uu____114 = FStar_ST.read _z3version  in
    match uu____114 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____120 =
          let uu____124 = FStar_Options.z3_exe ()  in
          FStar_Util.run_proc uu____124 "-version" ""  in
        (match uu____120 with
         | (uu____125,out,uu____127) ->
             let out1 =
               match FStar_Util.splitlines out with
               | x::uu____130 when FStar_Util.starts_with x prefix1 ->
                   let x1 =
                     let uu____133 =
                       FStar_Util.substring_from x
                         (FStar_String.length prefix1)
                        in
                     FStar_Util.trim_string uu____133  in
                   let x2 =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x1 ".")
                     with | uu____148 -> []  in
                   (match x2 with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____152 -> Z3V_Unknown out)
               | uu____154 -> Z3V_Unknown out  in
             (FStar_ST.write _z3version (FStar_Pervasives_Native.Some out1);
              out1))
  
let ini_params : Prims.unit -> Prims.string =
  fun uu____163  ->
    let z3_v = get_z3version ()  in
    (let uu____166 =
       let uu____167 = get_z3version ()  in
       z3v_le uu____167
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0"))
        in
     if uu____166
     then
       let uu____168 =
         let uu____169 =
           let uu____170 = z3version_as_string z3_v  in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____170
            in
         FStar_Util.Failure uu____169  in
       FStar_All.pipe_left FStar_Pervasives.raise uu____168
     else ());
    (let uu____172 =
       let uu____174 =
         let uu____176 =
           let uu____178 =
             let uu____179 =
               let uu____180 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____180  in
             FStar_Util.format1 "smt.random_seed=%s" uu____179  in
           [uu____178]  in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____176
          in
       let uu____181 = FStar_Options.z3_cliopt ()  in
       FStar_List.append uu____174 uu____181  in
     FStar_String.concat " " uu____172)
  
type label = Prims.string
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
type z3status =
  | UNSAT of unsat_core 
  | SAT of label Prims.list 
  | UNKNOWN of label Prims.list 
  | TIMEOUT of label Prims.list 
  | KILLED 
let uu___is_UNSAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____209 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____224 -> false
  
let __proj__SAT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____242 -> false
  
let __proj__UNKNOWN__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____260 -> false
  
let __proj__TIMEOUT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____276 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let status_to_string : z3status -> Prims.string =
  fun uu___97_281  ->
    match uu___97_281 with
    | SAT uu____282 -> "sat"
    | UNSAT uu____284 -> "unsat"
    | UNKNOWN uu____285 -> "unknown"
    | TIMEOUT uu____287 -> "timeout"
    | KILLED  -> "killed"
  
let tid : Prims.unit -> Prims.string =
  fun uu____292  ->
    let uu____293 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____293 FStar_Util.string_of_int
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let uu____306 = FStar_Options.z3_exe ()  in
    let uu____307 = ini_params ()  in
    FStar_Util.start_process id uu____306 uu____307 cond
  
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
    FStar_ST.write current_module_name (FStar_Pervasives_Native.Some n1)  in
  let get_module_name uu____623 =
    let uu____624 = FStar_ST.read current_module_name  in
    match uu____624 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____633 =
    let uu____634 = FStar_ST.read current_module_name  in
    match uu____634 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____641 =
            let uu____645 = FStar_ST.read used_file_names  in
            FStar_List.tryFind
              (fun uu____659  ->
                 match uu____659 with | (m,uu____663) -> n1 = m) uu____645
             in
          match uu____641 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____667 =
                  let uu____671 = FStar_ST.read used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____671  in
                FStar_ST.write used_file_names uu____667);
               n1)
          | FStar_Pervasives_Native.Some (uu____687,k) ->
              ((let uu____692 =
                  let uu____696 = FStar_ST.read used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____696  in
                FStar_ST.write used_file_names uu____692);
               (let uu____712 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____712))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.write current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.write log_file_opt (FStar_Pervasives_Native.Some fh); fh))
     in
  let get_log_file uu____726 =
    let uu____727 = FStar_ST.read log_file_opt  in
    match uu____727 with
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
    let uu____737 = get_log_file ()  in
    FStar_Util.append_to_file uu____737 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____743 = FStar_ST.read current_file_name  in
      match uu____743 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____749 = FStar_ST.read current_module_name  in
            match uu____749 with
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1
             in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.write current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
      | FStar_Pervasives_Native.Some n1 -> n1  in
    let qnum = FStar_ST.read query_number  in
    (let uu____765 =
       let uu____766 = FStar_ST.read query_number  in
       uu____766 + (Prims.parse_int "1")  in
     FStar_ST.write query_number uu____765);
    (let file_name =
       let uu____772 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____772  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____778 =
      let uu____779 = FStar_Options.n_cores ()  in
      uu____779 > (Prims.parse_int "1")  in
    if uu____778 then write_to_new_log str else append_to_log str  in
  let close_log uu____784 =
    let uu____785 = FStar_ST.read log_file_opt  in
    match uu____785 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.write log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____798 =
    let uu____799 = FStar_ST.read current_file_name  in
    match uu____799 with
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  } 
let bg_z3_proc : bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____816  ->
      let uu____817 =
        let uu____818 =
          FStar_Util.incr ctr;
          (let uu____823 = FStar_ST.read ctr  in
           FStar_All.pipe_right uu____823 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____818  in
      new_z3proc uu____817
     in
  let z3proc uu____829 =
    (let uu____831 =
       let uu____832 = FStar_ST.read the_z3proc  in
       uu____832 = FStar_Pervasives_Native.None  in
     if uu____831
     then
       let uu____838 =
         let uu____840 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____840  in
       FStar_ST.write the_z3proc uu____838
     else ());
    (let uu____845 = FStar_ST.read the_z3proc  in FStar_Util.must uu____845)
     in
  let x = []  in
  let grab uu____855 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____861 = FStar_Util.monitor_exit x  in
  let refresh uu____866 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let uu____870 =
       let uu____872 = new_proc ()  in FStar_Pervasives_Native.Some uu____872
        in
     FStar_ST.write the_z3proc uu____870);
    query_logging.close_log ();
    release ()  in
  let restart uu____880 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc FStar_Pervasives_Native.None;
    (let uu____888 =
       let uu____890 = new_proc ()  in FStar_Pervasives_Native.Some uu____890
        in
     FStar_ST.write the_z3proc uu____888);
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let at_log_file : Prims.unit -> Prims.string =
  fun uu____897  ->
    let uu____898 = FStar_Options.log_queries ()  in
    if uu____898
    then
      let uu____899 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____899
    else ""
  
let doZ3Exe' :
  Prims.bool ->
    Prims.string -> (z3status,z3statistics) FStar_Pervasives_Native.tuple2
  =
  fun fresh1  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string)
           in
        let get_data lines1 =
          let parse_core s =
            let s1 = FStar_Util.trim_string s  in
            let s2 =
              FStar_Util.substring s1 (Prims.parse_int "1")
                ((FStar_String.length s1) - (Prims.parse_int "2"))
               in
            if FStar_Util.starts_with s2 "error"
            then FStar_Pervasives_Native.None
            else
              (let uu____948 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare)
                  in
               FStar_All.pipe_right uu____948
                 (fun _0_38  -> FStar_Pervasives_Native.Some _0_38))
             in
          let core = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
          let statistics = FStar_Util.smap_create (Prims.parse_int "0")  in
          let reason_unknown = FStar_Util.mk_ref ""  in
          let in_core = FStar_Util.mk_ref false  in
          let in_statistics = FStar_Util.mk_ref false  in
          let in_reason_unknown = FStar_Util.mk_ref false  in
          let parse line =
            match line with
            | "<unsat-core>" -> FStar_ST.write in_core true
            | "<statistics>" -> FStar_ST.write in_statistics true
            | "<reason-unknown>" -> FStar_ST.write in_reason_unknown true
            | "</unsat-core>" -> FStar_ST.write in_core false
            | "</statistics>" -> FStar_ST.write in_statistics false
            | "</reason-unknown>" -> FStar_ST.write in_reason_unknown false
            | uu____993 ->
                let uu____994 = FStar_ST.read in_core  in
                if uu____994
                then
                  let uu____997 = parse_core line  in
                  FStar_ST.write core uu____997
                else
                  (let uu____1005 = FStar_ST.read in_statistics  in
                   if uu____1005
                   then
                     let pline =
                       FStar_Util.split (FStar_Util.trim_string line) ":"  in
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
                     | uu____1048 -> ()
                   else
                     (let uu____1051 = FStar_ST.read in_reason_unknown  in
                      if uu____1051
                      then
                        let tkns = FStar_Util.split line "\""  in
                        let rsn =
                          match tkns with
                          | uu____1057::txt::uu____1059::[] -> txt
                          | uu____1060 -> line  in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             (Prims.strcat "\"" (Prims.strcat rsn "\""))
                         else ())
                      else ()))
             in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____1067 = FStar_ST.read core  in
           let uu____1074 = FStar_ST.read reason_unknown  in
           (uu____1067, statistics, uu____1074))
           in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____1090 = lblnegs rest  in lname :: uu____1090
          | lname::uu____1093::rest when
              FStar_Util.starts_with lname "label_" -> lblnegs rest
          | uu____1096 -> []  in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____1111 = lblnegs tl1  in UNKNOWN uu____1111
          | "sat"::tl1 -> let uu____1115 = lblnegs tl1  in SAT uu____1115
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____1126 =
                  let uu____1127 = query_logging.get_module_name ()  in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____1127 hd1
                   in
                FStar_Errors.warn FStar_Range.dummyRange uu____1126);
               result tl1 core)
          | uu____1128 ->
              let uu____1130 =
                let uu____1131 =
                  let uu____1132 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1
                     in
                  FStar_String.concat "\n" uu____1132  in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____1131
                 in
              FStar_All.pipe_left failwith uu____1130
           in
        let uu____1136 = get_data lines  in
        match uu____1136 with
        | (core,statistics,reason_unknown) ->
            let uu____1151 = result lines core  in (uu____1151, statistics)
         in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
      let stdout1 =
        if fresh1
        then
          let uu____1161 = tid ()  in
          let uu____1162 = FStar_Options.z3_exe ()  in
          let uu____1163 = ini_params ()  in
          FStar_Util.launch_process uu____1161 uu____1162 uu____1163 input
            cond
        else
          (let proc = bg_z3_proc.grab ()  in
           let stdout1 = FStar_Util.ask_process proc input  in
           bg_z3_proc.release (); stdout1)
         in
      parse (FStar_Util.trim_string stdout1)
  
let doZ3Exe :
  Prims.bool ->
    Prims.string -> (z3status,z3statistics) FStar_Pervasives_Native.tuple2
  = fun fresh1  -> fun input  -> doZ3Exe' fresh1 input 
let z3_options : Prims.unit -> Prims.string =
  fun uu____1181  ->
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
type 'a job = {
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }
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
let uu___is_Timeout : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____1245 -> false
  
let uu___is_Kill : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____1250 -> false
  
let uu___is_Default : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____1255 -> false
  
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3 job
let job_queue : z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let pending_jobs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let with_monitor m f =
  FStar_Util.monitor_enter m;
  (let res = f ()  in FStar_Util.monitor_exit m; res) 
let z3_job :
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
        fun uu____1320  ->
          let ekind uu___98_1331 =
            match uu___98_1331 with
            | TIMEOUT uu____1332 -> Timeout
            | SAT uu____1334 -> Default
            | UNKNOWN uu____1336 -> Default
            | KILLED  -> Kill
            | uu____1338 -> failwith "Impossible"  in
          let start = FStar_Util.now ()  in
          let uu____1340 = doZ3Exe fresh1 input  in
          match uu____1340 with
          | (status,statistics) ->
              let uu____1352 =
                let uu____1355 = FStar_Util.now ()  in
                FStar_Util.time_diff start uu____1355  in
              (match uu____1352 with
               | (uu____1363,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____1443 = FStar_Options.debug_any ()  in
                           if uu____1443
                           then
                             let uu____1444 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1444
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1468 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1490  ->
                                               match uu____1490 with
                                               | (m,uu____1497,uu____1498) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____1468 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____1543 =
                             let uu____1554 =
                               let uu____1563 = ekind status  in
                               (failing_assertions, uu____1563)  in
                             FStar_Util.Inr uu____1554  in
                           (uu____1543, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____1591 = FStar_Options.debug_any ()  in
                           if uu____1591
                           then
                             let uu____1592 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1592
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1616 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1638  ->
                                               match uu____1638 with
                                               | (m,uu____1645,uu____1646) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____1616 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____1691 =
                             let uu____1702 =
                               let uu____1711 = ekind status  in
                               (failing_assertions, uu____1711)  in
                             FStar_Util.Inr uu____1702  in
                           (uu____1691, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____1739 = FStar_Options.debug_any ()  in
                           if uu____1739
                           then
                             let uu____1740 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____1740
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____1764 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____1786  ->
                                               match uu____1786 with
                                               | (m,uu____1793,uu____1794) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____1764 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____1839 =
                             let uu____1850 =
                               let uu____1859 = ekind status  in
                               (failing_assertions, uu____1859)  in
                             FStar_Util.Inr uu____1850  in
                           (uu____1839, elapsed_time, statistics)))
                      in
                   result)
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : Prims.unit -> Prims.unit =
  fun uu____1893  ->
    let j =
      let uu____1895 = FStar_ST.read job_queue  in
      match uu____1895 with
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.write job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1923  -> FStar_Util.decr pending_jobs);
    dequeue ()

and dequeue : Prims.unit -> Prims.unit =
  fun uu____1928  ->
    let uu____1929 = FStar_ST.read running  in
    if uu____1929
    then
      let rec aux uu____1935 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1941 = FStar_ST.read job_queue  in
         match uu____1941 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1952 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> Prims.unit =
  fun j  ->
    let uu____1955 = j.job ()  in FStar_All.pipe_left j.callback uu____1955

let init : Prims.unit -> Prims.unit =
  fun uu____1987  ->
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
    (let uu____2009 =
       let uu____2011 = FStar_ST.read job_queue  in
       FStar_List.append uu____2011 [j]  in
     FStar_ST.write job_queue uu____2009);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
  
let finish : Prims.unit -> Prims.unit =
  fun uu____2031  ->
    let rec aux uu____2035 =
      let uu____2036 =
        with_monitor job_queue
          (fun uu____2048  ->
             let uu____2049 = FStar_ST.read pending_jobs  in
             let uu____2052 =
               let uu____2053 = FStar_ST.read job_queue  in
               FStar_List.length uu____2053  in
             (uu____2049, uu____2052))
         in
      match uu____2036 with
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.write running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let mk_fresh_scope :
  Prims.unit -> FStar_SMTEncoding_Term.decl Prims.list Prims.list =
  fun uu____2088  -> FStar_ST.read fresh_scope 
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let push : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2103 =
       let uu____2106 = FStar_ST.read fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____2106
        in
     FStar_ST.write fresh_scope uu____2103);
    (let uu____2118 =
       let uu____2120 = FStar_ST.read bg_scope  in
       FStar_List.append uu____2120
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.write bg_scope uu____2118)
  
let pop : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____2133 =
       let uu____2136 = FStar_ST.read fresh_scope  in
       FStar_List.tl uu____2136  in
     FStar_ST.write fresh_scope uu____2133);
    (let uu____2148 =
       let uu____2150 = FStar_ST.read bg_scope  in
       FStar_List.append uu____2150
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.write bg_scope uu____2148)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___99_2167  ->
            match uu___99_2167 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
            | uu____2168 -> ()));
    (let uu____2170 = FStar_ST.read fresh_scope  in
     match uu____2170 with
     | hd1::tl1 ->
         FStar_ST.write fresh_scope ((FStar_List.append hd1 decls) :: tl1)
     | uu____2188 -> failwith "Impossible");
    (let uu____2191 =
       let uu____2193 = FStar_ST.read bg_scope  in
       FStar_List.append uu____2193 decls  in
     FStar_ST.write bg_scope uu____2191)
  
let refresh : Prims.unit -> Prims.unit =
  fun uu____2204  ->
    (let uu____2206 =
       let uu____2207 = FStar_Options.n_cores ()  in
       uu____2207 < (Prims.parse_int "2")  in
     if uu____2206 then bg_z3_proc.refresh () else ());
    (let uu____2209 =
       let uu____2211 =
         let uu____2214 = FStar_ST.read fresh_scope  in
         FStar_List.rev uu____2214  in
       FStar_List.flatten uu____2211  in
     FStar_ST.write bg_scope uu____2209)
  
let mark : Prims.string -> Prims.unit = fun msg  -> push msg 
let reset_mark : Prims.string -> Prims.unit = fun msg  -> pop msg; refresh () 
let commit_mark : Prims.string -> Prims.unit =
  fun msg  ->
    let uu____2238 = FStar_ST.read fresh_scope  in
    match uu____2238 with
    | hd1::s::tl1 ->
        FStar_ST.write fresh_scope ((FStar_List.append hd1 s) :: tl1)
    | uu____2259 -> failwith "Impossible"
  
let mk_cb used_unsat_core cb uu____2316 =
  match uu____2316 with
  | (uc_errs,time,statistics) ->
      if used_unsat_core
      then
        (match uc_errs with
         | FStar_Util.Inl uu____2348 -> cb (uc_errs, time, statistics)
         | FStar_Util.Inr (uu____2357,ek) ->
             cb ((FStar_Util.Inr ([], ek)), time, statistics))
      else cb (uc_errs, time, statistics)
  
let mk_input : FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
  fun theory  ->
    let r =
      let uu____2386 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
          theory
         in
      FStar_All.pipe_right uu____2386 (FStar_String.concat "\n")  in
    (let uu____2390 = FStar_Options.log_queries ()  in
     if uu____2390 then query_logging.write_to_log r else ());
    r
  
type z3result =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3
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
            let uu____2430 = FStar_ST.read bg_scope  in
            FStar_List.append uu____2430
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
             in
          let uu____2435 = filter_theory theory  in
          match uu____2435 with
          | (theory1,used_unsat_core) ->
              let cb1 = mk_cb used_unsat_core cb  in
              let input = mk_input theory1  in
              (FStar_ST.write bg_scope [];
               run_job
                 { job = (z3_job false label_messages input); callback = cb1
                 })
  
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
              let uu____2500 =
                match scope with
                | FStar_Pervasives_Native.Some s -> FStar_List.rev s
                | FStar_Pervasives_Native.None  ->
                    (FStar_ST.write bg_scope [];
                     (let uu____2511 = FStar_ST.read fresh_scope  in
                      FStar_List.rev uu____2511))
                 in
              FStar_List.flatten uu____2500  in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
               in
            let uu____2521 = filter_theory theory1  in
            match uu____2521 with
            | (theory2,used_unsat_core) ->
                let cb1 = mk_cb used_unsat_core cb  in
                let input = mk_input theory2  in
                enqueue
                  { job = (z3_job true label_messages input); callback = cb1
                  }
  
let ask :
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
            let uu____2581 =
              let uu____2582 = FStar_Options.n_cores ()  in
              uu____2582 = (Prims.parse_int "1")  in
            if uu____2581
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
  
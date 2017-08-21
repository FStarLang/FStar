open Prims
type z3version =
<<<<<<< HEAD
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
  fun uu___96_70  ->
    match uu___96_70 with
=======
  | Z3V_Unknown of Prims.string
  | Z3V of (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
let (uu___is_Z3V_Unknown :z3version -> Prims.bool)=
  fun projectee  ->
    match projectee with | Z3V_Unknown _0 -> true | uu____20 -> false
let (__proj__Z3V_Unknown__item___0 :z3version -> Prims.string)=
  fun projectee  -> match projectee with | Z3V_Unknown _0 -> _0
let (uu___is_Z3V :z3version -> Prims.bool)=
  fun projectee  -> match projectee with | Z3V _0 -> true | uu____40 -> false
let (__proj__Z3V__item___0
  :z3version ->
     (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)=
  fun projectee  -> match projectee with | Z3V _0 -> _0
let (z3version_as_string :z3version -> Prims.string)=
  fun uu___95_70  ->
    match uu___95_70 with
>>>>>>> taramana_pointers_with_codes_modifies
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let uu____75 = FStar_Util.string_of_int i  in
        let uu____76 = FStar_Util.string_of_int j  in
        let uu____77 = FStar_Util.string_of_int k  in
        FStar_Util.format3 "%s.%s.%s" uu____75 uu____76 uu____77
<<<<<<< HEAD
  
let z3v_compare :
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.int FStar_Pervasives_Native.option
  =
=======
let (z3v_compare
  :z3version ->
     (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
       Prims.int FStar_Pervasives_Native.option)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let z3v_le :
  z3version ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
      Prims.bool
  =
=======
let (z3v_le
  :z3version ->
     (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3 ->
       Prims.bool)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | FStar_Pervasives_Native.None  -> false
      | FStar_Pervasives_Native.Some i -> i >= (Prims.parse_int "0")
<<<<<<< HEAD
  
let _z3version : z3version FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let get_z3version : Prims.unit -> z3version =
=======
let (_z3version :z3version FStar_Pervasives_Native.option FStar_ST.ref)=
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (get_z3version :Prims.unit -> z3version)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____150  ->
    let prefix1 = "Z3 version "  in
    let uu____152 = FStar_ST.op_Bang _z3version  in
    match uu____152 with
    | FStar_Pervasives_Native.Some version -> version
    | FStar_Pervasives_Native.None  ->
        let uu____174 =
          let uu____181 = FStar_Options.z3_exe ()  in
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
<<<<<<< HEAD
  
let ini_params : Prims.unit -> Prims.string =
=======
let (ini_params :Prims.unit -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun uu____238  ->
    let z3_v = get_z3version ()  in
    (let uu____241 =
       let uu____242 = get_z3version ()  in
       z3v_le uu____242
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0"))
        in
     if uu____241
     then
       let uu____243 =
         let uu____244 =
           let uu____245 = z3version_as_string z3_v  in
           FStar_Util.format1
             "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
             uu____245
            in
         FStar_Util.Failure uu____244  in
       FStar_All.pipe_left FStar_Exn.raise uu____243
     else ());
    (let uu____247 =
       let uu____250 =
         let uu____253 =
           let uu____256 =
             let uu____257 =
               let uu____258 = FStar_Options.z3_seed ()  in
               FStar_Util.string_of_int uu____258  in
             FStar_Util.format1 "smt.random_seed=%s" uu____257  in
           [uu____256]  in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" ::
           uu____253
          in
       let uu____259 = FStar_Options.z3_cliopt ()  in
       FStar_List.append uu____250 uu____259  in
     FStar_String.concat " " uu____247)
  
type label = Prims.string
type unsat_core = Prims.string Prims.list FStar_Pervasives_Native.option
type z3status =
<<<<<<< HEAD
  | UNSAT of unsat_core 
  | SAT of label Prims.list 
  | UNKNOWN of label Prims.list 
  | TIMEOUT of label Prims.list 
  | KILLED 
let uu___is_UNSAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____293 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____309 -> false
  
let __proj__SAT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____331 -> false
  
let __proj__UNKNOWN__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____353 -> false
  
let __proj__TIMEOUT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____372 -> false
  
type z3statistics = Prims.string FStar_Util.smap
let status_to_string : z3status -> Prims.string =
  fun uu___97_378  ->
    match uu___97_378 with
    | SAT uu____379 -> "sat"
    | UNSAT uu____382 -> "unsat"
    | UNKNOWN uu____383 -> "unknown"
    | TIMEOUT uu____386 -> "timeout"
    | KILLED  -> "killed"
  
let tid : Prims.unit -> Prims.string =
  fun uu____392  ->
    let uu____393 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right uu____393 FStar_Util.string_of_int
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let uu____406 = FStar_Options.z3_exe ()  in
    let uu____407 = ini_params ()  in
    FStar_Util.start_process id uu____406 uu____407 cond
  
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc ;
  release: Prims.unit -> Prims.unit ;
  refresh: Prims.unit -> Prims.unit ;
  restart: Prims.unit -> Prims.unit }
let __proj__Mkbgproc__item__grab : bgproc -> Prims.unit -> FStar_Util.proc =
=======
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
let (uu___is_UNSAT :z3status -> Prims.bool)=
  fun projectee  ->
    match projectee with | UNSAT _0 -> true | uu____305 -> false
let (__proj__UNSAT__item___0 :z3status -> unsat_core)=
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let (uu___is_SAT :z3status -> Prims.bool)=
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____325 -> false
let (__proj__SAT__item___0
  :z3status ->
     (FStar_SMTEncoding_Term.error_labels,Prims.string
                                            FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | SAT _0 -> _0
let (uu___is_UNKNOWN :z3status -> Prims.bool)=
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____363 -> false
let (__proj__UNKNOWN__item___0
  :z3status ->
     (FStar_SMTEncoding_Term.error_labels,Prims.string
                                            FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let (uu___is_TIMEOUT :z3status -> Prims.bool)=
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____401 -> false
let (__proj__TIMEOUT__item___0
  :z3status ->
     (FStar_SMTEncoding_Term.error_labels,Prims.string
                                            FStar_Pervasives_Native.option)
       FStar_Pervasives_Native.tuple2)=
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let (uu___is_KILLED :z3status -> Prims.bool)=
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____432 -> false
type z3statistics = Prims.string FStar_Util.smap
let (status_tag :z3status -> Prims.string)=
  fun uu___96_438  ->
    match uu___96_438 with
    | SAT uu____439 -> "sat"
    | UNSAT uu____446 -> "unsat"
    | UNKNOWN uu____447 -> "unknown"
    | TIMEOUT uu____454 -> "timeout"
    | KILLED  -> "killed"
let (status_string_and_errors
  :z3status ->
     (Prims.string,FStar_SMTEncoding_Term.error_labels)
       FStar_Pervasives_Native.tuple2)=
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
let (tid :Prims.unit -> Prims.string)=
  fun uu____505  ->
    let uu____506 = FStar_Util.current_tid () in
    FStar_All.pipe_right uu____506 FStar_Util.string_of_int
let (new_z3proc :Prims.string -> FStar_Util.proc)=
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let uu____519 = FStar_Options.z3_exe () in
    let uu____520 = ini_params () in
    FStar_Util.start_process id uu____519 uu____520 cond
type bgproc =
  {
  grab: Prims.unit -> FStar_Util.proc;
  release: Prims.unit -> Prims.unit;
  refresh: Prims.unit -> Prims.unit;
  restart: Prims.unit -> Prims.unit;}
let (__proj__Mkbgproc__item__grab :bgproc -> Prims.unit -> FStar_Util.proc)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__grab
<<<<<<< HEAD
  
let __proj__Mkbgproc__item__release : bgproc -> Prims.unit -> Prims.unit =
=======
let (__proj__Mkbgproc__item__release :bgproc -> Prims.unit -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__release
<<<<<<< HEAD
  
let __proj__Mkbgproc__item__refresh : bgproc -> Prims.unit -> Prims.unit =
=======
let (__proj__Mkbgproc__item__refresh :bgproc -> Prims.unit -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__refresh
<<<<<<< HEAD
  
let __proj__Mkbgproc__item__restart : bgproc -> Prims.unit -> Prims.unit =
=======
let (__proj__Mkbgproc__item__restart :bgproc -> Prims.unit -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { grab = __fname__grab; release = __fname__release;
        refresh = __fname__refresh; restart = __fname__restart;_} ->
        __fname__restart
  
type query_log =
  {
<<<<<<< HEAD
  get_module_name: Prims.unit -> Prims.string ;
  set_module_name: Prims.string -> Prims.unit ;
  write_to_log: Prims.string -> Prims.unit ;
  close_log: Prims.unit -> Prims.unit ;
  log_file_name: Prims.unit -> Prims.string }
let __proj__Mkquery_log__item__get_module_name :
  query_log -> Prims.unit -> Prims.string =
=======
  get_module_name: Prims.unit -> Prims.string;
  set_module_name: Prims.string -> Prims.unit;
  write_to_log: Prims.string -> Prims.unit;
  close_log: Prims.unit -> Prims.unit;
  log_file_name: Prims.unit -> Prims.string;}
let (__proj__Mkquery_log__item__get_module_name
  :query_log -> Prims.unit -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__get_module_name
<<<<<<< HEAD
  
let __proj__Mkquery_log__item__set_module_name :
  query_log -> Prims.string -> Prims.unit =
=======
let (__proj__Mkquery_log__item__set_module_name
  :query_log -> Prims.string -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__set_module_name
<<<<<<< HEAD
  
let __proj__Mkquery_log__item__write_to_log :
  query_log -> Prims.string -> Prims.unit =
=======
let (__proj__Mkquery_log__item__write_to_log
  :query_log -> Prims.string -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__write_to_log
<<<<<<< HEAD
  
let __proj__Mkquery_log__item__close_log :
  query_log -> Prims.unit -> Prims.unit =
=======
let (__proj__Mkquery_log__item__close_log
  :query_log -> Prims.unit -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__close_log
<<<<<<< HEAD
  
let __proj__Mkquery_log__item__log_file_name :
  query_log -> Prims.unit -> Prims.string =
=======
let (__proj__Mkquery_log__item__log_file_name
  :query_log -> Prims.unit -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { get_module_name = __fname__get_module_name;
        set_module_name = __fname__set_module_name;
        write_to_log = __fname__write_to_log; close_log = __fname__close_log;
        log_file_name = __fname__log_file_name;_} -> __fname__log_file_name
<<<<<<< HEAD
  
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
  let get_module_name uu____766 =
    let uu____767 = FStar_ST.op_Bang current_module_name  in
    match uu____767 with
    | FStar_Pervasives_Native.None  -> failwith "Module name not set"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  let new_log_file uu____806 =
    let uu____807 = FStar_ST.op_Bang current_module_name  in
    match uu____807 with
    | FStar_Pervasives_Native.None  -> failwith "current module not set"
    | FStar_Pervasives_Native.Some n1 ->
        let file_name =
          let uu____844 =
            let uu____851 = FStar_ST.op_Bang used_file_names  in
            FStar_List.tryFind
              (fun uu____913  ->
                 match uu____913 with | (m,uu____919) -> n1 = m) uu____851
             in
          match uu____844 with
          | FStar_Pervasives_Native.None  ->
              ((let uu____925 =
                  let uu____932 = FStar_ST.op_Bang used_file_names  in
                  (n1, (Prims.parse_int "0")) :: uu____932  in
                FStar_ST.op_Colon_Equals used_file_names uu____925);
               n1)
          | FStar_Pervasives_Native.Some (uu____1039,k) ->
              ((let uu____1046 =
                  let uu____1053 = FStar_ST.op_Bang used_file_names  in
                  (n1, (k + (Prims.parse_int "1"))) :: uu____1053  in
                FStar_ST.op_Colon_Equals used_file_names uu____1046);
               (let uu____1160 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n1 uu____1160))
           in
        let file_name1 = FStar_Util.format1 "queries-%s.smt2" file_name  in
=======
let (query_logging :query_log)=
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
>>>>>>> taramana_pointers_with_codes_modifies
        (FStar_ST.op_Colon_Equals current_file_name
           (FStar_Pervasives_Native.Some file_name1);
         (let fh = FStar_Util.open_file_for_writing file_name1  in
          FStar_ST.op_Colon_Equals log_file_opt
            (FStar_Pervasives_Native.Some fh);
<<<<<<< HEAD
          fh))
     in
  let get_log_file uu____1232 =
    let uu____1233 = FStar_ST.op_Bang log_file_opt  in
    match uu____1233 with
=======
          fh)) in
  let get_log_file uu____1345 =
    let uu____1346 = FStar_ST.op_Bang log_file_opt in
    match uu____1346 with
>>>>>>> taramana_pointers_with_codes_modifies
    | FStar_Pervasives_Native.None  -> new_log_file ()
    | FStar_Pervasives_Native.Some fh -> fh  in
  let append_to_log str =
<<<<<<< HEAD
    let uu____1273 = get_log_file ()  in
    FStar_Util.append_to_file uu____1273 str  in
  let write_to_new_log str =
    let dir_name =
      let uu____1279 = FStar_ST.op_Bang current_file_name  in
      match uu____1279 with
      | FStar_Pervasives_Native.None  ->
          let dir_name =
            let uu____1315 = FStar_ST.op_Bang current_module_name  in
            match uu____1315 with
=======
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
>>>>>>> taramana_pointers_with_codes_modifies
            | FStar_Pervasives_Native.None  ->
                failwith "current module not set"
            | FStar_Pervasives_Native.Some n1 ->
                FStar_Util.format1 "queries-%s" n1
             in
          (FStar_Util.mkdir true dir_name;
           FStar_ST.op_Colon_Equals current_file_name
             (FStar_Pervasives_Native.Some dir_name);
           dir_name)
<<<<<<< HEAD
      | FStar_Pervasives_Native.Some n1 -> n1  in
    let qnum = FStar_ST.op_Bang query_number  in
    (let uu____1412 =
       let uu____1413 = FStar_ST.op_Bang query_number  in
       uu____1413 + (Prims.parse_int "1")  in
     FStar_ST.op_Colon_Equals query_number uu____1412);
    (let file_name =
       let uu____1463 = FStar_Util.string_of_int qnum  in
       FStar_Util.format1 "query-%s.smt2" uu____1463  in
     let file_name1 = FStar_Util.concat_dir_filename dir_name file_name  in
     FStar_Util.write_file file_name1 str)
     in
  let write_to_log str =
    let uu____1469 =
      let uu____1470 = FStar_Options.n_cores ()  in
      uu____1470 > (Prims.parse_int "1")  in
    if uu____1469 then write_to_new_log str else append_to_log str  in
  let close_log uu____1475 =
    let uu____1476 = FStar_ST.op_Bang log_file_opt  in
    match uu____1476 with
    | FStar_Pervasives_Native.None  -> ()
    | FStar_Pervasives_Native.Some fh ->
        (FStar_Util.close_file fh;
         FStar_ST.op_Colon_Equals log_file_opt FStar_Pervasives_Native.None)
     in
  let log_file_name uu____1548 =
    let uu____1549 = FStar_ST.op_Bang current_file_name  in
    match uu____1549 with
=======
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
>>>>>>> taramana_pointers_with_codes_modifies
    | FStar_Pervasives_Native.None  -> failwith "no log file"
    | FStar_Pervasives_Native.Some n1 -> n1  in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
<<<<<<< HEAD
  } 
let bg_z3_proc : bgproc =
  let the_z3proc = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____1598  ->
      let uu____1599 =
        let uu____1600 =
          FStar_Util.incr ctr;
          (let uu____1623 = FStar_ST.op_Bang ctr  in
           FStar_All.pipe_right uu____1623 FStar_Util.string_of_int)
           in
        FStar_Util.format1 "bg-%s" uu____1600  in
      new_z3proc uu____1599
     in
  let z3proc uu____1651 =
    (let uu____1653 =
       let uu____1654 = FStar_ST.op_Bang the_z3proc  in
       uu____1654 = FStar_Pervasives_Native.None  in
     if uu____1653
     then
       let uu____1691 =
         let uu____1694 = new_proc ()  in
         FStar_Pervasives_Native.Some uu____1694  in
       FStar_ST.op_Colon_Equals the_z3proc uu____1691
     else ());
    (let uu____1728 = FStar_ST.op_Bang the_z3proc  in
     FStar_Util.must uu____1728)
     in
  let x = []  in
  let grab uu____1769 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____1776 = FStar_Util.monitor_exit x  in
  let refresh uu____1782 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let uu____1786 =
       let uu____1789 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____1789  in
     FStar_ST.op_Colon_Equals the_z3proc uu____1786);
    query_logging.close_log ();
    release ()  in
  let restart uu____1826 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.op_Colon_Equals the_z3proc FStar_Pervasives_Native.None;
    (let uu____1863 =
       let uu____1866 = new_proc ()  in
       FStar_Pervasives_Native.Some uu____1866  in
     FStar_ST.op_Colon_Equals the_z3proc uu____1863);
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let at_log_file : Prims.unit -> Prims.string =
  fun uu____1902  ->
    let uu____1903 = FStar_Options.log_queries ()  in
    if uu____1903
    then
      let uu____1904 = query_logging.log_file_name ()  in
      Prims.strcat "@" uu____1904
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
              (let uu____1964 =
                 FStar_All.pipe_right (FStar_Util.split s2 " ")
                   (FStar_Util.sort_with FStar_String.compare)
                  in
               FStar_All.pipe_right uu____1964
                 (fun _0_40  -> FStar_Pervasives_Native.Some _0_40))
             in
          let core = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
          let statistics = FStar_Util.smap_create (Prims.parse_int "0")  in
          let reason_unknown = FStar_Util.mk_ref ""  in
          let in_core = FStar_Util.mk_ref false  in
          let in_statistics = FStar_Util.mk_ref false  in
          let in_reason_unknown = FStar_Util.mk_ref false  in
          let parse line =
            match line with
            | "<unsat-core>" -> FStar_ST.op_Colon_Equals in_core true
            | "<statistics>" -> FStar_ST.op_Colon_Equals in_statistics true
            | "<reason-unknown>" ->
                FStar_ST.op_Colon_Equals in_reason_unknown true
            | "</unsat-core>" -> FStar_ST.op_Colon_Equals in_core false
            | "</statistics>" -> FStar_ST.op_Colon_Equals in_statistics false
            | "</reason-unknown>" ->
                FStar_ST.op_Colon_Equals in_reason_unknown false
            | uu____2153 ->
                let uu____2154 = FStar_ST.op_Bang in_core  in
                if uu____2154
                then
                  let uu____2179 = parse_core line  in
                  FStar_ST.op_Colon_Equals core uu____2179
                else
                  (let uu____2225 = FStar_ST.op_Bang in_statistics  in
                   if uu____2225
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
                     | uu____2269 -> ()
                   else
                     (let uu____2273 = FStar_ST.op_Bang in_reason_unknown  in
                      if uu____2273
                      then
                        let tkns = FStar_Util.split line "\""  in
                        let rsn =
                          match tkns with
                          | uu____2302::txt::uu____2304::[] -> txt
                          | uu____2305 -> line  in
                        (if rsn <> "unknown"
                         then
                           FStar_Util.smap_add statistics "reason-unknown"
                             (Prims.strcat "\"" (Prims.strcat rsn "\""))
                         else ())
                      else ()))
             in
          FStar_List.iter (fun line  -> parse line) lines1;
          (let uu____2313 = FStar_ST.op_Bang core  in
           let uu____2358 = FStar_ST.op_Bang reason_unknown  in
           (uu____2313, statistics, uu____2358))
           in
        let rec lblnegs lines1 =
          match lines1 with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let uu____2403 = lblnegs rest  in lname :: uu____2403
          | lname::uu____2407::rest when
              FStar_Util.starts_with lname "label_" -> lblnegs rest
          | uu____2411 -> []  in
        let rec result lines1 core =
          match lines1 with
          | "timeout"::tl1 -> TIMEOUT []
          | "unknown"::tl1 ->
              let uu____2431 = lblnegs tl1  in UNKNOWN uu____2431
          | "sat"::tl1 -> let uu____2437 = lblnegs tl1  in SAT uu____2437
          | "unsat"::tl1 -> UNSAT core
          | "killed"::tl1 -> (bg_z3_proc.restart (); KILLED)
          | hd1::tl1 ->
              ((let uu____2452 =
                  let uu____2453 = query_logging.get_module_name ()  in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    uu____2453 hd1
                   in
                FStar_Errors.warn FStar_Range.dummyRange uu____2452);
               result tl1 core)
          | uu____2454 ->
              let uu____2457 =
                let uu____2458 =
                  let uu____2459 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines1
                     in
                  FStar_String.concat "\n" uu____2459  in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n"
                  uu____2458
                 in
              FStar_All.pipe_left failwith uu____2457
           in
        let uu____2464 = get_data lines  in
        match uu____2464 with
        | (core,statistics,reason_unknown) ->
            let uu____2490 = result lines core  in (uu____2490, statistics)
         in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
      let stdout1 =
        if fresh1
        then
          let uu____2500 = tid ()  in
          let uu____2501 = FStar_Options.z3_exe ()  in
          let uu____2502 = ini_params ()  in
          FStar_Util.launch_process uu____2500 uu____2501 uu____2502 input
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
  fun uu____2522  ->
=======
  }
let (bg_z3_proc :bgproc)=
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
let (at_log_file :Prims.unit -> Prims.string)=
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
let (__proj__Mksmt_output__item__smt_result
  :smt_output -> smt_output_section)=
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_result
let (__proj__Mksmt_output__item__smt_reason_unknown
  :smt_output -> smt_output_section FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_reason_unknown
let (__proj__Mksmt_output__item__smt_unsat_core
  :smt_output -> smt_output_section FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_unsat_core
let (__proj__Mksmt_output__item__smt_statistics
  :smt_output -> smt_output_section FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_statistics
let (__proj__Mksmt_output__item__smt_labels
  :smt_output -> smt_output_section FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { smt_result = __fname__smt_result;
        smt_reason_unknown = __fname__smt_reason_unknown;
        smt_unsat_core = __fname__smt_unsat_core;
        smt_statistics = __fname__smt_statistics;
        smt_labels = __fname__smt_labels;_} -> __fname__smt_labels
let (smt_output_sections :Prims.string Prims.list -> smt_output)=
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
let (doZ3Exe
  :Prims.bool ->
     Prims.string ->
       FStar_SMTEncoding_Term.error_labels ->
         (z3status,z3statistics) FStar_Pervasives_Native.tuple2)=
  fun fresh1  ->
    fun input  ->
      fun label_messages  ->
        let parse z3out =
          let lines =
            FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
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
            FStar_Util.launch_process uu____3023 uu____3024 uu____3025 input
              cond
          else
            (let proc = bg_z3_proc.grab () in
             let stdout1 = FStar_Util.ask_process proc input in
             bg_z3_proc.release (); stdout1) in
        parse (FStar_Util.trim_string stdout1)
let (z3_options :Prims.unit -> Prims.string)=
  fun uu____3033  ->
>>>>>>> taramana_pointers_with_codes_modifies
    "(set-option :global-decls false)\n(set-option :smt.mbqi false)\n(set-option :auto_config false)\n(set-option :produce-unsat-cores true)\n"
  
type 'a job = {
<<<<<<< HEAD
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }
let __proj__Mkjob__item__job : 'a . 'a job -> Prims.unit -> 'a =
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
  
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> Prims.unit =
=======
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
let __proj__Mkjob__item__job : 'a . 'a job -> Prims.unit -> 'a=
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} -> __fname__job
let __proj__Mkjob__item__callback : 'a . 'a job -> 'a -> Prims.unit=
>>>>>>> taramana_pointers_with_codes_modifies
  fun projectee  ->
    match projectee with
    | { job = __fname__job; callback = __fname__callback;_} ->
        __fname__callback
<<<<<<< HEAD
  
type error_kind =
  | Timeout 
  | Kill 
  | Default 
let uu___is_Timeout : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____2591 -> false
  
let uu___is_Kill : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Kill  -> true | uu____2596 -> false
  
let uu___is_Default : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____2601 -> false
  
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                 FStar_Pervasives_Native.tuple2)
     FStar_Util.either,Prims.int,z3statistics)
    FStar_Pervasives_Native.tuple3 job
let job_queue : z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let pending_jobs : Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0") 
let with_monitor :
  'Auu____2648 'Auu____2649 .
    'Auu____2649 -> (Prims.unit -> 'Auu____2648) -> 'Auu____2648
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
          ((unsat_core,(FStar_SMTEncoding_Term.error_labels,error_kind)
                         FStar_Pervasives_Native.tuple2)
             FStar_Util.either,Prims.int,z3statistics)
            FStar_Pervasives_Native.tuple3
  =
  fun fresh1  ->
    fun label_messages  ->
      fun input  ->
        fun uu____2695  ->
          let ekind uu___98_2713 =
            match uu___98_2713 with
            | TIMEOUT uu____2714 -> Timeout
            | SAT uu____2717 -> Default
            | UNKNOWN uu____2720 -> Default
            | KILLED  -> Kill
            | uu____2723 -> failwith "Impossible"  in
          let start = FStar_Util.now ()  in
          let uu____2725 = doZ3Exe fresh1 input  in
          match uu____2725 with
          | (status,statistics) ->
              let uu____2746 =
                let uu____2751 = FStar_Util.now ()  in
                FStar_Util.time_diff start uu____2751  in
              (match uu____2746 with
               | (uu____2766,elapsed_time) ->
                   let result =
                     match status with
                     | UNSAT core ->
                         ((FStar_Util.Inl core), elapsed_time, statistics)
                     | KILLED  ->
                         ((FStar_Util.Inr ([], Kill)), elapsed_time,
                           statistics)
                     | TIMEOUT lblnegs ->
                         ((let uu____2920 = FStar_Options.debug_any ()  in
                           if uu____2920
                           then
                             let uu____2921 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____2921
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____2963 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____3002  ->
                                               match uu____3002 with
                                               | (m,uu____3014,uu____3015) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____2963 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____3101 =
                             let uu____3122 =
                               let uu____3139 = ekind status  in
                               (failing_assertions, uu____3139)  in
                             FStar_Util.Inr uu____3122  in
                           (uu____3101, elapsed_time, statistics)))
                     | SAT lblnegs ->
                         ((let uu____3192 = FStar_Options.debug_any ()  in
                           if uu____3192
                           then
                             let uu____3193 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____3193
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____3235 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____3274  ->
                                               match uu____3274 with
                                               | (m,uu____3286,uu____3287) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____3235 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____3373 =
                             let uu____3394 =
                               let uu____3411 = ekind status  in
                               (failing_assertions, uu____3411)  in
                             FStar_Util.Inr uu____3394  in
                           (uu____3373, elapsed_time, statistics)))
                     | UNKNOWN lblnegs ->
                         ((let uu____3464 = FStar_Options.debug_any ()  in
                           if uu____3464
                           then
                             let uu____3465 =
                               FStar_Util.format1 "Z3 says: %s\n"
                                 (status_to_string status)
                                in
                             FStar_All.pipe_left FStar_Util.print_string
                               uu____3465
                           else ());
                          (let failing_assertions =
                             FStar_All.pipe_right lblnegs
                               (FStar_List.collect
                                  (fun l  ->
                                     let uu____3507 =
                                       FStar_All.pipe_right label_messages
                                         (FStar_List.tryFind
                                            (fun uu____3546  ->
                                               match uu____3546 with
                                               | (m,uu____3558,uu____3559) ->
                                                   (FStar_Pervasives_Native.fst
                                                      m)
                                                     = l))
                                        in
                                     match uu____3507 with
                                     | FStar_Pervasives_Native.None  -> []
                                     | FStar_Pervasives_Native.Some
                                         (lbl,msg,r) -> [(lbl, msg, r)]))
                              in
                           let uu____3645 =
                             let uu____3666 =
                               let uu____3683 = ekind status  in
                               (failing_assertions, uu____3683)  in
                             FStar_Util.Inr uu____3666  in
                           (uu____3645, elapsed_time, statistics)))
                      in
                   result)
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : Prims.unit -> Prims.unit =
  fun uu____3747  ->
    let j =
      let uu____3749 = FStar_ST.op_Bang job_queue  in
      match uu____3749 with
=======
type z3job =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3 job
let (job_queue :z3job Prims.list FStar_ST.ref)= FStar_Util.mk_ref []
let (pending_jobs :Prims.int FStar_ST.ref)=
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor :
  'Auu____3136 'Auu____3137 .
    'Auu____3137 -> (Prims.unit -> 'Auu____3136) -> 'Auu____3136=
  fun m  ->
    fun f  ->
      FStar_Util.monitor_enter m;
      (let res = f () in FStar_Util.monitor_exit m; res)
let (z3_job
  :Prims.bool ->
     FStar_SMTEncoding_Term.error_labels ->
       Prims.string ->
         Prims.unit ->
           (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3)=
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
let (running :Prims.bool FStar_ST.ref)= FStar_Util.mk_ref false
let rec (dequeue' :Prims.unit -> Prims.unit)=
  fun uu____3225  ->
    let j =
      let uu____3227 = FStar_ST.op_Bang job_queue in
      match uu____3227 with
>>>>>>> taramana_pointers_with_codes_modifies
      | [] -> failwith "Impossible"
      | hd1::tl1 -> (FStar_ST.op_Colon_Equals job_queue tl1; hd1)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____3284  -> FStar_Util.decr pending_jobs);
    dequeue ()
<<<<<<< HEAD

and dequeue : Prims.unit -> Prims.unit =
  fun uu____3808  ->
    let uu____3809 = FStar_ST.op_Bang running  in
    if uu____3809
=======
and (dequeue :Prims.unit -> Prims.unit)=
  fun uu____3286  ->
    let uu____3287 = FStar_ST.op_Bang running in
    if uu____3287
>>>>>>> taramana_pointers_with_codes_modifies
    then
      let rec aux uu____3301 =
        FStar_Util.monitor_enter job_queue;
<<<<<<< HEAD
        (let uu____3829 = FStar_ST.op_Bang job_queue  in
         match uu____3829 with
=======
        (let uu____3307 = FStar_ST.op_Bang job_queue in
         match uu____3307 with
>>>>>>> taramana_pointers_with_codes_modifies
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
<<<<<<< HEAD
         | uu____3856 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> Prims.unit =
  fun j  ->
    let uu____3860 = j.job ()  in FStar_All.pipe_left j.callback uu____3860

let init : Prims.unit -> Prims.unit =
  fun uu____3920  ->
=======
         | uu____3334 -> dequeue' ()) in
      aux ()
    else ()
and (run_job :z3job -> Prims.unit)=
  fun j  ->
    let uu____3338 = j.job () in FStar_All.pipe_left j.callback uu____3338
let (init :Prims.unit -> Prims.unit)=
  fun uu____3366  ->
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
  
let enqueue : z3job -> Prims.unit =
  fun j  ->
    FStar_Util.monitor_enter job_queue;
    (let uu____3950 =
       let uu____3953 = FStar_ST.op_Bang job_queue  in
       FStar_List.append uu____3953 [j]  in
     FStar_ST.op_Colon_Equals job_queue uu____3950);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
  
let finish : Prims.unit -> Prims.unit =
  fun uu____4004  ->
    let rec aux uu____4008 =
      let uu____4009 =
        with_monitor job_queue
          (fun uu____4025  ->
             let uu____4026 = FStar_ST.op_Bang pending_jobs  in
             let uu____4037 =
               let uu____4038 = FStar_ST.op_Bang job_queue  in
               FStar_List.length uu____4038  in
             (uu____4026, uu____4037))
         in
      match uu____4009 with
=======
let (enqueue :z3job -> Prims.unit)=
  fun j  ->
    FStar_Util.monitor_enter job_queue;
    (let uu____3396 =
       let uu____3399 = FStar_ST.op_Bang job_queue in
       FStar_List.append uu____3399 [j] in
     FStar_ST.op_Colon_Equals job_queue uu____3396);
    FStar_Util.monitor_pulse job_queue;
    FStar_Util.monitor_exit job_queue
let (finish :Prims.unit -> Prims.unit)=
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
>>>>>>> taramana_pointers_with_codes_modifies
      | (n1,m) ->
          if (n1 + m) = (Prims.parse_int "0")
          then FStar_ST.op_Colon_Equals running false
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ())
       in
    aux ()
  
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
<<<<<<< HEAD
let fresh_scope :
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]] 
let mk_fresh_scope : Prims.unit -> scope_t =
  fun uu____4109  -> FStar_ST.op_Bang fresh_scope 
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [] 
let push : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____4154 =
       let uu____4159 = FStar_ST.op_Bang fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         uu____4159
        in
     FStar_ST.op_Colon_Equals fresh_scope uu____4154);
    (let uu____4218 =
       let uu____4221 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4221
         [FStar_SMTEncoding_Term.Push; FStar_SMTEncoding_Term.Caption msg]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4218)
  
let pop : Prims.string -> Prims.unit =
  fun msg  ->
    (let uu____4265 =
       let uu____4270 = FStar_ST.op_Bang fresh_scope  in
       FStar_List.tl uu____4270  in
     FStar_ST.op_Colon_Equals fresh_scope uu____4265);
    (let uu____4329 =
       let uu____4332 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4332
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Pop]
        in
     FStar_ST.op_Colon_Equals bg_scope uu____4329)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
=======
let (fresh_scope
  :FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref)=
  FStar_Util.mk_ref [[]]
let (mk_fresh_scope :Prims.unit -> scope_t)=
  fun uu____3555  -> FStar_ST.op_Bang fresh_scope
let (bg_scope :FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref)=
  FStar_Util.mk_ref []
let (push :Prims.string -> Prims.unit)=
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
let (pop :Prims.string -> Prims.unit)=
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
let (giveZ3 :FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___97_3829  ->
            match uu___97_3829 with
            | FStar_SMTEncoding_Term.Push  -> failwith "Unexpected push/pop"
            | FStar_SMTEncoding_Term.Pop  -> failwith "Unexpected push/pop"
<<<<<<< HEAD
            | uu____4384 -> ()));
    (let uu____4386 = FStar_ST.op_Bang fresh_scope  in
     match uu____4386 with
     | hd1::tl1 ->
         FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 decls)
           :: tl1)
     | uu____4455 -> failwith "Impossible");
    (let uu____4460 =
       let uu____4463 = FStar_ST.op_Bang bg_scope  in
       FStar_List.append uu____4463 decls  in
     FStar_ST.op_Colon_Equals bg_scope uu____4460)
  
let refresh : Prims.unit -> Prims.unit =
  fun uu____4505  ->
    (let uu____4507 =
       let uu____4508 = FStar_Options.n_cores ()  in
       uu____4508 < (Prims.parse_int "2")  in
     if uu____4507 then bg_z3_proc.refresh () else ());
    (let uu____4510 =
       let uu____4513 =
         let uu____4518 = FStar_ST.op_Bang fresh_scope  in
         FStar_List.rev uu____4518  in
       FStar_List.flatten uu____4513  in
     FStar_ST.op_Colon_Equals bg_scope uu____4510)
  
let mark : Prims.string -> Prims.unit = fun msg  -> push msg 
let reset_mark : Prims.string -> Prims.unit = fun msg  -> pop msg; refresh () 
let commit_mark : Prims.string -> Prims.unit =
  fun msg  ->
    let uu____4582 = FStar_ST.op_Bang fresh_scope  in
    match uu____4582 with
    | hd1::s::tl1 ->
        FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 s) ::
          tl1)
    | uu____4656 -> failwith "Impossible"
  
let mk_cb :
  'Auu____4679 'Auu____4680 'Auu____4681 'Auu____4682 'Auu____4683
    'Auu____4684 .
    Prims.bool ->
      ((('Auu____4684,('Auu____4683 Prims.list,'Auu____4682)
                        FStar_Pervasives_Native.tuple2)
          FStar_Util.either,'Auu____4681,'Auu____4680)
         FStar_Pervasives_Native.tuple3 -> 'Auu____4679)
        ->
        (('Auu____4684,('Auu____4683 Prims.list,'Auu____4682)
                         FStar_Pervasives_Native.tuple2)
           FStar_Util.either,'Auu____4681,'Auu____4680)
          FStar_Pervasives_Native.tuple3 -> 'Auu____4679
  =
  fun used_unsat_core  ->
    fun cb  ->
      fun uu____4731  ->
        match uu____4731 with
        | (uc_errs,time,statistics) ->
            if used_unsat_core
            then
              (match uc_errs with
               | FStar_Util.Inl uu____4789 -> cb (uc_errs, time, statistics)
               | FStar_Util.Inr (uu____4806,ek) ->
                   cb ((FStar_Util.Inr ([], ek)), time, statistics))
            else cb (uc_errs, time, statistics)
  
let mk_input : FStar_SMTEncoding_Term.decl Prims.list -> Prims.string =
=======
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
let (refresh :Prims.unit -> Prims.unit)=
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
let (mark :Prims.string -> Prims.unit)= fun msg  -> push msg
let (reset_mark :Prims.string -> Prims.unit)= fun msg  -> pop msg; refresh ()
let (commit_mark :Prims.string -> Prims.unit)=
  fun msg  ->
    let uu____4028 = FStar_ST.op_Bang fresh_scope in
    match uu____4028 with
    | hd1::s::tl1 ->
        FStar_ST.op_Colon_Equals fresh_scope ((FStar_List.append hd1 s) ::
          tl1)
    | uu____4102 -> failwith "Impossible"
let (mk_input :FStar_SMTEncoding_Term.decl Prims.list -> Prims.string)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun theory  ->
    let r =
      let uu____4116 =
        FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ()))
<<<<<<< HEAD
          theory
         in
      FStar_All.pipe_right uu____4856 (FStar_String.concat "\n")  in
    (let uu____4862 = FStar_Options.log_queries ()  in
     if uu____4862 then query_logging.write_to_log r else ());
=======
          theory in
      FStar_All.pipe_right uu____4116 (FStar_String.concat "\n") in
    (let uu____4122 = FStar_Options.log_queries () in
     if uu____4122 then query_logging.write_to_log r else ());
>>>>>>> taramana_pointers_with_codes_modifies
    r
  
type z3result =
  (z3status,Prims.int,z3statistics) FStar_Pervasives_Native.tuple3
type cb = z3result -> Prims.unit
<<<<<<< HEAD
let ask_1_core :
  (FStar_SMTEncoding_Term.decls_t ->
     (FStar_SMTEncoding_Term.decls_t,Prims.bool)
       FStar_Pervasives_Native.tuple2)
    ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit
  =
=======
let (ask_1_core
  :(FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t,Prims.bool)
        FStar_Pervasives_Native.tuple2)
     ->
     FStar_SMTEncoding_Term.error_labels ->
       FStar_SMTEncoding_Term.decls_t -> cb -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun filter_theory  ->
    fun label_messages  ->
      fun qry  ->
        fun cb  ->
          let theory =
<<<<<<< HEAD
            let uu____4914 = FStar_ST.op_Bang bg_scope  in
            FStar_List.append uu____4914
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
             in
          let uu____4935 = filter_theory theory  in
          match uu____4935 with
          | (theory1,used_unsat_core) ->
              let cb1 = mk_cb used_unsat_core cb  in
              let input = mk_input theory1  in
              (FStar_ST.op_Colon_Equals bg_scope [];
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
=======
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
let (ask_n_cores
  :(FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t,Prims.bool)
        FStar_Pervasives_Native.tuple2)
     ->
     FStar_SMTEncoding_Term.error_labels ->
       FStar_SMTEncoding_Term.decls_t ->
         scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
                     (let uu____5070 = FStar_ST.op_Bang fresh_scope  in
                      FStar_List.rev uu____5070))
                 in
              FStar_List.flatten uu____5039  in
            let theory1 =
              FStar_List.append theory
                (FStar_List.append [FStar_SMTEncoding_Term.Push]
                   (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
               in
            let uu____5106 = filter_theory theory1  in
            match uu____5106 with
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
      FStar_SMTEncoding_Term.decl Prims.list ->
        scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit
  =
=======
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
let (ask
  :(FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t,Prims.bool)
        FStar_Pervasives_Native.tuple2)
     ->
     FStar_SMTEncoding_Term.error_labels ->
       FStar_SMTEncoding_Term.decl Prims.list ->
         scope_t FStar_Pervasives_Native.option -> cb -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun filter1  ->
    fun label_messages  ->
      fun qry  ->
        fun scope  ->
          fun cb  ->
<<<<<<< HEAD
            let uu____5190 =
              let uu____5191 = FStar_Options.n_cores ()  in
              uu____5191 = (Prims.parse_int "1")  in
            if uu____5190
=======
            let uu____4388 =
              let uu____4389 = FStar_Options.n_cores () in
              uu____4389 = (Prims.parse_int "1") in
            if uu____4388
>>>>>>> taramana_pointers_with_codes_modifies
            then ask_1_core filter1 label_messages qry cb
            else ask_n_cores filter1 label_messages qry scope cb
  
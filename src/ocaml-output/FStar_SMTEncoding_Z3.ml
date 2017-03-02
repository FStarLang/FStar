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
  fun uu___90_48  ->
    match uu___90_48 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let _0_355 = FStar_Util.string_of_int i  in
        let _0_354 = FStar_Util.string_of_int j  in
        let _0_353 = FStar_Util.string_of_int k  in
        FStar_Util.format3 "%s.%s.%s" _0_355 _0_354 _0_353
  
let z3v_compare :
  z3version -> (Prims.int * Prims.int * Prims.int) -> Prims.int Prims.option
  =
  fun known  ->
    fun uu____62  ->
      match uu____62 with
      | (w1,w2,w3) ->
          (match known with
           | Z3V_Unknown uu____71 -> None
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
  fun uu____97  ->
    let prefix = "Z3 version "  in
    let uu____99 = FStar_ST.read _z3version  in
    match uu____99 with
    | Some version -> version
    | None  ->
        let uu____105 =
          let _0_356 = FStar_Options.z3_exe ()  in
          FStar_Util.run_proc _0_356 "-version" ""  in
        (match uu____105 with
         | (uu____109,out,uu____111) ->
             let out =
               match FStar_Util.splitlines out with
               | x::uu____114 when FStar_Util.starts_with x prefix ->
                   let x =
                     FStar_Util.trim_string
                       (FStar_Util.substring_from x
                          (FStar_String.length prefix))
                      in
                   let x =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x ".")
                     with | uu____126 -> []  in
                   (match x with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____130 -> Z3V_Unknown out)
               | uu____132 -> Z3V_Unknown out  in
             (FStar_ST.write _z3version (Some out); out))
  
let ini_params : Prims.unit -> Prims.string =
  fun uu____140  ->
    let z3_v = get_z3version ()  in
    (let uu____143 =
       let _0_357 = get_z3version ()  in
       z3v_le _0_357
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0"))
        in
     if uu____143
     then
       let _0_359 =
         FStar_Util.Failure
           (let _0_358 = z3version_as_string z3_v  in
            FStar_Util.format1
              "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
              _0_358)
          in
       FStar_All.pipe_left Prims.raise _0_359
     else ());
    (let _0_365 =
       let _0_364 =
         let _0_362 =
           let _0_361 =
             let _0_360 = FStar_Util.string_of_int (FStar_Options.z3_seed ())
                in
             FStar_Util.format1 "smt.random_seed=%s" _0_360  in
           [_0_361]  in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" :: _0_362
          in
       let _0_363 = FStar_Options.z3_cliopt ()  in
       FStar_List.append _0_364 _0_363  in
     FStar_String.concat " " _0_365)
  
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
    match projectee with | UNSAT _0 -> true | uu____166 -> false
  
let __proj__UNSAT__item___0 : z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0 
let uu___is_SAT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____179 -> false
  
let __proj__SAT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0 
let uu___is_UNKNOWN : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____195 -> false
  
let __proj__UNKNOWN__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0 
let uu___is_TIMEOUT : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____211 -> false
  
let __proj__TIMEOUT__item___0 : z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0 
let uu___is_KILLED : z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____225 -> false
  
let status_to_string : z3status -> Prims.string =
  fun uu___91_228  ->
    match uu___91_228 with
    | SAT uu____229 -> "sat"
    | UNSAT uu____231 -> "unsat"
    | UNKNOWN uu____232 -> "unknown"
    | TIMEOUT uu____234 -> "timeout"
    | KILLED  -> "killed"
  
let tid : Prims.unit -> Prims.string =
  fun uu____238  ->
    let _0_366 = FStar_Util.current_tid ()  in
    FStar_All.pipe_right _0_366 FStar_Util.string_of_int
  
let new_z3proc : Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
    let _0_368 = FStar_Options.z3_exe ()  in
    let _0_367 = ini_params ()  in
    FStar_Util.start_process id _0_368 _0_367 cond
  
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
  append_to_log: Prims.string -> Prims.unit ;
  close_log: Prims.unit -> Prims.unit ;
  log_file_name: Prims.unit -> Prims.string }
let query_logging : query_log =
  let log_file_opt = FStar_Util.mk_ref None  in
  let used_file_names = FStar_Util.mk_ref []  in
  let current_module_name = FStar_Util.mk_ref None  in
  let current_file_name = FStar_Util.mk_ref None  in
  let set_module_name n = FStar_ST.write current_module_name (Some n)  in
  let get_module_name uu____412 =
    let uu____413 = FStar_ST.read current_module_name  in
    match uu____413 with
    | None  -> failwith "Module name not set"
    | Some n -> n  in
  let new_log_file uu____422 =
    let uu____423 = FStar_ST.read current_module_name  in
    match uu____423 with
    | None  -> failwith "current module not set"
    | Some n ->
        let file_name =
          let uu____430 =
            let _0_369 = FStar_ST.read used_file_names  in
            FStar_List.tryFind
              (fun uu____436  ->
                 match uu____436 with | (m,uu____440) -> n = m) _0_369
             in
          match uu____430 with
          | None  ->
              ((let _0_371 =
                  let _0_370 = FStar_ST.read used_file_names  in
                  (n, (Prims.parse_int "0")) :: _0_370  in
                FStar_ST.write used_file_names _0_371);
               n)
          | Some (uu____461,k) ->
              ((let _0_373 =
                  let _0_372 = FStar_ST.read used_file_names  in
                  (n, (k + (Prims.parse_int "1"))) :: _0_372  in
                FStar_ST.write used_file_names _0_373);
               (let _0_374 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1"))  in
                FStar_Util.format2 "%s-%s" n _0_374))
           in
        let file_name = FStar_Util.format1 "queries-%s.smt2" file_name  in
        (FStar_ST.write current_file_name (Some file_name);
         (let fh = FStar_Util.open_file_for_writing file_name  in
          FStar_ST.write log_file_opt (Some fh); fh))
     in
  let get_log_file uu____491 =
    let uu____492 = FStar_ST.read log_file_opt  in
    match uu____492 with | None  -> new_log_file () | Some fh -> fh  in
  let append_to_log str =
    let _0_375 = get_log_file ()  in FStar_Util.append_to_file _0_375 str  in
  let close_log uu____505 =
    let uu____506 = FStar_ST.read log_file_opt  in
    match uu____506 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None)
     in
  let log_file_name uu____519 =
    let uu____520 = FStar_ST.read current_file_name  in
    match uu____520 with | None  -> failwith "no log file" | Some n -> n  in
  { get_module_name; set_module_name; append_to_log; close_log; log_file_name
  } 
let bg_z3_proc : bgproc =
  let the_z3proc = FStar_Util.mk_ref None  in
  let new_proc =
    let ctr = FStar_Util.mk_ref (~- (Prims.parse_int "1"))  in
    fun uu____537  ->
      new_z3proc
        (let _0_377 =
           FStar_Util.incr ctr;
           (let _0_376 = FStar_ST.read ctr  in
            FStar_All.pipe_right _0_376 FStar_Util.string_of_int)
            in
         FStar_Util.format1 "bg-%s" _0_377)
     in
  let z3proc uu____547 =
    (let uu____549 = let _0_378 = FStar_ST.read the_z3proc  in _0_378 = None
        in
     if uu____549
     then
       let _0_379 = Some (new_proc ())  in FStar_ST.write the_z3proc _0_379
     else ());
    FStar_Util.must (FStar_ST.read the_z3proc)  in
  let x = []  in
  let grab uu____566 = FStar_Util.monitor_enter x; z3proc ()  in
  let release uu____572 = FStar_Util.monitor_exit x  in
  let refresh uu____577 =
    let proc = grab ()  in
    FStar_Util.kill_process proc;
    (let _0_380 = Some (new_proc ())  in FStar_ST.write the_z3proc _0_380);
    query_logging.close_log ();
    release ()  in
  let restart uu____588 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let _0_381 = Some (new_proc ())  in FStar_ST.write the_z3proc _0_381);
    FStar_Util.monitor_exit ()  in
  { grab; release; refresh; restart } 
let at_log_file : Prims.unit -> Prims.string =
  fun uu____601  ->
    let uu____602 = FStar_Options.log_queries ()  in
    if uu____602
    then
      let _0_382 = query_logging.log_file_name ()  in Prims.strcat "@" _0_382
    else ""
  
let doZ3Exe' : Prims.bool -> Prims.string -> z3status =
  fun fresh  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string)
           in
        let print_stats lines =
          let starts_with c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let _0_383 = FStar_String.get s (Prims.parse_int "0")  in
               _0_383 = c)
             in
          let ends_with c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let _0_384 =
                 FStar_String.get s
                   ((FStar_String.length s) - (Prims.parse_int "1"))
                  in
               _0_384 = c)
             in
          let last l =
            FStar_List.nth l ((FStar_List.length l) - (Prims.parse_int "1"))
             in
          let uu____656 = FStar_Options.print_z3_statistics ()  in
          if uu____656
          then
            let uu____657 =
              (((FStar_List.length lines) >= (Prims.parse_int "2")) &&
                 (let _0_385 = FStar_List.hd lines  in starts_with '(' _0_385))
                && (let _0_386 = last lines  in ends_with ')' _0_386)
               in
            (if uu____657
             then
               (FStar_Util.print_string
                  (let _0_389 =
                     let _0_387 = query_logging.get_module_name ()  in
                     FStar_Util.format1 "BEGIN-STATS %s\n" _0_387  in
                   let _0_388 = at_log_file ()  in Prims.strcat _0_389 _0_388);
                FStar_List.iter
                  (fun s  ->
                     FStar_Util.print_string (FStar_Util.format1 "%s\n" s))
                  lines;
                FStar_Util.print_string "END-STATS\n")
             else
               failwith
                 "Unexpected output from Z3: could not find statistics\n")
          else ()  in
        let unsat_core lines =
          let parse_core s =
            let s = FStar_Util.trim_string s  in
            let s =
              FStar_Util.substring s (Prims.parse_int "1")
                ((FStar_String.length s) - (Prims.parse_int "2"))
               in
            if FStar_Util.starts_with s "error"
            then None
            else
              (let _0_391 =
                 FStar_All.pipe_right (FStar_Util.split s " ")
                   (FStar_Util.sort_with FStar_String.compare)
                  in
               FStar_All.pipe_right _0_391 (fun _0_390  -> Some _0_390))
             in
          match lines with
          | "<unsat-core>"::core::"</unsat-core>"::rest ->
              let _0_392 = parse_core core  in (_0_392, lines)
          | uu____709 -> (None, lines)  in
        let rec lblnegs lines succeeded =
          match lines with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let _0_393 = lblnegs rest succeeded  in lname :: _0_393
          | lname::uu____730::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest succeeded
          | uu____733 -> (if succeeded then print_stats lines else (); [])
           in
        let unsat_core_and_lblnegs lines succeeded =
          let uu____751 = unsat_core lines  in
          match uu____751 with
          | (core_opt,rest) ->
              let _0_394 = lblnegs rest succeeded  in (core_opt, _0_394)
           in
        let rec result x =
          match x with
          | "timeout"::tl -> TIMEOUT []
          | "unknown"::tl ->
              UNKNOWN (Prims.snd (unsat_core_and_lblnegs tl false))
          | "sat"::tl -> SAT (Prims.snd (unsat_core_and_lblnegs tl false))
          | "unsat"::tl -> UNSAT (Prims.fst (unsat_core_and_lblnegs tl true))
          | "killed"::tl -> (bg_z3_proc.restart (); KILLED)
          | hd::tl ->
              ((let _0_396 =
                  let _0_395 = query_logging.get_module_name ()  in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    _0_395 hd
                   in
                FStar_Errors.warn FStar_Range.dummyRange _0_396);
               result tl)
          | uu____803 ->
              let _0_399 =
                let _0_398 =
                  let _0_397 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines
                     in
                  FStar_String.concat "\n" _0_397  in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n" _0_398
                 in
              FStar_All.pipe_left failwith _0_399
           in
        result lines  in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!"  in x  in
      let stdout =
        if fresh
        then
          let _0_402 = tid ()  in
          let _0_401 = FStar_Options.z3_exe ()  in
          let _0_400 = ini_params ()  in
          FStar_Util.launch_process _0_402 _0_401 _0_400 input cond
        else
          (let proc = bg_z3_proc.grab ()  in
           let stdout = FStar_Util.ask_process proc input  in
           bg_z3_proc.release (); stdout)
         in
      parse (FStar_Util.trim_string stdout)
  
let doZ3Exe : Prims.bool -> Prims.string -> z3status =
  fun fresh  -> fun input  -> doZ3Exe' fresh input 
let z3_options : Prims.unit -> Prims.string =
  fun uu____827  ->
    "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :auto_config false)(set-option :produce-unsat-cores true)"
  
type 'a job = {
  job: Prims.unit -> 'a ;
  callback: 'a -> Prims.unit }
type error_kind =
  | Timeout 
  | Kill 
  | Default 
let uu___is_Timeout : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____878 -> false
  
let uu___is_Kill : error_kind -> Prims.bool =
  fun projectee  -> match projectee with | Kill  -> true | uu____882 -> false 
let uu___is_Default : error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____886 -> false
  
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
  fun fresh  ->
    fun label_messages  ->
      fun input  ->
        fun uu____947  ->
          let ekind uu___92_963 =
            match uu___92_963 with
            | TIMEOUT uu____964 -> Timeout
            | SAT _|UNKNOWN _ -> Default
            | KILLED  -> Kill
            | uu____968 -> failwith "Impossible"  in
          let start = FStar_Util.now ()  in
          let status = doZ3Exe fresh input  in
          let uu____971 =
            let _0_403 = FStar_Util.now ()  in
            FStar_Util.time_diff start _0_403  in
          match uu____971 with
          | (uu____980,elapsed_time) ->
              let result =
                match status with
                | UNSAT core -> ((FStar_Util.Inl core), elapsed_time)
                | KILLED  -> ((FStar_Util.Inr ([], Kill)), elapsed_time)
                | TIMEOUT lblnegs|SAT lblnegs|UNKNOWN lblnegs ->
                    ((let uu____1060 = FStar_Options.debug_any ()  in
                      if uu____1060
                      then
                        let _0_404 =
                          FStar_Util.format1 "Z3 says: %s\n"
                            (status_to_string status)
                           in
                        FStar_All.pipe_left FStar_Util.print_string _0_404
                      else ());
                     (let failing_assertions =
                        FStar_All.pipe_right lblnegs
                          (FStar_List.collect
                             (fun l  ->
                                let uu____1082 =
                                  FStar_All.pipe_right label_messages
                                    (FStar_List.tryFind
                                       (fun uu____1106  ->
                                          match uu____1106 with
                                          | (m,uu____1113,uu____1114) ->
                                              (Prims.fst m) = l))
                                   in
                                match uu____1082 with
                                | None  -> []
                                | Some (lbl,msg,r) -> [(lbl, msg, r)]))
                         in
                      let _0_406 =
                        FStar_Util.Inr
                          (let _0_405 = ekind status  in
                           (failing_assertions, _0_405))
                         in
                      (_0_406, elapsed_time)))
                 in
              result
  
let running : Prims.bool FStar_ST.ref = FStar_Util.mk_ref false 
let rec dequeue' : Prims.unit -> Prims.unit =
  fun uu____1192  ->
    let j =
      let uu____1194 = FStar_ST.read job_queue  in
      match uu____1194 with
      | [] -> failwith "Impossible"
      | hd::tl -> (FStar_ST.write job_queue tl; hd)  in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1221  -> FStar_Util.decr pending_jobs);
    dequeue ()

and dequeue : Prims.unit -> Prims.unit =
  fun uu____1226  ->
    let uu____1227 = FStar_ST.read running  in
    if uu____1227
    then
      let rec aux uu____1233 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1239 = FStar_ST.read job_queue  in
         match uu____1239 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1250 -> dequeue' ())
         in
      aux ()
    else ()

and run_job : z3job -> Prims.unit =
  fun j  -> let _0_407 = j.job ()  in FStar_All.pipe_left j.callback _0_407

let init : Prims.unit -> Prims.unit =
  fun uu____1273  ->
    FStar_ST.write running true;
    (let n_cores = FStar_Options.n_cores ()  in
     if n_cores > (Prims.parse_int "1")
     then
       let rec aux n =
         if n = (Prims.parse_int "0")
         then ()
         else (FStar_Util.spawn dequeue; aux (n - (Prims.parse_int "1")))  in
       aux n_cores
     else ())
  
let enqueue : Prims.bool -> z3job -> Prims.unit =
  fun fresh  ->
    fun j  ->
      if Prims.op_Negation fresh
      then run_job j
      else
        (FStar_Util.monitor_enter job_queue;
         (let _0_409 =
            let _0_408 = FStar_ST.read job_queue  in
            FStar_List.append _0_408 [j]  in
          FStar_ST.write job_queue _0_409);
         FStar_Util.monitor_pulse job_queue;
         FStar_Util.monitor_exit job_queue)
  
let finish : Prims.unit -> Prims.unit =
  fun uu____1315  ->
    let rec aux uu____1319 =
      let uu____1320 =
        with_monitor job_queue
          (fun uu____1329  ->
             let _0_411 = FStar_ST.read pending_jobs  in
             let _0_410 = FStar_List.length (FStar_ST.read job_queue)  in
             (_0_411, _0_410))
         in
      match uu____1320 with
      | (n,m) ->
          if (n + m) = (Prims.parse_int "0")
          then
            (FStar_ST.write running false;
             (let _0_412 = FStar_Errors.report_all ()  in
              FStar_All.pipe_right _0_412 Prims.ignore))
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
    (let _0_414 =
       let _0_413 = FStar_ST.read fresh_scope  in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         _0_413
        in
     FStar_ST.write fresh_scope _0_414);
    (let _0_416 =
       let _0_415 = FStar_ST.read bg_scope  in
       FStar_List.append
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
         _0_415
        in
     FStar_ST.write bg_scope _0_416)
  
let pop : Prims.string -> Prims.unit =
  fun msg  ->
    (let _0_417 = FStar_List.tl (FStar_ST.read fresh_scope)  in
     FStar_ST.write fresh_scope _0_417);
    (let _0_419 =
       let _0_418 = FStar_ST.read bg_scope  in
       FStar_List.append
         [FStar_SMTEncoding_Term.Pop; FStar_SMTEncoding_Term.Caption msg]
         _0_418
        in
     FStar_ST.write bg_scope _0_419)
  
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___93_1409  ->
            match uu___93_1409 with
            | FStar_SMTEncoding_Term.Push |FStar_SMTEncoding_Term.Pop  ->
                failwith "Unexpected push/pop"
            | uu____1410 -> ()));
    (let uu____1412 = FStar_ST.read fresh_scope  in
     match uu____1412 with
     | hd::tl ->
         FStar_ST.write fresh_scope ((FStar_List.append hd decls) :: tl)
     | uu____1430 -> failwith "Impossible");
    (let _0_421 =
       let _0_420 = FStar_ST.read bg_scope  in
       FStar_List.append (FStar_List.rev decls) _0_420  in
     FStar_ST.write bg_scope _0_421)
  
let bgtheory : Prims.bool -> FStar_SMTEncoding_Term.decl Prims.list =
  fun fresh  ->
    if fresh
    then
      (FStar_ST.write bg_scope [];
       (let _0_422 = FStar_List.rev (FStar_ST.read fresh_scope)  in
        FStar_All.pipe_right _0_422 FStar_List.flatten))
    else
      (let bg = FStar_ST.read bg_scope  in
       FStar_ST.write bg_scope []; FStar_List.rev bg)
  
let refresh : Prims.unit -> Prims.unit =
  fun uu____1468  ->
    (let uu____1470 =
       let _0_423 = FStar_Options.n_cores ()  in
       _0_423 < (Prims.parse_int "2")  in
     if uu____1470 then bg_z3_proc.refresh () else ());
    (let theory = bgtheory true  in
     FStar_ST.write bg_scope (FStar_List.rev theory))
  
let mark : Prims.string -> Prims.unit = fun msg  -> push msg 
let reset_mark : Prims.string -> Prims.unit = fun msg  -> pop msg; refresh () 
let commit_mark msg =
  let uu____1491 = FStar_ST.read fresh_scope  in
  match uu____1491 with
  | hd::s::tl -> FStar_ST.write fresh_scope ((FStar_List.append hd s) :: tl)
  | uu____1512 -> failwith "Impossible" 
let ask :
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
          let fresh =
            let _0_424 = FStar_Options.n_cores ()  in
            _0_424 > (Prims.parse_int "1")  in
          let filter_assertions theory =
            match core with
            | None  -> (theory, false)
            | Some core ->
                let uu____1576 =
                  FStar_List.fold_right
                    (fun d  ->
                       fun uu____1586  ->
                         match uu____1586 with
                         | (theory,n_retained,n_pruned) ->
                             (match d with
                              | FStar_SMTEncoding_Term.Assume
                                  (uu____1604,uu____1605,Some name) ->
                                  if FStar_List.contains name core
                                  then
                                    ((d :: theory),
                                      (n_retained + (Prims.parse_int "1")),
                                      n_pruned)
                                  else
                                    if FStar_Util.starts_with name "@"
                                    then
                                      ((d :: theory), n_retained, n_pruned)
                                    else
                                      (theory, n_retained,
                                        (n_pruned + (Prims.parse_int "1")))
                              | uu____1621 ->
                                  ((d :: theory), n_retained, n_pruned)))
                    theory ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
                   in
                (match uu____1576 with
                 | (theory',n_retained,n_pruned) ->
                     let missed_assertions th core =
                       let missed =
                         let _0_426 =
                           FStar_All.pipe_right core
                             (FStar_List.filter
                                (fun nm  ->
                                   let _0_425 =
                                     FStar_All.pipe_right th
                                       (FStar_Util.for_some
                                          (fun uu___94_1649  ->
                                             match uu___94_1649 with
                                             | FStar_SMTEncoding_Term.Assume
                                                 (uu____1650,uu____1651,Some
                                                  nm')
                                                 -> nm = nm'
                                             | uu____1654 -> false))
                                      in
                                   FStar_All.pipe_right _0_425
                                     Prims.op_Negation))
                            in
                         FStar_All.pipe_right _0_426
                           (FStar_String.concat ", ")
                          in
                       let included =
                         let _0_427 =
                           FStar_All.pipe_right th
                             (FStar_List.collect
                                (fun uu___95_1659  ->
                                   match uu___95_1659 with
                                   | FStar_SMTEncoding_Term.Assume
                                       (uu____1661,uu____1662,Some nm) ->
                                       [nm]
                                   | uu____1665 -> []))
                            in
                         FStar_All.pipe_right _0_427
                           (FStar_String.concat ", ")
                          in
                       FStar_Util.format2 "missed={%s}; included={%s}" missed
                         included
                        in
                     ((let uu____1667 =
                         (FStar_Options.hint_info ()) &&
                           (FStar_Options.debug_any ())
                          in
                       if uu____1667
                       then
                         let n = FStar_List.length core  in
                         let missed =
                           if n <> n_retained
                           then missed_assertions theory' core
                           else ""  in
                         let _0_431 = FStar_Util.string_of_int n_retained  in
                         let _0_430 =
                           if n <> n_retained
                           then
                             let _0_428 = FStar_Util.string_of_int n  in
                             FStar_Util.format2
                               " (expected %s (%s); replay may be inaccurate)"
                               _0_428 missed
                           else ""  in
                         let _0_429 = FStar_Util.string_of_int n_pruned  in
                         FStar_Util.print3
                           "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                           _0_431 _0_430 _0_429
                       else ());
                      (let _0_435 =
                         let _0_434 =
                           let _0_433 =
                             FStar_SMTEncoding_Term.Caption
                               (let _0_432 =
                                  FStar_All.pipe_right core
                                    (FStar_String.concat ", ")
                                   in
                                Prims.strcat "UNSAT CORE: " _0_432)
                              in
                           [_0_433]  in
                         FStar_List.append theory' _0_434  in
                       (_0_435, true))))
             in
          let theory = bgtheory fresh  in
          let theory =
            FStar_List.append theory
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop]))
             in
          let uu____1687 = filter_assertions theory  in
          match uu____1687 with
          | (theory,used_unsat_core) ->
              let cb uu____1704 =
                match uu____1704 with
                | (uc_errs,time) ->
                    if used_unsat_core
                    then
                      (match uc_errs with
                       | FStar_Util.Inl uu____1721 -> cb (uc_errs, time)
                       | FStar_Util.Inr (uu____1728,ek) ->
                           cb ((FStar_Util.Inr ([], ek)), time))
                    else cb (uc_errs, time)
                 in
              let input =
                let _0_436 =
                  FStar_List.map
                    (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory
                   in
                FStar_All.pipe_right _0_436 (FStar_String.concat "\n")  in
              ((let uu____1749 = FStar_Options.log_queries ()  in
                if uu____1749 then query_logging.append_to_log input else ());
               enqueue fresh
                 { job = (z3_job fresh label_messages input); callback = cb })
  
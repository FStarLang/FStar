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
  fun uu___91_48  ->
    match uu___91_48 with
    | Z3V_Unknown s -> FStar_Util.format1 "unknown version: %s" s
    | Z3V (i,j,k) ->
        let _0_362 = FStar_Util.string_of_int i in
        let _0_361 = FStar_Util.string_of_int j in
        let _0_360 = FStar_Util.string_of_int k in
        FStar_Util.format3 "%s.%s.%s" _0_362 _0_361 _0_360
let z3v_compare:
  z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.int Prims.option =
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
let z3v_le: z3version -> (Prims.int* Prims.int* Prims.int) -> Prims.bool =
  fun known  ->
    fun wanted  ->
      match z3v_compare known wanted with
      | None  -> false
      | Some i -> i >= (Prims.parse_int "0")
let _z3version: z3version Prims.option FStar_ST.ref = FStar_Util.mk_ref None
let get_z3version: Prims.unit -> z3version =
  fun uu____97  ->
    let prefix = "Z3 version " in
    let uu____99 = FStar_ST.read _z3version in
    match uu____99 with
    | Some version -> version
    | None  ->
        let uu____105 =
          let _0_363 = FStar_Options.z3_exe () in
          FStar_Util.run_proc _0_363 "-version" "" in
        (match uu____105 with
         | (uu____109,out,uu____111) ->
             let out =
               match FStar_Util.splitlines out with
               | x::uu____114 when FStar_Util.starts_with x prefix ->
                   let x =
                     FStar_Util.trim_string
                       (FStar_Util.substring_from x
                          (FStar_String.length prefix)) in
                   let x =
                     try
                       FStar_List.map FStar_Util.int_of_string
                         (FStar_Util.split x ".")
                     with | uu____126 -> [] in
                   (match x with
                    | i1::i2::i3::[] -> Z3V (i1, i2, i3)
                    | uu____130 -> Z3V_Unknown out)
               | uu____132 -> Z3V_Unknown out in
             (FStar_ST.write _z3version (Some out); out))
let ini_params: Prims.unit -> Prims.string =
  fun uu____140  ->
    let z3_v = get_z3version () in
    (let uu____143 =
       let _0_364 = get_z3version () in
       z3v_le _0_364
         ((Prims.parse_int "4"), (Prims.parse_int "4"),
           (Prims.parse_int "0")) in
     if uu____143
     then
       let _0_366 =
         FStar_Util.Failure
           (let _0_365 = z3version_as_string z3_v in
            FStar_Util.format1
              "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n"
              _0_365) in
       FStar_All.pipe_left Prims.raise _0_366
     else ());
    (let _0_372 =
       let _0_371 =
         let _0_369 =
           let _0_368 =
             let _0_367 = FStar_Util.string_of_int (FStar_Options.z3_seed ()) in
             FStar_Util.format1 "smt.random_seed=%s" _0_367 in
           [_0_368] in
         "-smt2 -in auto_config=false model=true smt.relevancy=2" :: _0_369 in
       let _0_370 = FStar_Options.z3_cliopt () in
       FStar_List.append _0_371 _0_370 in
     FStar_String.concat " " _0_372)
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
    match projectee with | UNSAT _0 -> true | uu____166 -> false
let __proj__UNSAT__item___0: z3status -> unsat_core =
  fun projectee  -> match projectee with | UNSAT _0 -> _0
let uu___is_SAT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | SAT _0 -> true | uu____179 -> false
let __proj__SAT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | SAT _0 -> _0
let uu___is_UNKNOWN: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | UNKNOWN _0 -> true | uu____195 -> false
let __proj__UNKNOWN__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | UNKNOWN _0 -> _0
let uu___is_TIMEOUT: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | TIMEOUT _0 -> true | uu____211 -> false
let __proj__TIMEOUT__item___0: z3status -> label Prims.list =
  fun projectee  -> match projectee with | TIMEOUT _0 -> _0
let uu___is_KILLED: z3status -> Prims.bool =
  fun projectee  ->
    match projectee with | KILLED  -> true | uu____225 -> false
let status_to_string: z3status -> Prims.string =
  fun uu___92_228  ->
    match uu___92_228 with
    | SAT uu____229 -> "sat"
    | UNSAT uu____231 -> "unsat"
    | UNKNOWN uu____232 -> "unknown"
    | TIMEOUT uu____234 -> "timeout"
    | KILLED  -> "killed"
let tid: Prims.unit -> Prims.string =
  fun uu____238  ->
    let _0_373 = FStar_Util.current_tid () in
    FStar_All.pipe_right _0_373 FStar_Util.string_of_int
let new_z3proc: Prims.string -> FStar_Util.proc =
  fun id  ->
    let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
    let _0_375 = FStar_Options.z3_exe () in
    let _0_374 = ini_params () in
    FStar_Util.start_process id _0_375 _0_374 cond
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
  let set_module_name n = FStar_ST.write current_module_name (Some n) in
  let get_module_name uu____415 =
    let uu____416 = FStar_ST.read current_module_name in
    match uu____416 with
    | None  -> failwith "Module name not set"
    | Some n -> n in
  let new_log_file uu____425 =
    let uu____426 = FStar_ST.read current_module_name in
    match uu____426 with
    | None  -> failwith "current module not set"
    | Some n ->
        let file_name =
          let uu____433 =
            let _0_376 = FStar_ST.read used_file_names in
            FStar_List.tryFind
              (fun uu____439  ->
                 match uu____439 with | (m,uu____443) -> n = m) _0_376 in
          match uu____433 with
          | None  ->
              ((let _0_378 =
                  let _0_377 = FStar_ST.read used_file_names in
                  (n, (Prims.parse_int "0")) :: _0_377 in
                FStar_ST.write used_file_names _0_378);
               n)
          | Some (uu____464,k) ->
              ((let _0_380 =
                  let _0_379 = FStar_ST.read used_file_names in
                  (n, (k + (Prims.parse_int "1"))) :: _0_379 in
                FStar_ST.write used_file_names _0_380);
               (let _0_381 =
                  FStar_Util.string_of_int (k + (Prims.parse_int "1")) in
                FStar_Util.format2 "%s-%s" n _0_381)) in
        let file_name = FStar_Util.format1 "queries-%s.smt2" file_name in
        (FStar_ST.write current_file_name (Some file_name);
         (let fh = FStar_Util.open_file_for_writing file_name in
          FStar_ST.write log_file_opt (Some fh); fh)) in
  let get_log_file uu____494 =
    let uu____495 = FStar_ST.read log_file_opt in
    match uu____495 with | None  -> new_log_file () | Some fh -> fh in
  let append_to_log str =
    let _0_382 = get_log_file () in FStar_Util.append_to_file _0_382 str in
  let write_to_new_log str =
    let dir_name =
      let uu____510 = FStar_ST.read current_file_name in
      match uu____510 with
      | None  ->
          let dir_name =
            let uu____516 = FStar_ST.read current_module_name in
            match uu____516 with
            | None  -> failwith "current module not set"
            | Some n -> FStar_Util.format1 "queries-%s" n in
          (FStar_Util.mkdir_clean dir_name;
           FStar_ST.write current_file_name (Some dir_name);
           dir_name)
      | Some n -> n in
    let qnum = FStar_ST.read query_number in
    (let _0_384 =
       let _0_383 = FStar_ST.read query_number in
       _0_383 + (Prims.parse_int "1") in
     FStar_ST.write query_number _0_384);
    (let file_name =
       let _0_385 = FStar_Util.string_of_int qnum in
       FStar_Util.format1 "query-%s.smt2" _0_385 in
     let file_name = FStar_Util.concat_dir_filename dir_name file_name in
     FStar_Util.write_file file_name str) in
  let write_to_log str =
    let uu____542 =
      let _0_386 = FStar_Options.n_cores () in _0_386 > (Prims.parse_int "1") in
    if uu____542 then write_to_new_log str else append_to_log str in
  let close_log uu____547 =
    let uu____548 = FStar_ST.read log_file_opt in
    match uu____548 with
    | None  -> ()
    | Some fh -> (FStar_Util.close_file fh; FStar_ST.write log_file_opt None) in
  let log_file_name uu____561 =
    let uu____562 = FStar_ST.read current_file_name in
    match uu____562 with | None  -> failwith "no log file" | Some n -> n in
  { get_module_name; set_module_name; write_to_log; close_log; log_file_name
  }
let bg_z3_proc: bgproc =
  let the_z3proc = FStar_Util.mk_ref None in
  let new_proc =
    let ctr = FStar_Util.mk_ref (- (Prims.parse_int "1")) in
    fun uu____579  ->
      new_z3proc
        (let _0_388 =
           FStar_Util.incr ctr;
           (let _0_387 = FStar_ST.read ctr in
            FStar_All.pipe_right _0_387 FStar_Util.string_of_int) in
         FStar_Util.format1 "bg-%s" _0_388) in
  let z3proc uu____589 =
    (let uu____591 = let _0_389 = FStar_ST.read the_z3proc in _0_389 = None in
     if uu____591
     then let _0_390 = Some (new_proc ()) in FStar_ST.write the_z3proc _0_390
     else ());
    FStar_Util.must (FStar_ST.read the_z3proc) in
  let x = [] in
  let grab uu____608 = FStar_Util.monitor_enter x; z3proc () in
  let release uu____614 = FStar_Util.monitor_exit x in
  let refresh uu____619 =
    let proc = grab () in
    FStar_Util.kill_process proc;
    (let _0_391 = Some (new_proc ()) in FStar_ST.write the_z3proc _0_391);
    query_logging.close_log ();
    release () in
  let restart uu____630 =
    FStar_Util.monitor_enter ();
    query_logging.close_log ();
    FStar_ST.write the_z3proc None;
    (let _0_392 = Some (new_proc ()) in FStar_ST.write the_z3proc _0_392);
    FStar_Util.monitor_exit () in
  { grab; release; refresh; restart }
let at_log_file: Prims.unit -> Prims.string =
  fun uu____643  ->
    let uu____644 = FStar_Options.log_queries () in
    if uu____644
    then
      let _0_393 = query_logging.log_file_name () in Prims.strcat "@" _0_393
    else ""
let doZ3Exe': Prims.bool -> Prims.string -> z3status =
  fun fresh  ->
    fun input  ->
      let parse z3out =
        let lines =
          FStar_All.pipe_right (FStar_String.split ['\n'] z3out)
            (FStar_List.map FStar_Util.trim_string) in
        let print_stats lines =
          let starts_with c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let _0_394 = FStar_String.get s (Prims.parse_int "0") in
               _0_394 = c) in
          let ends_with c s =
            ((FStar_String.length s) >= (Prims.parse_int "1")) &&
              (let _0_395 =
                 FStar_String.get s
                   ((FStar_String.length s) - (Prims.parse_int "1")) in
               _0_395 = c) in
          let last l =
            FStar_List.nth l ((FStar_List.length l) - (Prims.parse_int "1")) in
          let uu____698 = FStar_Options.print_z3_statistics () in
          if uu____698
          then
            let uu____699 =
              (((FStar_List.length lines) >= (Prims.parse_int "2")) &&
                 (let _0_396 = FStar_List.hd lines in starts_with '(' _0_396))
                && (let _0_397 = last lines in ends_with ')' _0_397) in
            (if uu____699
             then
               (FStar_Util.print_string
                  (let _0_400 =
                     let _0_398 = query_logging.get_module_name () in
                     FStar_Util.format1 "BEGIN-STATS %s\n" _0_398 in
                   let _0_399 = at_log_file () in Prims.strcat _0_400 _0_399);
                FStar_List.iter
                  (fun s  ->
                     FStar_Util.print_string (FStar_Util.format1 "%s\n" s))
                  lines;
                FStar_Util.print_string "END-STATS\n")
             else
               failwith
                 "Unexpected output from Z3: could not find statistics\n")
          else () in
        let unsat_core lines =
          let parse_core s =
            let s = FStar_Util.trim_string s in
            let s =
              FStar_Util.substring s (Prims.parse_int "1")
                ((FStar_String.length s) - (Prims.parse_int "2")) in
            if FStar_Util.starts_with s "error"
            then None
            else
              (let _0_402 =
                 FStar_All.pipe_right (FStar_Util.split s " ")
                   (FStar_Util.sort_with FStar_String.compare) in
               FStar_All.pipe_right _0_402 (fun _0_401  -> Some _0_401)) in
          match lines with
          | "<unsat-core>"::core::"</unsat-core>"::rest ->
              let _0_403 = parse_core core in (_0_403, lines)
          | uu____751 -> (None, lines) in
        let rec lblnegs lines succeeded =
          match lines with
          | lname::"false"::rest when FStar_Util.starts_with lname "label_"
              -> let _0_404 = lblnegs rest succeeded in lname :: _0_404
          | lname::uu____772::rest when FStar_Util.starts_with lname "label_"
              -> lblnegs rest succeeded
          | uu____775 -> (if succeeded then print_stats lines else (); []) in
        let unsat_core_and_lblnegs lines succeeded =
          let uu____793 = unsat_core lines in
          match uu____793 with
          | (core_opt,rest) ->
              let _0_405 = lblnegs rest succeeded in (core_opt, _0_405) in
        let rec result x =
          match x with
          | "timeout"::tl -> TIMEOUT []
          | "unknown"::tl ->
              UNKNOWN (Prims.snd (unsat_core_and_lblnegs tl false))
          | "sat"::tl -> SAT (Prims.snd (unsat_core_and_lblnegs tl false))
          | "unsat"::tl -> UNSAT (Prims.fst (unsat_core_and_lblnegs tl true))
          | "killed"::tl -> (bg_z3_proc.restart (); KILLED)
          | hd::tl ->
              ((let _0_407 =
                  let _0_406 = query_logging.get_module_name () in
                  FStar_Util.format2 "%s: Unexpected output from Z3: %s\n"
                    _0_406 hd in
                FStar_Errors.warn FStar_Range.dummyRange _0_407);
               result tl)
          | uu____845 ->
              let _0_410 =
                let _0_409 =
                  let _0_408 =
                    FStar_List.map
                      (fun l  ->
                         FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))
                      lines in
                  FStar_String.concat "\n" _0_408 in
                FStar_Util.format1
                  "Unexpected output from Z3: got output lines: %s\n" _0_409 in
              FStar_All.pipe_left failwith _0_410 in
        result lines in
      let cond pid s = let x = (FStar_Util.trim_string s) = "Done!" in x in
      let stdout =
        if fresh
        then
          let _0_413 = tid () in
          let _0_412 = FStar_Options.z3_exe () in
          let _0_411 = ini_params () in
          FStar_Util.launch_process _0_413 _0_412 _0_411 input cond
        else
          (let proc = bg_z3_proc.grab () in
           let stdout = FStar_Util.ask_process proc input in
           bg_z3_proc.release (); stdout) in
      parse (FStar_Util.trim_string stdout)
let doZ3Exe: Prims.bool -> Prims.string -> z3status =
  fun fresh  -> fun input  -> doZ3Exe' fresh input
let z3_options: Prims.unit -> Prims.string =
  fun uu____869  ->
    "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :auto_config false)(set-option :produce-unsat-cores true)"
type 'a job = {
  job: Prims.unit -> 'a;
  callback: 'a -> Prims.unit;}
type error_kind =
  | Timeout
  | Kill
  | Default
let uu___is_Timeout: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Timeout  -> true | uu____920 -> false
let uu___is_Kill: error_kind -> Prims.bool =
  fun projectee  -> match projectee with | Kill  -> true | uu____924 -> false
let uu___is_Default: error_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | Default  -> true | uu____928 -> false
type z3job =
  ((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
    FStar_Util.either* Prims.int) job
let job_queue: z3job Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let pending_jobs: Prims.int FStar_ST.ref =
  FStar_Util.mk_ref (Prims.parse_int "0")
let with_monitor m f =
  FStar_Util.monitor_enter m;
  (let res = f () in FStar_Util.monitor_exit m; res)
let z3_job:
  Prims.bool ->
    ((label* FStar_SMTEncoding_Term.sort)* Prims.string* FStar_Range.range)
      Prims.list ->
      Prims.string ->
        Prims.unit ->
          ((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
            FStar_Util.either* Prims.int)
  =
  fun fresh  ->
    fun label_messages  ->
      fun input  ->
        fun uu____989  ->
          let ekind uu___93_1005 =
            match uu___93_1005 with
            | TIMEOUT uu____1006 -> Timeout
            | SAT _|UNKNOWN _ -> Default
            | KILLED  -> Kill
            | uu____1010 -> failwith "Impossible" in
          let start = FStar_Util.now () in
          let status = doZ3Exe fresh input in
          let uu____1013 =
            let _0_414 = FStar_Util.now () in
            FStar_Util.time_diff start _0_414 in
          match uu____1013 with
          | (uu____1022,elapsed_time) ->
              let result =
                match status with
                | UNSAT core -> ((FStar_Util.Inl core), elapsed_time)
                | KILLED  -> ((FStar_Util.Inr ([], Kill)), elapsed_time)
                | TIMEOUT lblnegs|SAT lblnegs|UNKNOWN lblnegs ->
                    ((let uu____1102 = FStar_Options.debug_any () in
                      if uu____1102
                      then
                        let _0_415 =
                          FStar_Util.format1 "Z3 says: %s\n"
                            (status_to_string status) in
                        FStar_All.pipe_left FStar_Util.print_string _0_415
                      else ());
                     (let failing_assertions =
                        FStar_All.pipe_right lblnegs
                          (FStar_List.collect
                             (fun l  ->
                                let uu____1124 =
                                  FStar_All.pipe_right label_messages
                                    (FStar_List.tryFind
                                       (fun uu____1148  ->
                                          match uu____1148 with
                                          | (m,uu____1155,uu____1156) ->
                                              (Prims.fst m) = l)) in
                                match uu____1124 with
                                | None  -> []
                                | Some (lbl,msg,r) -> [(lbl, msg, r)])) in
                      let _0_417 =
                        FStar_Util.Inr
                          (let _0_416 = ekind status in
                           (failing_assertions, _0_416)) in
                      (_0_417, elapsed_time))) in
              result
let running: Prims.bool FStar_ST.ref = FStar_Util.mk_ref false
let rec dequeue': Prims.unit -> Prims.unit =
  fun uu____1234  ->
    let j =
      let uu____1236 = FStar_ST.read job_queue in
      match uu____1236 with
      | [] -> failwith "Impossible"
      | hd::tl -> (FStar_ST.write job_queue tl; hd) in
    FStar_Util.incr pending_jobs;
    FStar_Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun uu____1263  -> FStar_Util.decr pending_jobs);
    dequeue ()
and dequeue: Prims.unit -> Prims.unit =
  fun uu____1268  ->
    let uu____1269 = FStar_ST.read running in
    if uu____1269
    then
      let rec aux uu____1275 =
        FStar_Util.monitor_enter job_queue;
        (let uu____1281 = FStar_ST.read job_queue in
         match uu____1281 with
         | [] ->
             (FStar_Util.monitor_exit job_queue;
              FStar_Util.sleep (Prims.parse_int "50");
              aux ())
         | uu____1292 -> dequeue' ()) in
      aux ()
    else ()
and run_job: z3job -> Prims.unit =
  fun j  -> let _0_418 = j.job () in FStar_All.pipe_left j.callback _0_418
let init: Prims.unit -> Prims.unit =
  fun uu____1315  ->
    FStar_ST.write running true;
    (let n_cores = FStar_Options.n_cores () in
     if n_cores > (Prims.parse_int "1")
     then
       let rec aux n =
         if n = (Prims.parse_int "0")
         then ()
         else (FStar_Util.spawn dequeue; aux (n - (Prims.parse_int "1"))) in
       aux n_cores
     else ())
let enqueue: Prims.bool -> z3job -> Prims.unit =
  fun fresh  ->
    fun j  ->
      if Prims.op_Negation fresh
      then run_job j
      else
        (FStar_Util.monitor_enter job_queue;
         (let _0_420 =
            let _0_419 = FStar_ST.read job_queue in
            FStar_List.append _0_419 [j] in
          FStar_ST.write job_queue _0_420);
         FStar_Util.monitor_pulse job_queue;
         FStar_Util.monitor_exit job_queue)
let finish: Prims.unit -> Prims.unit =
  fun uu____1357  ->
    let rec aux uu____1361 =
      let uu____1362 =
        with_monitor job_queue
          (fun uu____1371  ->
             let _0_422 = FStar_ST.read pending_jobs in
             let _0_421 = FStar_List.length (FStar_ST.read job_queue) in
             (_0_422, _0_421)) in
      match uu____1362 with
      | (n,m) ->
          if (n + m) = (Prims.parse_int "0")
          then
            (FStar_ST.write running false;
             (let _0_423 = FStar_Errors.report_all () in
              FStar_All.pipe_right _0_423 Prims.ignore))
          else (FStar_Util.sleep (Prims.parse_int "500"); aux ()) in
    aux ()
type scope_t = FStar_SMTEncoding_Term.decl Prims.list Prims.list
let fresh_scope:
  FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref =
  FStar_Util.mk_ref [[]]
let bg_scope: FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref =
  FStar_Util.mk_ref []
let push: Prims.string -> Prims.unit =
  fun msg  ->
    (let _0_425 =
       let _0_424 = FStar_ST.read fresh_scope in
       [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push] ::
         _0_424 in
     FStar_ST.write fresh_scope _0_425);
    (let _0_427 =
       let _0_426 = FStar_ST.read bg_scope in
       FStar_List.append
         [FStar_SMTEncoding_Term.Caption msg; FStar_SMTEncoding_Term.Push]
         _0_426 in
     FStar_ST.write bg_scope _0_427)
let pop: Prims.string -> Prims.unit =
  fun msg  ->
    (let _0_428 = FStar_List.tl (FStar_ST.read fresh_scope) in
     FStar_ST.write fresh_scope _0_428);
    (let _0_430 =
       let _0_429 = FStar_ST.read bg_scope in
       FStar_List.append
         [FStar_SMTEncoding_Term.Pop; FStar_SMTEncoding_Term.Caption msg]
         _0_429 in
     FStar_ST.write bg_scope _0_430)
let giveZ3: FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit =
  fun decls  ->
    FStar_All.pipe_right decls
      (FStar_List.iter
         (fun uu___94_1451  ->
            match uu___94_1451 with
            | FStar_SMTEncoding_Term.Push |FStar_SMTEncoding_Term.Pop  ->
                failwith "Unexpected push/pop"
            | uu____1452 -> ()));
    (let uu____1454 = FStar_ST.read fresh_scope in
     match uu____1454 with
     | hd::tl ->
         FStar_ST.write fresh_scope ((FStar_List.append hd decls) :: tl)
     | uu____1472 -> failwith "Impossible");
    (let _0_432 =
       let _0_431 = FStar_ST.read bg_scope in
       FStar_List.append (FStar_List.rev decls) _0_431 in
     FStar_ST.write bg_scope _0_432)
let bgtheory: Prims.bool -> FStar_SMTEncoding_Term.decl Prims.list =
  fun fresh  ->
    if fresh
    then
      (FStar_ST.write bg_scope [];
       (let _0_433 = FStar_List.rev (FStar_ST.read fresh_scope) in
        FStar_All.pipe_right _0_433 FStar_List.flatten))
    else
      (let bg = FStar_ST.read bg_scope in
       FStar_ST.write bg_scope []; FStar_List.rev bg)
let refresh: Prims.unit -> Prims.unit =
  fun uu____1510  ->
    (let uu____1512 =
       let _0_434 = FStar_Options.n_cores () in
       _0_434 < (Prims.parse_int "2") in
     if uu____1512 then bg_z3_proc.refresh () else ());
    (let theory = bgtheory true in
     FStar_ST.write bg_scope (FStar_List.rev theory))
let mark: Prims.string -> Prims.unit = fun msg  -> push msg
let reset_mark: Prims.string -> Prims.unit = fun msg  -> pop msg; refresh ()
let commit_mark msg =
  let uu____1533 = FStar_ST.read fresh_scope in
  match uu____1533 with
  | hd::s::tl -> FStar_ST.write fresh_scope ((FStar_List.append hd s) :: tl)
  | uu____1554 -> failwith "Impossible"
let ask:
  unsat_core ->
    ((label* FStar_SMTEncoding_Term.sort)* Prims.string* FStar_Range.range)
      Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (((unsat_core,(FStar_SMTEncoding_Term.error_labels* error_kind))
           FStar_Util.either* Prims.int) -> Prims.unit)
          -> Prims.unit
  =
  fun core  ->
    fun label_messages  ->
      fun qry  ->
        fun cb  ->
          let fresh =
            let _0_435 = FStar_Options.n_cores () in
            _0_435 > (Prims.parse_int "1") in
          let filter_assertions theory =
            match core with
            | None  -> (theory, false)
            | Some core ->
                let uu____1618 =
                  FStar_List.fold_right
                    (fun d  ->
                       fun uu____1628  ->
                         match uu____1628 with
                         | (theory,n_retained,n_pruned) ->
                             (match d with
                              | FStar_SMTEncoding_Term.Assume
                                  (uu____1646,uu____1647,Some name) ->
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
                              | uu____1663 ->
                                  ((d :: theory), n_retained, n_pruned)))
                    theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
                (match uu____1618 with
                 | (theory',n_retained,n_pruned) ->
                     let missed_assertions th core =
                       let missed =
                         let _0_437 =
                           FStar_All.pipe_right core
                             (FStar_List.filter
                                (fun nm  ->
                                   let _0_436 =
                                     FStar_All.pipe_right th
                                       (FStar_Util.for_some
                                          (fun uu___95_1691  ->
                                             match uu___95_1691 with
                                             | FStar_SMTEncoding_Term.Assume
                                                 (uu____1692,uu____1693,Some
                                                  nm')
                                                 -> nm = nm'
                                             | uu____1696 -> false)) in
                                   FStar_All.pipe_right _0_436
                                     Prims.op_Negation)) in
                         FStar_All.pipe_right _0_437
                           (FStar_String.concat ", ") in
                       let included =
                         let _0_438 =
                           FStar_All.pipe_right th
                             (FStar_List.collect
                                (fun uu___96_1701  ->
                                   match uu___96_1701 with
                                   | FStar_SMTEncoding_Term.Assume
                                       (uu____1703,uu____1704,Some nm) ->
                                       [nm]
                                   | uu____1707 -> [])) in
                         FStar_All.pipe_right _0_438
                           (FStar_String.concat ", ") in
                       FStar_Util.format2 "missed={%s}; included={%s}" missed
                         included in
                     ((let uu____1709 =
                         (FStar_Options.hint_info ()) &&
                           (FStar_Options.debug_any ()) in
                       if uu____1709
                       then
                         let n = FStar_List.length core in
                         let missed =
                           if n <> n_retained
                           then missed_assertions theory' core
                           else "" in
                         let _0_442 = FStar_Util.string_of_int n_retained in
                         let _0_441 =
                           if n <> n_retained
                           then
                             let _0_439 = FStar_Util.string_of_int n in
                             FStar_Util.format2
                               " (expected %s (%s); replay may be inaccurate)"
                               _0_439 missed
                           else "" in
                         let _0_440 = FStar_Util.string_of_int n_pruned in
                         FStar_Util.print3
                           "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                           _0_442 _0_441 _0_440
                       else ());
                      (let _0_446 =
                         let _0_445 =
                           let _0_444 =
                             FStar_SMTEncoding_Term.Caption
                               (let _0_443 =
                                  FStar_All.pipe_right core
                                    (FStar_String.concat ", ") in
                                Prims.strcat "UNSAT CORE: " _0_443) in
                           [_0_444] in
                         FStar_List.append theory' _0_445 in
                       (_0_446, true)))) in
          let theory = bgtheory fresh in
          let theory =
            FStar_List.append theory
              (FStar_List.append [FStar_SMTEncoding_Term.Push]
                 (FStar_List.append qry [FStar_SMTEncoding_Term.Pop])) in
          let uu____1729 = filter_assertions theory in
          match uu____1729 with
          | (theory,used_unsat_core) ->
              let cb uu____1746 =
                match uu____1746 with
                | (uc_errs,time) ->
                    if used_unsat_core
                    then
                      (match uc_errs with
                       | FStar_Util.Inl uu____1763 -> cb (uc_errs, time)
                       | FStar_Util.Inr (uu____1770,ek) ->
                           cb ((FStar_Util.Inr ([], ek)), time))
                    else cb (uc_errs, time) in
              let input =
                let _0_447 =
                  FStar_List.map
                    (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory in
                FStar_All.pipe_right _0_447 (FStar_String.concat "\n") in
              ((let uu____1791 = FStar_Options.log_queries () in
                if uu____1791 then query_logging.write_to_log input else ());
               enqueue fresh
                 { job = (z3_job fresh label_messages input); callback = cb })
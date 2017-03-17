open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___91_23 =
  match uu___91_23 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____32) -> FStar_Util.Inr r 
type hint_stat =
  {
  hint: FStar_Util.hint Prims.option ;
  replay_result: z3_replay_result ;
  elapsed_time: Prims.int ;
  source_location: FStar_Range.range }
type hint_stats_t = hint_stat Prims.list
let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None 
let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None 
let hint_stats : hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let format_hints_file_name : Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____102 = FStar_Options.record_hints ()  in
   match uu____102 with
   | true  -> FStar_ST.write recorded_hints (Some [])
   | uu____109 -> ());
  (let uu____110 = FStar_Options.use_hints ()  in
   match uu____110 with
   | true  ->
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename = format_hints_file_name norm_src_filename  in
       let uu____113 = FStar_Util.read_hints val_filename  in
       (match uu____113 with
        | Some hints ->
            let expected_digest = FStar_Util.digest_of_file norm_src_filename
               in
            ((let uu____118 = FStar_Options.hint_info ()  in
              match uu____118 with
              | true  ->
                  (match hints.FStar_Util.module_digest = expected_digest
                   with
                   | true  ->
                       FStar_Util.print1
                         "(%s) digest is valid; using hints db.\n"
                         norm_src_filename
                   | uu____119 ->
                       FStar_Util.print1
                         "(%s) digest is invalid; using potentially stale hints\n"
                         norm_src_filename)
              | uu____120 -> ());
             FStar_ST.write replaying_hints (Some (hints.FStar_Util.hints)))
        | None  ->
            let uu____124 = FStar_Options.hint_info ()  in
            (match uu____124 with
             | true  ->
                 FStar_Util.print1 "(%s) Unable to read hints db.\n"
                   norm_src_filename
             | uu____125 -> ()))
   | uu____126 -> ())
  
let finalize_hints_db : Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____131 = FStar_Options.record_hints ()  in
     match uu____131 with
     | true  ->
         let hints = FStar_Option.get (FStar_ST.read recorded_hints)  in
         let hints_db =
           let _0_332 = FStar_Util.digest_of_file src_filename  in
           { FStar_Util.module_digest = _0_332; FStar_Util.hints = hints }
            in
         let hints_file_name = format_hints_file_name src_filename  in
         FStar_Util.write_hints hints_file_name hints_db
     | uu____138 -> ());
    (let uu____140 = FStar_Options.hint_info ()  in
     match uu____140 with
     | true  ->
         let stats =
           let _0_333 = FStar_ST.read hint_stats  in
           FStar_All.pipe_right _0_333 FStar_List.rev  in
         FStar_All.pipe_right stats
           (FStar_List.iter
              (fun s  ->
                 match s.replay_result with
                 | FStar_Util.Inl _unsat_core ->
                     let _0_335 =
                       FStar_Range.string_of_range s.source_location  in
                     let _0_334 = FStar_Util.string_of_int s.elapsed_time  in
                     FStar_Util.print2
                       "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                       _0_335 _0_334
                 | FStar_Util.Inr _error ->
                     let _0_337 =
                       FStar_Range.string_of_range s.source_location  in
                     let _0_336 = FStar_Util.string_of_int s.elapsed_time  in
                     FStar_Util.print2
                       "Hint-info (%s): Replay failed in %s milliseconds\n"
                       _0_337 _0_336))
     | uu____152 -> ());
    FStar_ST.write recorded_hints None;
    FStar_ST.write replaying_hints None;
    FStar_ST.write hint_stats []
  
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f ()  in finalize_hints_db fname; result) 
let next_hint : Prims.string -> Prims.int -> FStar_Util.hint Prims.option =
  fun qname  ->
    fun qindex  ->
      let uu____191 = FStar_ST.read replaying_hints  in
      match uu____191 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___92_208  ->
               match uu___92_208 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____203 -> None)
      | uu____205 -> None
  
let record_hint : FStar_Util.hint Prims.option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___91_216 = h  in
             {
               FStar_Util.hint_name = (uu___94_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___94_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___94_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___94_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___94_225.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             })
       in
    let uu____217 = FStar_ST.read recorded_hints  in
    match uu____217 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint]))
    | uu____231 -> ()
  
let record_hint_stat :
  FStar_Util.hint Prims.option ->
    z3_result -> Prims.int -> FStar_Range.range -> Prims.unit
  =
  fun h  ->
    fun res  ->
      fun time  ->
        fun r  ->
          let s =
            {
              hint = h;
              replay_result = (z3_result_as_replay_result res);
              elapsed_time = time;
              source_location = r
            }  in
          let _0_339 = let _0_338 = FStar_ST.read hint_stats  in s :: _0_338
             in
          FStar_ST.write hint_stats _0_339
  
let ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) *
      Prims.string * FStar_Range.range) Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____299 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n) -> ((FStar_Ident.text_of_lid q), n)  in
             match uu____286 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None  in
                 let set_minimum_workable_fuel f uu___90_342 =
                   match uu___90_342 with
                   | ([],uu____349) -> ()
                   | errs ->
                       let uu____355 = FStar_ST.read minimum_workable_fuel
                          in
                       (match uu____355 with
                        | Some uu____376 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs)))
                    in
                 let with_fuel label_assumptions p uu____440 =
                   match uu____440 with
                   | (n,i,rlimit) ->
                       let _0_361 =
                         let _0_352 =
                           FStar_SMTEncoding_Term.Caption
                             (let _0_341 = FStar_Util.string_of_int n  in
                              let _0_340 = FStar_Util.string_of_int i  in
                              FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                                _0_341 _0_340)
                            in
                         let _0_351 =
                           let _0_350 =
                             FStar_SMTEncoding_Term.Assume
                               (let _0_344 =
                                  FStar_SMTEncoding_Util.mkEq
                                    (let _0_343 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxFuel", [])
                                        in
                                     let _0_342 =
                                       FStar_SMTEncoding_Term.n_fuel n  in
                                     (_0_343, _0_342))
                                   in
                                (_0_344, None, None))
                              in
                           let _0_349 =
                             let _0_348 =
                               FStar_SMTEncoding_Term.Assume
                                 (let _0_347 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (let _0_346 =
                                         FStar_SMTEncoding_Util.mkApp
                                           ("MaxIFuel", [])
                                          in
                                       let _0_345 =
                                         FStar_SMTEncoding_Term.n_fuel i  in
                                       (_0_346, _0_345))
                                     in
                                  (_0_347, None, None))
                                in
                             [_0_348; p]  in
                           _0_350 :: _0_349  in
                         _0_352 :: _0_351  in
                       let _0_360 =
                         let _0_359 =
                           let _0_358 =
                             let _0_354 =
                               FStar_SMTEncoding_Term.SetOption
                                 (let _0_353 =
                                    FStar_Util.string_of_int rlimit  in
                                  ("rlimit", _0_353))
                                in
                             [_0_354]  in
                           let _0_357 =
                             let _0_356 =
                               let _0_355 =
                                 let uu____455 =
                                   FStar_Options.record_hints ()  in
                                 match uu____455 with
                                 | true  ->
                                     [FStar_SMTEncoding_Term.GetUnsatCore]
                                 | uu____457 -> []  in
                               FStar_List.append _0_355 suffix  in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] _0_356
                              in
                           FStar_List.append _0_358 _0_357  in
                         FStar_List.append label_assumptions _0_359  in
                       FStar_List.append _0_361 _0_360
                    in
                 let check p =
                   let rlimit =
                     let _0_362 = FStar_Options.z3_rlimit ()  in
                     _0_362 * (Prims.parse_int "544656")  in
                   let default_initial_config =
                     let _0_364 = FStar_Options.initial_fuel ()  in
                     let _0_363 = FStar_Options.initial_ifuel ()  in
                     (_0_364, _0_363, rlimit)  in
                   let hint_opt = next_hint query_name query_index  in
                   let uu____469 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____491 =
                           match FStar_Option.isSome
                                   hint.FStar_Util.unsat_core
                           with
                           | true  -> ((hint.FStar_Util.unsat_core), rlimit)
                           | uu____503 ->
                               (None,
                                 ((Prims.parse_int "60") *
                                    (Prims.parse_int "544656")))
                            in
                         (match uu____491 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout)))
                      in
                   match uu____469 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         FStar_List.flatten
                           (let _0_395 =
                              let _0_394 =
                                let uu____571 =
                                  let _0_366 = FStar_Options.max_ifuel ()  in
                                  let _0_365 = FStar_Options.initial_ifuel ()
                                     in
                                  _0_366 > _0_365  in
                                match uu____571 with
                                | true  ->
                                    let _0_369 =
                                      let _0_368 =
                                        FStar_Options.initial_fuel ()  in
                                      let _0_367 = FStar_Options.max_ifuel ()
                                         in
                                      (_0_368, _0_367, rlimit)  in
                                    [_0_369]
                                | uu____582 -> []  in
                              let _0_393 =
                                let _0_392 =
                                  let uu____590 =
                                    let _0_372 =
                                      let _0_370 = FStar_Options.max_fuel ()
                                         in
                                      _0_370 / (Prims.parse_int "2")  in
                                    let _0_371 =
                                      FStar_Options.initial_fuel ()  in
                                    _0_372 > _0_371  in
                                  match uu____590 with
                                  | true  ->
                                      let _0_376 =
                                        let _0_375 =
                                          let _0_373 =
                                            FStar_Options.max_fuel ()  in
                                          _0_373 / (Prims.parse_int "2")  in
                                        let _0_374 =
                                          FStar_Options.max_ifuel ()  in
                                        (_0_375, _0_374, rlimit)  in
                                      [_0_376]
                                  | uu____601 -> []  in
                                let _0_391 =
                                  let _0_390 =
                                    let uu____609 =
                                      (let _0_378 = FStar_Options.max_fuel ()
                                          in
                                       let _0_377 =
                                         FStar_Options.initial_fuel ()  in
                                       _0_378 > _0_377) &&
                                        (let _0_380 =
                                           FStar_Options.max_ifuel ()  in
                                         let _0_379 =
                                           FStar_Options.initial_ifuel ()  in
                                         _0_380 > _0_379)
                                       in
                                    match uu____609 with
                                    | true  ->
                                        let _0_383 =
                                          let _0_382 =
                                            FStar_Options.max_fuel ()  in
                                          let _0_381 =
                                            FStar_Options.max_ifuel ()  in
                                          (_0_382, _0_381, rlimit)  in
                                        [_0_383]
                                    | uu____620 -> []  in
                                  let _0_389 =
                                    let _0_388 =
                                      let uu____628 =
                                        let _0_385 =
                                          FStar_Options.min_fuel ()  in
                                        let _0_384 =
                                          FStar_Options.initial_fuel ()  in
                                        _0_385 < _0_384  in
                                      match uu____628 with
                                      | true  ->
                                          let _0_387 =
                                            let _0_386 =
                                              FStar_Options.min_fuel ()  in
                                            (_0_386, (Prims.parse_int "1"),
                                              rlimit)
                                             in
                                          [_0_387]
                                      | uu____639 -> []  in
                                    [_0_388]  in
                                  _0_390 :: _0_389  in
                                _0_392 :: _0_391  in
                              _0_394 :: _0_393  in
                            (match (default_initial_config <> initial_config)
                                     || (FStar_Option.isSome unsat_core)
                             with
                             | true  -> [default_initial_config]
                             | uu____563 -> []) :: _0_395)
                          in
                       let report p errs =
                         let errs =
                           let uu____655 =
                             (FStar_Options.detail_errors ()) &&
                               (let _0_396 = FStar_Options.n_cores ()  in
                                _0_396 = (Prims.parse_int "1"))
                              in
                           match uu____655 with
                           | true  ->
                               let uu____656 =
                                 let uu____665 =
                                   FStar_ST.read minimum_workable_fuel  in
                                 match uu____665 with
                                 | Some (f,errs) -> (f, errs)
                                 | None  ->
                                     let _0_398 =
                                       let _0_397 = FStar_Options.min_fuel ()
                                          in
                                       (_0_397, (Prims.parse_int "1"),
                                         rlimit)
                                        in
                                     (_0_398, errs)
                                  in
                               (match uu____656 with
                                | (min_fuel,potential_errors) ->
                                    let ask_z3 label_assumptions =
                                      let res = FStar_Util.mk_ref None  in
                                      (let _0_399 =
                                         with_fuel label_assumptions p
                                           min_fuel
                                          in
                                       FStar_SMTEncoding_Z3.ask None
                                         all_labels _0_399
                                         (fun r  ->
                                            FStar_ST.write res (Some r)));
                                      FStar_Option.get (FStar_ST.read res)
                                       in
                                    let _0_400 =
                                      FStar_SMTEncoding_ErrorReporting.detail_errors
                                        env all_labels ask_z3
                                       in
                                    (_0_400, FStar_SMTEncoding_Z3.Default))
                           | uu____821 ->
                               (match errs with
                                | ([],FStar_SMTEncoding_Z3.Timeout ) ->
                                    ([(("", FStar_SMTEncoding_Term.Term_sort),
                                        "Timeout: Unknown assertion failed",
                                        FStar_Range.dummyRange)],
                                      (Prims.snd errs))
                                | ([],FStar_SMTEncoding_Z3.Default ) ->
                                    ([(("", FStar_SMTEncoding_Term.Term_sort),
                                        "Unknown assertion failed",
                                        FStar_Range.dummyRange)],
                                      (Prims.snd errs))
                                | (uu____860,FStar_SMTEncoding_Z3.Kill ) ->
                                    ([(("", FStar_SMTEncoding_Term.Term_sort),
                                        "Killed: Unknown assertion failed",
                                        FStar_Range.dummyRange)],
                                      (Prims.snd errs))
                                | uu____879 -> errs)
                            in
                         record_hint None;
                         (let uu____882 = FStar_Options.print_fuels ()  in
                          match uu____882 with
                          | true  ->
                              let _0_405 =
                                FStar_Range.string_of_range
                                  (FStar_TypeChecker_Env.get_range env)
                                 in
                              let _0_404 =
                                let _0_401 = FStar_Options.max_fuel ()  in
                                FStar_All.pipe_right _0_401
                                  FStar_Util.string_of_int
                                 in
                              let _0_403 =
                                let _0_402 = FStar_Options.max_ifuel ()  in
                                FStar_All.pipe_right _0_402
                                  FStar_Util.string_of_int
                                 in
                              FStar_Util.print3
                                "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                                _0_405 _0_404 _0_403
                          | uu____883 -> ());
                         (let _0_406 =
                            FStar_All.pipe_right (Prims.fst errs)
                              (FStar_List.map
                                 (fun uu____892  ->
                                    match uu____892 with
                                    | (uu____898,x,y) -> (x, y)))
                             in
                          FStar_TypeChecker_Err.add_errors env _0_406)
                          in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____926,FStar_Util.Inr uu____927) ->
                             FStar_Util.Inr errs
                          in
                       let rec try_alt_configs prev_f p errs cfgs =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::[],uu____1192) ->
                              (match errs with
                               | ([],uu____1020) ->
                                   let _0_407 = with_fuel [] p mi  in
                                   FStar_SMTEncoding_Z3.ask None all_labels
                                     uu____1208 (Some scope)
                                     (cb false mi p1 [] scope)
                               | uu____1214 ->
                                   (set_minimum_workable_fuel prev_f errs;
                                    report p errs))
                          | (mi::tl,uu____1030) ->
                              let _0_410 = with_fuel [] p mi  in
                              FStar_SMTEncoding_Z3.ask None all_labels _0_410
                                (fun uu____1046  ->
                                   match uu____1046 with
                                   | (result,elapsed_time) ->
                                       let _0_409 =
                                         let _0_408 = use_errors errs result
                                            in
                                         (_0_408, elapsed_time)  in
                                       cb false mi p tl _0_409))
                       
                       and cb used_hint uu____1064 p alt uu____1067 =
                         match (uu____1064, uu____1067) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time))
                             ->
                             ((match used_hint with
                               | true  ->
                                   (FStar_SMTEncoding_Z3.refresh ();
                                    (let _0_411 =
                                       FStar_TypeChecker_Env.get_range env
                                        in
                                     record_hint_stat hint_opt result
                                       elapsed_time _0_411))
                               | uu____1114 -> ());
                              (let uu____1116 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.print_z3_statistics ())
                                  in
                               match uu____1116 with
                               | true  -> FStar_SMTEncoding_Z3.refresh ()
                               | uu____1117 -> ());
                              (let query_info tag =
                                 let _0_426 =
                                   let _0_425 =
                                     FStar_Range.string_of_range
                                       (FStar_TypeChecker_Env.get_range env)
                                      in
                                   let _0_424 =
                                     let _0_423 =
                                       FStar_SMTEncoding_Z3.at_log_file ()
                                        in
                                     let _0_422 =
                                       let _0_421 =
                                         let _0_420 =
                                           FStar_Util.string_of_int
                                             query_index
                                            in
                                         let _0_419 =
                                           let _0_418 =
                                             let _0_417 =
                                               let _0_416 =
                                                 FStar_Util.string_of_int
                                                   elapsed_time
                                                  in
                                               let _0_415 =
                                                 let _0_414 =
                                                   FStar_Util.string_of_int
                                                     prev_fuel
                                                    in
                                                 let _0_413 =
                                                   let _0_412 =
                                                     FStar_Util.string_of_int
                                                       prev_ifuel
                                                      in
                                                   [_0_412]  in
                                                 _0_414 :: _0_413  in
                                               _0_416 :: _0_415  in
                                             (match used_hint with
                                              | true  -> " (with hint)"
                                              | uu____1122 -> "") :: _0_417
                                              in
                                           tag :: _0_418  in
                                         _0_420 :: _0_419  in
                                       query_name :: _0_421  in
                                     _0_423 :: _0_422  in
                                   _0_425 :: _0_424  in
                                 FStar_Util.print
                                   "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n"
                                   _0_426
                                  in
                               match result with
                               | FStar_Util.Inl unsat_core ->
                                   ((match Prims.op_Negation used_hint with
                                     | true  ->
                                         let hint =
                                           {
                                             FStar_Util.hint_name =
                                               query_name;
                                             FStar_Util.hint_index =
                                               query_index;
                                             FStar_Util.fuel = prev_fuel;
                                             FStar_Util.ifuel = prev_ifuel;
                                             FStar_Util.unsat_core =
                                               unsat_core;
                                             FStar_Util.query_elapsed_time =
                                               elapsed_time
                                           }  in
                                         record_hint (Some hint)
                                     | uu____1128 -> record_hint hint_opt);
                                    (let uu____1129 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ())
                                        in
                                     match uu____1129 with
                                     | true  -> query_info "succeeded"
                                     | uu____1130 -> ()))
                               | FStar_Util.Inr errs ->
                                   ((let uu____1362 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ())
                                        in
                                     match uu____1137 with
                                     | true  -> query_info "failed"
                                     | uu____1138 -> ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p errs
                                      alt)))
                        in
                       ((match FStar_Option.isSome unsat_core with
                         | true  -> FStar_SMTEncoding_Z3.refresh ()
                         | uu____1141 -> ());
                        (let _0_427 = with_fuel [] p initial_config  in
                         FStar_SMTEncoding_Z3.ask unsat_core all_labels
                           _0_427
                           (cb (FStar_Option.isSome unsat_core)
                              initial_config p alt_configs)))
                    in
                 let process_query q =
                   let uu____1147 =
                     let _0_428 = FStar_Options.split_cases ()  in
                     _0_428 > (Prims.parse_int "0")  in
                   match uu____1147 with
                   | true  ->
                       let uu____1148 =
                         let _0_429 = FStar_Options.split_cases ()  in
                         FStar_SMTEncoding_SplitQueryCases.can_handle_query
                           _0_429 q
                          in
                       (match uu____1148 with
                        | (b,cb) ->
                            (match b with
                             | true  ->
                                 FStar_SMTEncoding_SplitQueryCases.handle_query
                                   cb check
                             | uu____1171 -> check q))
                   | uu____1172 -> check q  in
                 let uu____1173 = FStar_Options.admit_smt_queries ()  in
                 (match uu____1173 with
                  | true  -> ()
                  | uu____1174 -> process_query query))
  
let solve :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        FStar_SMTEncoding_Encode.push
          (let _0_431 =
             let _0_430 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range _0_430  in
           FStar_Util.format1 "Starting query at %s" _0_431);
        (let tcenv = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____1193 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q  in
         match uu____1193 with
         | (prefix,labels,qry,suffix) ->
             let pop uu____1214 =
               FStar_SMTEncoding_Encode.pop
                 (let _0_433 =
                    let _0_432 = FStar_TypeChecker_Env.get_range tcenv  in
                    FStar_All.pipe_left FStar_Range.string_of_range _0_432
                     in
                  FStar_Util.format1 "Ending query at %s" _0_433)
                in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  ({
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.FalseOp ,uu____1215);
                     FStar_SMTEncoding_Term.freevars = uu____1216;
                     FStar_SMTEncoding_Term.rng = uu____1217;_},uu____1218,uu____1219)
                  -> pop ()
              | uu____1229 when tcenv.FStar_TypeChecker_Env.admit -> pop ()
              | FStar_SMTEncoding_Term.Assume (q,uu____1232,uu____1233) ->
                  (ask_and_report_errors tcenv labels prefix qry suffix;
                   pop ())
              | uu____1237 -> failwith "Impossible"))
  
let solver : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark;
    FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark;
    FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark;
    FStar_TypeChecker_Env.encode_modul =
      FStar_SMTEncoding_Encode.encode_modul;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1462  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1463  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1464  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1465  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1466  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1467  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1468  -> fun uu____1469  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1470  -> fun uu____1471  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1478  -> fun uu____1479  -> fun uu____1480  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1254  -> fun uu____1255  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1256  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1257  -> ())
  } 
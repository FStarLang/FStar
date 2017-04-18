open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels* FStar_SMTEncoding_Z3.error_kind)
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
  hint: FStar_Util.hint Prims.option;
  replay_result: z3_replay_result;
  elapsed_time: Prims.int;
  source_location: FStar_Range.range;}
type hint_stats_t = hint_stat Prims.list
let recorded_hints: FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None
let replaying_hints: FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None
let hint_stats: hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____102 = FStar_Options.record_hints () in
   if uu____102 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____110 = FStar_Options.use_hints () in
   if uu____110
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____113 = FStar_Util.read_hints val_filename in
     match uu____113 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____118 = FStar_Options.hint_info () in
           if uu____118
           then
             (if hints.FStar_Util.module_digest = expected_digest
              then
                FStar_Util.print1 "(%s) digest is valid; using hints db.\n"
                  norm_src_filename
              else
                FStar_Util.print1
                  "(%s) digest is invalid; using potentially stale hints\n"
                  norm_src_filename)
           else ());
          FStar_ST.write replaying_hints (Some (hints.FStar_Util.hints)))
     | None  ->
         let uu____124 = FStar_Options.hint_info () in
         (if uu____124
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____131 = FStar_Options.record_hints () in
     if uu____131
     then
       let hints =
         let uu____133 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____133 in
       let hints_db =
         let uu____139 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____139; FStar_Util.hints = hints } in
       let hints_file_name = format_hints_file_name src_filename in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____143 = FStar_Options.hint_info () in
     if uu____143
     then
       let stats =
         let uu____146 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____146 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____156 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____157 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____156 uu____157
               | FStar_Util.Inr _error ->
                   let uu____159 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____160 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____159 uu____160))
     else ());
    FStar_ST.write recorded_hints None;
    FStar_ST.write replaying_hints None;
    FStar_ST.write hint_stats []
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f () in finalize_hints_db fname; result)
let next_hint: Prims.string -> Prims.int -> FStar_Util.hint Prims.option =
  fun qname  ->
    fun qindex  ->
      let uu____200 = FStar_ST.read replaying_hints in
      match uu____200 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___92_208  ->
               match uu___92_208 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____212 -> None)
      | uu____214 -> None
let record_hint: FStar_Util.hint Prims.option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___94_225 = h in
             {
               FStar_Util.hint_name = (uu___94_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___94_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___94_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___94_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___94_225.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____226 = FStar_ST.read recorded_hints in
    match uu____226 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____240 -> ()
let record_hint_stat:
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
            } in
          let uu____257 =
            let uu____259 = FStar_ST.read hint_stats in s :: uu____259 in
          FStar_ST.write hint_stats uu____257
let ask_and_report_errors:
  FStar_TypeChecker_Env.env ->
    ((FStar_SMTEncoding_Z3.label* FStar_SMTEncoding_Term.sort)* Prims.string*
      FStar_Range.range) Prims.list ->
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
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____299 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___93_355 =
                   match uu___93_355 with
                   | ([],uu____362) -> ()
                   | errs ->
                       let uu____368 = FStar_ST.read minimum_workable_fuel in
                       (match uu____368 with
                        | Some uu____389 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____453 =
                   match uu____453 with
                   | (n1,i,rlimit) ->
                       let uu____462 =
                         let uu____464 =
                           let uu____465 =
                             let uu____466 = FStar_Util.string_of_int n1 in
                             let uu____467 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____466 uu____467 in
                           FStar_SMTEncoding_Term.Caption uu____465 in
                         let uu____468 =
                           let uu____470 =
                             let uu____471 =
                               let uu____475 =
                                 let uu____476 =
                                   let uu____479 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____481 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____479, uu____481) in
                                 FStar_SMTEncoding_Util.mkEq uu____476 in
                               (uu____475, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Term.Assume uu____471 in
                           let uu____483 =
                             let uu____485 =
                               let uu____486 =
                                 let uu____490 =
                                   let uu____491 =
                                     let uu____494 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____496 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____494, uu____496) in
                                   FStar_SMTEncoding_Util.mkEq uu____491 in
                                 (uu____490, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Term.Assume uu____486 in
                             [uu____485; p] in
                           uu____470 :: uu____483 in
                         uu____464 :: uu____468 in
                       let uu____498 =
                         let uu____500 =
                           let uu____502 =
                             let uu____504 =
                               let uu____505 =
                                 let uu____508 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____508) in
                               FStar_SMTEncoding_Term.SetOption uu____505 in
                             [uu____504] in
                           let uu____509 =
                             let uu____511 =
                               let uu____513 =
                                 let uu____515 =
                                   FStar_Options.record_hints () in
                                 if uu____515
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               FStar_List.append uu____513 suffix in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____511 in
                           FStar_List.append uu____502 uu____509 in
                         FStar_List.append label_assumptions uu____500 in
                       FStar_List.append uu____462 uu____498 in
                 let check p =
                   let rlimit =
                     let uu____523 = FStar_Options.z3_rlimit_factor () in
                     let uu____524 =
                       let uu____525 = FStar_Options.z3_rlimit () in
                       uu____525 * (Prims.parse_int "544656") in
                     uu____523 * uu____524 in
                   let default_initial_config =
                     let uu____530 = FStar_Options.initial_fuel () in
                     let uu____531 = FStar_Options.initial_ifuel () in
                     (uu____530, uu____531, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____534 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____556 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____556 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____534 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____607 =
                           let uu____613 =
                             let uu____619 =
                               let uu____624 =
                                 let uu____625 = FStar_Options.max_ifuel () in
                                 let uu____626 =
                                   FStar_Options.initial_ifuel () in
                                 uu____625 > uu____626 in
                               if uu____624
                               then
                                 let uu____631 =
                                   let uu____635 =
                                     FStar_Options.initial_fuel () in
                                   let uu____636 = FStar_Options.max_ifuel () in
                                   (uu____635, uu____636, rlimit) in
                                 [uu____631]
                               else [] in
                             let uu____647 =
                               let uu____653 =
                                 let uu____658 =
                                   let uu____659 =
                                     let uu____660 =
                                       FStar_Options.max_fuel () in
                                     uu____660 / (Prims.parse_int "2") in
                                   let uu____664 =
                                     FStar_Options.initial_fuel () in
                                   uu____659 > uu____664 in
                                 if uu____658
                                 then
                                   let uu____669 =
                                     let uu____673 =
                                       let uu____674 =
                                         FStar_Options.max_fuel () in
                                       uu____674 / (Prims.parse_int "2") in
                                     let uu____678 =
                                       FStar_Options.max_ifuel () in
                                     (uu____673, uu____678, rlimit) in
                                   [uu____669]
                                 else [] in
                               let uu____689 =
                                 let uu____695 =
                                   let uu____700 =
                                     (let uu____701 =
                                        FStar_Options.max_fuel () in
                                      let uu____702 =
                                        FStar_Options.initial_fuel () in
                                      uu____701 > uu____702) &&
                                       (let uu____703 =
                                          FStar_Options.max_ifuel () in
                                        let uu____704 =
                                          FStar_Options.initial_ifuel () in
                                        uu____703 > uu____704) in
                                   if uu____700
                                   then
                                     let uu____709 =
                                       let uu____713 =
                                         FStar_Options.max_fuel () in
                                       let uu____714 =
                                         FStar_Options.max_ifuel () in
                                       (uu____713, uu____714, rlimit) in
                                     [uu____709]
                                   else [] in
                                 let uu____725 =
                                   let uu____731 =
                                     let uu____736 =
                                       let uu____737 =
                                         FStar_Options.min_fuel () in
                                       let uu____738 =
                                         FStar_Options.initial_fuel () in
                                       uu____737 < uu____738 in
                                     if uu____736
                                     then
                                       let uu____743 =
                                         let uu____747 =
                                           FStar_Options.min_fuel () in
                                         (uu____747, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____743]
                                     else [] in
                                   [uu____731] in
                                 uu____695 :: uu____725 in
                               uu____653 :: uu____689 in
                             uu____619 :: uu____647 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____613 in
                         FStar_List.flatten uu____607 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____811 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____812 = FStar_Options.n_cores () in
                                uu____812 = (Prims.parse_int "1")) in
                           if uu____811
                           then
                             let uu____813 =
                               let uu____822 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____822 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____887 =
                                     let uu____891 =
                                       FStar_Options.min_fuel () in
                                     (uu____891, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____887, errs) in
                             match uu____813 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____945 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask None all_labels
                                      uu____945 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____970 = FStar_ST.read res in
                                    FStar_Option.get uu____970) in
                                 let uu____993 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____993, FStar_SMTEncoding_Z3.Default)
                           else
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
                              | (uu____1033,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (Prims.snd errs))
                              | uu____1052 -> errs) in
                         record_hint None;
                         (let uu____1055 = FStar_Options.print_fuels () in
                          if uu____1055
                          then
                            let uu____1056 =
                              let uu____1057 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1057 in
                            let uu____1058 =
                              let uu____1059 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1059
                                FStar_Util.string_of_int in
                            let uu____1060 =
                              let uu____1061 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1061
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1056 uu____1058 uu____1060
                          else ());
                         (let uu____1063 =
                            FStar_All.pipe_right (Prims.fst errs1)
                              (FStar_List.map
                                 (fun uu____1075  ->
                                    match uu____1075 with
                                    | (uu____1081,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1063) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____1109,FStar_Util.Inr uu____1110) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::[],uu____1194) ->
                              (match errs with
                               | ([],uu____1208) ->
                                   let uu____1210 = with_fuel [] p1 mi in
                                   FStar_SMTEncoding_Z3.ask None all_labels
                                     uu____1210 (Some scope)
                                     (cb false mi p1 [] scope)
                               | uu____1216 ->
                                   (set_minimum_workable_fuel prev_f errs;
                                    report1 p1 errs))
                          | (mi::tl1,uu____1220) ->
                              let uu____1235 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask None all_labels
                                uu____1235 (Some scope)
                                (fun uu____1238  ->
                                   match uu____1238 with
                                   | (result,elapsed_time) ->
                                       let uu____1255 =
                                         let uu____1262 =
                                           use_errors errs result in
                                         (uu____1262, elapsed_time) in
                                       cb false mi p1 tl1 scope uu____1255))
                       and cb used_hint uu____1264 p1 alt scope uu____1268 =
                         match (uu____1264, uu____1268) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1315 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1315))
                              else ();
                              (let uu____1318 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.print_z3_statistics ()) in
                               if uu____1318
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info tag =
                                 let uu____1324 =
                                   let uu____1326 =
                                     let uu____1327 =
                                       FStar_TypeChecker_Env.get_range env in
                                     FStar_Range.string_of_range uu____1327 in
                                   let uu____1328 =
                                     let uu____1330 =
                                       FStar_SMTEncoding_Z3.at_log_file () in
                                     let uu____1331 =
                                       let uu____1333 =
                                         let uu____1335 =
                                           FStar_Util.string_of_int
                                             query_index in
                                         let uu____1336 =
                                           let uu____1338 =
                                             let uu____1340 =
                                               let uu____1342 =
                                                 FStar_Util.string_of_int
                                                   elapsed_time in
                                               let uu____1343 =
                                                 let uu____1345 =
                                                   FStar_Util.string_of_int
                                                     prev_fuel in
                                                 let uu____1346 =
                                                   let uu____1348 =
                                                     FStar_Util.string_of_int
                                                       prev_ifuel in
                                                   [uu____1348] in
                                                 uu____1345 :: uu____1346 in
                                               uu____1342 :: uu____1343 in
                                             (if used_hint
                                              then " (with hint)"
                                              else "") :: uu____1340 in
                                           tag :: uu____1338 in
                                         uu____1335 :: uu____1336 in
                                       query_name :: uu____1333 in
                                     uu____1330 :: uu____1331 in
                                   uu____1326 :: uu____1328 in
                                 FStar_Util.print
                                   "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n"
                                   uu____1324 in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (if Prims.op_Negation used_hint
                                    then
                                      (let hint =
                                         {
                                           FStar_Util.hint_name = query_name;
                                           FStar_Util.hint_index =
                                             query_index;
                                           FStar_Util.fuel = prev_fuel;
                                           FStar_Util.ifuel = prev_ifuel;
                                           FStar_Util.unsat_core =
                                             unsat_core1;
                                           FStar_Util.query_elapsed_time =
                                             elapsed_time
                                         } in
                                       record_hint (Some hint))
                                    else record_hint hint_opt;
                                    (let uu____1356 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ()) in
                                     if uu____1356
                                     then query_info "succeeded"
                                     else ()))
                               | FStar_Util.Inr errs ->
                                   ((let uu____1364 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ()) in
                                     if uu____1364
                                     then query_info "failed"
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope))) in
                       ((let uu____1367 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1367
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let uu____1370 = with_fuel [] p initial_config in
                         let uu____1372 =
                           let uu____1381 =
                             FStar_ST.read FStar_SMTEncoding_Z3.fresh_scope in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1381 in
                         FStar_SMTEncoding_Z3.ask unsat_core all_labels
                           uu____1370 None uu____1372)) in
                 let process_query q = check q in
                 let uu____1391 = FStar_Options.admit_smt_queries () in
                 if uu____1391 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1410 =
           let uu____1411 =
             let uu____1412 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1412 in
           FStar_Util.format1 "Starting query at %s" uu____1411 in
         FStar_SMTEncoding_Encode.push uu____1410);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1414 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1414 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1435 =
               let uu____1436 =
                 let uu____1437 =
                   let uu____1438 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1438 in
                 FStar_Util.format1 "Ending query at %s" uu____1437 in
               FStar_SMTEncoding_Encode.pop uu____1436 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  ({
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.FalseOp ,uu____1439);
                     FStar_SMTEncoding_Term.freevars = uu____1440;
                     FStar_SMTEncoding_Term.rng = uu____1441;_},uu____1442,uu____1443)
                  -> pop1 ()
              | uu____1451 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume (q1,uu____1454,uu____1455) ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1457 -> failwith "Impossible"))
let solver: FStar_TypeChecker_Env.solver_t =
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
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1464  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1465  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1466  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1467  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1468  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1469  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1470  -> fun uu____1471  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1472  -> fun uu____1473  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1480  -> fun uu____1481  -> fun uu____1482  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1486  -> fun uu____1487  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1488  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1489  -> ())
  }
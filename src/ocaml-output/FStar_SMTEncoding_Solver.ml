open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels* FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___97_23 =
  match uu___97_23 with
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
            (fun uu___98_208  ->
               match uu___98_208 with
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
            (let uu___100_225 = h in
             {
               FStar_Util.hint_name = (uu___100_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___100_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___100_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___100_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___100_225.FStar_Util.unsat_core);
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
                 let set_minimum_workable_fuel f uu___99_355 =
                   match uu___99_355 with
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
                               let uu____518 =
                                 let uu____520 =
                                   let uu____522 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____522
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____525 =
                                   let uu____527 =
                                     let uu____529 =
                                       FStar_Options.check_hints () in
                                     if uu____529
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____527 suffix in
                                 FStar_List.append uu____520 uu____525 in
                               FStar_List.append uu____513 uu____518 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____511 in
                           FStar_List.append uu____502 uu____509 in
                         FStar_List.append label_assumptions uu____500 in
                       FStar_List.append uu____462 uu____498 in
                 let check p =
                   let rlimit =
                     let uu____537 = FStar_Options.z3_rlimit_factor () in
                     let uu____538 =
                       let uu____539 = FStar_Options.z3_rlimit () in
                       uu____539 * (Prims.parse_int "544656") in
                     uu____537 * uu____538 in
                   let default_initial_config =
                     let uu____544 = FStar_Options.initial_fuel () in
                     let uu____545 = FStar_Options.initial_ifuel () in
                     (uu____544, uu____545, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____548 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____570 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____570 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____548 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____621 =
                           let uu____627 =
                             let uu____633 =
                               let uu____638 =
                                 let uu____639 = FStar_Options.max_ifuel () in
                                 let uu____640 =
                                   FStar_Options.initial_ifuel () in
                                 uu____639 > uu____640 in
                               if uu____638
                               then
                                 let uu____645 =
                                   let uu____649 =
                                     FStar_Options.initial_fuel () in
                                   let uu____650 = FStar_Options.max_ifuel () in
                                   (uu____649, uu____650, rlimit) in
                                 [uu____645]
                               else [] in
                             let uu____661 =
                               let uu____667 =
                                 let uu____672 =
                                   let uu____673 =
                                     let uu____674 =
                                       FStar_Options.max_fuel () in
                                     uu____674 / (Prims.parse_int "2") in
                                   let uu____678 =
                                     FStar_Options.initial_fuel () in
                                   uu____673 > uu____678 in
                                 if uu____672
                                 then
                                   let uu____683 =
                                     let uu____687 =
                                       let uu____688 =
                                         FStar_Options.max_fuel () in
                                       uu____688 / (Prims.parse_int "2") in
                                     let uu____692 =
                                       FStar_Options.max_ifuel () in
                                     (uu____687, uu____692, rlimit) in
                                   [uu____683]
                                 else [] in
                               let uu____703 =
                                 let uu____709 =
                                   let uu____714 =
                                     (let uu____715 =
                                        FStar_Options.max_fuel () in
                                      let uu____716 =
                                        FStar_Options.initial_fuel () in
                                      uu____715 > uu____716) &&
                                       (let uu____717 =
                                          FStar_Options.max_ifuel () in
                                        let uu____718 =
                                          FStar_Options.initial_ifuel () in
                                        uu____717 >= uu____718) in
                                   if uu____714
                                   then
                                     let uu____723 =
                                       let uu____727 =
                                         FStar_Options.max_fuel () in
                                       let uu____728 =
                                         FStar_Options.max_ifuel () in
                                       (uu____727, uu____728, rlimit) in
                                     [uu____723]
                                   else [] in
                                 let uu____739 =
                                   let uu____745 =
                                     let uu____750 =
                                       let uu____751 =
                                         FStar_Options.min_fuel () in
                                       let uu____752 =
                                         FStar_Options.initial_fuel () in
                                       uu____751 < uu____752 in
                                     if uu____750
                                     then
                                       let uu____757 =
                                         let uu____761 =
                                           FStar_Options.min_fuel () in
                                         (uu____761, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____757]
                                     else [] in
                                   [uu____745] in
                                 uu____709 :: uu____739 in
                               uu____667 :: uu____703 in
                             uu____633 :: uu____661 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____627 in
                         FStar_List.flatten uu____621 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____825 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____826 = FStar_Options.n_cores () in
                                uu____826 = (Prims.parse_int "1")) in
                           if uu____825
                           then
                             let uu____827 =
                               let uu____836 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____836 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____901 =
                                     let uu____905 =
                                       FStar_Options.min_fuel () in
                                     (uu____905, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____901, errs) in
                             match uu____827 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____963 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask None all_labels
                                      uu____963 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____991 = FStar_ST.read res in
                                    FStar_Option.get uu____991) in
                                 let uu____1017 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1017, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1057,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (Prims.snd errs))
                              | uu____1076 -> errs) in
                         record_hint None;
                         (let uu____1079 = FStar_Options.print_fuels () in
                          if uu____1079
                          then
                            let uu____1080 =
                              let uu____1081 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1081 in
                            let uu____1082 =
                              let uu____1083 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1083
                                FStar_Util.string_of_int in
                            let uu____1084 =
                              let uu____1085 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1085
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1080 uu____1082 uu____1084
                          else ());
                         (let uu____1087 =
                            FStar_All.pipe_right (Prims.fst errs1)
                              (FStar_List.map
                                 (fun uu____1099  ->
                                    match uu____1099 with
                                    | (uu____1105,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1087) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____1133,FStar_Util.Inr uu____1134) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1216) ->
                              let uu____1231 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask None all_labels
                                uu____1231 (Some scope)
                                (fun uu____1234  ->
                                   match uu____1234 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1253 =
                                         let uu____1257 =
                                           use_errors errs result in
                                         (uu____1257, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1253))
                       and cb used_hint uu____1259 p1 alt scope uu____1263 =
                         match (uu____1259, uu____1263) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1294 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1294))
                              else ();
                              (let uu____1297 =
                                 ((FStar_Options.z3_refresh ()) ||
                                    (FStar_Options.print_z3_statistics ()))
                                   || (FStar_Options.check_hints ()) in
                               if uu____1297
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1316 =
                                   (FStar_Options.print_fuels ()) ||
                                     (FStar_Options.hint_info ()) in
                                 if uu____1316
                                 then
                                   let uu____1317 =
                                     let uu____1319 =
                                       match env1 with
                                       | Some e ->
                                           let uu____1321 =
                                             let uu____1322 =
                                               let uu____1323 =
                                                 FStar_TypeChecker_Env.get_range
                                                   e in
                                               FStar_Range.string_of_range
                                                 uu____1323 in
                                             let uu____1324 =
                                               let uu____1325 =
                                                 FStar_SMTEncoding_Z3.at_log_file
                                                   () in
                                               Prims.strcat uu____1325 ")" in
                                             Prims.strcat uu____1322
                                               uu____1324 in
                                           Prims.strcat "(" uu____1321
                                       | None  -> "" in
                                     let uu____1326 =
                                       let uu____1328 =
                                         let uu____1330 =
                                           let uu____1332 =
                                             FStar_Util.string_of_int
                                               query_index in
                                           let uu____1333 =
                                             let uu____1335 =
                                               let uu____1337 =
                                                 let uu____1339 =
                                                   FStar_Util.string_of_int
                                                     elapsed_time in
                                                 let uu____1340 =
                                                   let uu____1342 =
                                                     FStar_Util.string_of_int
                                                       prev_fuel in
                                                   let uu____1343 =
                                                     let uu____1345 =
                                                       FStar_Util.string_of_int
                                                         prev_ifuel in
                                                     let uu____1346 =
                                                       let uu____1348 =
                                                         FStar_Util.string_of_int
                                                           rlimit in
                                                       let uu____1349 =
                                                         let uu____1351 =
                                                           let uu____1352 =
                                                             FStar_Util.smap_try_find
                                                               statistics1
                                                               "rlimit-count" in
                                                           match uu____1352
                                                           with
                                                           | Some v1 ->
                                                               Prims.strcat
                                                                 " (consumed "
                                                                 (Prims.strcat
                                                                    v1 ")")
                                                           | uu____1355 -> "" in
                                                         let uu____1357 =
                                                           let uu____1359 =
                                                             let uu____1360 =
                                                               FStar_Util.smap_try_find
                                                                 statistics1
                                                                 "reason-unknown" in
                                                             match uu____1360
                                                             with
                                                             | Some v1 ->
                                                                 Prims.strcat
                                                                   " (failure reason: "
                                                                   (Prims.strcat
                                                                    v1 ")")
                                                             | uu____1363 ->
                                                                 "" in
                                                           [uu____1359] in
                                                         uu____1351 ::
                                                           uu____1357 in
                                                       uu____1348 ::
                                                         uu____1349 in
                                                     uu____1345 :: uu____1346 in
                                                   uu____1342 :: uu____1343 in
                                                 uu____1339 :: uu____1340 in
                                               (match env1 with
                                                | Some e ->
                                                    if used_hint
                                                    then " (with hint)"
                                                    else ""
                                                | None  -> "") :: uu____1337 in
                                             tag :: uu____1335 in
                                           uu____1332 :: uu____1333 in
                                         query_name :: uu____1330 in
                                       name :: uu____1328 in
                                     uu____1319 :: uu____1326 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s%s%s\n"
                                     uu____1317
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1385 =
                                     let uu____1386 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1386 in
                                   if uu____1385
                                   then
                                     let hint_check_cb uu____1400 =
                                       match uu____1400 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1423 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1429 ->
                                                 "failed" in
                                           let uu____1434 =
                                             FStar_Options.hint_info () in
                                           if uu____1434
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1438 =
                                         FStar_ST.read current_core in
                                       let uu____1441 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1438
                                         all_labels uu____1441 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1443 =
                                         let uu____1444 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1444 in
                                       if uu____1443
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1451 =
                                             let uu____1452 =
                                               let uu____1454 =
                                                 let uu____1456 =
                                                   let uu____1457 =
                                                     let uu____1458 =
                                                       let uu____1460 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1460] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1458 in
                                                   FStar_Options.String
                                                     uu____1457 in
                                                 [uu____1456] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1454 in
                                             FStar_Options.List uu____1452 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1451);
                                          (let hint_refinement_cb uu____1472
                                             =
                                             match uu____1472 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1494 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1494
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1505 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1505))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1514 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask None
                                              all_labels uu____1514
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1517 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1517
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1522 =
                                                     let uu____1524 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1524] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1522);
                                                  FStar_ST.write current_core
                                                    None)
                                               else
                                                 refine_hint
                                                   (core_ext_max_dist +
                                                      (Prims.parse_int "1")))
                                            else ())))
                                       else ()))
                                   else () in
                                 (let z3cliopts_before =
                                    FStar_Options.z3_cliopt () in
                                  let log_queries_before =
                                    FStar_Options.log_queries () in
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool false);
                                  refine_hint (Prims.parse_int "1");
                                  (let uu____1539 =
                                     let uu____1540 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1540 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1539);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1543 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1543;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1550 =
                                       let uu____1552 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1552
                                       then
                                         let uu____1554 =
                                           let uu____1555 =
                                             FStar_Options.check_hints () in
                                           if uu____1555
                                           then refine_hint unsat_core1 scope
                                           else
                                             {
                                               FStar_Util.hint_name =
                                                 query_name;
                                               FStar_Util.hint_index =
                                                 query_index;
                                               FStar_Util.fuel = prev_fuel;
                                               FStar_Util.ifuel = prev_ifuel;
                                               FStar_Util.unsat_core =
                                                 unsat_core1;
                                               FStar_Util.query_elapsed_time
                                                 = elapsed_time
                                             } in
                                         Some uu____1554
                                       else hint_opt in
                                     record_hint uu____1550))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    if used_hint
                                    then
                                      (FStar_Util.print_string
                                         "Failed hint:\n";
                                       (match unsat_core with
                                        | None  ->
                                            FStar_Util.print_string "<empty>"
                                        | Some core ->
                                            ((let uu____1567 =
                                                FStar_List.map
                                                  (fun x  ->
                                                     FStar_Util.print_string
                                                       (Prims.strcat " " x))
                                                  core in
                                              ());
                                             FStar_Util.print_string "\n")))
                                    else ();
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope))) in
                       ((let uu____1573 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1573
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1578 =
                           let uu____1588 =
                             FStar_ST.read FStar_SMTEncoding_Z3.fresh_scope in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1588 in
                         FStar_SMTEncoding_Z3.ask unsat_core all_labels wf
                           None uu____1578)) in
                 let process_query q = check q in
                 let uu____1598 = FStar_Options.admit_smt_queries () in
                 if uu____1598 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1617 =
           let uu____1618 =
             let uu____1619 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1619 in
           FStar_Util.format1 "Starting query at %s" uu____1618 in
         FStar_SMTEncoding_Encode.push uu____1617);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1621 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1621 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1642 =
               let uu____1643 =
                 let uu____1644 =
                   let uu____1645 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1645 in
                 FStar_Util.format1 "Ending query at %s" uu____1644 in
               FStar_SMTEncoding_Encode.pop uu____1643 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  ({
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.FalseOp ,uu____1646);
                     FStar_SMTEncoding_Term.freevars = uu____1647;
                     FStar_SMTEncoding_Term.rng = uu____1648;_},uu____1649,uu____1650)
                  -> pop1 ()
              | uu____1658 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume (q1,uu____1661,uu____1662) ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1664 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1671  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1672  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1673  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1674  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1675  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1676  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1677  -> fun uu____1678  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1679  -> fun uu____1680  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1687  -> fun uu____1688  -> fun uu____1689  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1693  -> fun uu____1694  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1695  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1696  -> ())
  }
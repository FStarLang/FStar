open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels,FStar_SMTEncoding_Z3.error_kind)
    FStar_Pervasives_Native.tuple2
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___83_35 =
  match uu___83_35 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____50) -> FStar_Util.Inr r
type hint_stat =
  {
  hint: FStar_Util.hint FStar_Pervasives_Native.option;
  replay_result: z3_replay_result;
  elapsed_time: Prims.int;
  source_location: FStar_Range.range;}
type hint_stats_t = hint_stat Prims.list
let recorded_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let replaying_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let hint_stats: hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db src_filename format_filename =
  FStar_ST.write hint_stats [];
  (let uu____135 = FStar_Options.record_hints () in
   if uu____135
   then FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some [])
   else ());
  (let uu____145 = FStar_Options.use_hints () in
   if uu____145
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename =
       let uu____148 = FStar_Options.hint_file () in
       match uu____148 with
       | FStar_Pervasives_Native.Some fn -> fn
       | FStar_Pervasives_Native.None  ->
           format_hints_file_name norm_src_filename in
     let uu____152 = FStar_Util.read_hints val_filename in
     match uu____152 with
     | FStar_Pervasives_Native.Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____158 = FStar_Options.hint_info () in
           if uu____158
           then
             let uu____159 =
               let uu____160 = FStar_Options.hint_file () in
               match uu____160 with
               | FStar_Pervasives_Native.Some fn ->
                   Prims.strcat " from '" (Prims.strcat val_filename "'")
               | uu____164 -> "" in
             FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
               (if hints.FStar_Util.module_digest = expected_digest
                then "valid; using hints"
                else "invalid; using potentially stale hints") uu____159
           else ());
          FStar_ST.write replaying_hints
            (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
     | FStar_Pervasives_Native.None  ->
         let uu____171 = FStar_Options.hint_info () in
         (if uu____171
          then
            FStar_Util.print1 "(%s) Unable to read hint file.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____178 = FStar_Options.record_hints () in
     if uu____178
     then
       let hints =
         let uu____180 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____180 in
       let hints_db =
         let uu____186 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____186; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____189 = FStar_Options.hint_file () in
         match uu____189 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    (let uu____195 = FStar_Options.hint_info () in
     if uu____195
     then
       let stats =
         let uu____199 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____199 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               let uu____211 = FStar_Range.string_of_range s.source_location in
               let uu____212 = FStar_Util.string_of_int s.elapsed_time in
               FStar_Util.print3
                 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____211
                 (match s.replay_result with
                  | FStar_Util.Inl uu____213 -> "succeeded"
                  | FStar_Util.Inr uu____214 -> "failed") uu____212))
     else ());
    FStar_ST.write recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.write replaying_hints FStar_Pervasives_Native.None;
    FStar_ST.write hint_stats []
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f () in finalize_hints_db fname; result)
let next_hint:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____252 = FStar_ST.read replaying_hints in
      match uu____252 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_262  ->
               match uu___84_262 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____268 -> FStar_Pervasives_Native.None)
      | uu____271 -> FStar_Pervasives_Native.None
let record_hint: FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit
  =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___89_287 = h in
             {
               FStar_Util.hint_name = (uu___89_287.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_287.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_287.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_287.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_287.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____288 = FStar_ST.read recorded_hints in
    match uu____288 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.write recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____306 -> ()
let record_hint_stat:
  FStar_Util.hint FStar_Pervasives_Native.option ->
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
          let uu____326 =
            let uu____329 = FStar_ST.read hint_stats in s :: uu____329 in
          FStar_ST.write hint_stats uu____326
let filter_using_facts_from:
  FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t =
  fun theory  ->
    let uu____339 = FStar_Options.using_facts_from () in
    match uu____339 with
    | FStar_Pervasives_Native.None  -> theory
    | FStar_Pervasives_Native.Some namespace_strings ->
        let fact_id_in_namespace ns uu___85_357 =
          match uu___85_357 with
          | FStar_SMTEncoding_Term.Namespace lid ->
              FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns
          | FStar_SMTEncoding_Term.Name _lid -> false
          | FStar_SMTEncoding_Term.Tag _s -> false in
        let matches_fact_ids include_assumption_names a =
          match a.FStar_SMTEncoding_Term.assumption_fact_ids with
          | [] -> true
          | uu____372 ->
              (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
                 include_assumption_names)
                ||
                (FStar_All.pipe_right
                   a.FStar_SMTEncoding_Term.assumption_fact_ids
                   (FStar_Util.for_some
                      (fun fid  ->
                         FStar_All.pipe_right namespace_strings
                           (FStar_Util.for_some
                              (fun ns  -> fact_id_in_namespace ns fid))))) in
        let theory_rev = FStar_List.rev theory in
        let uu____384 =
          FStar_List.fold_left
            (fun uu____401  ->
               fun d  ->
                 match uu____401 with
                 | (out,include_assumption_names) ->
                     (match d with
                      | FStar_SMTEncoding_Term.Assume a ->
                          let uu____438 =
                            matches_fact_ids include_assumption_names a in
                          if uu____438
                          then ((d :: out), include_assumption_names)
                          else (out, include_assumption_names)
                      | FStar_SMTEncoding_Term.RetainAssumptions names ->
                          ((d :: out),
                            (FStar_List.append names include_assumption_names))
                      | uu____463 -> ((d :: out), include_assumption_names)))
            ([], []) theory_rev in
        (match uu____384 with | (pruned_theory,uu____473) -> pruned_theory)
let filter_assertions:
  FStar_SMTEncoding_Z3.unsat_core ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun core  ->
    fun theory  ->
      match core with
      | FStar_Pervasives_Native.None  ->
          let uu____498 = filter_using_facts_from theory in
          (uu____498, false)
      | FStar_Pervasives_Native.Some core1 ->
          let uu____504 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____522  ->
                   match uu____522 with
                   | (theory1,n_retained,n_pruned) ->
                       (match d with
                        | FStar_SMTEncoding_Term.Assume a ->
                            if
                              FStar_List.contains
                                a.FStar_SMTEncoding_Term.assumption_name
                                core1
                            then
                              ((d :: theory1),
                                (n_retained + (Prims.parse_int "1")),
                                n_pruned)
                            else
                              if
                                FStar_Util.starts_with
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  "@"
                              then ((d :: theory1), n_retained, n_pruned)
                              else
                                (theory1, n_retained,
                                  (n_pruned + (Prims.parse_int "1")))
                        | uu____579 -> ((d :: theory1), n_retained, n_pruned)))
              theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
          (match uu____504 with
           | (theory',n_retained,n_pruned) ->
               let missed_assertions th core2 =
                 let missed =
                   let uu____611 =
                     FStar_All.pipe_right core2
                       (FStar_List.filter
                          (fun nm  ->
                             let uu____619 =
                               FStar_All.pipe_right th
                                 (FStar_Util.for_some
                                    (fun uu___86_622  ->
                                       match uu___86_622 with
                                       | FStar_SMTEncoding_Term.Assume a ->
                                           nm =
                                             a.FStar_SMTEncoding_Term.assumption_name
                                       | uu____624 -> false)) in
                             FStar_All.pipe_right uu____619 Prims.op_Negation)) in
                   FStar_All.pipe_right uu____611 (FStar_String.concat ", ") in
                 let included =
                   let uu____628 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___87_635  ->
                             match uu___87_635 with
                             | FStar_SMTEncoding_Term.Assume a ->
                                 [a.FStar_SMTEncoding_Term.assumption_name]
                             | uu____639 -> [])) in
                   FStar_All.pipe_right uu____628 (FStar_String.concat ", ") in
                 FStar_Util.format2 "missed={%s}; included={%s}" missed
                   included in
               ((let uu____643 =
                   (FStar_Options.hint_info ()) &&
                     (FStar_Options.debug_any ()) in
                 if uu____643
                 then
                   let n1 = FStar_List.length core1 in
                   let missed =
                     if n1 <> n_retained
                     then missed_assertions theory' core1
                     else "" in
                   let uu____649 = FStar_Util.string_of_int n_retained in
                   let uu____650 =
                     if n1 <> n_retained
                     then
                       let uu____653 = FStar_Util.string_of_int n1 in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____653 missed
                     else "" in
                   let uu____658 = FStar_Util.string_of_int n_pruned in
                   FStar_Util.print3
                     "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____649 uu____650 uu____658
                 else ());
                (let uu____660 =
                   let uu____663 =
                     let uu____666 =
                       let uu____667 =
                         let uu____668 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____668 in
                       FStar_SMTEncoding_Term.Caption uu____667 in
                     [uu____666] in
                   FStar_List.append theory' uu____663 in
                 (uu____660, true))))
let filter_facts_without_core:
  FStar_SMTEncoding_Term.decls_t ->
    (FStar_SMTEncoding_Term.decls_t,Prims.bool)
      FStar_Pervasives_Native.tuple2
  = fun x  -> let uu____680 = filter_using_facts_from x in (uu____680, false)
let ask_and_report_errors:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
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
            (let uu____705 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1) in
             match uu____705 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None in
                 let set_minimum_workable_fuel f uu___88_803 =
                   match uu___88_803 with
                   | ([],uu____816) -> ()
                   | errs ->
                       let uu____826 = FStar_ST.read minimum_workable_fuel in
                       (match uu____826 with
                        | FStar_Pervasives_Native.Some uu____865 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.write minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs))) in
                 let with_fuel label_assumptions p uu____981 =
                   match uu____981 with
                   | (n1,i,rlimit) ->
                       let uu____995 =
                         let uu____998 =
                           let uu____999 =
                             let uu____1000 = FStar_Util.string_of_int n1 in
                             let uu____1001 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____1000 uu____1001 in
                           FStar_SMTEncoding_Term.Caption uu____999 in
                         let uu____1002 =
                           let uu____1005 =
                             let uu____1006 =
                               let uu____1013 =
                                 let uu____1014 =
                                   let uu____1019 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____1022 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____1019, uu____1022) in
                                 FStar_SMTEncoding_Util.mkEq uu____1014 in
                               (uu____1013, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____1006 in
                           let uu____1025 =
                             let uu____1028 =
                               let uu____1029 =
                                 let uu____1036 =
                                   let uu____1037 =
                                     let uu____1042 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____1045 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____1042, uu____1045) in
                                   FStar_SMTEncoding_Util.mkEq uu____1037 in
                                 (uu____1036, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____1029 in
                             [uu____1028; p] in
                           uu____1005 :: uu____1025 in
                         uu____998 :: uu____1002 in
                       let uu____1048 =
                         let uu____1051 =
                           let uu____1054 =
                             let uu____1057 =
                               let uu____1058 =
                                 let uu____1063 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____1063) in
                               FStar_SMTEncoding_Term.SetOption uu____1058 in
                             [uu____1057] in
                           let uu____1064 =
                             let uu____1067 =
                               let uu____1070 =
                                 let uu____1073 =
                                   FStar_Options.record_hints () in
                                 if uu____1073
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____1077 =
                                 let uu____1080 =
                                   let uu____1083 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____1083
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics;
                                     FStar_SMTEncoding_Term.GetReasonUnknown]
                                   else [] in
                                 FStar_List.append uu____1080 suffix in
                               FStar_List.append uu____1070 uu____1077 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____1067 in
                           FStar_List.append uu____1054 uu____1064 in
                         FStar_List.append label_assumptions uu____1051 in
                       FStar_List.append uu____995 uu____1048 in
                 let check p =
                   let rlimit =
                     let uu____1092 = FStar_Options.z3_rlimit_factor () in
                     let uu____1093 =
                       let uu____1094 = FStar_Options.z3_rlimit () in
                       uu____1094 * (Prims.parse_int "544656") in
                     uu____1092 * uu____1093 in
                   let default_initial_config =
                     let uu____1102 = FStar_Options.initial_fuel () in
                     let uu____1103 = FStar_Options.initial_ifuel () in
                     (uu____1102, uu____1103, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____1107 =
                     match hint_opt with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None,
                           default_initial_config)
                     | FStar_Pervasives_Native.Some hint ->
                         let uu____1149 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (FStar_Pervasives_Native.None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____1149 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____1107 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____1244 =
                           let uu____1255 =
                             let uu____1266 =
                               let uu____1275 =
                                 let uu____1276 = FStar_Options.max_ifuel () in
                                 let uu____1277 =
                                   FStar_Options.initial_ifuel () in
                                 uu____1276 > uu____1277 in
                               if uu____1275
                               then
                                 let uu____1286 =
                                   let uu____1293 =
                                     FStar_Options.initial_fuel () in
                                   let uu____1294 =
                                     FStar_Options.max_ifuel () in
                                   (uu____1293, uu____1294, rlimit) in
                                 [uu____1286]
                               else [] in
                             let uu____1314 =
                               let uu____1325 =
                                 let uu____1334 =
                                   let uu____1335 =
                                     let uu____1336 =
                                       FStar_Options.max_fuel () in
                                     uu____1336 / (Prims.parse_int "2") in
                                   let uu____1340 =
                                     FStar_Options.initial_fuel () in
                                   uu____1335 > uu____1340 in
                                 if uu____1334
                                 then
                                   let uu____1349 =
                                     let uu____1356 =
                                       let uu____1357 =
                                         FStar_Options.max_fuel () in
                                       uu____1357 / (Prims.parse_int "2") in
                                     let uu____1361 =
                                       FStar_Options.max_ifuel () in
                                     (uu____1356, uu____1361, rlimit) in
                                   [uu____1349]
                                 else [] in
                               let uu____1381 =
                                 let uu____1392 =
                                   let uu____1401 =
                                     (let uu____1402 =
                                        FStar_Options.max_fuel () in
                                      let uu____1403 =
                                        FStar_Options.initial_fuel () in
                                      uu____1402 > uu____1403) &&
                                       (let uu____1404 =
                                          FStar_Options.max_ifuel () in
                                        let uu____1405 =
                                          FStar_Options.initial_ifuel () in
                                        uu____1404 >= uu____1405) in
                                   if uu____1401
                                   then
                                     let uu____1414 =
                                       let uu____1421 =
                                         FStar_Options.max_fuel () in
                                       let uu____1422 =
                                         FStar_Options.max_ifuel () in
                                       (uu____1421, uu____1422, rlimit) in
                                     [uu____1414]
                                   else [] in
                                 let uu____1442 =
                                   let uu____1453 =
                                     let uu____1462 =
                                       let uu____1463 =
                                         FStar_Options.min_fuel () in
                                       let uu____1464 =
                                         FStar_Options.initial_fuel () in
                                       uu____1463 < uu____1464 in
                                     if uu____1462
                                     then
                                       let uu____1473 =
                                         let uu____1480 =
                                           FStar_Options.min_fuel () in
                                         (uu____1480, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1473]
                                     else [] in
                                   [uu____1453] in
                                 uu____1392 :: uu____1442 in
                               uu____1325 :: uu____1381 in
                             uu____1266 :: uu____1314 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____1255 in
                         FStar_List.flatten uu____1244 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1597 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1598 = FStar_Options.n_cores () in
                                uu____1598 = (Prims.parse_int "1")) in
                           if uu____1597
                           then
                             let uu____1599 =
                               let uu____1616 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1616 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____1741 =
                                     let uu____1748 =
                                       FStar_Options.min_fuel () in
                                     (uu____1748, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1741, errs) in
                             match uu____1599 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (let uu____1797 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      filter_facts_without_core all_labels
                                      uu____1797 FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.write res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____1805 = FStar_ST.read res in
                                    FStar_Option.get uu____1805) in
                                 let uu____1812 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1812, FStar_SMTEncoding_Z3.Default)
                           else
                             (match errs with
                              | ([],FStar_SMTEncoding_Z3.Timeout ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Timeout: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | ([],FStar_SMTEncoding_Z3.Default ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | (uu____1890,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____1927 -> errs) in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____1930 = FStar_Options.print_fuels () in
                          if uu____1930
                          then
                            let uu____1931 =
                              let uu____1932 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1932 in
                            let uu____1933 =
                              let uu____1934 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1934
                                FStar_Util.string_of_int in
                            let uu____1935 =
                              let uu____1936 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1936
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1931 uu____1933 uu____1935
                          else ());
                         (let uu____1938 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.fst errs1)
                              (FStar_List.map
                                 (fun uu____1961  ->
                                    match uu____1961 with
                                    | (uu____1972,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1938) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1994),uu____1995) -> result
                         | (uu____2004,FStar_Util.Inl uu____2005) -> result
                         | (uu____2018,FStar_Util.Inr uu____2019) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____2122) -> report1 p1 errs
                          | (uu____2137,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____2156) ->
                              let uu____2185 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                filter_facts_without_core all_labels
                                uu____2185
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____2188  ->
                                   match uu____2188 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____2208 =
                                         let uu____2215 =
                                           use_errors errs result in
                                         (uu____2215, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____2208))
                       and cb used_hint uu____2217 p1 alt scope uu____2221 =
                         match (uu____2217, uu____2221) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____2274 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____2274))
                              else ();
                              (let uu____2277 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____2277
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____2300 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____2300
                                 then
                                   let uu____2301 =
                                     let uu____2304 =
                                       let uu____2307 =
                                         match env1 with
                                         | FStar_Pervasives_Native.Some e ->
                                             let uu____2309 =
                                               let uu____2310 =
                                                 let uu____2311 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____2311 in
                                               let uu____2312 =
                                                 let uu____2313 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____2313 ")" in
                                               Prims.strcat uu____2310
                                                 uu____2312 in
                                             Prims.strcat "(" uu____2309
                                         | FStar_Pervasives_Native.None  ->
                                             "" in
                                       let uu____2314 =
                                         let uu____2317 =
                                           let uu____2320 =
                                             let uu____2323 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____2324 =
                                               let uu____2327 =
                                                 let uu____2330 =
                                                   let uu____2333 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____2334 =
                                                     let uu____2337 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____2338 =
                                                       let uu____2341 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____2342 =
                                                         let uu____2345 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____2345] in
                                                       uu____2341 ::
                                                         uu____2342 in
                                                     uu____2337 :: uu____2338 in
                                                   uu____2333 :: uu____2334 in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____2330 in
                                               tag :: uu____2327 in
                                             uu____2323 :: uu____2324 in
                                           query_name :: uu____2320 in
                                         name :: uu____2317 in
                                       uu____2307 :: uu____2314 in
                                     let uu____2348 =
                                       let uu____2351 =
                                         let uu____2352 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____2352
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____2364 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____2364 "}"
                                         else
                                           (let uu____2366 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____2366 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____2370 -> "") in
                                       [uu____2351] in
                                     FStar_List.append uu____2304 uu____2348 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____2301
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____2391 =
                                     let uu____2392 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____2392 in
                                   if uu____2391
                                   then
                                     let hint_check_cb uu____2414 =
                                       match uu____2414 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____2455 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____2463 ->
                                                 "failed" in
                                           let uu____2472 =
                                             FStar_Options.hint_info () in
                                           if uu____2472
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____2476 =
                                         let uu____2483 =
                                           FStar_ST.read current_core in
                                         filter_assertions uu____2483 in
                                       let uu____2486 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____2476
                                         all_labels uu____2486
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____2489 =
                                         let uu____2490 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____2490 in
                                       if uu____2489
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____2497 =
                                             let uu____2498 =
                                               let uu____2501 =
                                                 let uu____2504 =
                                                   let uu____2505 =
                                                     let uu____2506 =
                                                       let uu____2509 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____2509] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____2506 in
                                                   FStar_Options.String
                                                     uu____2505 in
                                                 [uu____2504] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____2501 in
                                             FStar_Options.List uu____2498 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____2497);
                                          (let hint_refinement_cb uu____2529
                                             =
                                             match uu____2529 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____2569 =
                                                   FStar_Options.hint_info () in
                                                 if uu____2569
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____2582 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____2582))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info
                                                     FStar_Pervasives_Native.None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____2595 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              filter_facts_without_core
                                              all_labels uu____2595
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____2598 =
                                              FStar_ST.read refinement_ok in
                                            if uu____2598
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____2603 =
                                                     let uu____2606 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____2606] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____2603);
                                                  FStar_ST.write current_core
                                                    FStar_Pervasives_Native.None)
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
                                  (let uu____2623 =
                                     let uu____2624 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____2624 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____2623);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____2628 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____2628;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____2637 =
                                       let uu____2640 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____2640
                                       then
                                         let uu____2643 =
                                           let uu____2644 =
                                             FStar_Options.check_hints () in
                                           if uu____2644
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
                                         FStar_Pervasives_Native.Some
                                           uu____2643
                                       else hint_opt in
                                     record_hint uu____2637))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____2650 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____2650
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | FStar_Pervasives_Native.Some core
                                             ->
                                             ((let uu____2660 =
                                                 FStar_List.map
                                                   (fun x  ->
                                                      FStar_Util.print_string
                                                        (Prims.strcat " " x))
                                                   core in
                                               ());
                                              FStar_Util.print_string "\n")))
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope))) in
                       ((let uu____2668 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____2668
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____2675 =
                           let uu____2676 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____2676 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____2675)) in
                 let process_query q = check q in
                 let uu____2685 =
                   let uu____2692 = FStar_Options.admit_smt_queries () in
                   let uu____2693 = FStar_Options.admit_except () in
                   (uu____2692, uu____2693) in
                 (match uu____2685 with
                  | (true ,uu____2698) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      process_query query
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let cur_id =
                        let uu____2709 =
                          let uu____2710 =
                            let uu____2711 =
                              let uu____2712 =
                                FStar_Util.string_of_int query_index in
                              Prims.strcat uu____2712 ")" in
                            Prims.strcat ", " uu____2711 in
                          Prims.strcat query_name uu____2710 in
                        Prims.strcat "(" uu____2709 in
                      if cur_id = id then process_query query else ()))
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2733 =
           let uu____2734 =
             let uu____2735 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2735 in
           FStar_Util.format1 "Starting query at %s" uu____2734 in
         FStar_SMTEncoding_Encode.push uu____2733);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2737 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2737 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2771 =
               let uu____2772 =
                 let uu____2773 =
                   let uu____2774 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2774 in
                 FStar_Util.format1 "Ending query at %s" uu____2773 in
               FStar_SMTEncoding_Encode.pop uu____2772 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2775);
                        FStar_SMTEncoding_Term.freevars = uu____2776;
                        FStar_SMTEncoding_Term.rng = uu____2777;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2778;
                    FStar_SMTEncoding_Term.assumption_name = uu____2779;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2780;_}
                  -> pop1 ()
              | uu____2795 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2796 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2798 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____2809  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2810  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2811  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____2812  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____2813  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____2814  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2815  -> fun uu____2816  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2817  -> fun uu____2818  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2829  -> fun uu____2830  -> fun uu____2831  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____2836  -> fun uu____2837  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____2838  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2839  -> ())
  }
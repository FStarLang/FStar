open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels* FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___83_23 =
  match uu___83_23 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____32) -> FStar_Util.Inr r
type hint_stat =
  {
  hint: FStar_Util.hint option;
  replay_result: z3_replay_result;
  elapsed_time: Prims.int;
  source_location: FStar_Range.range;}
type hint_stats_t = hint_stat Prims.list
let recorded_hints: FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None
let replaying_hints: FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None
let hint_stats: hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____106 = FStar_Options.record_hints () in
   if uu____106 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____114 = FStar_Options.use_hints () in
   if uu____114
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____117 = FStar_Util.read_hints val_filename in
     match uu____117 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____122 = FStar_Options.hint_info () in
           if uu____122
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
         let uu____128 = FStar_Options.hint_info () in
         (if uu____128
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____135 = FStar_Options.record_hints () in
     if uu____135
     then
       let hints =
         let uu____137 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____137 in
       let hints_db =
         let uu____143 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____143; FStar_Util.hints = hints } in
       let hints_file_name = format_hints_file_name src_filename in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____147 = FStar_Options.hint_info () in
     if uu____147
     then
       let stats =
         let uu____150 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____150 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____160 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____161 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____160 uu____161
               | FStar_Util.Inr _error ->
                   let uu____163 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____164 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____163 uu____164))
     else ());
    FStar_ST.write recorded_hints None;
    FStar_ST.write replaying_hints None;
    FStar_ST.write hint_stats []
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f () in finalize_hints_db fname; result)
let next_hint: Prims.string -> Prims.int -> FStar_Util.hint option =
  fun qname  ->
    fun qindex  ->
      let uu____204 = FStar_ST.read replaying_hints in
      match uu____204 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_212  ->
               match uu___84_212 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____216 -> None)
      | uu____218 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___88_229 = h in
             {
               FStar_Util.hint_name = (uu___88_229.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___88_229.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___88_229.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___88_229.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___88_229.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____230 = FStar_ST.read recorded_hints in
    match uu____230 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____244 -> ()
let record_hint_stat:
  FStar_Util.hint option ->
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
          let uu____261 =
            let uu____263 = FStar_ST.read hint_stats in s :: uu____263 in
          FStar_ST.write hint_stats uu____261
let filter_using_facts_from:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____283 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____293 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____299 =
        FStar_List.fold_left
          (fun uu____308  ->
             fun d  ->
               match uu____308 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____329 =
                          matches_fact_ids include_assumption_names a in
                        if uu____329
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____343 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____299 with | (pruned_theory,uu____350) -> pruned_theory
let filter_assertions:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | None  ->
            let uu____371 = filter_using_facts_from e theory in
            (uu____371, false)
        | Some core1 ->
            let uu____377 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____387  ->
                     match uu____387 with
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
                          | uu____419 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____377 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____442 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____447 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___85_449  ->
                                         match uu___85_449 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____451 -> false)) in
                               FStar_All.pipe_right uu____447
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____442
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____454 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___86_458  ->
                               match uu___86_458 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____461 -> [])) in
                     FStar_All.pipe_right uu____454
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____464 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____464
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____474 = FStar_Util.string_of_int n_retained in
                     let uu____475 =
                       if n1 <> n_retained
                       then
                         let uu____480 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____480 missed
                       else "" in
                     let uu____488 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____474 uu____475 uu____488
                   else ());
                  (let uu____490 =
                     let uu____492 =
                       let uu____494 =
                         let uu____495 =
                           let uu____496 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____496 in
                         FStar_SMTEncoding_Term.Caption uu____495 in
                       [uu____494] in
                     FStar_List.append theory' uu____492 in
                   (uu____490, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____508 = filter_using_facts_from e x in (uu____508, false)
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
            (let uu____531 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____531 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_587 =
                   match uu___87_587 with
                   | ([],uu____594) -> ()
                   | errs ->
                       let uu____600 = FStar_ST.read minimum_workable_fuel in
                       (match uu____600 with
                        | Some uu____621 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____685 =
                   match uu____685 with
                   | (n1,i,rlimit) ->
                       let uu____694 =
                         let uu____696 =
                           let uu____697 =
                             let uu____698 = FStar_Util.string_of_int n1 in
                             let uu____699 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____698 uu____699 in
                           FStar_SMTEncoding_Term.Caption uu____697 in
                         let uu____700 =
                           let uu____702 =
                             let uu____703 =
                               let uu____707 =
                                 let uu____708 =
                                   let uu____711 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____713 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____711, uu____713) in
                                 FStar_SMTEncoding_Util.mkEq uu____708 in
                               (uu____707, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____703 in
                           let uu____715 =
                             let uu____717 =
                               let uu____718 =
                                 let uu____722 =
                                   let uu____723 =
                                     let uu____726 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____728 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____726, uu____728) in
                                   FStar_SMTEncoding_Util.mkEq uu____723 in
                                 (uu____722, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____718 in
                             [uu____717; p] in
                           uu____702 :: uu____715 in
                         uu____696 :: uu____700 in
                       let uu____730 =
                         let uu____732 =
                           let uu____734 =
                             let uu____736 =
                               let uu____737 =
                                 let uu____740 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____740) in
                               FStar_SMTEncoding_Term.SetOption uu____737 in
                             [uu____736] in
                           let uu____741 =
                             let uu____743 =
                               let uu____745 =
                                 let uu____747 =
                                   FStar_Options.record_hints () in
                                 if uu____747
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____750 =
                                 let uu____752 =
                                   let uu____754 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____754
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____757 =
                                   let uu____759 =
                                     let uu____761 =
                                       FStar_Options.check_hints () in
                                     if uu____761
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____759 suffix in
                                 FStar_List.append uu____752 uu____757 in
                               FStar_List.append uu____745 uu____750 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____743 in
                           FStar_List.append uu____734 uu____741 in
                         FStar_List.append label_assumptions uu____732 in
                       FStar_List.append uu____694 uu____730 in
                 let check p =
                   let rlimit =
                     let uu____769 = FStar_Options.z3_rlimit_factor () in
                     let uu____770 =
                       let uu____771 = FStar_Options.z3_rlimit () in
                       uu____771 * (Prims.parse_int "544656") in
                     uu____769 * uu____770 in
                   let default_initial_config =
                     let uu____776 = FStar_Options.initial_fuel () in
                     let uu____777 = FStar_Options.initial_ifuel () in
                     (uu____776, uu____777, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____780 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____802 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____802 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____780 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____853 =
                           let uu____859 =
                             let uu____865 =
                               let uu____870 =
                                 let uu____871 = FStar_Options.max_ifuel () in
                                 let uu____872 =
                                   FStar_Options.initial_ifuel () in
                                 uu____871 > uu____872 in
                               if uu____870
                               then
                                 let uu____877 =
                                   let uu____881 =
                                     FStar_Options.initial_fuel () in
                                   let uu____882 = FStar_Options.max_ifuel () in
                                   (uu____881, uu____882, rlimit) in
                                 [uu____877]
                               else [] in
                             let uu____893 =
                               let uu____899 =
                                 let uu____904 =
                                   let uu____905 =
                                     let uu____906 =
                                       FStar_Options.max_fuel () in
                                     uu____906 / (Prims.parse_int "2") in
                                   let uu____913 =
                                     FStar_Options.initial_fuel () in
                                   uu____905 > uu____913 in
                                 if uu____904
                                 then
                                   let uu____918 =
                                     let uu____922 =
                                       let uu____923 =
                                         FStar_Options.max_fuel () in
                                       uu____923 / (Prims.parse_int "2") in
                                     let uu____930 =
                                       FStar_Options.max_ifuel () in
                                     (uu____922, uu____930, rlimit) in
                                   [uu____918]
                                 else [] in
                               let uu____941 =
                                 let uu____947 =
                                   let uu____952 =
                                     (let uu____953 =
                                        FStar_Options.max_fuel () in
                                      let uu____954 =
                                        FStar_Options.initial_fuel () in
                                      uu____953 > uu____954) &&
                                       (let uu____955 =
                                          FStar_Options.max_ifuel () in
                                        let uu____956 =
                                          FStar_Options.initial_ifuel () in
                                        uu____955 >= uu____956) in
                                   if uu____952
                                   then
                                     let uu____961 =
                                       let uu____965 =
                                         FStar_Options.max_fuel () in
                                       let uu____966 =
                                         FStar_Options.max_ifuel () in
                                       (uu____965, uu____966, rlimit) in
                                     [uu____961]
                                   else [] in
                                 let uu____977 =
                                   let uu____983 =
                                     let uu____988 =
                                       let uu____989 =
                                         FStar_Options.min_fuel () in
                                       let uu____990 =
                                         FStar_Options.initial_fuel () in
                                       uu____989 < uu____990 in
                                     if uu____988
                                     then
                                       let uu____995 =
                                         let uu____999 =
                                           FStar_Options.min_fuel () in
                                         (uu____999, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____995]
                                     else [] in
                                   [uu____983] in
                                 uu____947 :: uu____977 in
                               uu____899 :: uu____941 in
                             uu____865 :: uu____893 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____859 in
                         FStar_List.flatten uu____853 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1063 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1064 = FStar_Options.n_cores () in
                                uu____1064 = (Prims.parse_int "1")) in
                           if uu____1063
                           then
                             let uu____1065 =
                               let uu____1074 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1074 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1139 =
                                     let uu____1143 =
                                       FStar_Options.min_fuel () in
                                     (uu____1143, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1139, errs) in
                             match uu____1065 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1173 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1173 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1179 = FStar_ST.read res in
                                    FStar_Option.get uu____1179) in
                                 let uu____1184 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1184, FStar_SMTEncoding_Z3.Default)
                           else
                             (match errs with
                              | ([],FStar_SMTEncoding_Z3.Timeout ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Timeout: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | ([],FStar_SMTEncoding_Z3.Default ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | (uu____1224,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1243 -> errs) in
                         record_hint None;
                         (let uu____1246 = FStar_Options.print_fuels () in
                          if uu____1246
                          then
                            let uu____1247 =
                              let uu____1248 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1248 in
                            let uu____1249 =
                              let uu____1250 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1250
                                FStar_Util.string_of_int in
                            let uu____1251 =
                              let uu____1252 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1252
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1247 uu____1249 uu____1251
                          else ());
                         (let uu____1254 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1266  ->
                                    match uu____1266 with
                                    | (uu____1272,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1254) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1288),uu____1289) -> result
                         | (uu____1294,FStar_Util.Inl uu____1295) -> result
                         | (uu____1302,FStar_Util.Inr uu____1303) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1370) -> report1 p1 errs
                          | (uu____1378,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1389) ->
                              let uu____1404 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1404 (Some scope)
                                (fun uu____1406  ->
                                   match uu____1406 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1418 =
                                         let uu____1422 =
                                           use_errors errs result in
                                         (uu____1422, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1418))
                       and cb used_hint uu____1424 p1 alt scope uu____1428 =
                         match (uu____1424, uu____1428) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1459 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1459))
                              else ();
                              (let uu____1462 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1462
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1481 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1481
                                 then
                                   let uu____1482 =
                                     let uu____1484 =
                                       let uu____1486 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1488 =
                                               let uu____1489 =
                                                 let uu____1490 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1490 in
                                               let uu____1491 =
                                                 let uu____1492 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1492 ")" in
                                               Prims.strcat uu____1489
                                                 uu____1491 in
                                             Prims.strcat "(" uu____1488
                                         | None  -> "" in
                                       let uu____1493 =
                                         let uu____1495 =
                                           let uu____1497 =
                                             let uu____1499 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1500 =
                                               let uu____1502 =
                                                 let uu____1504 =
                                                   let uu____1506 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1507 =
                                                     let uu____1509 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1510 =
                                                       let uu____1512 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1513 =
                                                         let uu____1515 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1515] in
                                                       uu____1512 ::
                                                         uu____1513 in
                                                     uu____1509 :: uu____1510 in
                                                   uu____1506 :: uu____1507 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1504 in
                                               tag :: uu____1502 in
                                             uu____1499 :: uu____1500 in
                                           query_name :: uu____1497 in
                                         name :: uu____1495 in
                                       uu____1486 :: uu____1493 in
                                     let uu____1518 =
                                       let uu____1520 =
                                         let uu____1521 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1521
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1533 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1533 "}"
                                         else
                                           (let uu____1541 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1541 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1544 -> "") in
                                       [uu____1520] in
                                     FStar_List.append uu____1484 uu____1518 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1482
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1564 =
                                     let uu____1565 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1565 in
                                   if uu____1564
                                   then
                                     let hint_check_cb uu____1579 =
                                       match uu____1579 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1602 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1608 ->
                                                 "failed" in
                                           let uu____1613 =
                                             FStar_Options.hint_info () in
                                           if uu____1613
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1617 =
                                         let uu____1622 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1622 in
                                       let uu____1625 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1617
                                         all_labels uu____1625 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1627 =
                                         let uu____1628 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1628 in
                                       if uu____1627
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1635 =
                                             let uu____1636 =
                                               let uu____1638 =
                                                 let uu____1640 =
                                                   let uu____1641 =
                                                     let uu____1642 =
                                                       let uu____1644 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1644] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1642 in
                                                   FStar_Options.String
                                                     uu____1641 in
                                                 [uu____1640] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1638 in
                                             FStar_Options.List uu____1636 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1635);
                                          (let hint_refinement_cb uu____1656
                                             =
                                             match uu____1656 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1678 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1678
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1689 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1689))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1698 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1698
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1700 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1700
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1705 =
                                                     let uu____1707 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1707] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1705);
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
                                  (let uu____1722 =
                                     let uu____1723 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1723 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1722);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1726 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1726;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1733 =
                                       let uu____1735 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1735
                                       then
                                         let uu____1737 =
                                           let uu____1738 =
                                             FStar_Options.check_hints () in
                                           if uu____1738
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
                                         Some uu____1737
                                       else hint_opt in
                                     record_hint uu____1733))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1744 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1744
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1751 =
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
                       ((let uu____1757 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1757
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1762 =
                           let uu____1763 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1763 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1762)) in
                 let process_query q = check q in
                 let uu____1771 = FStar_Options.admit_smt_queries () in
                 if uu____1771 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1790 =
           let uu____1791 =
             let uu____1792 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1792 in
           FStar_Util.format1 "Starting query at %s" uu____1791 in
         FStar_SMTEncoding_Encode.push uu____1790);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1794 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1794 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1815 =
               let uu____1816 =
                 let uu____1817 =
                   let uu____1818 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1818 in
                 FStar_Util.format1 "Ending query at %s" uu____1817 in
               FStar_SMTEncoding_Encode.pop uu____1816 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1819);
                        FStar_SMTEncoding_Term.freevars = uu____1820;
                        FStar_SMTEncoding_Term.rng = uu____1821;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1822;
                    FStar_SMTEncoding_Term.assumption_name = uu____1823;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1824;_}
                  -> pop1 ()
              | uu____1832 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1833 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1835 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1842  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1843  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1844  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1845  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1846  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1847  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1848  -> fun uu____1849  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1850  -> fun uu____1851  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1858  -> fun uu____1859  -> fun uu____1860  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1864  -> fun uu____1865  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1866  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1867  -> ())
  }
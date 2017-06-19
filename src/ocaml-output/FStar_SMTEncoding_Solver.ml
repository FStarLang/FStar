open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels* FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___83_27 =
  match uu___83_27 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____36) -> FStar_Util.Inr r
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
  (let uu____118 = FStar_Options.record_hints () in
   if uu____118 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____126 = FStar_Options.use_hints () in
   if uu____126
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____129 = FStar_Util.read_hints val_filename in
     match uu____129 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____134 = FStar_Options.hint_info () in
           if uu____134
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
         let uu____140 = FStar_Options.hint_info () in
         (if uu____140
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____148 = FStar_Options.record_hints () in
     if uu____148
     then
       let hints =
         let uu____150 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____150 in
       let hints_db =
         let uu____156 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____156; FStar_Util.hints = hints } in
       let hints_file_name = format_hints_file_name src_filename in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____160 = FStar_Options.hint_info () in
     if uu____160
     then
       let stats =
         let uu____163 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____163 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____173 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____174 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____173 uu____174
               | FStar_Util.Inr _error ->
                   let uu____176 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____177 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____176 uu____177))
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
      let uu____222 = FStar_ST.read replaying_hints in
      match uu____222 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_230  ->
               match uu___84_230 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____234 -> None)
      | uu____236 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___88_248 = h in
             {
               FStar_Util.hint_name = (uu___88_248.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___88_248.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___88_248.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___88_248.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___88_248.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____249 = FStar_ST.read recorded_hints in
    match uu____249 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____263 -> ()
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
          let uu____284 =
            let uu____286 = FStar_ST.read hint_stats in s :: uu____286 in
          FStar_ST.write hint_stats uu____284
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
        | uu____308 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____318 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____324 =
        FStar_List.fold_left
          (fun uu____333  ->
             fun d  ->
               match uu____333 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____354 =
                          matches_fact_ids include_assumption_names a in
                        if uu____354
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____368 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____324 with | (pruned_theory,uu____375) -> pruned_theory
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
            let uu____399 = filter_using_facts_from e theory in
            (uu____399, false)
        | Some core1 ->
            let uu____405 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____415  ->
                     match uu____415 with
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
                          | uu____447 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____405 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____470 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____475 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___85_477  ->
                                         match uu___85_477 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____479 -> false)) in
                               FStar_All.pipe_right uu____475
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____470
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____482 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___86_486  ->
                               match uu___86_486 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____489 -> [])) in
                     FStar_All.pipe_right uu____482
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____492 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____492
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____502 = FStar_Util.string_of_int n_retained in
                     let uu____503 =
                       if n1 <> n_retained
                       then
                         let uu____508 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____508 missed
                       else "" in
                     let uu____516 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____502 uu____503 uu____516
                   else ());
                  (let uu____518 =
                     let uu____520 =
                       let uu____522 =
                         let uu____523 =
                           let uu____524 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____524 in
                         FStar_SMTEncoding_Term.Caption uu____523 in
                       [uu____522] in
                     FStar_List.append theory' uu____520 in
                   (uu____518, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____538 = filter_using_facts_from e x in (uu____538, false)
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
            (let uu____566 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____566 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_622 =
                   match uu___87_622 with
                   | ([],uu____629) -> ()
                   | errs ->
                       let uu____635 = FStar_ST.read minimum_workable_fuel in
                       (match uu____635 with
                        | Some uu____656 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____720 =
                   match uu____720 with
                   | (n1,i,rlimit) ->
                       let uu____729 =
                         let uu____731 =
                           let uu____732 =
                             let uu____733 = FStar_Util.string_of_int n1 in
                             let uu____734 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____733 uu____734 in
                           FStar_SMTEncoding_Term.Caption uu____732 in
                         let uu____735 =
                           let uu____737 =
                             let uu____738 =
                               let uu____742 =
                                 let uu____743 =
                                   let uu____746 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____748 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____746, uu____748) in
                                 FStar_SMTEncoding_Util.mkEq uu____743 in
                               (uu____742, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____738 in
                           let uu____750 =
                             let uu____752 =
                               let uu____753 =
                                 let uu____757 =
                                   let uu____758 =
                                     let uu____761 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____763 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____761, uu____763) in
                                   FStar_SMTEncoding_Util.mkEq uu____758 in
                                 (uu____757, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____753 in
                             [uu____752; p] in
                           uu____737 :: uu____750 in
                         uu____731 :: uu____735 in
                       let uu____765 =
                         let uu____767 =
                           let uu____769 =
                             let uu____771 =
                               let uu____772 =
                                 let uu____775 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____775) in
                               FStar_SMTEncoding_Term.SetOption uu____772 in
                             [uu____771] in
                           let uu____776 =
                             let uu____778 =
                               let uu____780 =
                                 let uu____782 =
                                   FStar_Options.record_hints () in
                                 if uu____782
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____785 =
                                 let uu____787 =
                                   let uu____789 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____789
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____792 =
                                   let uu____794 =
                                     let uu____796 =
                                       FStar_Options.check_hints () in
                                     if uu____796
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____794 suffix in
                                 FStar_List.append uu____787 uu____792 in
                               FStar_List.append uu____780 uu____785 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____778 in
                           FStar_List.append uu____769 uu____776 in
                         FStar_List.append label_assumptions uu____767 in
                       FStar_List.append uu____729 uu____765 in
                 let check p =
                   let rlimit =
                     let uu____804 = FStar_Options.z3_rlimit_factor () in
                     let uu____805 =
                       let uu____806 = FStar_Options.z3_rlimit () in
                       uu____806 * (Prims.parse_int "544656") in
                     uu____804 * uu____805 in
                   let default_initial_config =
                     let uu____811 = FStar_Options.initial_fuel () in
                     let uu____812 = FStar_Options.initial_ifuel () in
                     (uu____811, uu____812, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____815 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____837 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____837 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____815 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____888 =
                           let uu____894 =
                             let uu____900 =
                               let uu____905 =
                                 let uu____906 = FStar_Options.max_ifuel () in
                                 let uu____907 =
                                   FStar_Options.initial_ifuel () in
                                 uu____906 > uu____907 in
                               if uu____905
                               then
                                 let uu____912 =
                                   let uu____916 =
                                     FStar_Options.initial_fuel () in
                                   let uu____917 = FStar_Options.max_ifuel () in
                                   (uu____916, uu____917, rlimit) in
                                 [uu____912]
                               else [] in
                             let uu____928 =
                               let uu____934 =
                                 let uu____939 =
                                   let uu____940 =
                                     let uu____941 =
                                       FStar_Options.max_fuel () in
                                     uu____941 / (Prims.parse_int "2") in
                                   let uu____948 =
                                     FStar_Options.initial_fuel () in
                                   uu____940 > uu____948 in
                                 if uu____939
                                 then
                                   let uu____953 =
                                     let uu____957 =
                                       let uu____958 =
                                         FStar_Options.max_fuel () in
                                       uu____958 / (Prims.parse_int "2") in
                                     let uu____965 =
                                       FStar_Options.max_ifuel () in
                                     (uu____957, uu____965, rlimit) in
                                   [uu____953]
                                 else [] in
                               let uu____976 =
                                 let uu____982 =
                                   let uu____987 =
                                     (let uu____988 =
                                        FStar_Options.max_fuel () in
                                      let uu____989 =
                                        FStar_Options.initial_fuel () in
                                      uu____988 > uu____989) &&
                                       (let uu____990 =
                                          FStar_Options.max_ifuel () in
                                        let uu____991 =
                                          FStar_Options.initial_ifuel () in
                                        uu____990 >= uu____991) in
                                   if uu____987
                                   then
                                     let uu____996 =
                                       let uu____1000 =
                                         FStar_Options.max_fuel () in
                                       let uu____1001 =
                                         FStar_Options.max_ifuel () in
                                       (uu____1000, uu____1001, rlimit) in
                                     [uu____996]
                                   else [] in
                                 let uu____1012 =
                                   let uu____1018 =
                                     let uu____1023 =
                                       let uu____1024 =
                                         FStar_Options.min_fuel () in
                                       let uu____1025 =
                                         FStar_Options.initial_fuel () in
                                       uu____1024 < uu____1025 in
                                     if uu____1023
                                     then
                                       let uu____1030 =
                                         let uu____1034 =
                                           FStar_Options.min_fuel () in
                                         (uu____1034, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1030]
                                     else [] in
                                   [uu____1018] in
                                 uu____982 :: uu____1012 in
                               uu____934 :: uu____976 in
                             uu____900 :: uu____928 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____894 in
                         FStar_List.flatten uu____888 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1098 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1099 = FStar_Options.n_cores () in
                                uu____1099 = (Prims.parse_int "1")) in
                           if uu____1098
                           then
                             let uu____1100 =
                               let uu____1109 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1109 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1174 =
                                     let uu____1178 =
                                       FStar_Options.min_fuel () in
                                     (uu____1178, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1174, errs) in
                             match uu____1100 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1208 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1208 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1214 = FStar_ST.read res in
                                    FStar_Option.get uu____1214) in
                                 let uu____1219 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1219, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1259,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1278 -> errs) in
                         record_hint None;
                         (let uu____1281 = FStar_Options.print_fuels () in
                          if uu____1281
                          then
                            let uu____1282 =
                              let uu____1283 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1283 in
                            let uu____1284 =
                              let uu____1285 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1285
                                FStar_Util.string_of_int in
                            let uu____1286 =
                              let uu____1287 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1287
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1282 uu____1284 uu____1286
                          else ());
                         (let uu____1289 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1301  ->
                                    match uu____1301 with
                                    | (uu____1307,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1289) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1323),uu____1324) -> result
                         | (uu____1329,FStar_Util.Inl uu____1330) -> result
                         | (uu____1337,FStar_Util.Inr uu____1338) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1405) -> report1 p1 errs
                          | (uu____1413,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1424) ->
                              let uu____1439 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1439 (Some scope)
                                (fun uu____1441  ->
                                   match uu____1441 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1453 =
                                         let uu____1457 =
                                           use_errors errs result in
                                         (uu____1457, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1453))
                       and cb used_hint uu____1459 p1 alt scope uu____1463 =
                         match (uu____1459, uu____1463) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1494 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1494))
                              else ();
                              (let uu____1497 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1497
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1516 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1516
                                 then
                                   let uu____1517 =
                                     let uu____1519 =
                                       let uu____1521 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1523 =
                                               let uu____1524 =
                                                 let uu____1525 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1525 in
                                               let uu____1526 =
                                                 let uu____1527 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1527 ")" in
                                               Prims.strcat uu____1524
                                                 uu____1526 in
                                             Prims.strcat "(" uu____1523
                                         | None  -> "" in
                                       let uu____1528 =
                                         let uu____1530 =
                                           let uu____1532 =
                                             let uu____1534 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1535 =
                                               let uu____1537 =
                                                 let uu____1539 =
                                                   let uu____1541 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1542 =
                                                     let uu____1544 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1545 =
                                                       let uu____1547 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1548 =
                                                         let uu____1550 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1550] in
                                                       uu____1547 ::
                                                         uu____1548 in
                                                     uu____1544 :: uu____1545 in
                                                   uu____1541 :: uu____1542 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1539 in
                                               tag :: uu____1537 in
                                             uu____1534 :: uu____1535 in
                                           query_name :: uu____1532 in
                                         name :: uu____1530 in
                                       uu____1521 :: uu____1528 in
                                     let uu____1553 =
                                       let uu____1555 =
                                         let uu____1556 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1556
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1568 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1568 "}"
                                         else
                                           (let uu____1576 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1576 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1579 -> "") in
                                       [uu____1555] in
                                     FStar_List.append uu____1519 uu____1553 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1517
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1599 =
                                     let uu____1600 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1600 in
                                   if uu____1599
                                   then
                                     let hint_check_cb uu____1614 =
                                       match uu____1614 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1637 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1643 ->
                                                 "failed" in
                                           let uu____1648 =
                                             FStar_Options.hint_info () in
                                           if uu____1648
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1652 =
                                         let uu____1657 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1657 in
                                       let uu____1660 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1652
                                         all_labels uu____1660 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1662 =
                                         let uu____1663 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1663 in
                                       if uu____1662
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1670 =
                                             let uu____1671 =
                                               let uu____1673 =
                                                 let uu____1675 =
                                                   let uu____1676 =
                                                     let uu____1677 =
                                                       let uu____1679 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1679] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1677 in
                                                   FStar_Options.String
                                                     uu____1676 in
                                                 [uu____1675] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1673 in
                                             FStar_Options.List uu____1671 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1670);
                                          (let hint_refinement_cb uu____1691
                                             =
                                             match uu____1691 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1713 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1713
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1724 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1724))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1733 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1733
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1735 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1735
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1740 =
                                                     let uu____1742 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1742] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1740);
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
                                  (let uu____1757 =
                                     let uu____1758 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1758 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1757);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1761 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1761;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1768 =
                                       let uu____1770 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1770
                                       then
                                         let uu____1772 =
                                           let uu____1773 =
                                             FStar_Options.check_hints () in
                                           if uu____1773
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
                                         Some uu____1772
                                       else hint_opt in
                                     record_hint uu____1768))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1779 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1779
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1786 =
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
                       ((let uu____1792 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1792
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1797 =
                           let uu____1798 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1798 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1797)) in
                 let process_query q = check q in
                 let uu____1806 = FStar_Options.admit_smt_queries () in
                 if uu____1806 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1828 =
           let uu____1829 =
             let uu____1830 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1830 in
           FStar_Util.format1 "Starting query at %s" uu____1829 in
         FStar_SMTEncoding_Encode.push uu____1828);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1832 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1832 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1853 =
               let uu____1854 =
                 let uu____1855 =
                   let uu____1856 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1856 in
                 FStar_Util.format1 "Ending query at %s" uu____1855 in
               FStar_SMTEncoding_Encode.pop uu____1854 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1857);
                        FStar_SMTEncoding_Term.freevars = uu____1858;
                        FStar_SMTEncoding_Term.rng = uu____1859;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1860;
                    FStar_SMTEncoding_Term.assumption_name = uu____1861;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1862;_}
                  -> pop1 ()
              | uu____1870 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1871 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1873 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1880  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1881  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1882  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1883  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1884  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1885  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1886  -> fun uu____1887  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1888  -> fun uu____1889  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1896  -> fun uu____1897  -> fun uu____1898  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1902  -> fun uu____1903  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1904  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1905  -> ())
  }
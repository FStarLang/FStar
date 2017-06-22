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
            (let uu___89_229 = h in
             {
               FStar_Util.hint_name = (uu___89_229.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_229.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_229.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_229.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_229.FStar_Util.unsat_core);
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
  FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t =
  fun theory  ->
    let uu____274 = FStar_Options.using_facts_from () in
    match uu____274 with
    | None  -> theory
    | Some namespace_strings ->
        let fact_id_in_namespace ns uu___85_287 =
          match uu___85_287 with
          | FStar_SMTEncoding_Term.Namespace lid ->
              FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns
          | FStar_SMTEncoding_Term.Name _lid -> false
          | FStar_SMTEncoding_Term.Tag _s -> false in
        let matches_fact_ids include_assumption_names a =
          match a.FStar_SMTEncoding_Term.assumption_fact_ids with
          | [] -> true
          | uu____300 ->
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
        let uu____308 =
          FStar_List.fold_left
            (fun uu____317  ->
               fun d  ->
                 match uu____317 with
                 | (out,include_assumption_names) ->
                     (match d with
                      | FStar_SMTEncoding_Term.Assume a ->
                          let uu____338 =
                            matches_fact_ids include_assumption_names a in
                          if uu____338
                          then ((d :: out), include_assumption_names)
                          else (out, include_assumption_names)
                      | FStar_SMTEncoding_Term.RetainAssumptions names ->
                          ((d :: out),
                            (FStar_List.append names include_assumption_names))
                      | uu____352 -> ((d :: out), include_assumption_names)))
            ([], []) theory_rev in
        (match uu____308 with | (pruned_theory,uu____358) -> pruned_theory)
let filter_assertions:
  FStar_SMTEncoding_Z3.unsat_core ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  =
  fun core  ->
    fun theory  ->
      match core with
      | None  ->
          let uu____374 = filter_using_facts_from theory in
          (uu____374, false)
      | Some core1 ->
          let uu____378 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____388  ->
                   match uu____388 with
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
                        | uu____420 -> ((d :: theory1), n_retained, n_pruned)))
              theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
          (match uu____378 with
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
                                    (fun uu___86_449  ->
                                       match uu___86_449 with
                                       | FStar_SMTEncoding_Term.Assume a ->
                                           nm =
                                             a.FStar_SMTEncoding_Term.assumption_name
                                       | uu____451 -> false)) in
                             FStar_All.pipe_right uu____447 Prims.op_Negation)) in
                   FStar_All.pipe_right uu____442 (FStar_String.concat ", ") in
                 let included =
                   let uu____454 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___87_458  ->
                             match uu___87_458 with
                             | FStar_SMTEncoding_Term.Assume a ->
                                 [a.FStar_SMTEncoding_Term.assumption_name]
                             | uu____461 -> [])) in
                   FStar_All.pipe_right uu____454 (FStar_String.concat ", ") in
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
                   let uu____471 = FStar_Util.string_of_int n_retained in
                   let uu____472 =
                     if n1 <> n_retained
                     then
                       let uu____475 = FStar_Util.string_of_int n1 in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____475 missed
                     else "" in
                   let uu____480 = FStar_Util.string_of_int n_pruned in
                   FStar_Util.print3
                     "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____471 uu____472 uu____480
                 else ());
                (let uu____482 =
                   let uu____484 =
                     let uu____486 =
                       let uu____487 =
                         let uu____488 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____488 in
                       FStar_SMTEncoding_Term.Caption uu____487 in
                     [uu____486] in
                   FStar_List.append theory' uu____484 in
                 (uu____482, true))))
let filter_facts_without_core:
  FStar_SMTEncoding_Term.decls_t ->
    (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  = fun x  -> let uu____496 = filter_using_facts_from x in (uu____496, false)
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
            (let uu____517 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____517 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___88_573 =
                   match uu___88_573 with
                   | ([],uu____580) -> ()
                   | errs ->
                       let uu____586 = FStar_ST.read minimum_workable_fuel in
                       (match uu____586 with
                        | Some uu____607 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____671 =
                   match uu____671 with
                   | (n1,i,rlimit) ->
                       let uu____680 =
                         let uu____682 =
                           let uu____683 =
                             let uu____684 = FStar_Util.string_of_int n1 in
                             let uu____685 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____684 uu____685 in
                           FStar_SMTEncoding_Term.Caption uu____683 in
                         let uu____686 =
                           let uu____688 =
                             let uu____689 =
                               let uu____693 =
                                 let uu____694 =
                                   let uu____697 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____699 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____697, uu____699) in
                                 FStar_SMTEncoding_Util.mkEq uu____694 in
                               (uu____693, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____689 in
                           let uu____701 =
                             let uu____703 =
                               let uu____704 =
                                 let uu____708 =
                                   let uu____709 =
                                     let uu____712 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____714 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____712, uu____714) in
                                   FStar_SMTEncoding_Util.mkEq uu____709 in
                                 (uu____708, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____704 in
                             [uu____703; p] in
                           uu____688 :: uu____701 in
                         uu____682 :: uu____686 in
                       let uu____716 =
                         let uu____718 =
                           let uu____720 =
                             let uu____722 =
                               let uu____723 =
                                 let uu____726 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____726) in
                               FStar_SMTEncoding_Term.SetOption uu____723 in
                             [uu____722] in
                           let uu____727 =
                             let uu____729 =
                               let uu____731 =
                                 let uu____733 =
                                   FStar_Options.record_hints () in
                                 if uu____733
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____736 =
                                 let uu____738 =
                                   let uu____740 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____740
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____743 =
                                   let uu____745 =
                                     let uu____747 =
                                       FStar_Options.check_hints () in
                                     if uu____747
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____745 suffix in
                                 FStar_List.append uu____738 uu____743 in
                               FStar_List.append uu____731 uu____736 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____729 in
                           FStar_List.append uu____720 uu____727 in
                         FStar_List.append label_assumptions uu____718 in
                       FStar_List.append uu____680 uu____716 in
                 let check p =
                   let rlimit =
                     let uu____755 = FStar_Options.z3_rlimit_factor () in
                     let uu____756 =
                       let uu____757 = FStar_Options.z3_rlimit () in
                       uu____757 * (Prims.parse_int "544656") in
                     uu____755 * uu____756 in
                   let default_initial_config =
                     let uu____762 = FStar_Options.initial_fuel () in
                     let uu____763 = FStar_Options.initial_ifuel () in
                     (uu____762, uu____763, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____766 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____788 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____788 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____766 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____839 =
                           let uu____845 =
                             let uu____851 =
                               let uu____856 =
                                 let uu____857 = FStar_Options.max_ifuel () in
                                 let uu____858 =
                                   FStar_Options.initial_ifuel () in
                                 uu____857 > uu____858 in
                               if uu____856
                               then
                                 let uu____863 =
                                   let uu____867 =
                                     FStar_Options.initial_fuel () in
                                   let uu____868 = FStar_Options.max_ifuel () in
                                   (uu____867, uu____868, rlimit) in
                                 [uu____863]
                               else [] in
                             let uu____879 =
                               let uu____885 =
                                 let uu____890 =
                                   let uu____891 =
                                     let uu____892 =
                                       FStar_Options.max_fuel () in
                                     uu____892 / (Prims.parse_int "2") in
                                   let uu____896 =
                                     FStar_Options.initial_fuel () in
                                   uu____891 > uu____896 in
                                 if uu____890
                                 then
                                   let uu____901 =
                                     let uu____905 =
                                       let uu____906 =
                                         FStar_Options.max_fuel () in
                                       uu____906 / (Prims.parse_int "2") in
                                     let uu____910 =
                                       FStar_Options.max_ifuel () in
                                     (uu____905, uu____910, rlimit) in
                                   [uu____901]
                                 else [] in
                               let uu____921 =
                                 let uu____927 =
                                   let uu____932 =
                                     (let uu____933 =
                                        FStar_Options.max_fuel () in
                                      let uu____934 =
                                        FStar_Options.initial_fuel () in
                                      uu____933 > uu____934) &&
                                       (let uu____935 =
                                          FStar_Options.max_ifuel () in
                                        let uu____936 =
                                          FStar_Options.initial_ifuel () in
                                        uu____935 >= uu____936) in
                                   if uu____932
                                   then
                                     let uu____941 =
                                       let uu____945 =
                                         FStar_Options.max_fuel () in
                                       let uu____946 =
                                         FStar_Options.max_ifuel () in
                                       (uu____945, uu____946, rlimit) in
                                     [uu____941]
                                   else [] in
                                 let uu____957 =
                                   let uu____963 =
                                     let uu____968 =
                                       let uu____969 =
                                         FStar_Options.min_fuel () in
                                       let uu____970 =
                                         FStar_Options.initial_fuel () in
                                       uu____969 < uu____970 in
                                     if uu____968
                                     then
                                       let uu____975 =
                                         let uu____979 =
                                           FStar_Options.min_fuel () in
                                         (uu____979, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____975]
                                     else [] in
                                   [uu____963] in
                                 uu____927 :: uu____957 in
                               uu____885 :: uu____921 in
                             uu____851 :: uu____879 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____845 in
                         FStar_List.flatten uu____839 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1043 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1044 = FStar_Options.n_cores () in
                                uu____1044 = (Prims.parse_int "1")) in
                           if uu____1043
                           then
                             let uu____1045 =
                               let uu____1054 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1054 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1119 =
                                     let uu____1123 =
                                       FStar_Options.min_fuel () in
                                     (uu____1123, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1119, errs) in
                             match uu____1045 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1153 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      filter_facts_without_core all_labels
                                      uu____1153 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1159 = FStar_ST.read res in
                                    FStar_Option.get uu____1159) in
                                 let uu____1164 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1164, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1204,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1223 -> errs) in
                         record_hint None;
                         (let uu____1226 = FStar_Options.print_fuels () in
                          if uu____1226
                          then
                            let uu____1227 =
                              let uu____1228 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1228 in
                            let uu____1229 =
                              let uu____1230 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1230
                                FStar_Util.string_of_int in
                            let uu____1231 =
                              let uu____1232 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1232
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1227 uu____1229 uu____1231
                          else ());
                         (let uu____1234 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1246  ->
                                    match uu____1246 with
                                    | (uu____1252,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1234) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1268),uu____1269) -> result
                         | (uu____1274,FStar_Util.Inl uu____1275) -> result
                         | (uu____1282,FStar_Util.Inr uu____1283) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1350) -> report1 p1 errs
                          | (uu____1358,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1369) ->
                              let uu____1384 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                filter_facts_without_core all_labels
                                uu____1384 (Some scope)
                                (fun uu____1386  ->
                                   match uu____1386 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1398 =
                                         let uu____1402 =
                                           use_errors errs result in
                                         (uu____1402, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1398))
                       and cb used_hint uu____1404 p1 alt scope uu____1408 =
                         match (uu____1404, uu____1408) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1439 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1439))
                              else ();
                              (let uu____1442 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1442
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1461 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1461
                                 then
                                   let uu____1462 =
                                     let uu____1464 =
                                       let uu____1466 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1468 =
                                               let uu____1469 =
                                                 let uu____1470 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1470 in
                                               let uu____1471 =
                                                 let uu____1472 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1472 ")" in
                                               Prims.strcat uu____1469
                                                 uu____1471 in
                                             Prims.strcat "(" uu____1468
                                         | None  -> "" in
                                       let uu____1473 =
                                         let uu____1475 =
                                           let uu____1477 =
                                             let uu____1479 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1480 =
                                               let uu____1482 =
                                                 let uu____1484 =
                                                   let uu____1486 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1487 =
                                                     let uu____1489 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1490 =
                                                       let uu____1492 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1493 =
                                                         let uu____1495 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1495] in
                                                       uu____1492 ::
                                                         uu____1493 in
                                                     uu____1489 :: uu____1490 in
                                                   uu____1486 :: uu____1487 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1484 in
                                               tag :: uu____1482 in
                                             uu____1479 :: uu____1480 in
                                           query_name :: uu____1477 in
                                         name :: uu____1475 in
                                       uu____1466 :: uu____1473 in
                                     let uu____1498 =
                                       let uu____1500 =
                                         let uu____1501 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1501
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1513 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1513 "}"
                                         else
                                           (let uu____1518 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1518 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1521 -> "") in
                                       [uu____1500] in
                                     FStar_List.append uu____1464 uu____1498 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1462
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1541 =
                                     let uu____1542 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1542 in
                                   if uu____1541
                                   then
                                     let hint_check_cb uu____1556 =
                                       match uu____1556 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1579 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1585 ->
                                                 "failed" in
                                           let uu____1590 =
                                             FStar_Options.hint_info () in
                                           if uu____1590
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1594 =
                                         let uu____1599 =
                                           FStar_ST.read current_core in
                                         filter_assertions uu____1599 in
                                       let uu____1602 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1594
                                         all_labels uu____1602 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1604 =
                                         let uu____1605 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1605 in
                                       if uu____1604
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1612 =
                                             let uu____1613 =
                                               let uu____1615 =
                                                 let uu____1617 =
                                                   let uu____1618 =
                                                     let uu____1619 =
                                                       let uu____1621 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1621] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1619 in
                                                   FStar_Options.String
                                                     uu____1618 in
                                                 [uu____1617] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1615 in
                                             FStar_Options.List uu____1613 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1612);
                                          (let hint_refinement_cb uu____1633
                                             =
                                             match uu____1633 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1655 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1655
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1666 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1666))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1675 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              filter_facts_without_core
                                              all_labels uu____1675
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1677 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1677
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1682 =
                                                     let uu____1684 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1684] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1682);
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
                                  (let uu____1699 =
                                     let uu____1700 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1700 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1699);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1703 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1703;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1710 =
                                       let uu____1712 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1712
                                       then
                                         let uu____1714 =
                                           let uu____1715 =
                                             FStar_Options.check_hints () in
                                           if uu____1715
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
                                         Some uu____1714
                                       else hint_opt in
                                     record_hint uu____1710))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1721 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1721
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1728 =
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
                       ((let uu____1734 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1734
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1739 =
                           let uu____1740 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1740 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions unsat_core) all_labels wf None
                           uu____1739)) in
                 let process_query q = check q in
                 let uu____1748 = FStar_Options.admit_smt_queries () in
                 if uu____1748 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1767 =
           let uu____1768 =
             let uu____1769 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1769 in
           FStar_Util.format1 "Starting query at %s" uu____1768 in
         FStar_SMTEncoding_Encode.push uu____1767);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1771 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1771 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1792 =
               let uu____1793 =
                 let uu____1794 =
                   let uu____1795 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1795 in
                 FStar_Util.format1 "Ending query at %s" uu____1794 in
               FStar_SMTEncoding_Encode.pop uu____1793 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1796);
                        FStar_SMTEncoding_Term.freevars = uu____1797;
                        FStar_SMTEncoding_Term.rng = uu____1798;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1799;
                    FStar_SMTEncoding_Term.assumption_name = uu____1800;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1801;_}
                  -> pop1 ()
              | uu____1809 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1810 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1812 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1819  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1820  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1821  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1822  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1823  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1824  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1825  -> fun uu____1826  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1827  -> fun uu____1828  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1835  -> fun uu____1836  -> fun uu____1837  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1841  -> fun uu____1842  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1843  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1844  -> ())
  }
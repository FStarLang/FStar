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
                   let uu____164 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____165 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____164 uu____165
               | FStar_Util.Inr _error ->
                   let uu____167 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____168 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____167 uu____168))
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
      let uu____208 = FStar_ST.read replaying_hints in
      match uu____208 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_218  ->
               match uu___84_218 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____222 -> None)
      | uu____224 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___89_236 = h in
             {
               FStar_Util.hint_name = (uu___89_236.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_236.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_236.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_236.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_236.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____237 = FStar_ST.read recorded_hints in
    match uu____237 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____251 -> ()
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
          let uu____268 =
            let uu____270 = FStar_ST.read hint_stats in s :: uu____270 in
          FStar_ST.write hint_stats uu____268
let filter_using_facts_from:
  FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t =
  fun theory  ->
    let uu____281 = FStar_Options.using_facts_from () in
    match uu____281 with
    | None  -> theory
    | Some namespace_strings ->
        let fact_id_in_namespace ns uu___85_294 =
          match uu___85_294 with
          | FStar_SMTEncoding_Term.Namespace lid ->
              FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns
          | FStar_SMTEncoding_Term.Name _lid -> false
          | FStar_SMTEncoding_Term.Tag _s -> false in
        let matches_fact_ids include_assumption_names a =
          match a.FStar_SMTEncoding_Term.assumption_fact_ids with
          | [] -> true
          | uu____307 ->
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
        let uu____317 =
          FStar_List.fold_left
            (fun uu____332  ->
               fun d  ->
                 match uu____332 with
                 | (out,include_assumption_names) ->
                     (match d with
                      | FStar_SMTEncoding_Term.Assume a ->
                          let uu____353 =
                            matches_fact_ids include_assumption_names a in
                          if uu____353
                          then ((d :: out), include_assumption_names)
                          else (out, include_assumption_names)
                      | FStar_SMTEncoding_Term.RetainAssumptions names ->
                          ((d :: out),
                            (FStar_List.append names include_assumption_names))
                      | uu____367 -> ((d :: out), include_assumption_names)))
            ([], []) theory_rev in
        (match uu____317 with | (pruned_theory,uu____373) -> pruned_theory)
let filter_assertions:
  FStar_SMTEncoding_Z3.unsat_core ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  =
  fun core  ->
    fun theory  ->
      match core with
      | None  ->
          let uu____389 = filter_using_facts_from theory in
          (uu____389, false)
      | Some core1 ->
          let uu____393 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____409  ->
                   match uu____409 with
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
                        | uu____441 -> ((d :: theory1), n_retained, n_pruned)))
              theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
          (match uu____393 with
           | (theory',n_retained,n_pruned) ->
               let missed_assertions th core2 =
                 let missed =
                   let uu____463 =
                     FStar_All.pipe_right core2
                       (FStar_List.filter
                          (fun nm  ->
                             let uu____470 =
                               FStar_All.pipe_right th
                                 (FStar_Util.for_some
                                    (fun uu___86_474  ->
                                       match uu___86_474 with
                                       | FStar_SMTEncoding_Term.Assume a ->
                                           nm =
                                             a.FStar_SMTEncoding_Term.assumption_name
                                       | uu____476 -> false)) in
                             FStar_All.pipe_right uu____470 Prims.op_Negation)) in
                   FStar_All.pipe_right uu____463 (FStar_String.concat ", ") in
                 let included =
                   let uu____479 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___87_485  ->
                             match uu___87_485 with
                             | FStar_SMTEncoding_Term.Assume a ->
                                 [a.FStar_SMTEncoding_Term.assumption_name]
                             | uu____488 -> [])) in
                   FStar_All.pipe_right uu____479 (FStar_String.concat ", ") in
                 FStar_Util.format2 "missed={%s}; included={%s}" missed
                   included in
               ((let uu____491 =
                   (FStar_Options.hint_info ()) &&
                     (FStar_Options.debug_any ()) in
                 if uu____491
                 then
                   let n1 = FStar_List.length core1 in
                   let missed =
                     if n1 <> n_retained
                     then missed_assertions theory' core1
                     else "" in
                   let uu____498 = FStar_Util.string_of_int n_retained in
                   let uu____499 =
                     if n1 <> n_retained
                     then
                       let uu____502 = FStar_Util.string_of_int n1 in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____502 missed
                     else "" in
                   let uu____507 = FStar_Util.string_of_int n_pruned in
                   FStar_Util.print3
                     "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____498 uu____499 uu____507
                 else ());
                (let uu____509 =
                   let uu____511 =
                     let uu____513 =
                       let uu____514 =
                         let uu____515 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____515 in
                       FStar_SMTEncoding_Term.Caption uu____514 in
                     [uu____513] in
                   FStar_List.append theory' uu____511 in
                 (uu____509, true))))
let filter_facts_without_core:
  FStar_SMTEncoding_Term.decls_t ->
    (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  = fun x  -> let uu____523 = filter_using_facts_from x in (uu____523, false)
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
            (let uu____544 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____544 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___88_600 =
                   match uu___88_600 with
                   | ([],uu____607) -> ()
                   | errs ->
                       let uu____613 = FStar_ST.read minimum_workable_fuel in
                       (match uu____613 with
                        | Some uu____634 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____698 =
                   match uu____698 with
                   | (n1,i,rlimit) ->
                       let uu____707 =
                         let uu____709 =
                           let uu____710 =
                             let uu____711 = FStar_Util.string_of_int n1 in
                             let uu____712 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____711 uu____712 in
                           FStar_SMTEncoding_Term.Caption uu____710 in
                         let uu____713 =
                           let uu____715 =
                             let uu____716 =
                               let uu____720 =
                                 let uu____721 =
                                   let uu____724 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____726 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____724, uu____726) in
                                 FStar_SMTEncoding_Util.mkEq uu____721 in
                               (uu____720, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____716 in
                           let uu____728 =
                             let uu____730 =
                               let uu____731 =
                                 let uu____735 =
                                   let uu____736 =
                                     let uu____739 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____741 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____739, uu____741) in
                                   FStar_SMTEncoding_Util.mkEq uu____736 in
                                 (uu____735, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____731 in
                             [uu____730; p] in
                           uu____715 :: uu____728 in
                         uu____709 :: uu____713 in
                       let uu____743 =
                         let uu____745 =
                           let uu____747 =
                             let uu____749 =
                               let uu____750 =
                                 let uu____753 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____753) in
                               FStar_SMTEncoding_Term.SetOption uu____750 in
                             [uu____749] in
                           let uu____754 =
                             let uu____756 =
                               let uu____758 =
                                 let uu____760 =
                                   FStar_Options.record_hints () in
                                 if uu____760
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____763 =
                                 let uu____765 =
                                   let uu____767 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____767
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____770 =
                                   let uu____772 =
                                     let uu____774 =
                                       FStar_Options.check_hints () in
                                     if uu____774
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____772 suffix in
                                 FStar_List.append uu____765 uu____770 in
                               FStar_List.append uu____758 uu____763 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____756 in
                           FStar_List.append uu____747 uu____754 in
                         FStar_List.append label_assumptions uu____745 in
                       FStar_List.append uu____707 uu____743 in
                 let check p =
                   let rlimit =
                     let uu____782 = FStar_Options.z3_rlimit_factor () in
                     let uu____783 =
                       let uu____784 = FStar_Options.z3_rlimit () in
                       uu____784 * (Prims.parse_int "544656") in
                     uu____782 * uu____783 in
                   let default_initial_config =
                     let uu____789 = FStar_Options.initial_fuel () in
                     let uu____790 = FStar_Options.initial_ifuel () in
                     (uu____789, uu____790, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____793 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____815 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____815 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____793 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____866 =
                           let uu____872 =
                             let uu____878 =
                               let uu____883 =
                                 let uu____884 = FStar_Options.max_ifuel () in
                                 let uu____885 =
                                   FStar_Options.initial_ifuel () in
                                 uu____884 > uu____885 in
                               if uu____883
                               then
                                 let uu____890 =
                                   let uu____894 =
                                     FStar_Options.initial_fuel () in
                                   let uu____895 = FStar_Options.max_ifuel () in
                                   (uu____894, uu____895, rlimit) in
                                 [uu____890]
                               else [] in
                             let uu____906 =
                               let uu____912 =
                                 let uu____917 =
                                   let uu____918 =
                                     let uu____919 =
                                       FStar_Options.max_fuel () in
                                     uu____919 / (Prims.parse_int "2") in
                                   let uu____923 =
                                     FStar_Options.initial_fuel () in
                                   uu____918 > uu____923 in
                                 if uu____917
                                 then
                                   let uu____928 =
                                     let uu____932 =
                                       let uu____933 =
                                         FStar_Options.max_fuel () in
                                       uu____933 / (Prims.parse_int "2") in
                                     let uu____937 =
                                       FStar_Options.max_ifuel () in
                                     (uu____932, uu____937, rlimit) in
                                   [uu____928]
                                 else [] in
                               let uu____948 =
                                 let uu____954 =
                                   let uu____959 =
                                     (let uu____964 =
                                        FStar_Options.max_fuel () in
                                      let uu____965 =
                                        FStar_Options.initial_fuel () in
                                      uu____964 > uu____965) &&
                                       (let uu____968 =
                                          FStar_Options.max_ifuel () in
                                        let uu____969 =
                                          FStar_Options.initial_ifuel () in
                                        uu____968 >= uu____969) in
                                   if uu____959
                                   then
                                     let uu____974 =
                                       let uu____978 =
                                         FStar_Options.max_fuel () in
                                       let uu____979 =
                                         FStar_Options.max_ifuel () in
                                       (uu____978, uu____979, rlimit) in
                                     [uu____974]
                                   else [] in
                                 let uu____990 =
                                   let uu____996 =
                                     let uu____1001 =
                                       let uu____1002 =
                                         FStar_Options.min_fuel () in
                                       let uu____1003 =
                                         FStar_Options.initial_fuel () in
                                       uu____1002 < uu____1003 in
                                     if uu____1001
                                     then
                                       let uu____1008 =
                                         let uu____1012 =
                                           FStar_Options.min_fuel () in
                                         (uu____1012, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1008]
                                     else [] in
                                   [uu____996] in
                                 uu____954 :: uu____990 in
                               uu____912 :: uu____948 in
                             uu____878 :: uu____906 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____872 in
                         FStar_List.flatten uu____866 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1076 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1078 = FStar_Options.n_cores () in
                                uu____1078 = (Prims.parse_int "1")) in
                           if uu____1076
                           then
                             let uu____1079 =
                               let uu____1088 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1088 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1153 =
                                     let uu____1157 =
                                       FStar_Options.min_fuel () in
                                     (uu____1157, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1153, errs) in
                             match uu____1079 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1187 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      filter_facts_without_core all_labels
                                      uu____1187 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1194 = FStar_ST.read res in
                                    FStar_Option.get uu____1194) in
                                 let uu____1199 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1199, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1239,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1258 -> errs) in
                         record_hint None;
                         (let uu____1261 = FStar_Options.print_fuels () in
                          if uu____1261
                          then
                            let uu____1262 =
                              let uu____1263 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1263 in
                            let uu____1264 =
                              let uu____1265 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1265
                                FStar_Util.string_of_int in
                            let uu____1266 =
                              let uu____1267 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1267
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1262 uu____1264 uu____1266
                          else ());
                         (let uu____1269 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1285  ->
                                    match uu____1285 with
                                    | (uu____1291,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1269) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1307),uu____1308) -> result
                         | (uu____1313,FStar_Util.Inl uu____1314) -> result
                         | (uu____1321,FStar_Util.Inr uu____1322) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1389) -> report1 p1 errs
                          | (uu____1397,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1408) ->
                              let uu____1423 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                filter_facts_without_core all_labels
                                uu____1423 (Some scope)
                                (fun uu____1430  ->
                                   match uu____1430 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1442 =
                                         let uu____1446 =
                                           use_errors errs result in
                                         (uu____1446, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1442))
                       and cb used_hint uu____1448 p1 alt scope uu____1452 =
                         match (uu____1448, uu____1452) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1483 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1483))
                              else ();
                              (let uu____1486 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1486
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1505 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1505
                                 then
                                   let uu____1506 =
                                     let uu____1508 =
                                       let uu____1510 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1512 =
                                               let uu____1513 =
                                                 let uu____1514 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1514 in
                                               let uu____1515 =
                                                 let uu____1516 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1516 ")" in
                                               Prims.strcat uu____1513
                                                 uu____1515 in
                                             Prims.strcat "(" uu____1512
                                         | None  -> "" in
                                       let uu____1517 =
                                         let uu____1519 =
                                           let uu____1521 =
                                             let uu____1523 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1524 =
                                               let uu____1526 =
                                                 let uu____1528 =
                                                   let uu____1530 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1531 =
                                                     let uu____1533 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1534 =
                                                       let uu____1536 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1537 =
                                                         let uu____1539 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1539] in
                                                       uu____1536 ::
                                                         uu____1537 in
                                                     uu____1533 :: uu____1534 in
                                                   uu____1530 :: uu____1531 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1528 in
                                               tag :: uu____1526 in
                                             uu____1523 :: uu____1524 in
                                           query_name :: uu____1521 in
                                         name :: uu____1519 in
                                       uu____1510 :: uu____1517 in
                                     let uu____1543 =
                                       let uu____1545 =
                                         let uu____1546 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1546
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1558 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1558 "}"
                                         else
                                           (let uu____1563 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1563 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1566 -> "") in
                                       [uu____1545] in
                                     FStar_List.append uu____1508 uu____1543 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1506
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1586 =
                                     let uu____1587 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1587 in
                                   if uu____1586
                                   then
                                     let hint_check_cb uu____1601 =
                                       match uu____1601 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1624 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1630 ->
                                                 "failed" in
                                           let uu____1635 =
                                             FStar_Options.hint_info () in
                                           if uu____1635
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1639 =
                                         let uu____1644 =
                                           FStar_ST.read current_core in
                                         filter_assertions uu____1644 in
                                       let uu____1647 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1639
                                         all_labels uu____1647 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1649 =
                                         let uu____1650 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1650 in
                                       if uu____1649
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1657 =
                                             let uu____1658 =
                                               let uu____1660 =
                                                 let uu____1662 =
                                                   let uu____1663 =
                                                     let uu____1664 =
                                                       let uu____1666 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1666] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1664 in
                                                   FStar_Options.String
                                                     uu____1663 in
                                                 [uu____1662] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1660 in
                                             FStar_Options.List uu____1658 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1657);
                                          (let hint_refinement_cb uu____1678
                                             =
                                             match uu____1678 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1700 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1700
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1711 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1711))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1720 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              filter_facts_without_core
                                              all_labels uu____1720
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1722 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1722
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1727 =
                                                     let uu____1729 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1729] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1727);
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
                                  (let uu____1744 =
                                     let uu____1745 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1745 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1744);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1749 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1749;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1756 =
                                       let uu____1758 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1758
                                       then
                                         let uu____1760 =
                                           let uu____1761 =
                                             FStar_Options.check_hints () in
                                           if uu____1761
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
                                         Some uu____1760
                                       else hint_opt in
                                     record_hint uu____1756))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1767 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1767
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1774 =
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
                       ((let uu____1781 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1781
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1786 =
                           let uu____1787 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1787 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions unsat_core) all_labels wf None
                           uu____1786)) in
                 let process_query q = check q in
                 let uu____1795 = FStar_Options.admit_smt_queries () in
                 if uu____1795 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1814 =
           let uu____1815 =
             let uu____1816 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1816 in
           FStar_Util.format1 "Starting query at %s" uu____1815 in
         FStar_SMTEncoding_Encode.push uu____1814);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1818 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1818 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1839 =
               let uu____1840 =
                 let uu____1841 =
                   let uu____1842 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1842 in
                 FStar_Util.format1 "Ending query at %s" uu____1841 in
               FStar_SMTEncoding_Encode.pop uu____1840 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1843);
                        FStar_SMTEncoding_Term.freevars = uu____1844;
                        FStar_SMTEncoding_Term.rng = uu____1845;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1846;
                    FStar_SMTEncoding_Term.assumption_name = uu____1847;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1848;_}
                  -> pop1 ()
              | uu____1856 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1857 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1859 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1870  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1872  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1874  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1876  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1878  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1880  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1883  -> fun uu____1884  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1887  -> fun uu____1888  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1900  -> fun uu____1901  -> fun uu____1902  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1908  -> fun uu____1909  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1911  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1913  -> ())
  }
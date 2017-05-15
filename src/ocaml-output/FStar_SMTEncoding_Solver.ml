open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels* FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___86_23 =
  match uu___86_23 with
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
            (fun uu___87_208  ->
               match uu___87_208 with
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
            (let uu___92_225 = h in
             {
               FStar_Util.hint_name = (uu___92_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___92_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___92_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___92_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___92_225.FStar_Util.unsat_core);
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
let filter_using_facts_from:
  FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t =
  fun theory  ->
    let uu____270 = FStar_Options.using_facts_from () in
    match uu____270 with
    | None  -> theory
    | Some namespace_strings ->
        let fact_id_in_namespace ns uu___88_283 =
          match uu___88_283 with
          | FStar_SMTEncoding_Term.Namespace lid ->
              FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns
          | FStar_SMTEncoding_Term.Name _lid -> false
          | FStar_SMTEncoding_Term.Tag _s -> false in
        let matches_fact_ids include_assumption_names a =
          match a.FStar_SMTEncoding_Term.assumption_fact_ids with
          | [] -> true
          | uu____296 ->
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
        let uu____304 =
          FStar_List.fold_left
            (fun uu____313  ->
               fun d  ->
                 match uu____313 with
                 | (out,include_assumption_names) ->
                     (match d with
                      | FStar_SMTEncoding_Term.Assume a ->
                          let uu____334 =
                            matches_fact_ids include_assumption_names a in
                          if uu____334
                          then ((d :: out), include_assumption_names)
                          else (out, include_assumption_names)
                      | FStar_SMTEncoding_Term.RetainAssumptions names ->
                          ((d :: out),
                            (FStar_List.append names include_assumption_names))
                      | uu____348 -> ((d :: out), include_assumption_names)))
            ([], []) theory_rev in
        (match uu____304 with | (pruned_theory,uu____354) -> pruned_theory)
let filter_assertions:
  FStar_SMTEncoding_Z3.unsat_core ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  =
  fun core  ->
    fun theory  ->
      match core with
      | None  ->
          let uu____370 = filter_using_facts_from theory in
          (uu____370, false)
      | Some core1 ->
          let uu____374 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____384  ->
                   match uu____384 with
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
                        | uu____416 -> ((d :: theory1), n_retained, n_pruned)))
              theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
          (match uu____374 with
           | (theory',n_retained,n_pruned) ->
               let missed_assertions th core2 =
                 let missed =
                   let uu____438 =
                     FStar_All.pipe_right core2
                       (FStar_List.filter
                          (fun nm  ->
                             let uu____443 =
                               FStar_All.pipe_right th
                                 (FStar_Util.for_some
                                    (fun uu___89_445  ->
                                       match uu___89_445 with
                                       | FStar_SMTEncoding_Term.Assume a ->
                                           nm =
                                             a.FStar_SMTEncoding_Term.assumption_name
                                       | uu____447 -> false)) in
                             FStar_All.pipe_right uu____443 Prims.op_Negation)) in
                   FStar_All.pipe_right uu____438 (FStar_String.concat ", ") in
                 let included =
                   let uu____450 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___90_454  ->
                             match uu___90_454 with
                             | FStar_SMTEncoding_Term.Assume a ->
                                 [a.FStar_SMTEncoding_Term.assumption_name]
                             | uu____457 -> [])) in
                   FStar_All.pipe_right uu____450 (FStar_String.concat ", ") in
                 FStar_Util.format2 "missed={%s}; included={%s}" missed
                   included in
               ((let uu____460 =
                   (FStar_Options.hint_info ()) &&
                     (FStar_Options.debug_any ()) in
                 if uu____460
                 then
                   let n1 = FStar_List.length core1 in
                   let missed =
                     if n1 <> n_retained
                     then missed_assertions theory' core1
                     else "" in
                   let uu____467 = FStar_Util.string_of_int n_retained in
                   let uu____468 =
                     if n1 <> n_retained
                     then
                       let uu____471 = FStar_Util.string_of_int n1 in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____471 missed
                     else "" in
                   let uu____476 = FStar_Util.string_of_int n_pruned in
                   FStar_Util.print3
                     "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____467 uu____468 uu____476
                 else ());
                (let uu____478 =
                   let uu____480 =
                     let uu____482 =
                       let uu____483 =
                         let uu____484 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____484 in
                       FStar_SMTEncoding_Term.Caption uu____483 in
                     [uu____482] in
                   FStar_List.append theory' uu____480 in
                 (uu____478, true))))
let filter_facts_without_core:
  FStar_SMTEncoding_Term.decls_t ->
    (FStar_SMTEncoding_Term.decls_t* Prims.bool)
  = fun x  -> let uu____492 = filter_using_facts_from x in (uu____492, false)
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
            (let uu____513 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____513 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___91_569 =
                   match uu___91_569 with
                   | ([],uu____576) -> ()
                   | errs ->
                       let uu____582 = FStar_ST.read minimum_workable_fuel in
                       (match uu____582 with
                        | Some uu____603 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____667 =
                   match uu____667 with
                   | (n1,i,rlimit) ->
                       let uu____676 =
                         let uu____678 =
                           let uu____679 =
                             let uu____680 = FStar_Util.string_of_int n1 in
                             let uu____681 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____680 uu____681 in
                           FStar_SMTEncoding_Term.Caption uu____679 in
                         let uu____682 =
                           let uu____684 =
                             let uu____685 =
                               let uu____689 =
                                 let uu____690 =
                                   let uu____693 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____695 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____693, uu____695) in
                                 FStar_SMTEncoding_Util.mkEq uu____690 in
                               (uu____689, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____685 in
                           let uu____697 =
                             let uu____699 =
                               let uu____700 =
                                 let uu____704 =
                                   let uu____705 =
                                     let uu____708 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____710 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____708, uu____710) in
                                   FStar_SMTEncoding_Util.mkEq uu____705 in
                                 (uu____704, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____700 in
                             [uu____699; p] in
                           uu____684 :: uu____697 in
                         uu____678 :: uu____682 in
                       let uu____712 =
                         let uu____714 =
                           let uu____716 =
                             let uu____718 =
                               let uu____719 =
                                 let uu____722 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____722) in
                               FStar_SMTEncoding_Term.SetOption uu____719 in
                             [uu____718] in
                           let uu____723 =
                             let uu____725 =
                               let uu____727 =
                                 let uu____729 =
                                   FStar_Options.record_hints () in
                                 if uu____729
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____732 =
                                 let uu____734 =
                                   let uu____736 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____736
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____739 =
                                   let uu____741 =
                                     let uu____743 =
                                       FStar_Options.check_hints () in
                                     if uu____743
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____741 suffix in
                                 FStar_List.append uu____734 uu____739 in
                               FStar_List.append uu____727 uu____732 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____725 in
                           FStar_List.append uu____716 uu____723 in
                         FStar_List.append label_assumptions uu____714 in
                       FStar_List.append uu____676 uu____712 in
                 let check p =
                   let rlimit =
                     let uu____751 = FStar_Options.z3_rlimit_factor () in
                     let uu____752 =
                       let uu____753 = FStar_Options.z3_rlimit () in
                       uu____753 * (Prims.parse_int "544656") in
                     uu____751 * uu____752 in
                   let default_initial_config =
                     let uu____758 = FStar_Options.initial_fuel () in
                     let uu____759 = FStar_Options.initial_ifuel () in
                     (uu____758, uu____759, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____762 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____784 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____784 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____762 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____835 =
                           let uu____841 =
                             let uu____847 =
                               let uu____852 =
                                 let uu____853 = FStar_Options.max_ifuel () in
                                 let uu____854 =
                                   FStar_Options.initial_ifuel () in
                                 uu____853 > uu____854 in
                               if uu____852
                               then
                                 let uu____859 =
                                   let uu____863 =
                                     FStar_Options.initial_fuel () in
                                   let uu____864 = FStar_Options.max_ifuel () in
                                   (uu____863, uu____864, rlimit) in
                                 [uu____859]
                               else [] in
                             let uu____875 =
                               let uu____881 =
                                 let uu____886 =
                                   let uu____887 =
                                     let uu____888 =
                                       FStar_Options.max_fuel () in
                                     uu____888 / (Prims.parse_int "2") in
                                   let uu____892 =
                                     FStar_Options.initial_fuel () in
                                   uu____887 > uu____892 in
                                 if uu____886
                                 then
                                   let uu____897 =
                                     let uu____901 =
                                       let uu____902 =
                                         FStar_Options.max_fuel () in
                                       uu____902 / (Prims.parse_int "2") in
                                     let uu____906 =
                                       FStar_Options.max_ifuel () in
                                     (uu____901, uu____906, rlimit) in
                                   [uu____897]
                                 else [] in
                               let uu____917 =
                                 let uu____923 =
                                   let uu____928 =
                                     (let uu____929 =
                                        FStar_Options.max_fuel () in
                                      let uu____930 =
                                        FStar_Options.initial_fuel () in
                                      uu____929 > uu____930) &&
                                       (let uu____931 =
                                          FStar_Options.max_ifuel () in
                                        let uu____932 =
                                          FStar_Options.initial_ifuel () in
                                        uu____931 >= uu____932) in
                                   if uu____928
                                   then
                                     let uu____937 =
                                       let uu____941 =
                                         FStar_Options.max_fuel () in
                                       let uu____942 =
                                         FStar_Options.max_ifuel () in
                                       (uu____941, uu____942, rlimit) in
                                     [uu____937]
                                   else [] in
                                 let uu____953 =
                                   let uu____959 =
                                     let uu____964 =
                                       let uu____965 =
                                         FStar_Options.min_fuel () in
                                       let uu____966 =
                                         FStar_Options.initial_fuel () in
                                       uu____965 < uu____966 in
                                     if uu____964
                                     then
                                       let uu____971 =
                                         let uu____975 =
                                           FStar_Options.min_fuel () in
                                         (uu____975, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____971]
                                     else [] in
                                   [uu____959] in
                                 uu____923 :: uu____953 in
                               uu____881 :: uu____917 in
                             uu____847 :: uu____875 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____841 in
                         FStar_List.flatten uu____835 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1039 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1040 = FStar_Options.n_cores () in
                                uu____1040 = (Prims.parse_int "1")) in
                           if uu____1039
                           then
                             let uu____1041 =
                               let uu____1050 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1050 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1115 =
                                     let uu____1119 =
                                       FStar_Options.min_fuel () in
                                     (uu____1119, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1115, errs) in
                             match uu____1041 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1149 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      filter_facts_without_core all_labels
                                      uu____1149 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1155 = FStar_ST.read res in
                                    FStar_Option.get uu____1155) in
                                 let uu____1160 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1160, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1200,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (Prims.snd errs))
                              | uu____1219 -> errs) in
                         record_hint None;
                         (let uu____1222 = FStar_Options.print_fuels () in
                          if uu____1222
                          then
                            let uu____1223 =
                              let uu____1224 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1224 in
                            let uu____1225 =
                              let uu____1226 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1226
                                FStar_Util.string_of_int in
                            let uu____1227 =
                              let uu____1228 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1228
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1223 uu____1225 uu____1227
                          else ());
                         (let uu____1230 =
                            FStar_All.pipe_right (Prims.fst errs1)
                              (FStar_List.map
                                 (fun uu____1242  ->
                                    match uu____1242 with
                                    | (uu____1248,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1230) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____1276,FStar_Util.Inr uu____1277) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1359) ->
                              let uu____1374 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                filter_facts_without_core all_labels
                                uu____1374 (Some scope)
                                (fun uu____1376  ->
                                   match uu____1376 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1388 =
                                         let uu____1392 =
                                           use_errors errs result in
                                         (uu____1392, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1388))
                       and cb used_hint uu____1394 p1 alt scope uu____1398 =
                         match (uu____1394, uu____1398) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1429 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1429))
                              else ();
                              (let uu____1432 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1432
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1451 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1451
                                 then
                                   let uu____1452 =
                                     let uu____1454 =
                                       let uu____1456 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1458 =
                                               let uu____1459 =
                                                 let uu____1460 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1460 in
                                               let uu____1461 =
                                                 let uu____1462 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1462 ")" in
                                               Prims.strcat uu____1459
                                                 uu____1461 in
                                             Prims.strcat "(" uu____1458
                                         | None  -> "" in
                                       let uu____1463 =
                                         let uu____1465 =
                                           let uu____1467 =
                                             let uu____1469 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1470 =
                                               let uu____1472 =
                                                 let uu____1474 =
                                                   let uu____1476 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1477 =
                                                     let uu____1479 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1480 =
                                                       let uu____1482 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1483 =
                                                         let uu____1485 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1485] in
                                                       uu____1482 ::
                                                         uu____1483 in
                                                     uu____1479 :: uu____1480 in
                                                   uu____1476 :: uu____1477 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1474 in
                                               tag :: uu____1472 in
                                             uu____1469 :: uu____1470 in
                                           query_name :: uu____1467 in
                                         name :: uu____1465 in
                                       uu____1456 :: uu____1463 in
                                     let uu____1488 =
                                       let uu____1490 =
                                         let uu____1491 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1491
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1503 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1503 "}"
                                         else
                                           (let uu____1508 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1508 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1511 -> "") in
                                       [uu____1490] in
                                     FStar_List.append uu____1454 uu____1488 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1452
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1531 =
                                     let uu____1532 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1532 in
                                   if uu____1531
                                   then
                                     let hint_check_cb uu____1546 =
                                       match uu____1546 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1569 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1575 ->
                                                 "failed" in
                                           let uu____1580 =
                                             FStar_Options.hint_info () in
                                           if uu____1580
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1584 =
                                         let uu____1589 =
                                           FStar_ST.read current_core in
                                         filter_assertions uu____1589 in
                                       let uu____1592 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1584
                                         all_labels uu____1592 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1594 =
                                         let uu____1595 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1595 in
                                       if uu____1594
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1602 =
                                             let uu____1603 =
                                               let uu____1605 =
                                                 let uu____1607 =
                                                   let uu____1608 =
                                                     let uu____1609 =
                                                       let uu____1611 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1611] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1609 in
                                                   FStar_Options.String
                                                     uu____1608 in
                                                 [uu____1607] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1605 in
                                             FStar_Options.List uu____1603 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1602);
                                          (let hint_refinement_cb uu____1623
                                             =
                                             match uu____1623 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1645 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1645
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1656 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1656))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1665 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              filter_facts_without_core
                                              all_labels uu____1665
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1667 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1667
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1672 =
                                                     let uu____1674 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1674] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1672);
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
                                  (let uu____1689 =
                                     let uu____1690 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1690 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1689);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1693 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1693;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1700 =
                                       let uu____1702 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1702
                                       then
                                         let uu____1704 =
                                           let uu____1705 =
                                             FStar_Options.check_hints () in
                                           if uu____1705
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
                                         Some uu____1704
                                       else hint_opt in
                                     record_hint uu____1700))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1711 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1711
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1718 =
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
                       ((let uu____1724 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1724
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1729 =
                           let uu____1730 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1730 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions unsat_core) all_labels wf None
                           uu____1729)) in
                 let process_query q = check q in
                 let uu____1738 = FStar_Options.admit_smt_queries () in
                 if uu____1738 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1757 =
           let uu____1758 =
             let uu____1759 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1759 in
           FStar_Util.format1 "Starting query at %s" uu____1758 in
         FStar_SMTEncoding_Encode.push uu____1757);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1761 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1761 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1782 =
               let uu____1783 =
                 let uu____1784 =
                   let uu____1785 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1785 in
                 FStar_Util.format1 "Ending query at %s" uu____1784 in
               FStar_SMTEncoding_Encode.pop uu____1783 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1786);
                        FStar_SMTEncoding_Term.freevars = uu____1787;
                        FStar_SMTEncoding_Term.rng = uu____1788;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1789;
                    FStar_SMTEncoding_Term.assumption_name = uu____1790;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1791;_}
                  -> pop1 ()
              | uu____1799 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1800 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1802 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1809  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1810  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1811  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1812  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1813  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1814  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1815  -> fun uu____1816  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1817  -> fun uu____1818  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1825  -> fun uu____1826  -> fun uu____1827  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1831  -> fun uu____1832  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1833  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1834  -> ())
  }
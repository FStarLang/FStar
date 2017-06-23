open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels,FStar_SMTEncoding_Z3.error_kind)
    FStar_Pervasives_Native.tuple2
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
  (let uu____106 = FStar_Options.record_hints () in
   if uu____106
   then FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some [])
   else ());
  (let uu____114 = FStar_Options.use_hints () in
   if uu____114
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename =
       let uu____117 = FStar_Options.hint_file () in
       match uu____117 with
       | FStar_Pervasives_Native.Some fn -> fn
       | FStar_Pervasives_Native.None  ->
           format_hints_file_name norm_src_filename in
     let uu____120 = FStar_Util.read_hints val_filename in
     match uu____120 with
     | FStar_Pervasives_Native.Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____125 = FStar_Options.hint_info () in
           if uu____125
           then
             let uu____126 =
               let uu____127 = FStar_Options.hint_file () in
               match uu____127 with
               | FStar_Pervasives_Native.Some fn ->
                   Prims.strcat " from '" (Prims.strcat val_filename "'")
               | uu____130 -> "" in
             FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
               (if hints.FStar_Util.module_digest = expected_digest
                then "valid; using hints"
                else "invalid; using potentially stale hints") uu____126
           else ());
          FStar_ST.write replaying_hints
            (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
     | FStar_Pervasives_Native.None  ->
         let uu____137 = FStar_Options.hint_info () in
         (if uu____137
          then
            FStar_Util.print1 "(%s) Unable to read hint file.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____144 = FStar_Options.record_hints () in
     if uu____144
     then
       let hints =
         let uu____146 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____146 in
       let hints_db =
         let uu____152 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____152; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____155 = FStar_Options.hint_file () in
         match uu____155 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
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
               let uu____172 = FStar_Range.string_of_range s.source_location in
               let uu____173 = FStar_Util.string_of_int s.elapsed_time in
               FStar_Util.print3
                 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____172
                 (match s.replay_result with
                  | FStar_Util.Inl uu____174 -> "succeeded"
                  | FStar_Util.Inr uu____175 -> "failed") uu____173))
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
      let uu____215 = FStar_ST.read replaying_hints in
      match uu____215 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_223  ->
               match uu___84_223 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____227 -> FStar_Pervasives_Native.None)
      | uu____229 -> FStar_Pervasives_Native.None
let record_hint: FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit
  =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___89_240 = h in
             {
               FStar_Util.hint_name = (uu___89_240.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_240.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_240.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_240.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_240.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____241 = FStar_ST.read recorded_hints in
    match uu____241 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.write recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____255 -> ()
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
          let uu____272 =
            let uu____274 = FStar_ST.read hint_stats in s :: uu____274 in
          FStar_ST.write hint_stats uu____272
let filter_using_facts_from:
  FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decls_t =
  fun theory  ->
    let uu____285 = FStar_Options.using_facts_from () in
    match uu____285 with
    | FStar_Pervasives_Native.None  -> theory
    | FStar_Pervasives_Native.Some namespace_strings ->
        let fact_id_in_namespace ns uu___85_298 =
          match uu___85_298 with
          | FStar_SMTEncoding_Term.Namespace lid ->
              FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns
          | FStar_SMTEncoding_Term.Name _lid -> false
          | FStar_SMTEncoding_Term.Tag _s -> false in
        let matches_fact_ids include_assumption_names a =
          match a.FStar_SMTEncoding_Term.assumption_fact_ids with
          | [] -> true
          | uu____311 ->
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
        let uu____319 =
          FStar_List.fold_left
            (fun uu____328  ->
               fun d  ->
                 match uu____328 with
                 | (out,include_assumption_names) ->
                     (match d with
                      | FStar_SMTEncoding_Term.Assume a ->
                          let uu____349 =
                            matches_fact_ids include_assumption_names a in
                          if uu____349
                          then ((d :: out), include_assumption_names)
                          else (out, include_assumption_names)
                      | FStar_SMTEncoding_Term.RetainAssumptions names ->
                          ((d :: out),
                            (FStar_List.append names include_assumption_names))
                      | uu____363 -> ((d :: out), include_assumption_names)))
            ([], []) theory_rev in
        (match uu____319 with | (pruned_theory,uu____369) -> pruned_theory)
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
          let uu____385 = filter_using_facts_from theory in
          (uu____385, false)
      | FStar_Pervasives_Native.Some core1 ->
          let uu____389 =
            FStar_List.fold_right
              (fun d  ->
                 fun uu____399  ->
                   match uu____399 with
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
                        | uu____431 -> ((d :: theory1), n_retained, n_pruned)))
              theory ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
          (match uu____389 with
           | (theory',n_retained,n_pruned) ->
               let missed_assertions th core2 =
                 let missed =
                   let uu____453 =
                     FStar_All.pipe_right core2
                       (FStar_List.filter
                          (fun nm  ->
                             let uu____458 =
                               FStar_All.pipe_right th
                                 (FStar_Util.for_some
                                    (fun uu___86_460  ->
                                       match uu___86_460 with
                                       | FStar_SMTEncoding_Term.Assume a ->
                                           nm =
                                             a.FStar_SMTEncoding_Term.assumption_name
                                       | uu____462 -> false)) in
                             FStar_All.pipe_right uu____458 Prims.op_Negation)) in
                   FStar_All.pipe_right uu____453 (FStar_String.concat ", ") in
                 let included =
                   let uu____465 =
                     FStar_All.pipe_right th
                       (FStar_List.collect
                          (fun uu___87_469  ->
                             match uu___87_469 with
                             | FStar_SMTEncoding_Term.Assume a ->
                                 [a.FStar_SMTEncoding_Term.assumption_name]
                             | uu____472 -> [])) in
                   FStar_All.pipe_right uu____465 (FStar_String.concat ", ") in
                 FStar_Util.format2 "missed={%s}; included={%s}" missed
                   included in
               ((let uu____475 =
                   (FStar_Options.hint_info ()) &&
                     (FStar_Options.debug_any ()) in
                 if uu____475
                 then
                   let n1 = FStar_List.length core1 in
                   let missed =
                     if n1 <> n_retained
                     then missed_assertions theory' core1
                     else "" in
                   let uu____482 = FStar_Util.string_of_int n_retained in
                   let uu____483 =
                     if n1 <> n_retained
                     then
                       let uu____486 = FStar_Util.string_of_int n1 in
                       FStar_Util.format2
                         " (expected %s (%s); replay may be inaccurate)"
                         uu____486 missed
                     else "" in
                   let uu____491 = FStar_Util.string_of_int n_pruned in
                   FStar_Util.print3
                     "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                     uu____482 uu____483 uu____491
                 else ());
                (let uu____493 =
                   let uu____495 =
                     let uu____497 =
                       let uu____498 =
                         let uu____499 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____499 in
                       FStar_SMTEncoding_Term.Caption uu____498 in
                     [uu____497] in
                   FStar_List.append theory' uu____495 in
                 (uu____493, true))))
let filter_facts_without_core:
  FStar_SMTEncoding_Term.decls_t ->
    (FStar_SMTEncoding_Term.decls_t,Prims.bool)
      FStar_Pervasives_Native.tuple2
  = fun x  -> let uu____507 = filter_using_facts_from x in (uu____507, false)
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
            (let uu____528 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1) in
             match uu____528 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None in
                 let set_minimum_workable_fuel f uu___88_584 =
                   match uu___88_584 with
                   | ([],uu____591) -> ()
                   | errs ->
                       let uu____597 = FStar_ST.read minimum_workable_fuel in
                       (match uu____597 with
                        | FStar_Pervasives_Native.Some uu____618 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.write minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs))) in
                 let with_fuel label_assumptions p uu____682 =
                   match uu____682 with
                   | (n1,i,rlimit) ->
                       let uu____691 =
                         let uu____693 =
                           let uu____694 =
                             let uu____695 = FStar_Util.string_of_int n1 in
                             let uu____696 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____695 uu____696 in
                           FStar_SMTEncoding_Term.Caption uu____694 in
                         let uu____697 =
                           let uu____699 =
                             let uu____700 =
                               let uu____704 =
                                 let uu____705 =
                                   let uu____708 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____710 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____708, uu____710) in
                                 FStar_SMTEncoding_Util.mkEq uu____705 in
                               (uu____704, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____700 in
                           let uu____712 =
                             let uu____714 =
                               let uu____715 =
                                 let uu____719 =
                                   let uu____720 =
                                     let uu____723 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____725 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____723, uu____725) in
                                   FStar_SMTEncoding_Util.mkEq uu____720 in
                                 (uu____719, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____715 in
                             [uu____714; p] in
                           uu____699 :: uu____712 in
                         uu____693 :: uu____697 in
                       let uu____727 =
                         let uu____729 =
                           let uu____731 =
                             let uu____733 =
                               let uu____734 =
                                 let uu____737 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____737) in
                               FStar_SMTEncoding_Term.SetOption uu____734 in
                             [uu____733] in
                           let uu____738 =
                             let uu____740 =
                               let uu____742 =
                                 let uu____744 =
                                   FStar_Options.record_hints () in
                                 if uu____744
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____747 =
                                 let uu____749 =
                                   let uu____751 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____751
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics;
                                     FStar_SMTEncoding_Term.GetReasonUnknown]
                                   else [] in
                                 FStar_List.append uu____749 suffix in
                               FStar_List.append uu____742 uu____747 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____740 in
                           FStar_List.append uu____731 uu____738 in
                         FStar_List.append label_assumptions uu____729 in
                       FStar_List.append uu____691 uu____727 in
                 let check p =
                   let rlimit =
                     let uu____759 = FStar_Options.z3_rlimit_factor () in
                     let uu____760 =
                       let uu____761 = FStar_Options.z3_rlimit () in
                       uu____761 * (Prims.parse_int "544656") in
                     uu____759 * uu____760 in
                   let default_initial_config =
                     let uu____766 = FStar_Options.initial_fuel () in
                     let uu____767 = FStar_Options.initial_ifuel () in
                     (uu____766, uu____767, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____770 =
                     match hint_opt with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None,
                           default_initial_config)
                     | FStar_Pervasives_Native.Some hint ->
                         let uu____792 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (FStar_Pervasives_Native.None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____792 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____770 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____843 =
                           let uu____849 =
                             let uu____855 =
                               let uu____860 =
                                 let uu____861 = FStar_Options.max_ifuel () in
                                 let uu____862 =
                                   FStar_Options.initial_ifuel () in
                                 uu____861 > uu____862 in
                               if uu____860
                               then
                                 let uu____867 =
                                   let uu____871 =
                                     FStar_Options.initial_fuel () in
                                   let uu____872 = FStar_Options.max_ifuel () in
                                   (uu____871, uu____872, rlimit) in
                                 [uu____867]
                               else [] in
                             let uu____883 =
                               let uu____889 =
                                 let uu____894 =
                                   let uu____895 =
                                     let uu____896 =
                                       FStar_Options.max_fuel () in
                                     uu____896 / (Prims.parse_int "2") in
                                   let uu____900 =
                                     FStar_Options.initial_fuel () in
                                   uu____895 > uu____900 in
                                 if uu____894
                                 then
                                   let uu____905 =
                                     let uu____909 =
                                       let uu____910 =
                                         FStar_Options.max_fuel () in
                                       uu____910 / (Prims.parse_int "2") in
                                     let uu____914 =
                                       FStar_Options.max_ifuel () in
                                     (uu____909, uu____914, rlimit) in
                                   [uu____905]
                                 else [] in
                               let uu____925 =
                                 let uu____931 =
                                   let uu____936 =
                                     (let uu____937 =
                                        FStar_Options.max_fuel () in
                                      let uu____938 =
                                        FStar_Options.initial_fuel () in
                                      uu____937 > uu____938) &&
                                       (let uu____939 =
                                          FStar_Options.max_ifuel () in
                                        let uu____940 =
                                          FStar_Options.initial_ifuel () in
                                        uu____939 >= uu____940) in
                                   if uu____936
                                   then
                                     let uu____945 =
                                       let uu____949 =
                                         FStar_Options.max_fuel () in
                                       let uu____950 =
                                         FStar_Options.max_ifuel () in
                                       (uu____949, uu____950, rlimit) in
                                     [uu____945]
                                   else [] in
                                 let uu____961 =
                                   let uu____967 =
                                     let uu____972 =
                                       let uu____973 =
                                         FStar_Options.min_fuel () in
                                       let uu____974 =
                                         FStar_Options.initial_fuel () in
                                       uu____973 < uu____974 in
                                     if uu____972
                                     then
                                       let uu____979 =
                                         let uu____983 =
                                           FStar_Options.min_fuel () in
                                         (uu____983, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____979]
                                     else [] in
                                   [uu____967] in
                                 uu____931 :: uu____961 in
                               uu____889 :: uu____925 in
                             uu____855 :: uu____883 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____849 in
                         FStar_List.flatten uu____843 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1047 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1048 = FStar_Options.n_cores () in
                                uu____1048 = (Prims.parse_int "1")) in
                           if uu____1047
                           then
                             let uu____1049 =
                               let uu____1058 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1058 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____1123 =
                                     let uu____1127 =
                                       FStar_Options.min_fuel () in
                                     (uu____1127, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1123, errs) in
                             match uu____1049 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (let uu____1157 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      filter_facts_without_core all_labels
                                      uu____1157 FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.write res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____1163 = FStar_ST.read res in
                                    FStar_Option.get uu____1163) in
                                 let uu____1168 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1168, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1208,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____1227 -> errs) in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____1230 = FStar_Options.print_fuels () in
                          if uu____1230
                          then
                            let uu____1231 =
                              let uu____1232 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1232 in
                            let uu____1233 =
                              let uu____1234 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1234
                                FStar_Util.string_of_int in
                            let uu____1235 =
                              let uu____1236 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1236
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1231 uu____1233 uu____1235
                          else ());
                         (let uu____1238 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.fst errs1)
                              (FStar_List.map
                                 (fun uu____1250  ->
                                    match uu____1250 with
                                    | (uu____1256,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1238) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1272),uu____1273) -> result
                         | (uu____1278,FStar_Util.Inl uu____1279) -> result
                         | (uu____1286,FStar_Util.Inr uu____1287) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____1354) -> report1 p1 errs
                          | (uu____1362,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1373) ->
                              let uu____1388 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                filter_facts_without_core all_labels
                                uu____1388
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____1390  ->
                                   match uu____1390 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1402 =
                                         let uu____1406 =
                                           use_errors errs result in
                                         (uu____1406, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1402))
                       and cb used_hint uu____1408 p1 alt scope uu____1412 =
                         match (uu____1408, uu____1412) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1443 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1443))
                              else ();
                              (let uu____1446 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1446
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1465 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1465
                                 then
                                   let uu____1466 =
                                     let uu____1468 =
                                       let uu____1470 =
                                         match env1 with
                                         | FStar_Pervasives_Native.Some e ->
                                             let uu____1472 =
                                               let uu____1473 =
                                                 let uu____1474 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1474 in
                                               let uu____1475 =
                                                 let uu____1476 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1476 ")" in
                                               Prims.strcat uu____1473
                                                 uu____1475 in
                                             Prims.strcat "(" uu____1472
                                         | FStar_Pervasives_Native.None  ->
                                             "" in
                                       let uu____1477 =
                                         let uu____1479 =
                                           let uu____1481 =
                                             let uu____1483 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1484 =
                                               let uu____1486 =
                                                 let uu____1488 =
                                                   let uu____1490 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1491 =
                                                     let uu____1493 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1494 =
                                                       let uu____1496 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1497 =
                                                         let uu____1499 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1499] in
                                                       uu____1496 ::
                                                         uu____1497 in
                                                     uu____1493 :: uu____1494 in
                                                   uu____1490 :: uu____1491 in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____1488 in
                                               tag :: uu____1486 in
                                             uu____1483 :: uu____1484 in
                                           query_name :: uu____1481 in
                                         name :: uu____1479 in
                                       uu____1470 :: uu____1477 in
                                     let uu____1502 =
                                       let uu____1504 =
                                         let uu____1505 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1505
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1517 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1517 "}"
                                         else
                                           (let uu____1522 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1522 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1525 -> "") in
                                       [uu____1504] in
                                     FStar_List.append uu____1468 uu____1502 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1466
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1545 =
                                     let uu____1546 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1546 in
                                   if uu____1545
                                   then
                                     let hint_check_cb uu____1560 =
                                       match uu____1560 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1583 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1589 ->
                                                 "failed" in
                                           let uu____1594 =
                                             FStar_Options.hint_info () in
                                           if uu____1594
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1598 =
                                         let uu____1603 =
                                           FStar_ST.read current_core in
                                         filter_assertions uu____1603 in
                                       let uu____1606 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1598
                                         all_labels uu____1606
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____1608 =
                                         let uu____1609 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1609 in
                                       if uu____1608
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1616 =
                                             let uu____1617 =
                                               let uu____1619 =
                                                 let uu____1621 =
                                                   let uu____1622 =
                                                     let uu____1623 =
                                                       let uu____1625 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1625] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1623 in
                                                   FStar_Options.String
                                                     uu____1622 in
                                                 [uu____1621] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1619 in
                                             FStar_Options.List uu____1617 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1616);
                                          (let hint_refinement_cb uu____1637
                                             =
                                             match uu____1637 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1659 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1659
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1670 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1670))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info
                                                     FStar_Pervasives_Native.None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1679 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              filter_facts_without_core
                                              all_labels uu____1679
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____1681 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1681
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1686 =
                                                     let uu____1688 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1688] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1686);
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
                                  (let uu____1703 =
                                     let uu____1704 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1704 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1703);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1707 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1707;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____1714 =
                                       let uu____1716 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1716
                                       then
                                         let uu____1718 =
                                           let uu____1719 =
                                             FStar_Options.check_hints () in
                                           if uu____1719
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
                                           uu____1718
                                       else hint_opt in
                                     record_hint uu____1714))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____1725 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1725
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | FStar_Pervasives_Native.Some core
                                             ->
                                             ((let uu____1732 =
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
                       ((let uu____1738 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1738
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1743 =
                           let uu____1744 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1744 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____1743)) in
                 let process_query q = check q in
                 let uu____1752 = FStar_Options.admit_smt_queries () in
                 if uu____1752 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1771 =
           let uu____1772 =
             let uu____1773 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1773 in
           FStar_Util.format1 "Starting query at %s" uu____1772 in
         FStar_SMTEncoding_Encode.push uu____1771);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1775 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1775 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1796 =
               let uu____1797 =
                 let uu____1798 =
                   let uu____1799 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1799 in
                 FStar_Util.format1 "Ending query at %s" uu____1798 in
               FStar_SMTEncoding_Encode.pop uu____1797 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1800);
                        FStar_SMTEncoding_Term.freevars = uu____1801;
                        FStar_SMTEncoding_Term.rng = uu____1802;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1803;
                    FStar_SMTEncoding_Term.assumption_name = uu____1804;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1805;_}
                  -> pop1 ()
              | uu____1813 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1814 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1816 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1823  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1824  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1825  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1826  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1827  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1828  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1829  -> fun uu____1830  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1831  -> fun uu____1832  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1839  -> fun uu____1840  -> fun uu____1841  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1845  -> fun uu____1846  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1847  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1848  -> ())
  }
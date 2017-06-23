open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels,FStar_SMTEncoding_Z3.error_kind)
    FStar_Pervasives_Native.tuple2
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___84_27 =
  match uu___84_27 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____36) -> FStar_Util.Inr r
type hint_stat =
  {
  hint: FStar_Util.hint FStar_Pervasives_Native.option;
  replay_result: z3_replay_result;
  elapsed_time: Prims.int;
  source_location: FStar_Range.range;}
let __proj__Mkhint_stat__item__hint:
  hint_stat -> FStar_Util.hint FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} -> __fname__hint
let __proj__Mkhint_stat__item__replay_result: hint_stat -> z3_replay_result =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__replay_result
let __proj__Mkhint_stat__item__elapsed_time: hint_stat -> Prims.int =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__elapsed_time
let __proj__Mkhint_stat__item__source_location:
  hint_stat -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__source_location
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
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____134 = FStar_Options.record_hints () in
   if uu____134
   then FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some [])
   else ());
  (let uu____142 = FStar_Options.use_hints () in
   if uu____142
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____145 = FStar_Util.read_hints val_filename in
     match uu____145 with
     | FStar_Pervasives_Native.Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____150 = FStar_Options.hint_info () in
           if uu____150
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
          FStar_ST.write replaying_hints
            (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
     | FStar_Pervasives_Native.None  ->
         let uu____156 = FStar_Options.hint_info () in
         (if uu____156
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____164 = FStar_Options.record_hints () in
     if uu____164
     then
       let hints =
         let uu____166 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____166 in
       let hints_db =
         let uu____172 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____172; FStar_Util.hints = hints } in
       let hints_file_name = format_hints_file_name src_filename in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____176 = FStar_Options.hint_info () in
     if uu____176
     then
       let stats =
         let uu____179 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____179 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____193 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____194 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____193 uu____194
               | FStar_Util.Inr _error ->
                   let uu____196 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____197 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____196 uu____197))
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
      let uu____242 = FStar_ST.read replaying_hints in
      match uu____242 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___85_252  ->
               match uu___85_252 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____256 -> FStar_Pervasives_Native.None)
      | uu____258 -> FStar_Pervasives_Native.None
let record_hint: FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit
  =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___89_271 = h in
             {
               FStar_Util.hint_name = (uu___89_271.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_271.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_271.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_271.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_271.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____272 = FStar_ST.read recorded_hints in
    match uu____272 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.write recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____286 -> ()
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
          let uu____307 =
            let uu____309 = FStar_ST.read hint_stats in s :: uu____309 in
          FStar_ST.write hint_stats uu____307
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
        | uu____331 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____341 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____348 =
        FStar_List.fold_left
          (fun uu____363  ->
             fun d  ->
               match uu____363 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____384 =
                          matches_fact_ids include_assumption_names a in
                        if uu____384
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____398 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____348 with | (pruned_theory,uu____405) -> pruned_theory
let filter_assertions:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____429 = filter_using_facts_from e theory in
            (uu____429, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____435 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____451  ->
                     match uu____451 with
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
                          | uu____483 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____435 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____506 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____513 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___86_517  ->
                                         match uu___86_517 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____519 -> false)) in
                               FStar_All.pipe_right uu____513
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____506
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____522 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___87_528  ->
                               match uu___87_528 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____531 -> [])) in
                     FStar_All.pipe_right uu____522
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____534 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____534
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____544 = FStar_Util.string_of_int n_retained in
                     let uu____545 =
                       if n1 <> n_retained
                       then
                         let uu____550 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____550 missed
                       else "" in
                     let uu____558 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____544 uu____545 uu____558
                   else ());
                  (let uu____560 =
                     let uu____562 =
                       let uu____564 =
                         let uu____565 =
                           let uu____566 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____566 in
                         FStar_SMTEncoding_Term.Caption uu____565 in
                       [uu____564] in
                     FStar_List.append theory' uu____562 in
                   (uu____560, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____580 = filter_using_facts_from e x in (uu____580, false)
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
            (let uu____608 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1) in
             match uu____608 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None in
                 let set_minimum_workable_fuel f uu___88_664 =
                   match uu___88_664 with
                   | ([],uu____671) -> ()
                   | errs ->
                       let uu____677 = FStar_ST.read minimum_workable_fuel in
                       (match uu____677 with
                        | FStar_Pervasives_Native.Some uu____698 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.write minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs))) in
                 let with_fuel label_assumptions p uu____762 =
                   match uu____762 with
                   | (n1,i,rlimit) ->
                       let uu____771 =
                         let uu____773 =
                           let uu____774 =
                             let uu____775 = FStar_Util.string_of_int n1 in
                             let uu____776 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____775 uu____776 in
                           FStar_SMTEncoding_Term.Caption uu____774 in
                         let uu____777 =
                           let uu____779 =
                             let uu____780 =
                               let uu____784 =
                                 let uu____785 =
                                   let uu____788 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____790 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____788, uu____790) in
                                 FStar_SMTEncoding_Util.mkEq uu____785 in
                               (uu____784, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____780 in
                           let uu____792 =
                             let uu____794 =
                               let uu____795 =
                                 let uu____799 =
                                   let uu____800 =
                                     let uu____803 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____805 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____803, uu____805) in
                                   FStar_SMTEncoding_Util.mkEq uu____800 in
                                 (uu____799, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____795 in
                             [uu____794; p] in
                           uu____779 :: uu____792 in
                         uu____773 :: uu____777 in
                       let uu____807 =
                         let uu____809 =
                           let uu____811 =
                             let uu____813 =
                               let uu____814 =
                                 let uu____817 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____817) in
                               FStar_SMTEncoding_Term.SetOption uu____814 in
                             [uu____813] in
                           let uu____818 =
                             let uu____820 =
                               let uu____822 =
                                 let uu____824 =
                                   FStar_Options.record_hints () in
                                 if uu____824
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____827 =
                                 let uu____829 =
                                   let uu____831 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____831
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____834 =
                                   let uu____836 =
                                     let uu____838 =
                                       FStar_Options.check_hints () in
                                     if uu____838
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____836 suffix in
                                 FStar_List.append uu____829 uu____834 in
                               FStar_List.append uu____822 uu____827 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____820 in
                           FStar_List.append uu____811 uu____818 in
                         FStar_List.append label_assumptions uu____809 in
                       FStar_List.append uu____771 uu____807 in
                 let check p =
                   let rlimit =
                     let uu____846 = FStar_Options.z3_rlimit_factor () in
                     let uu____847 =
                       let uu____848 = FStar_Options.z3_rlimit () in
                       uu____848 * (Prims.parse_int "544656") in
                     uu____846 * uu____847 in
                   let default_initial_config =
                     let uu____853 = FStar_Options.initial_fuel () in
                     let uu____854 = FStar_Options.initial_ifuel () in
                     (uu____853, uu____854, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____857 =
                     match hint_opt with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None,
                           default_initial_config)
                     | FStar_Pervasives_Native.Some hint ->
                         let uu____879 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (FStar_Pervasives_Native.None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____879 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____857 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____930 =
                           let uu____936 =
                             let uu____942 =
                               let uu____947 =
                                 let uu____948 = FStar_Options.max_ifuel () in
                                 let uu____949 =
                                   FStar_Options.initial_ifuel () in
                                 uu____948 > uu____949 in
                               if uu____947
                               then
                                 let uu____954 =
                                   let uu____958 =
                                     FStar_Options.initial_fuel () in
                                   let uu____959 = FStar_Options.max_ifuel () in
                                   (uu____958, uu____959, rlimit) in
                                 [uu____954]
                               else [] in
                             let uu____970 =
                               let uu____976 =
                                 let uu____981 =
                                   let uu____982 =
                                     let uu____983 =
                                       FStar_Options.max_fuel () in
                                     uu____983 / (Prims.parse_int "2") in
                                   let uu____990 =
                                     FStar_Options.initial_fuel () in
                                   uu____982 > uu____990 in
                                 if uu____981
                                 then
                                   let uu____995 =
                                     let uu____999 =
                                       let uu____1000 =
                                         FStar_Options.max_fuel () in
                                       uu____1000 / (Prims.parse_int "2") in
                                     let uu____1007 =
                                       FStar_Options.max_ifuel () in
                                     (uu____999, uu____1007, rlimit) in
                                   [uu____995]
                                 else [] in
                               let uu____1018 =
                                 let uu____1024 =
                                   let uu____1029 =
                                     (let uu____1034 =
                                        FStar_Options.max_fuel () in
                                      let uu____1035 =
                                        FStar_Options.initial_fuel () in
                                      uu____1034 > uu____1035) &&
                                       (let uu____1038 =
                                          FStar_Options.max_ifuel () in
                                        let uu____1039 =
                                          FStar_Options.initial_ifuel () in
                                        uu____1038 >= uu____1039) in
                                   if uu____1029
                                   then
                                     let uu____1044 =
                                       let uu____1048 =
                                         FStar_Options.max_fuel () in
                                       let uu____1049 =
                                         FStar_Options.max_ifuel () in
                                       (uu____1048, uu____1049, rlimit) in
                                     [uu____1044]
                                   else [] in
                                 let uu____1060 =
                                   let uu____1066 =
                                     let uu____1071 =
                                       let uu____1072 =
                                         FStar_Options.min_fuel () in
                                       let uu____1073 =
                                         FStar_Options.initial_fuel () in
                                       uu____1072 < uu____1073 in
                                     if uu____1071
                                     then
                                       let uu____1078 =
                                         let uu____1082 =
                                           FStar_Options.min_fuel () in
                                         (uu____1082, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1078]
                                     else [] in
                                   [uu____1066] in
                                 uu____1024 :: uu____1060 in
                               uu____976 :: uu____1018 in
                             uu____942 :: uu____970 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____936 in
                         FStar_List.flatten uu____930 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1146 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1148 = FStar_Options.n_cores () in
                                uu____1148 = (Prims.parse_int "1")) in
                           if uu____1146
                           then
                             let uu____1149 =
                               let uu____1158 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1158 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____1223 =
                                     let uu____1227 =
                                       FStar_Options.min_fuel () in
                                     (uu____1227, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1223, errs) in
                             match uu____1149 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (let uu____1257 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1257
                                      FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.write res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____1264 = FStar_ST.read res in
                                    FStar_Option.get uu____1264) in
                                 let uu____1269 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1269, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1309,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____1328 -> errs) in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____1331 = FStar_Options.print_fuels () in
                          if uu____1331
                          then
                            let uu____1332 =
                              let uu____1333 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1333 in
                            let uu____1334 =
                              let uu____1335 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1335
                                FStar_Util.string_of_int in
                            let uu____1336 =
                              let uu____1337 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1337
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1332 uu____1334 uu____1336
                          else ());
                         (let uu____1339 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.fst errs1)
                              (FStar_List.map
                                 (fun uu____1355  ->
                                    match uu____1355 with
                                    | (uu____1361,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1339) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1377),uu____1378) -> result
                         | (uu____1383,FStar_Util.Inl uu____1384) -> result
                         | (uu____1391,FStar_Util.Inr uu____1392) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____1459) -> report1 p1 errs
                          | (uu____1467,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1478) ->
                              let uu____1493 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1493
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____1500  ->
                                   match uu____1500 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1512 =
                                         let uu____1516 =
                                           use_errors errs result in
                                         (uu____1516, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1512))
                       and cb used_hint uu____1518 p1 alt scope uu____1522 =
                         match (uu____1518, uu____1522) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1553 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1553))
                              else ();
                              (let uu____1556 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1556
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1575 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1575
                                 then
                                   let uu____1576 =
                                     let uu____1578 =
                                       let uu____1580 =
                                         match env1 with
                                         | FStar_Pervasives_Native.Some e ->
                                             let uu____1582 =
                                               let uu____1583 =
                                                 let uu____1584 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1584 in
                                               let uu____1585 =
                                                 let uu____1586 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1586 ")" in
                                               Prims.strcat uu____1583
                                                 uu____1585 in
                                             Prims.strcat "(" uu____1582
                                         | FStar_Pervasives_Native.None  ->
                                             "" in
                                       let uu____1587 =
                                         let uu____1589 =
                                           let uu____1591 =
                                             let uu____1593 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1594 =
                                               let uu____1596 =
                                                 let uu____1598 =
                                                   let uu____1600 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1601 =
                                                     let uu____1603 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1604 =
                                                       let uu____1606 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1607 =
                                                         let uu____1609 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1609] in
                                                       uu____1606 ::
                                                         uu____1607 in
                                                     uu____1603 :: uu____1604 in
                                                   uu____1600 :: uu____1601 in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____1598 in
                                               tag :: uu____1596 in
                                             uu____1593 :: uu____1594 in
                                           query_name :: uu____1591 in
                                         name :: uu____1589 in
                                       uu____1580 :: uu____1587 in
                                     let uu____1613 =
                                       let uu____1615 =
                                         let uu____1616 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1616
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1628 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1628 "}"
                                         else
                                           (let uu____1636 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1636 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1639 -> "") in
                                       [uu____1615] in
                                     FStar_List.append uu____1578 uu____1613 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1576
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1659 =
                                     let uu____1660 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1660 in
                                   if uu____1659
                                   then
                                     let hint_check_cb uu____1674 =
                                       match uu____1674 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1697 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1703 ->
                                                 "failed" in
                                           let uu____1708 =
                                             FStar_Options.hint_info () in
                                           if uu____1708
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1712 =
                                         let uu____1717 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1717 in
                                       let uu____1720 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1712
                                         all_labels uu____1720
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____1722 =
                                         let uu____1723 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1723 in
                                       if uu____1722
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1730 =
                                             let uu____1731 =
                                               let uu____1733 =
                                                 let uu____1735 =
                                                   let uu____1736 =
                                                     let uu____1737 =
                                                       let uu____1739 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1739] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1737 in
                                                   FStar_Options.String
                                                     uu____1736 in
                                                 [uu____1735] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1733 in
                                             FStar_Options.List uu____1731 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1730);
                                          (let hint_refinement_cb uu____1751
                                             =
                                             match uu____1751 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1773 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1773
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1784 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1784))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info
                                                     FStar_Pervasives_Native.None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1793 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1793
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____1795 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1795
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1800 =
                                                     let uu____1802 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1802] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1800);
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
                                  (let uu____1817 =
                                     let uu____1818 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1818 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1817);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1822 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1822;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____1829 =
                                       let uu____1831 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1831
                                       then
                                         let uu____1833 =
                                           let uu____1834 =
                                             FStar_Options.check_hints () in
                                           if uu____1834
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
                                           uu____1833
                                       else hint_opt in
                                     record_hint uu____1829))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____1840 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1840
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | FStar_Pervasives_Native.Some core
                                             ->
                                             ((let uu____1847 =
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
                       ((let uu____1854 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1854
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1859 =
                           let uu____1860 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1860 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____1859)) in
                 let process_query q = check q in
                 let uu____1868 = FStar_Options.admit_smt_queries () in
                 if uu____1868 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1890 =
           let uu____1891 =
             let uu____1892 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1892 in
           FStar_Util.format1 "Starting query at %s" uu____1891 in
         FStar_SMTEncoding_Encode.push uu____1890);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1894 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1894 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1915 =
               let uu____1916 =
                 let uu____1917 =
                   let uu____1918 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1918 in
                 FStar_Util.format1 "Ending query at %s" uu____1917 in
               FStar_SMTEncoding_Encode.pop uu____1916 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1919);
                        FStar_SMTEncoding_Term.freevars = uu____1920;
                        FStar_SMTEncoding_Term.rng = uu____1921;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1922;
                    FStar_SMTEncoding_Term.assumption_name = uu____1923;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1924;_}
                  -> pop1 ()
              | uu____1932 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1933 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1935 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____1941 =
             let uu____1945 = FStar_Options.peek () in (e, g, uu____1945) in
           [uu____1941]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1954  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1956  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1958  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1960  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1962  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1964  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1967  -> fun uu____1968  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1971  -> fun uu____1972  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____1978 =
             let uu____1982 = FStar_Options.peek () in (e, g, uu____1982) in
           [uu____1978]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1992  -> fun uu____1993  -> fun uu____1994  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____2000  -> fun uu____2001  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____2003  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2005  -> ())
  }
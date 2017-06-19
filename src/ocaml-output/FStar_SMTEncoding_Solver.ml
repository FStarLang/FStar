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
let __proj__Mkhint_stat__item__hint: hint_stat -> FStar_Util.hint option =
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
let recorded_hints: FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None
let replaying_hints: FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None
let hint_stats: hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____134 = FStar_Options.record_hints () in
   if uu____134 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____142 = FStar_Options.use_hints () in
   if uu____142
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____145 = FStar_Util.read_hints val_filename in
     match uu____145 with
     | Some hints ->
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
          FStar_ST.write replaying_hints (Some (hints.FStar_Util.hints)))
     | None  ->
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
                   let uu____189 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____190 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____189 uu____190
               | FStar_Util.Inr _error ->
                   let uu____192 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____193 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____192 uu____193))
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
      let uu____238 = FStar_ST.read replaying_hints in
      match uu____238 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_246  ->
               match uu___84_246 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____250 -> None)
      | uu____252 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___88_264 = h in
             {
               FStar_Util.hint_name = (uu___88_264.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___88_264.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___88_264.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___88_264.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___88_264.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____265 = FStar_ST.read recorded_hints in
    match uu____265 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____279 -> ()
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
          let uu____300 =
            let uu____302 = FStar_ST.read hint_stats in s :: uu____302 in
          FStar_ST.write hint_stats uu____300
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
        | uu____324 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____334 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____340 =
        FStar_List.fold_left
          (fun uu____349  ->
             fun d  ->
               match uu____349 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____370 =
                          matches_fact_ids include_assumption_names a in
                        if uu____370
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____384 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____340 with | (pruned_theory,uu____391) -> pruned_theory
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
            let uu____415 = filter_using_facts_from e theory in
            (uu____415, false)
        | Some core1 ->
            let uu____421 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____431  ->
                     match uu____431 with
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
                          | uu____463 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____421 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____486 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____491 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___85_493  ->
                                         match uu___85_493 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____495 -> false)) in
                               FStar_All.pipe_right uu____491
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____486
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____498 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___86_502  ->
                               match uu___86_502 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____505 -> [])) in
                     FStar_All.pipe_right uu____498
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____508 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____508
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____518 = FStar_Util.string_of_int n_retained in
                     let uu____519 =
                       if n1 <> n_retained
                       then
                         let uu____524 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____524 missed
                       else "" in
                     let uu____532 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____518 uu____519 uu____532
                   else ());
                  (let uu____534 =
                     let uu____536 =
                       let uu____538 =
                         let uu____539 =
                           let uu____540 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____540 in
                         FStar_SMTEncoding_Term.Caption uu____539 in
                       [uu____538] in
                     FStar_List.append theory' uu____536 in
                   (uu____534, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____554 = filter_using_facts_from e x in (uu____554, false)
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
            (let uu____582 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____582 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_638 =
                   match uu___87_638 with
                   | ([],uu____645) -> ()
                   | errs ->
                       let uu____651 = FStar_ST.read minimum_workable_fuel in
                       (match uu____651 with
                        | Some uu____672 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____736 =
                   match uu____736 with
                   | (n1,i,rlimit) ->
                       let uu____745 =
                         let uu____747 =
                           let uu____748 =
                             let uu____749 = FStar_Util.string_of_int n1 in
                             let uu____750 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____749 uu____750 in
                           FStar_SMTEncoding_Term.Caption uu____748 in
                         let uu____751 =
                           let uu____753 =
                             let uu____754 =
                               let uu____758 =
                                 let uu____759 =
                                   let uu____762 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____764 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____762, uu____764) in
                                 FStar_SMTEncoding_Util.mkEq uu____759 in
                               (uu____758, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____754 in
                           let uu____766 =
                             let uu____768 =
                               let uu____769 =
                                 let uu____773 =
                                   let uu____774 =
                                     let uu____777 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____779 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____777, uu____779) in
                                   FStar_SMTEncoding_Util.mkEq uu____774 in
                                 (uu____773, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____769 in
                             [uu____768; p] in
                           uu____753 :: uu____766 in
                         uu____747 :: uu____751 in
                       let uu____781 =
                         let uu____783 =
                           let uu____785 =
                             let uu____787 =
                               let uu____788 =
                                 let uu____791 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____791) in
                               FStar_SMTEncoding_Term.SetOption uu____788 in
                             [uu____787] in
                           let uu____792 =
                             let uu____794 =
                               let uu____796 =
                                 let uu____798 =
                                   FStar_Options.record_hints () in
                                 if uu____798
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____801 =
                                 let uu____803 =
                                   let uu____805 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____805
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____808 =
                                   let uu____810 =
                                     let uu____812 =
                                       FStar_Options.check_hints () in
                                     if uu____812
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____810 suffix in
                                 FStar_List.append uu____803 uu____808 in
                               FStar_List.append uu____796 uu____801 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____794 in
                           FStar_List.append uu____785 uu____792 in
                         FStar_List.append label_assumptions uu____783 in
                       FStar_List.append uu____745 uu____781 in
                 let check p =
                   let rlimit =
                     let uu____820 = FStar_Options.z3_rlimit_factor () in
                     let uu____821 =
                       let uu____822 = FStar_Options.z3_rlimit () in
                       uu____822 * (Prims.parse_int "544656") in
                     uu____820 * uu____821 in
                   let default_initial_config =
                     let uu____827 = FStar_Options.initial_fuel () in
                     let uu____828 = FStar_Options.initial_ifuel () in
                     (uu____827, uu____828, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____831 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____853 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____853 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____831 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____904 =
                           let uu____910 =
                             let uu____916 =
                               let uu____921 =
                                 let uu____922 = FStar_Options.max_ifuel () in
                                 let uu____923 =
                                   FStar_Options.initial_ifuel () in
                                 uu____922 > uu____923 in
                               if uu____921
                               then
                                 let uu____928 =
                                   let uu____932 =
                                     FStar_Options.initial_fuel () in
                                   let uu____933 = FStar_Options.max_ifuel () in
                                   (uu____932, uu____933, rlimit) in
                                 [uu____928]
                               else [] in
                             let uu____944 =
                               let uu____950 =
                                 let uu____955 =
                                   let uu____956 =
                                     let uu____957 =
                                       FStar_Options.max_fuel () in
                                     uu____957 / (Prims.parse_int "2") in
                                   let uu____964 =
                                     FStar_Options.initial_fuel () in
                                   uu____956 > uu____964 in
                                 if uu____955
                                 then
                                   let uu____969 =
                                     let uu____973 =
                                       let uu____974 =
                                         FStar_Options.max_fuel () in
                                       uu____974 / (Prims.parse_int "2") in
                                     let uu____981 =
                                       FStar_Options.max_ifuel () in
                                     (uu____973, uu____981, rlimit) in
                                   [uu____969]
                                 else [] in
                               let uu____992 =
                                 let uu____998 =
                                   let uu____1003 =
                                     (let uu____1004 =
                                        FStar_Options.max_fuel () in
                                      let uu____1005 =
                                        FStar_Options.initial_fuel () in
                                      uu____1004 > uu____1005) &&
                                       (let uu____1006 =
                                          FStar_Options.max_ifuel () in
                                        let uu____1007 =
                                          FStar_Options.initial_ifuel () in
                                        uu____1006 >= uu____1007) in
                                   if uu____1003
                                   then
                                     let uu____1012 =
                                       let uu____1016 =
                                         FStar_Options.max_fuel () in
                                       let uu____1017 =
                                         FStar_Options.max_ifuel () in
                                       (uu____1016, uu____1017, rlimit) in
                                     [uu____1012]
                                   else [] in
                                 let uu____1028 =
                                   let uu____1034 =
                                     let uu____1039 =
                                       let uu____1040 =
                                         FStar_Options.min_fuel () in
                                       let uu____1041 =
                                         FStar_Options.initial_fuel () in
                                       uu____1040 < uu____1041 in
                                     if uu____1039
                                     then
                                       let uu____1046 =
                                         let uu____1050 =
                                           FStar_Options.min_fuel () in
                                         (uu____1050, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1046]
                                     else [] in
                                   [uu____1034] in
                                 uu____998 :: uu____1028 in
                               uu____950 :: uu____992 in
                             uu____916 :: uu____944 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____910 in
                         FStar_List.flatten uu____904 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1114 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1115 = FStar_Options.n_cores () in
                                uu____1115 = (Prims.parse_int "1")) in
                           if uu____1114
                           then
                             let uu____1116 =
                               let uu____1125 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1125 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1190 =
                                     let uu____1194 =
                                       FStar_Options.min_fuel () in
                                     (uu____1194, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1190, errs) in
                             match uu____1116 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1224 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1224 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1230 = FStar_ST.read res in
                                    FStar_Option.get uu____1230) in
                                 let uu____1235 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1235, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1275,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1294 -> errs) in
                         record_hint None;
                         (let uu____1297 = FStar_Options.print_fuels () in
                          if uu____1297
                          then
                            let uu____1298 =
                              let uu____1299 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1299 in
                            let uu____1300 =
                              let uu____1301 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1301
                                FStar_Util.string_of_int in
                            let uu____1302 =
                              let uu____1303 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1303
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1298 uu____1300 uu____1302
                          else ());
                         (let uu____1305 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1317  ->
                                    match uu____1317 with
                                    | (uu____1323,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1305) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1339),uu____1340) -> result
                         | (uu____1345,FStar_Util.Inl uu____1346) -> result
                         | (uu____1353,FStar_Util.Inr uu____1354) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1421) -> report1 p1 errs
                          | (uu____1429,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1440) ->
                              let uu____1455 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1455 (Some scope)
                                (fun uu____1457  ->
                                   match uu____1457 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1469 =
                                         let uu____1473 =
                                           use_errors errs result in
                                         (uu____1473, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1469))
                       and cb used_hint uu____1475 p1 alt scope uu____1479 =
                         match (uu____1475, uu____1479) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1510 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1510))
                              else ();
                              (let uu____1513 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1513
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1532 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1532
                                 then
                                   let uu____1533 =
                                     let uu____1535 =
                                       let uu____1537 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1539 =
                                               let uu____1540 =
                                                 let uu____1541 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1541 in
                                               let uu____1542 =
                                                 let uu____1543 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1543 ")" in
                                               Prims.strcat uu____1540
                                                 uu____1542 in
                                             Prims.strcat "(" uu____1539
                                         | None  -> "" in
                                       let uu____1544 =
                                         let uu____1546 =
                                           let uu____1548 =
                                             let uu____1550 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1551 =
                                               let uu____1553 =
                                                 let uu____1555 =
                                                   let uu____1557 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1558 =
                                                     let uu____1560 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1561 =
                                                       let uu____1563 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1564 =
                                                         let uu____1566 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1566] in
                                                       uu____1563 ::
                                                         uu____1564 in
                                                     uu____1560 :: uu____1561 in
                                                   uu____1557 :: uu____1558 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1555 in
                                               tag :: uu____1553 in
                                             uu____1550 :: uu____1551 in
                                           query_name :: uu____1548 in
                                         name :: uu____1546 in
                                       uu____1537 :: uu____1544 in
                                     let uu____1569 =
                                       let uu____1571 =
                                         let uu____1572 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1572
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1584 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1584 "}"
                                         else
                                           (let uu____1592 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1592 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1595 -> "") in
                                       [uu____1571] in
                                     FStar_List.append uu____1535 uu____1569 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1533
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1615 =
                                     let uu____1616 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1616 in
                                   if uu____1615
                                   then
                                     let hint_check_cb uu____1630 =
                                       match uu____1630 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1653 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1659 ->
                                                 "failed" in
                                           let uu____1664 =
                                             FStar_Options.hint_info () in
                                           if uu____1664
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1668 =
                                         let uu____1673 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1673 in
                                       let uu____1676 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1668
                                         all_labels uu____1676 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1678 =
                                         let uu____1679 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1679 in
                                       if uu____1678
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1686 =
                                             let uu____1687 =
                                               let uu____1689 =
                                                 let uu____1691 =
                                                   let uu____1692 =
                                                     let uu____1693 =
                                                       let uu____1695 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1695] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1693 in
                                                   FStar_Options.String
                                                     uu____1692 in
                                                 [uu____1691] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1689 in
                                             FStar_Options.List uu____1687 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1686);
                                          (let hint_refinement_cb uu____1707
                                             =
                                             match uu____1707 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1729 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1729
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1740 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1740))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1749 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1749
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1751 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1751
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1756 =
                                                     let uu____1758 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1758] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1756);
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
                                  (let uu____1773 =
                                     let uu____1774 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1774 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1773);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1777 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1777;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1784 =
                                       let uu____1786 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1786
                                       then
                                         let uu____1788 =
                                           let uu____1789 =
                                             FStar_Options.check_hints () in
                                           if uu____1789
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
                                         Some uu____1788
                                       else hint_opt in
                                     record_hint uu____1784))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1795 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1795
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1802 =
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
                       ((let uu____1808 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1808
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1813 =
                           let uu____1814 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1814 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1813)) in
                 let process_query q = check q in
                 let uu____1822 = FStar_Options.admit_smt_queries () in
                 if uu____1822 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1844 =
           let uu____1845 =
             let uu____1846 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1846 in
           FStar_Util.format1 "Starting query at %s" uu____1845 in
         FStar_SMTEncoding_Encode.push uu____1844);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1848 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1848 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1869 =
               let uu____1870 =
                 let uu____1871 =
                   let uu____1872 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1872 in
                 FStar_Util.format1 "Ending query at %s" uu____1871 in
               FStar_SMTEncoding_Encode.pop uu____1870 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1873);
                        FStar_SMTEncoding_Term.freevars = uu____1874;
                        FStar_SMTEncoding_Term.rng = uu____1875;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1876;
                    FStar_SMTEncoding_Term.assumption_name = uu____1877;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1878;_}
                  -> pop1 ()
              | uu____1886 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1887 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1889 -> failwith "Impossible"))
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
           let uu____1892 =
             let uu____1896 = FStar_Options.peek () in (e, g, uu____1896) in
           [uu____1892]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1903  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1904  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1905  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1906  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1907  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1908  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1909  -> fun uu____1910  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1911  -> fun uu____1912  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____1915 =
             let uu____1919 = FStar_Options.peek () in (e, g, uu____1919) in
           [uu____1915]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1926  -> fun uu____1927  -> fun uu____1928  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1932  -> fun uu____1933  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1934  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1935  -> ())
  }
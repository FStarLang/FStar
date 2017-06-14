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
  (let uu____122 = FStar_Options.record_hints () in
   if uu____122 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____130 = FStar_Options.use_hints () in
   if uu____130
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename in
     let val_filename = format_hints_file_name norm_src_filename in
     let uu____133 = FStar_Util.read_hints val_filename in
     match uu____133 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename in
         ((let uu____138 = FStar_Options.hint_info () in
           if uu____138
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
         let uu____144 = FStar_Options.hint_info () in
         (if uu____144
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____151 = FStar_Options.record_hints () in
     if uu____151
     then
       let hints =
         let uu____153 = FStar_ST.read recorded_hints in
         FStar_Option.get uu____153 in
       let hints_db =
         let uu____159 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____159; FStar_Util.hints = hints } in
       let hints_file_name = format_hints_file_name src_filename in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____163 = FStar_Options.hint_info () in
     if uu____163
     then
       let stats =
         let uu____166 = FStar_ST.read hint_stats in
         FStar_All.pipe_right uu____166 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____176 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____177 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____176 uu____177
               | FStar_Util.Inr _error ->
                   let uu____179 =
                     FStar_Range.string_of_range s.source_location in
                   let uu____180 = FStar_Util.string_of_int s.elapsed_time in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____179 uu____180))
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
      let uu____220 = FStar_ST.read replaying_hints in
      match uu____220 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_228  ->
               match uu___84_228 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____232 -> None)
      | uu____234 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___88_245 = h in
             {
               FStar_Util.hint_name = (uu___88_245.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___88_245.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___88_245.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___88_245.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___88_245.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____246 = FStar_ST.read recorded_hints in
    match uu____246 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____260 -> ()
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
          let uu____277 =
            let uu____279 = FStar_ST.read hint_stats in s :: uu____279 in
          FStar_ST.write hint_stats uu____277
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
        | uu____299 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____309 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____315 =
        FStar_List.fold_left
          (fun uu____324  ->
             fun d  ->
               match uu____324 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____345 =
                          matches_fact_ids include_assumption_names a in
                        if uu____345
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____359 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____315 with | (pruned_theory,uu____366) -> pruned_theory
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
            let uu____387 = filter_using_facts_from e theory in
            (uu____387, false)
        | Some core1 ->
            let uu____393 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____403  ->
                     match uu____403 with
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
                          | uu____435 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____393 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____458 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____463 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___85_465  ->
                                         match uu___85_465 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____467 -> false)) in
                               FStar_All.pipe_right uu____463
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____458
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____470 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___86_474  ->
                               match uu___86_474 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____477 -> [])) in
                     FStar_All.pipe_right uu____470
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____480 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____480
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____490 = FStar_Util.string_of_int n_retained in
                     let uu____491 =
                       if n1 <> n_retained
                       then
                         let uu____496 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____496 missed
                       else "" in
                     let uu____504 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____490 uu____491 uu____504
                   else ());
                  (let uu____506 =
                     let uu____508 =
                       let uu____510 =
                         let uu____511 =
                           let uu____512 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____512 in
                         FStar_SMTEncoding_Term.Caption uu____511 in
                       [uu____510] in
                     FStar_List.append theory' uu____508 in
                   (uu____506, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____524 = filter_using_facts_from e x in (uu____524, false)
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
            (let uu____547 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____547 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_603 =
                   match uu___87_603 with
                   | ([],uu____610) -> ()
                   | errs ->
                       let uu____616 = FStar_ST.read minimum_workable_fuel in
                       (match uu____616 with
                        | Some uu____637 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____701 =
                   match uu____701 with
                   | (n1,i,rlimit) ->
                       let uu____710 =
                         let uu____712 =
                           let uu____713 =
                             let uu____714 = FStar_Util.string_of_int n1 in
                             let uu____715 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____714 uu____715 in
                           FStar_SMTEncoding_Term.Caption uu____713 in
                         let uu____716 =
                           let uu____718 =
                             let uu____719 =
                               let uu____723 =
                                 let uu____724 =
                                   let uu____727 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____729 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____727, uu____729) in
                                 FStar_SMTEncoding_Util.mkEq uu____724 in
                               (uu____723, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____719 in
                           let uu____731 =
                             let uu____733 =
                               let uu____734 =
                                 let uu____738 =
                                   let uu____739 =
                                     let uu____742 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____744 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____742, uu____744) in
                                   FStar_SMTEncoding_Util.mkEq uu____739 in
                                 (uu____738, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____734 in
                             [uu____733; p] in
                           uu____718 :: uu____731 in
                         uu____712 :: uu____716 in
                       let uu____746 =
                         let uu____748 =
                           let uu____750 =
                             let uu____752 =
                               let uu____753 =
                                 let uu____756 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____756) in
                               FStar_SMTEncoding_Term.SetOption uu____753 in
                             [uu____752] in
                           let uu____757 =
                             let uu____759 =
                               let uu____761 =
                                 let uu____763 =
                                   FStar_Options.record_hints () in
                                 if uu____763
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____766 =
                                 let uu____768 =
                                   let uu____770 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____770
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____773 =
                                   let uu____775 =
                                     let uu____777 =
                                       FStar_Options.check_hints () in
                                     if uu____777
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____775 suffix in
                                 FStar_List.append uu____768 uu____773 in
                               FStar_List.append uu____761 uu____766 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____759 in
                           FStar_List.append uu____750 uu____757 in
                         FStar_List.append label_assumptions uu____748 in
                       FStar_List.append uu____710 uu____746 in
                 let check p =
                   let rlimit =
                     let uu____785 = FStar_Options.z3_rlimit_factor () in
                     let uu____786 =
                       let uu____787 = FStar_Options.z3_rlimit () in
                       uu____787 * (Prims.parse_int "544656") in
                     uu____785 * uu____786 in
                   let default_initial_config =
                     let uu____792 = FStar_Options.initial_fuel () in
                     let uu____793 = FStar_Options.initial_ifuel () in
                     (uu____792, uu____793, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____796 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____818 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____818 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____796 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____869 =
                           let uu____875 =
                             let uu____881 =
                               let uu____886 =
                                 let uu____887 = FStar_Options.max_ifuel () in
                                 let uu____888 =
                                   FStar_Options.initial_ifuel () in
                                 uu____887 > uu____888 in
                               if uu____886
                               then
                                 let uu____893 =
                                   let uu____897 =
                                     FStar_Options.initial_fuel () in
                                   let uu____898 = FStar_Options.max_ifuel () in
                                   (uu____897, uu____898, rlimit) in
                                 [uu____893]
                               else [] in
                             let uu____909 =
                               let uu____915 =
                                 let uu____920 =
                                   let uu____921 =
                                     let uu____922 =
                                       FStar_Options.max_fuel () in
                                     uu____922 / (Prims.parse_int "2") in
                                   let uu____929 =
                                     FStar_Options.initial_fuel () in
                                   uu____921 > uu____929 in
                                 if uu____920
                                 then
                                   let uu____934 =
                                     let uu____938 =
                                       let uu____939 =
                                         FStar_Options.max_fuel () in
                                       uu____939 / (Prims.parse_int "2") in
                                     let uu____946 =
                                       FStar_Options.max_ifuel () in
                                     (uu____938, uu____946, rlimit) in
                                   [uu____934]
                                 else [] in
                               let uu____957 =
                                 let uu____963 =
                                   let uu____968 =
                                     (let uu____969 =
                                        FStar_Options.max_fuel () in
                                      let uu____970 =
                                        FStar_Options.initial_fuel () in
                                      uu____969 > uu____970) &&
                                       (let uu____971 =
                                          FStar_Options.max_ifuel () in
                                        let uu____972 =
                                          FStar_Options.initial_ifuel () in
                                        uu____971 >= uu____972) in
                                   if uu____968
                                   then
                                     let uu____977 =
                                       let uu____981 =
                                         FStar_Options.max_fuel () in
                                       let uu____982 =
                                         FStar_Options.max_ifuel () in
                                       (uu____981, uu____982, rlimit) in
                                     [uu____977]
                                   else [] in
                                 let uu____993 =
                                   let uu____999 =
                                     let uu____1004 =
                                       let uu____1005 =
                                         FStar_Options.min_fuel () in
                                       let uu____1006 =
                                         FStar_Options.initial_fuel () in
                                       uu____1005 < uu____1006 in
                                     if uu____1004
                                     then
                                       let uu____1011 =
                                         let uu____1015 =
                                           FStar_Options.min_fuel () in
                                         (uu____1015, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1011]
                                     else [] in
                                   [uu____999] in
                                 uu____963 :: uu____993 in
                               uu____915 :: uu____957 in
                             uu____881 :: uu____909 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____875 in
                         FStar_List.flatten uu____869 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1079 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1080 = FStar_Options.n_cores () in
                                uu____1080 = (Prims.parse_int "1")) in
                           if uu____1079
                           then
                             let uu____1081 =
                               let uu____1090 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1090 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1155 =
                                     let uu____1159 =
                                       FStar_Options.min_fuel () in
                                     (uu____1159, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1155, errs) in
                             match uu____1081 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1189 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1189 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1195 = FStar_ST.read res in
                                    FStar_Option.get uu____1195) in
                                 let uu____1200 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1200, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1240,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1259 -> errs) in
                         record_hint None;
                         (let uu____1262 = FStar_Options.print_fuels () in
                          if uu____1262
                          then
                            let uu____1263 =
                              let uu____1264 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1264 in
                            let uu____1265 =
                              let uu____1266 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1266
                                FStar_Util.string_of_int in
                            let uu____1267 =
                              let uu____1268 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1268
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1263 uu____1265 uu____1267
                          else ());
                         (let uu____1270 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1282  ->
                                    match uu____1282 with
                                    | (uu____1288,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1270) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1304),uu____1305) -> result
                         | (uu____1310,FStar_Util.Inl uu____1311) -> result
                         | (uu____1318,FStar_Util.Inr uu____1319) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1386) -> report1 p1 errs
                          | (uu____1394,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1405) ->
                              let uu____1420 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1420 (Some scope)
                                (fun uu____1422  ->
                                   match uu____1422 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1434 =
                                         let uu____1438 =
                                           use_errors errs result in
                                         (uu____1438, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1434))
                       and cb used_hint uu____1440 p1 alt scope uu____1444 =
                         match (uu____1440, uu____1444) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1475 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1475))
                              else ();
                              (let uu____1478 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1478
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1497 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1497
                                 then
                                   let uu____1498 =
                                     let uu____1500 =
                                       let uu____1502 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1504 =
                                               let uu____1505 =
                                                 let uu____1506 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1506 in
                                               let uu____1507 =
                                                 let uu____1508 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1508 ")" in
                                               Prims.strcat uu____1505
                                                 uu____1507 in
                                             Prims.strcat "(" uu____1504
                                         | None  -> "" in
                                       let uu____1509 =
                                         let uu____1511 =
                                           let uu____1513 =
                                             let uu____1515 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1516 =
                                               let uu____1518 =
                                                 let uu____1520 =
                                                   let uu____1522 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1523 =
                                                     let uu____1525 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1526 =
                                                       let uu____1528 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1529 =
                                                         let uu____1531 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1531] in
                                                       uu____1528 ::
                                                         uu____1529 in
                                                     uu____1525 :: uu____1526 in
                                                   uu____1522 :: uu____1523 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1520 in
                                               tag :: uu____1518 in
                                             uu____1515 :: uu____1516 in
                                           query_name :: uu____1513 in
                                         name :: uu____1511 in
                                       uu____1502 :: uu____1509 in
                                     let uu____1534 =
                                       let uu____1536 =
                                         let uu____1537 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1537
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1549 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1549 "}"
                                         else
                                           (let uu____1557 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1557 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1560 -> "") in
                                       [uu____1536] in
                                     FStar_List.append uu____1500 uu____1534 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1498
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1580 =
                                     let uu____1581 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1581 in
                                   if uu____1580
                                   then
                                     let hint_check_cb uu____1595 =
                                       match uu____1595 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1618 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1624 ->
                                                 "failed" in
                                           let uu____1629 =
                                             FStar_Options.hint_info () in
                                           if uu____1629
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1633 =
                                         let uu____1638 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1638 in
                                       let uu____1641 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1633
                                         all_labels uu____1641 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1643 =
                                         let uu____1644 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1644 in
                                       if uu____1643
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1651 =
                                             let uu____1652 =
                                               let uu____1654 =
                                                 let uu____1656 =
                                                   let uu____1657 =
                                                     let uu____1658 =
                                                       let uu____1660 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1660] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1658 in
                                                   FStar_Options.String
                                                     uu____1657 in
                                                 [uu____1656] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1654 in
                                             FStar_Options.List uu____1652 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1651);
                                          (let hint_refinement_cb uu____1672
                                             =
                                             match uu____1672 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1694 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1694
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1705 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1705))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1714 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1714
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1716 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1716
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1721 =
                                                     let uu____1723 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1723] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1721);
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
                                  (let uu____1738 =
                                     let uu____1739 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1739 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1738);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1742 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1742;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1749 =
                                       let uu____1751 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1751
                                       then
                                         let uu____1753 =
                                           let uu____1754 =
                                             FStar_Options.check_hints () in
                                           if uu____1754
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
                                         Some uu____1753
                                       else hint_opt in
                                     record_hint uu____1749))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1760 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1760
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1767 =
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
                       ((let uu____1773 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1773
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1778 =
                           let uu____1779 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1779 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1778)) in
                 let process_query q = check q in
                 let uu____1787 = FStar_Options.admit_smt_queries () in
                 if uu____1787 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1806 =
           let uu____1807 =
             let uu____1808 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1808 in
           FStar_Util.format1 "Starting query at %s" uu____1807 in
         FStar_SMTEncoding_Encode.push uu____1806);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1810 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1810 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1831 =
               let uu____1832 =
                 let uu____1833 =
                   let uu____1834 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1834 in
                 FStar_Util.format1 "Ending query at %s" uu____1833 in
               FStar_SMTEncoding_Encode.pop uu____1832 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1835);
                        FStar_SMTEncoding_Term.freevars = uu____1836;
                        FStar_SMTEncoding_Term.rng = uu____1837;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1838;
                    FStar_SMTEncoding_Term.assumption_name = uu____1839;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1840;_}
                  -> pop1 ()
              | uu____1848 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1849 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1851 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1858  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1859  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1860  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1861  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1862  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1863  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1864  -> fun uu____1865  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1866  -> fun uu____1867  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1874  -> fun uu____1875  -> fun uu____1876  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1880  -> fun uu____1881  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1882  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1883  -> ())
  }
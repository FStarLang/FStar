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
let next_hint: Prims.string -> Prims.int -> FStar_Util.hint option =
  fun qname  ->
    fun qindex  ->
      let uu____200 = FStar_ST.read replaying_hints in
      match uu____200 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___84_208  ->
               match uu___84_208 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____212 -> None)
      | uu____214 -> None
let record_hint: FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___88_225 = h in
             {
               FStar_Util.hint_name = (uu___88_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___88_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___88_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___88_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___88_225.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____226 = FStar_ST.read recorded_hints in
    match uu____226 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____240 -> ()
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
          let uu____257 =
            let uu____259 = FStar_ST.read hint_stats in s :: uu____259 in
          FStar_ST.write hint_stats uu____257
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
        | uu____279 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____289 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____295 =
        FStar_List.fold_left
          (fun uu____304  ->
             fun d  ->
               match uu____304 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____325 =
                          matches_fact_ids include_assumption_names a in
                        if uu____325
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names ->
                        ((d :: out),
                          (FStar_List.append names include_assumption_names))
                    | uu____339 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____295 with | (pruned_theory,uu____346) -> pruned_theory
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
            let uu____367 = filter_using_facts_from e theory in
            (uu____367, false)
        | Some core1 ->
            let uu____373 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____383  ->
                     match uu____383 with
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
                          | uu____415 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____373 with
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
                                      (fun uu___85_445  ->
                                         match uu___85_445 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____447 -> false)) in
                               FStar_All.pipe_right uu____443
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____438
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____450 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___86_454  ->
                               match uu___86_454 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____457 -> [])) in
                     FStar_All.pipe_right uu____450
                       (FStar_String.concat ", ") in
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
                     let uu____470 = FStar_Util.string_of_int n_retained in
                     let uu____471 =
                       if n1 <> n_retained
                       then
                         let uu____476 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____476 missed
                       else "" in
                     let uu____484 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____470 uu____471 uu____484
                   else ());
                  (let uu____486 =
                     let uu____488 =
                       let uu____490 =
                         let uu____491 =
                           let uu____492 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____492 in
                         FStar_SMTEncoding_Term.Caption uu____491 in
                       [uu____490] in
                     FStar_List.append theory' uu____488 in
                   (uu____486, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____504 = filter_using_facts_from e x in (uu____504, false)
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
            (let uu____527 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____527 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_583 =
                   match uu___87_583 with
                   | ([],uu____590) -> ()
                   | errs ->
                       let uu____596 = FStar_ST.read minimum_workable_fuel in
                       (match uu____596 with
                        | Some uu____617 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____681 =
                   match uu____681 with
                   | (n1,i,rlimit) ->
                       let uu____690 =
                         let uu____692 =
                           let uu____693 =
                             let uu____694 = FStar_Util.string_of_int n1 in
                             let uu____695 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____694 uu____695 in
                           FStar_SMTEncoding_Term.Caption uu____693 in
                         let uu____696 =
                           let uu____698 =
                             let uu____699 =
                               let uu____703 =
                                 let uu____704 =
                                   let uu____707 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____709 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____707, uu____709) in
                                 FStar_SMTEncoding_Util.mkEq uu____704 in
                               (uu____703, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____699 in
                           let uu____711 =
                             let uu____713 =
                               let uu____714 =
                                 let uu____718 =
                                   let uu____719 =
                                     let uu____722 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____724 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____722, uu____724) in
                                   FStar_SMTEncoding_Util.mkEq uu____719 in
                                 (uu____718, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____714 in
                             [uu____713; p] in
                           uu____698 :: uu____711 in
                         uu____692 :: uu____696 in
                       let uu____726 =
                         let uu____728 =
                           let uu____730 =
                             let uu____732 =
                               let uu____733 =
                                 let uu____736 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____736) in
                               FStar_SMTEncoding_Term.SetOption uu____733 in
                             [uu____732] in
                           let uu____737 =
                             let uu____739 =
                               let uu____741 =
                                 let uu____743 =
                                   FStar_Options.record_hints () in
                                 if uu____743
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____746 =
                                 let uu____748 =
                                   let uu____750 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____750
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____753 =
                                   let uu____755 =
                                     let uu____757 =
                                       FStar_Options.check_hints () in
                                     if uu____757
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____755 suffix in
                                 FStar_List.append uu____748 uu____753 in
                               FStar_List.append uu____741 uu____746 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____739 in
                           FStar_List.append uu____730 uu____737 in
                         FStar_List.append label_assumptions uu____728 in
                       FStar_List.append uu____690 uu____726 in
                 let check p =
                   let rlimit =
                     let uu____765 = FStar_Options.z3_rlimit_factor () in
                     let uu____766 =
                       let uu____767 = FStar_Options.z3_rlimit () in
                       uu____767 * (Prims.parse_int "544656") in
                     uu____765 * uu____766 in
                   let default_initial_config =
                     let uu____772 = FStar_Options.initial_fuel () in
                     let uu____773 = FStar_Options.initial_ifuel () in
                     (uu____772, uu____773, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____776 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____798 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____798 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____776 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____849 =
                           let uu____855 =
                             let uu____861 =
                               let uu____866 =
                                 let uu____867 = FStar_Options.max_ifuel () in
                                 let uu____868 =
                                   FStar_Options.initial_ifuel () in
                                 uu____867 > uu____868 in
                               if uu____866
                               then
                                 let uu____873 =
                                   let uu____877 =
                                     FStar_Options.initial_fuel () in
                                   let uu____878 = FStar_Options.max_ifuel () in
                                   (uu____877, uu____878, rlimit) in
                                 [uu____873]
                               else [] in
                             let uu____889 =
                               let uu____895 =
                                 let uu____900 =
                                   let uu____901 =
                                     let uu____902 =
                                       FStar_Options.max_fuel () in
                                     uu____902 / (Prims.parse_int "2") in
                                   let uu____909 =
                                     FStar_Options.initial_fuel () in
                                   uu____901 > uu____909 in
                                 if uu____900
                                 then
                                   let uu____914 =
                                     let uu____918 =
                                       let uu____919 =
                                         FStar_Options.max_fuel () in
                                       uu____919 / (Prims.parse_int "2") in
                                     let uu____926 =
                                       FStar_Options.max_ifuel () in
                                     (uu____918, uu____926, rlimit) in
                                   [uu____914]
                                 else [] in
                               let uu____937 =
                                 let uu____943 =
                                   let uu____948 =
                                     (let uu____949 =
                                        FStar_Options.max_fuel () in
                                      let uu____950 =
                                        FStar_Options.initial_fuel () in
                                      uu____949 > uu____950) &&
                                       (let uu____951 =
                                          FStar_Options.max_ifuel () in
                                        let uu____952 =
                                          FStar_Options.initial_ifuel () in
                                        uu____951 >= uu____952) in
                                   if uu____948
                                   then
                                     let uu____957 =
                                       let uu____961 =
                                         FStar_Options.max_fuel () in
                                       let uu____962 =
                                         FStar_Options.max_ifuel () in
                                       (uu____961, uu____962, rlimit) in
                                     [uu____957]
                                   else [] in
                                 let uu____973 =
                                   let uu____979 =
                                     let uu____984 =
                                       let uu____985 =
                                         FStar_Options.min_fuel () in
                                       let uu____986 =
                                         FStar_Options.initial_fuel () in
                                       uu____985 < uu____986 in
                                     if uu____984
                                     then
                                       let uu____991 =
                                         let uu____995 =
                                           FStar_Options.min_fuel () in
                                         (uu____995, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____991]
                                     else [] in
                                   [uu____979] in
                                 uu____943 :: uu____973 in
                               uu____895 :: uu____937 in
                             uu____861 :: uu____889 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____855 in
                         FStar_List.flatten uu____849 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1059 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1060 = FStar_Options.n_cores () in
                                uu____1060 = (Prims.parse_int "1")) in
                           if uu____1059
                           then
                             let uu____1061 =
                               let uu____1070 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1070 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1135 =
                                     let uu____1139 =
                                       FStar_Options.min_fuel () in
                                     (uu____1139, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1135, errs) in
                             match uu____1061 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1169 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1169 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1175 = FStar_ST.read res in
                                    FStar_Option.get uu____1175) in
                                 let uu____1180 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1180, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1220,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1239 -> errs) in
                         record_hint None;
                         (let uu____1242 = FStar_Options.print_fuels () in
                          if uu____1242
                          then
                            let uu____1243 =
                              let uu____1244 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1244 in
                            let uu____1245 =
                              let uu____1246 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1246
                                FStar_Util.string_of_int in
                            let uu____1247 =
                              let uu____1248 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1248
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1243 uu____1245 uu____1247
                          else ());
                         (let uu____1250 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1262  ->
                                    match uu____1262 with
                                    | (uu____1268,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1250) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1284),uu____1285) -> result
                         | (uu____1290,FStar_Util.Inl uu____1291) -> result
                         | (uu____1298,FStar_Util.Inr uu____1299) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1366) -> report1 p1 errs
                          | (uu____1374,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1385) ->
                              let uu____1400 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1400 (Some scope)
                                (fun uu____1402  ->
                                   match uu____1402 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1414 =
                                         let uu____1418 =
                                           use_errors errs result in
                                         (uu____1418, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1414))
                       and cb used_hint uu____1420 p1 alt scope uu____1424 =
                         match (uu____1420, uu____1424) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1455 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1455))
                              else ();
                              (let uu____1458 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1458
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1477 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1477
                                 then
                                   let uu____1478 =
                                     let uu____1480 =
                                       let uu____1482 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1484 =
                                               let uu____1485 =
                                                 let uu____1486 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1486 in
                                               let uu____1487 =
                                                 let uu____1488 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1488 ")" in
                                               Prims.strcat uu____1485
                                                 uu____1487 in
                                             Prims.strcat "(" uu____1484
                                         | None  -> "" in
                                       let uu____1489 =
                                         let uu____1491 =
                                           let uu____1493 =
                                             let uu____1495 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1496 =
                                               let uu____1498 =
                                                 let uu____1500 =
                                                   let uu____1502 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1503 =
                                                     let uu____1505 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1506 =
                                                       let uu____1508 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1509 =
                                                         let uu____1511 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1511] in
                                                       uu____1508 ::
                                                         uu____1509 in
                                                     uu____1505 :: uu____1506 in
                                                   uu____1502 :: uu____1503 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1500 in
                                               tag :: uu____1498 in
                                             uu____1495 :: uu____1496 in
                                           query_name :: uu____1493 in
                                         name :: uu____1491 in
                                       uu____1482 :: uu____1489 in
                                     let uu____1514 =
                                       let uu____1516 =
                                         let uu____1517 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1517
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1529 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1529 "}"
                                         else
                                           (let uu____1537 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1537 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1540 -> "") in
                                       [uu____1516] in
                                     FStar_List.append uu____1480 uu____1514 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1478
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1560 =
                                     let uu____1561 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1561 in
                                   if uu____1560
                                   then
                                     let hint_check_cb uu____1575 =
                                       match uu____1575 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1598 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1604 ->
                                                 "failed" in
                                           let uu____1609 =
                                             FStar_Options.hint_info () in
                                           if uu____1609
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1613 =
                                         let uu____1618 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1618 in
                                       let uu____1621 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1613
                                         all_labels uu____1621 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1623 =
                                         let uu____1624 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1624 in
                                       if uu____1623
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1631 =
                                             let uu____1632 =
                                               let uu____1634 =
                                                 let uu____1636 =
                                                   let uu____1637 =
                                                     let uu____1638 =
                                                       let uu____1640 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1640] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1638 in
                                                   FStar_Options.String
                                                     uu____1637 in
                                                 [uu____1636] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1634 in
                                             FStar_Options.List uu____1632 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1631);
                                          (let hint_refinement_cb uu____1652
                                             =
                                             match uu____1652 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1674 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1674
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1685 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1685))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1694 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1694
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1696 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1696
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1701 =
                                                     let uu____1703 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1703] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1701);
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
                                  (let uu____1718 =
                                     let uu____1719 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1719 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1718);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1722 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1722;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1729 =
                                       let uu____1731 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1731
                                       then
                                         let uu____1733 =
                                           let uu____1734 =
                                             FStar_Options.check_hints () in
                                           if uu____1734
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
                                         Some uu____1733
                                       else hint_opt in
                                     record_hint uu____1729))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1740 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1740
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1747 =
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
                       ((let uu____1753 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1753
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1758 =
                           let uu____1759 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1759 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1758)) in
                 let process_query q = check q in
                 let uu____1767 = FStar_Options.admit_smt_queries () in
                 if uu____1767 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1786 =
           let uu____1787 =
             let uu____1788 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1788 in
           FStar_Util.format1 "Starting query at %s" uu____1787 in
         FStar_SMTEncoding_Encode.push uu____1786);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1790 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1790 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1811 =
               let uu____1812 =
                 let uu____1813 =
                   let uu____1814 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1814 in
                 FStar_Util.format1 "Ending query at %s" uu____1813 in
               FStar_SMTEncoding_Encode.pop uu____1812 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1815);
                        FStar_SMTEncoding_Term.freevars = uu____1816;
                        FStar_SMTEncoding_Term.rng = uu____1817;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1818;
                    FStar_SMTEncoding_Term.assumption_name = uu____1819;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1820;_}
                  -> pop1 ()
              | uu____1828 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1829 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1831 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1838  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1839  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1840  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1841  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1842  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1843  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1844  -> fun uu____1845  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1846  -> fun uu____1847  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1854  -> fun uu____1855  -> fun uu____1856  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1860  -> fun uu____1861  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1862  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1863  -> ())
  }
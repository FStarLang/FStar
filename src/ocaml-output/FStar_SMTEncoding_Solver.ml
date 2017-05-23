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
            (fun uu___84_208  ->
               match uu___84_208 with
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
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list* Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____496 = filter_using_facts_from e x in (uu____496, false)
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
            (let uu____519 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1) in
             match uu____519 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None in
                 let set_minimum_workable_fuel f uu___87_575 =
                   match uu___87_575 with
                   | ([],uu____582) -> ()
                   | errs ->
                       let uu____588 = FStar_ST.read minimum_workable_fuel in
                       (match uu____588 with
                        | Some uu____609 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs))) in
                 let with_fuel label_assumptions p uu____673 =
                   match uu____673 with
                   | (n1,i,rlimit) ->
                       let uu____682 =
                         let uu____684 =
                           let uu____685 =
                             let uu____686 = FStar_Util.string_of_int n1 in
                             let uu____687 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____686 uu____687 in
                           FStar_SMTEncoding_Term.Caption uu____685 in
                         let uu____688 =
                           let uu____690 =
                             let uu____691 =
                               let uu____695 =
                                 let uu____696 =
                                   let uu____699 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____701 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____699, uu____701) in
                                 FStar_SMTEncoding_Util.mkEq uu____696 in
                               (uu____695, None, "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____691 in
                           let uu____703 =
                             let uu____705 =
                               let uu____706 =
                                 let uu____710 =
                                   let uu____711 =
                                     let uu____714 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____716 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____714, uu____716) in
                                   FStar_SMTEncoding_Util.mkEq uu____711 in
                                 (uu____710, None, "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____706 in
                             [uu____705; p] in
                           uu____690 :: uu____703 in
                         uu____684 :: uu____688 in
                       let uu____718 =
                         let uu____720 =
                           let uu____722 =
                             let uu____724 =
                               let uu____725 =
                                 let uu____728 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____728) in
                               FStar_SMTEncoding_Term.SetOption uu____725 in
                             [uu____724] in
                           let uu____729 =
                             let uu____731 =
                               let uu____733 =
                                 let uu____735 =
                                   FStar_Options.record_hints () in
                                 if uu____735
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____738 =
                                 let uu____740 =
                                   let uu____742 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____742
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else [] in
                                 let uu____745 =
                                   let uu____747 =
                                     let uu____749 =
                                       FStar_Options.check_hints () in
                                     if uu____749
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else [] in
                                   FStar_List.append uu____747 suffix in
                                 FStar_List.append uu____740 uu____745 in
                               FStar_List.append uu____733 uu____738 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____731 in
                           FStar_List.append uu____722 uu____729 in
                         FStar_List.append label_assumptions uu____720 in
                       FStar_List.append uu____682 uu____718 in
                 let check p =
                   let rlimit =
                     let uu____757 = FStar_Options.z3_rlimit_factor () in
                     let uu____758 =
                       let uu____759 = FStar_Options.z3_rlimit () in
                       uu____759 * (Prims.parse_int "544656") in
                     uu____757 * uu____758 in
                   let default_initial_config =
                     let uu____764 = FStar_Options.initial_fuel () in
                     let uu____765 = FStar_Options.initial_ifuel () in
                     (uu____764, uu____765, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____768 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____790 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____790 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____768 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____841 =
                           let uu____847 =
                             let uu____853 =
                               let uu____858 =
                                 let uu____859 = FStar_Options.max_ifuel () in
                                 let uu____860 =
                                   FStar_Options.initial_ifuel () in
                                 uu____859 > uu____860 in
                               if uu____858
                               then
                                 let uu____865 =
                                   let uu____869 =
                                     FStar_Options.initial_fuel () in
                                   let uu____870 = FStar_Options.max_ifuel () in
                                   (uu____869, uu____870, rlimit) in
                                 [uu____865]
                               else [] in
                             let uu____881 =
                               let uu____887 =
                                 let uu____892 =
                                   let uu____893 =
                                     let uu____894 =
                                       FStar_Options.max_fuel () in
                                     uu____894 / (Prims.parse_int "2") in
                                   let uu____898 =
                                     FStar_Options.initial_fuel () in
                                   uu____893 > uu____898 in
                                 if uu____892
                                 then
                                   let uu____903 =
                                     let uu____907 =
                                       let uu____908 =
                                         FStar_Options.max_fuel () in
                                       uu____908 / (Prims.parse_int "2") in
                                     let uu____912 =
                                       FStar_Options.max_ifuel () in
                                     (uu____907, uu____912, rlimit) in
                                   [uu____903]
                                 else [] in
                               let uu____923 =
                                 let uu____929 =
                                   let uu____934 =
                                     (let uu____935 =
                                        FStar_Options.max_fuel () in
                                      let uu____936 =
                                        FStar_Options.initial_fuel () in
                                      uu____935 > uu____936) &&
                                       (let uu____937 =
                                          FStar_Options.max_ifuel () in
                                        let uu____938 =
                                          FStar_Options.initial_ifuel () in
                                        uu____937 >= uu____938) in
                                   if uu____934
                                   then
                                     let uu____943 =
                                       let uu____947 =
                                         FStar_Options.max_fuel () in
                                       let uu____948 =
                                         FStar_Options.max_ifuel () in
                                       (uu____947, uu____948, rlimit) in
                                     [uu____943]
                                   else [] in
                                 let uu____959 =
                                   let uu____965 =
                                     let uu____970 =
                                       let uu____971 =
                                         FStar_Options.min_fuel () in
                                       let uu____972 =
                                         FStar_Options.initial_fuel () in
                                       uu____971 < uu____972 in
                                     if uu____970
                                     then
                                       let uu____977 =
                                         let uu____981 =
                                           FStar_Options.min_fuel () in
                                         (uu____981, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____977]
                                     else [] in
                                   [uu____965] in
                                 uu____929 :: uu____959 in
                               uu____887 :: uu____923 in
                             uu____853 :: uu____881 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____847 in
                         FStar_List.flatten uu____841 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1045 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1046 = FStar_Options.n_cores () in
                                uu____1046 = (Prims.parse_int "1")) in
                           if uu____1045
                           then
                             let uu____1047 =
                               let uu____1056 =
                                 FStar_ST.read minimum_workable_fuel in
                               match uu____1056 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1121 =
                                     let uu____1125 =
                                       FStar_Options.min_fuel () in
                                     (uu____1125, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____1121, errs) in
                             match uu____1047 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None in
                                   (let uu____1155 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1155 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1161 = FStar_ST.read res in
                                    FStar_Option.get uu____1161) in
                                 let uu____1166 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3 in
                                 (uu____1166, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1206,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (Prims.snd errs))
                              | uu____1225 -> errs) in
                         record_hint None;
                         (let uu____1228 = FStar_Options.print_fuels () in
                          if uu____1228
                          then
                            let uu____1229 =
                              let uu____1230 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____1230 in
                            let uu____1231 =
                              let uu____1232 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____1232
                                FStar_Util.string_of_int in
                            let uu____1233 =
                              let uu____1234 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____1234
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1229 uu____1231 uu____1233
                          else ());
                         (let uu____1236 =
                            FStar_All.pipe_right (Prims.fst errs1)
                              (FStar_List.map
                                 (fun uu____1248  ->
                                    match uu____1248 with
                                    | (uu____1254,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____1236) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____1282,FStar_Util.Inr uu____1283) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1365) ->
                              let uu____1380 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1380 (Some scope)
                                (fun uu____1382  ->
                                   match uu____1382 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1394 =
                                         let uu____1398 =
                                           use_errors errs result in
                                         (uu____1398, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____1394))
                       and cb used_hint uu____1400 p1 alt scope uu____1404 =
                         match (uu____1400, uu____1404) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1435 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1435))
                              else ();
                              (let uu____1438 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____1438
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1457 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____1457
                                 then
                                   let uu____1458 =
                                     let uu____1460 =
                                       let uu____1462 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1464 =
                                               let uu____1465 =
                                                 let uu____1466 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____1466 in
                                               let uu____1467 =
                                                 let uu____1468 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____1468 ")" in
                                               Prims.strcat uu____1465
                                                 uu____1467 in
                                             Prims.strcat "(" uu____1464
                                         | None  -> "" in
                                       let uu____1469 =
                                         let uu____1471 =
                                           let uu____1473 =
                                             let uu____1475 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____1476 =
                                               let uu____1478 =
                                                 let uu____1480 =
                                                   let uu____1482 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____1483 =
                                                     let uu____1485 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____1486 =
                                                       let uu____1488 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____1489 =
                                                         let uu____1491 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____1491] in
                                                       uu____1488 ::
                                                         uu____1489 in
                                                     uu____1485 :: uu____1486 in
                                                   uu____1482 :: uu____1483 in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1480 in
                                               tag :: uu____1478 in
                                             uu____1475 :: uu____1476 in
                                           query_name :: uu____1473 in
                                         name :: uu____1471 in
                                       uu____1462 :: uu____1469 in
                                     let uu____1494 =
                                       let uu____1496 =
                                         let uu____1497 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____1497
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____1509 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____1509 "}"
                                         else
                                           (let uu____1514 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____1514 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1517 -> "") in
                                       [uu____1496] in
                                     FStar_List.append uu____1460 uu____1494 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1458
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1537 =
                                     let uu____1538 =
                                       FStar_ST.read hint_worked in
                                     Prims.op_Negation uu____1538 in
                                   if uu____1537
                                   then
                                     let hint_check_cb uu____1552 =
                                       match uu____1552 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1575 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1581 ->
                                                 "failed" in
                                           let uu____1586 =
                                             FStar_Options.hint_info () in
                                           if uu____1586
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1590 =
                                         let uu____1595 =
                                           FStar_ST.read current_core in
                                         filter_assertions env uu____1595 in
                                       let uu____1598 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____1590
                                         all_labels uu____1598 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1600 =
                                         let uu____1601 =
                                           FStar_ST.read hint_worked in
                                         Prims.op_Negation uu____1601 in
                                       if uu____1600
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____1608 =
                                             let uu____1609 =
                                               let uu____1611 =
                                                 let uu____1613 =
                                                   let uu____1614 =
                                                     let uu____1615 =
                                                       let uu____1617 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____1617] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1615 in
                                                   FStar_Options.String
                                                     uu____1614 in
                                                 [uu____1613] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1611 in
                                             FStar_Options.List uu____1609 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1608);
                                          (let hint_refinement_cb uu____1629
                                             =
                                             match uu____1629 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1651 =
                                                   FStar_Options.hint_info () in
                                                 if uu____1651
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1662 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1662))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1671 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1671
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1673 =
                                              FStar_ST.read refinement_ok in
                                            if uu____1673
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1678 =
                                                     let uu____1680 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____1680] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1678);
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
                                  (let uu____1695 =
                                     let uu____1696 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____1696 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1695);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1699 = FStar_ST.read current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1699;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1706 =
                                       let uu____1708 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____1708
                                       then
                                         let uu____1710 =
                                           let uu____1711 =
                                             FStar_Options.check_hints () in
                                           if uu____1711
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
                                         Some uu____1710
                                       else hint_opt in
                                     record_hint uu____1706))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1717 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____1717
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1724 =
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
                       ((let uu____1730 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____1730
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____1735 =
                           let uu____1736 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1736 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1735)) in
                 let process_query q = check q in
                 let uu____1744 = FStar_Options.admit_smt_queries () in
                 if uu____1744 then () else process_query query)
let solve:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1763 =
           let uu____1764 =
             let uu____1765 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1765 in
           FStar_Util.format1 "Starting query at %s" uu____1764 in
         FStar_SMTEncoding_Encode.push uu____1763);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____1767 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____1767 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1788 =
               let uu____1789 =
                 let uu____1790 =
                   let uu____1791 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1791 in
                 FStar_Util.format1 "Ending query at %s" uu____1790 in
               FStar_SMTEncoding_Encode.pop uu____1789 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1792);
                        FStar_SMTEncoding_Term.freevars = uu____1793;
                        FStar_SMTEncoding_Term.rng = uu____1794;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1795;
                    FStar_SMTEncoding_Term.assumption_name = uu____1796;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1797;_}
                  -> pop1 ()
              | uu____1805 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1806 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1808 -> failwith "Impossible"))
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
    FStar_TypeChecker_Env.init = (fun uu____1815  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1816  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1817  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1818  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1819  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1820  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1821  -> fun uu____1822  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1823  -> fun uu____1824  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1831  -> fun uu____1832  -> fun uu____1833  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1837  -> fun uu____1838  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1839  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1840  -> ())
  }
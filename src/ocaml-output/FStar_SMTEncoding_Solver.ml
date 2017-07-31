open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels,FStar_SMTEncoding_Z3.error_kind)
    FStar_Pervasives_Native.tuple2
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result:
  'Auu____21 'Auu____22 'Auu____23 .
    ('Auu____23,('Auu____22,'Auu____21) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____23,'Auu____22) FStar_Util.either
  =
  fun uu___88_39  ->
    match uu___88_39 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____54) -> FStar_Util.Inr r
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
let initialize_hints_db:
  'Auu____172 . Prims.string -> 'Auu____172 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      FStar_ST.op_Colon_Equals hint_stats [];
      (let uu____201 = FStar_Options.record_hints () in
       if uu____201
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____227 = FStar_Options.use_hints () in
       if uu____227
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____230 = FStar_Options.hint_file () in
           match uu____230 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____234 = FStar_Util.read_hints val_filename in
         match uu____234 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____240 = FStar_Options.hint_info () in
               if uu____240
               then
                 let uu____241 =
                   let uu____242 = FStar_Options.hint_file () in
                   match uu____242 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____246 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____241
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____269 = FStar_Options.hint_info () in
             (if uu____269
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____277 = FStar_Options.record_hints () in
     if uu____277
     then
       let hints =
         let uu____279 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____279 in
       let hints_db =
         let uu____301 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____301; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____304 = FStar_Options.hint_file () in
         match uu____304 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    (let uu____310 = FStar_Options.hint_info () in
     if uu____310
     then
       let stats =
         let uu____314 = FStar_ST.op_Bang hint_stats in
         FStar_All.pipe_right uu____314 FStar_List.rev in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               let uu____345 = FStar_Range.string_of_range s.source_location in
               let uu____346 = FStar_Util.string_of_int s.elapsed_time in
               FStar_Util.print3
                 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____345
                 (match s.replay_result with
                  | FStar_Util.Inl uu____348 -> "succeeded"
                  | FStar_Util.Inr uu____349 -> "failed") uu____346))
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals hint_stats []
let with_hints_db: 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let next_hint:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____440 = FStar_ST.op_Bang replaying_hints in
      match uu____440 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___89_468  ->
               match uu___89_468 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____474 -> FStar_Pervasives_Native.None)
      | uu____477 -> FStar_Pervasives_Native.None
let record_hint: FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit
  =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___93_495 = h in
             {
               FStar_Util.hint_name = (uu___93_495.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___93_495.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___93_495.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___93_495.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___93_495.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             }) in
    let uu____496 = FStar_ST.op_Bang recorded_hints in
    match uu____496 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____546 -> ()
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
          let uu____570 =
            let uu____573 = FStar_ST.op_Bang hint_stats in s :: uu____573 in
          FStar_ST.op_Colon_Equals hint_stats uu____570
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
        | uu____627 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____639 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____649 =
        FStar_List.fold_left
          (fun uu____672  ->
             fun d  ->
               match uu____672 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____709 =
                          matches_fact_ids include_assumption_names a in
                        if uu____709
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____734 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____649 with | (pruned_theory,uu____746) -> pruned_theory
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
            let uu____781 = filter_using_facts_from e theory in
            (uu____781, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____791 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____815  ->
                     match uu____815 with
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
                          | uu____872 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____791 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____906 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____916 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___90_921  ->
                                         match uu___90_921 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____923 -> false)) in
                               FStar_All.pipe_right uu____916
                                 Prims.op_Negation)) in
                     FStar_All.pipe_right uu____906
                       (FStar_String.concat ", ") in
                   let included =
                     let uu____927 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___91_936  ->
                               match uu___91_936 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____940 -> [])) in
                     FStar_All.pipe_right uu____927
                       (FStar_String.concat ", ") in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included in
                 ((let uu____944 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ()) in
                   if uu____944
                   then
                     let n1 = FStar_List.length core1 in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else "" in
                     let uu____952 = FStar_Util.string_of_int n_retained in
                     let uu____953 =
                       if n1 <> n_retained
                       then
                         let uu____958 = FStar_Util.string_of_int n1 in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____958 missed
                       else "" in
                     let uu____966 = FStar_Util.string_of_int n_pruned in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____952 uu____953 uu____966
                   else ());
                  (let uu____968 =
                     let uu____971 =
                       let uu____974 =
                         let uu____975 =
                           let uu____976 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ") in
                           Prims.strcat "UNSAT CORE: " uu____976 in
                         FStar_SMTEncoding_Term.Caption uu____975 in
                       [uu____974] in
                     FStar_List.append theory' uu____971 in
                   (uu____968, true))))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____995 = filter_using_facts_from e x in (uu____995, false)
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
            (let uu____1029 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1) in
             match uu____1029 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None in
                 let set_minimum_workable_fuel f uu___92_1127 =
                   match uu___92_1127 with
                   | ([],uu____1140) -> ()
                   | errs ->
                       let uu____1150 =
                         FStar_ST.op_Bang minimum_workable_fuel in
                       (match uu____1150 with
                        | FStar_Pervasives_Native.Some uu____1265 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.op_Colon_Equals minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs))) in
                 let with_fuel label_assumptions p uu____1457 =
                   match uu____1457 with
                   | (n1,i,rlimit) ->
                       let uu____1471 =
                         let uu____1474 =
                           let uu____1475 =
                             let uu____1476 = FStar_Util.string_of_int n1 in
                             let uu____1477 = FStar_Util.string_of_int i in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____1476 uu____1477 in
                           FStar_SMTEncoding_Term.Caption uu____1475 in
                         let uu____1478 =
                           let uu____1481 =
                             let uu____1482 =
                               let uu____1489 =
                                 let uu____1490 =
                                   let uu____1495 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", []) in
                                   let uu____1498 =
                                     FStar_SMTEncoding_Term.n_fuel n1 in
                                   (uu____1495, uu____1498) in
                                 FStar_SMTEncoding_Util.mkEq uu____1490 in
                               (uu____1489, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption") in
                             FStar_SMTEncoding_Util.mkAssume uu____1482 in
                           let uu____1501 =
                             let uu____1504 =
                               let uu____1505 =
                                 let uu____1512 =
                                   let uu____1513 =
                                     let uu____1518 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", []) in
                                     let uu____1521 =
                                       FStar_SMTEncoding_Term.n_fuel i in
                                     (uu____1518, uu____1521) in
                                   FStar_SMTEncoding_Util.mkEq uu____1513 in
                                 (uu____1512, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption") in
                               FStar_SMTEncoding_Util.mkAssume uu____1505 in
                             [uu____1504; p] in
                           uu____1481 :: uu____1501 in
                         uu____1474 :: uu____1478 in
                       let uu____1524 =
                         let uu____1527 =
                           let uu____1530 =
                             let uu____1533 =
                               let uu____1534 =
                                 let uu____1539 =
                                   FStar_Util.string_of_int rlimit in
                                 ("rlimit", uu____1539) in
                               FStar_SMTEncoding_Term.SetOption uu____1534 in
                             [uu____1533] in
                           let uu____1540 =
                             let uu____1543 =
                               let uu____1546 =
                                 let uu____1549 =
                                   FStar_Options.record_hints () in
                                 if uu____1549
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else [] in
                               let uu____1553 =
                                 let uu____1556 =
                                   let uu____1559 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ()) in
                                   if uu____1559
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics;
                                     FStar_SMTEncoding_Term.GetReasonUnknown]
                                   else [] in
                                 FStar_List.append uu____1556 suffix in
                               FStar_List.append uu____1546 uu____1553 in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____1543 in
                           FStar_List.append uu____1530 uu____1540 in
                         FStar_List.append label_assumptions uu____1527 in
                       FStar_List.append uu____1471 uu____1524 in
                 let check p =
                   let rlimit =
                     let uu____1568 = FStar_Options.z3_rlimit_factor () in
                     let uu____1569 =
                       let uu____1570 = FStar_Options.z3_rlimit () in
                       uu____1570 * (Prims.parse_int "544656") in
                     uu____1568 * uu____1569 in
                   let default_initial_config =
                     let uu____1578 = FStar_Options.initial_fuel () in
                     let uu____1579 = FStar_Options.initial_ifuel () in
                     (uu____1578, uu____1579, rlimit) in
                   let hint_opt = next_hint query_name query_index in
                   let uu____1583 =
                     match hint_opt with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None,
                           default_initial_config)
                     | FStar_Pervasives_Native.Some hint ->
                         let uu____1625 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (FStar_Pervasives_Native.None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656"))) in
                         (match uu____1625 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout))) in
                   match uu____1583 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____1720 =
                           let uu____1731 =
                             let uu____1742 =
                               let uu____1751 =
                                 let uu____1752 = FStar_Options.max_ifuel () in
                                 let uu____1753 =
                                   FStar_Options.initial_ifuel () in
                                 uu____1752 > uu____1753 in
                               if uu____1751
                               then
                                 let uu____1762 =
                                   let uu____1769 =
                                     FStar_Options.initial_fuel () in
                                   let uu____1770 =
                                     FStar_Options.max_ifuel () in
                                   (uu____1769, uu____1770, rlimit) in
                                 [uu____1762]
                               else [] in
                             let uu____1790 =
                               let uu____1801 =
                                 let uu____1810 =
                                   let uu____1811 =
                                     let uu____1812 =
                                       FStar_Options.max_fuel () in
                                     uu____1812 / (Prims.parse_int "2") in
                                   let uu____1819 =
                                     FStar_Options.initial_fuel () in
                                   uu____1811 > uu____1819 in
                                 if uu____1810
                                 then
                                   let uu____1828 =
                                     let uu____1835 =
                                       let uu____1836 =
                                         FStar_Options.max_fuel () in
                                       uu____1836 / (Prims.parse_int "2") in
                                     let uu____1843 =
                                       FStar_Options.max_ifuel () in
                                     (uu____1835, uu____1843, rlimit) in
                                   [uu____1828]
                                 else [] in
                               let uu____1863 =
                                 let uu____1874 =
                                   let uu____1883 =
                                     (let uu____1888 =
                                        FStar_Options.max_fuel () in
                                      let uu____1889 =
                                        FStar_Options.initial_fuel () in
                                      uu____1888 > uu____1889) &&
                                       (let uu____1892 =
                                          FStar_Options.max_ifuel () in
                                        let uu____1893 =
                                          FStar_Options.initial_ifuel () in
                                        uu____1892 >= uu____1893) in
                                   if uu____1883
                                   then
                                     let uu____1902 =
                                       let uu____1909 =
                                         FStar_Options.max_fuel () in
                                       let uu____1910 =
                                         FStar_Options.max_ifuel () in
                                       (uu____1909, uu____1910, rlimit) in
                                     [uu____1902]
                                   else [] in
                                 let uu____1930 =
                                   let uu____1941 =
                                     let uu____1950 =
                                       let uu____1951 =
                                         FStar_Options.min_fuel () in
                                       let uu____1952 =
                                         FStar_Options.initial_fuel () in
                                       uu____1951 < uu____1952 in
                                     if uu____1950
                                     then
                                       let uu____1961 =
                                         let uu____1968 =
                                           FStar_Options.min_fuel () in
                                         (uu____1968, (Prims.parse_int "1"),
                                           rlimit) in
                                       [uu____1961]
                                     else [] in
                                   [uu____1941] in
                                 uu____1874 :: uu____1930 in
                               uu____1801 :: uu____1863 in
                             uu____1742 :: uu____1790 in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____1731 in
                         FStar_List.flatten uu____1720 in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____2085 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____2087 = FStar_Options.n_cores () in
                                uu____2087 = (Prims.parse_int "1")) in
                           if uu____2085
                           then
                             let uu____2088 =
                               let uu____2105 =
                                 FStar_ST.op_Bang minimum_workable_fuel in
                               match uu____2105 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____2306 =
                                     let uu____2313 =
                                       FStar_Options.min_fuel () in
                                     (uu____2313, (Prims.parse_int "1"),
                                       rlimit) in
                                   (uu____2306, errs) in
                             match uu____2088 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None in
                                   (let uu____2362 =
                                      with_fuel label_assumptions p1
                                        min_fuel1 in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____2362
                                      FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.op_Colon_Equals res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____2399 = FStar_ST.op_Bang res in
                                    FStar_Option.get uu____2399) in
                                 (FStar_SMTEncoding_ErrorReporting.detail_errors
                                    false env all_labels ask_z3;
                                  ([], FStar_SMTEncoding_Z3.Default))
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
                              | (uu____2514,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____2551 -> errs) in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____2554 = FStar_Options.print_fuels () in
                          if uu____2554
                          then
                            let uu____2555 =
                              let uu____2556 =
                                FStar_TypeChecker_Env.get_range env in
                              FStar_Range.string_of_range uu____2556 in
                            let uu____2557 =
                              let uu____2558 = FStar_Options.max_fuel () in
                              FStar_All.pipe_right uu____2558
                                FStar_Util.string_of_int in
                            let uu____2559 =
                              let uu____2560 = FStar_Options.max_ifuel () in
                              FStar_All.pipe_right uu____2560
                                FStar_Util.string_of_int in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____2555 uu____2557 uu____2559
                          else ());
                         (let uu____2562 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.fst errs1)
                              (FStar_List.map
                                 (fun uu____2589  ->
                                    match uu____2589 with
                                    | (uu____2600,x,y) -> (x, y))) in
                          FStar_TypeChecker_Err.add_errors env uu____2562) in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____2622),uu____2623) -> result
                         | (uu____2632,FStar_Util.Inl uu____2633) -> result
                         | (uu____2646,FStar_Util.Inr uu____2647) ->
                             FStar_Util.Inr errs in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____2750) -> report1 p1 errs
                          | (uu____2765,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____2784) ->
                              let uu____2813 = with_fuel [] p1 mi in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____2813
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____2821  ->
                                   match uu____2821 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____2841 =
                                         let uu____2848 =
                                           use_errors errs result in
                                         (uu____2848, elapsed_time,
                                           statistics) in
                                       cb false mi p1 tl1 scope uu____2841))
                       and cb used_hint uu____2850 p1 alt scope uu____2854 =
                         match (uu____2850, uu____2854) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____2907 =
                                    FStar_TypeChecker_Env.get_range env in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____2907))
                              else ();
                              (let uu____2910 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ()) in
                               if uu____2910
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____2933 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ()) in
                                 if uu____2933
                                 then
                                   let uu____2934 =
                                     let uu____2937 =
                                       let uu____2940 =
                                         match env1 with
                                         | FStar_Pervasives_Native.Some e ->
                                             let uu____2942 =
                                               let uu____2943 =
                                                 let uu____2944 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e in
                                                 FStar_Range.string_of_range
                                                   uu____2944 in
                                               let uu____2945 =
                                                 let uu____2946 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     () in
                                                 Prims.strcat uu____2946 ")" in
                                               Prims.strcat uu____2943
                                                 uu____2945 in
                                             Prims.strcat "(" uu____2942
                                         | FStar_Pervasives_Native.None  ->
                                             "" in
                                       let uu____2947 =
                                         let uu____2950 =
                                           let uu____2953 =
                                             let uu____2956 =
                                               FStar_Util.string_of_int
                                                 query_index in
                                             let uu____2957 =
                                               let uu____2960 =
                                                 let uu____2963 =
                                                   let uu____2966 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time in
                                                   let uu____2967 =
                                                     let uu____2970 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel in
                                                     let uu____2971 =
                                                       let uu____2974 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel in
                                                       let uu____2975 =
                                                         let uu____2978 =
                                                           FStar_Util.string_of_int
                                                             rlimit in
                                                         [uu____2978] in
                                                       uu____2974 ::
                                                         uu____2975 in
                                                     uu____2970 :: uu____2971 in
                                                   uu____2966 :: uu____2967 in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____2963 in
                                               tag :: uu____2960 in
                                             uu____2956 :: uu____2957 in
                                           query_name :: uu____2953 in
                                         name :: uu____2950 in
                                       uu____2940 :: uu____2947 in
                                     let uu____2982 =
                                       let uu____2985 =
                                         let uu____2986 =
                                           FStar_Options.print_z3_statistics
                                             () in
                                         if uu____2986
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " "))) in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={" in
                                           let uu____2998 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1")) in
                                           Prims.strcat uu____2998 "}"
                                         else
                                           (let uu____3000 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown" in
                                            match uu____3000 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____3004 -> "") in
                                       [uu____2985] in
                                     FStar_List.append uu____2937 uu____2982 in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____2934
                                 else () in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1 in
                                 let hint_worked = FStar_Util.mk_ref false in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____3025 =
                                     let uu____3026 =
                                       FStar_ST.op_Bang hint_worked in
                                     Prims.op_Negation uu____3026 in
                                   if uu____3025
                                   then
                                     let hint_check_cb uu____3070 =
                                       match uu____3070 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____3111 ->
                                                 (FStar_ST.op_Colon_Equals
                                                    hint_worked true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____3141 ->
                                                 "failed" in
                                           let uu____3150 =
                                             FStar_Options.hint_info () in
                                           if uu____3150
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else () in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____3154 =
                                         let uu____3161 =
                                           FStar_ST.op_Bang current_core in
                                         filter_assertions env uu____3161 in
                                       let uu____3186 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit) in
                                       FStar_SMTEncoding_Z3.ask uu____3154
                                         all_labels uu____3186
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____3189 =
                                         let uu____3190 =
                                           FStar_ST.op_Bang hint_worked in
                                         Prims.op_Negation uu____3190 in
                                       if uu____3189
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false in
                                         ((let uu____3219 =
                                             let uu____3220 =
                                               let uu____3223 =
                                                 let uu____3226 =
                                                   let uu____3227 =
                                                     let uu____3228 =
                                                       let uu____3231 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist in
                                                       [uu____3231] in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____3228 in
                                                   FStar_Options.String
                                                     uu____3227 in
                                                 [uu____3226] in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____3223 in
                                             FStar_Options.List uu____3220 in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____3219);
                                          (let hint_refinement_cb uu____3251
                                             =
                                             match uu____3251 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____3291 =
                                                   FStar_Options.hint_info () in
                                                 if uu____3291
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.op_Colon_Equals
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.op_Colon_Equals
                                                            current_core uc;
                                                          (let uu____3348 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____3348))
                                                     | FStar_Util.Inr errs ->
                                                         "failed" in
                                                   query_info
                                                     FStar_Pervasives_Native.None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else () in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____3361 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit) in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____3361
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____3364 =
                                              FStar_ST.op_Bang refinement_ok in
                                            if uu____3364
                                            then
                                              let cutoff =
                                                Prims.parse_int "10" in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____3391 =
                                                     let uu____3394 =
                                                       FStar_Util.string_of_int
                                                         cutoff in
                                                     [uu____3394] in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____3391);
                                                  FStar_ST.op_Colon_Equals
                                                    current_core
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
                                  (let uu____3433 =
                                     let uu____3434 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before in
                                     FStar_Options.List uu____3434 in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____3433);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____3439 =
                                    FStar_ST.op_Bang current_core in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____3439;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  }) in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____3470 =
                                       let uu____3473 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ()) in
                                       if uu____3473
                                       then
                                         let uu____3476 =
                                           let uu____3477 =
                                             FStar_Options.check_hints () in
                                           if uu____3477
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
                                           uu____3476
                                       else hint_opt in
                                     record_hint uu____3470))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____3483 =
                                       used_hint &&
                                         (FStar_Options.hint_info ()) in
                                     if uu____3483
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | FStar_Pervasives_Native.Some core
                                             ->
                                             (FStar_List.iter
                                                (fun x  ->
                                                   FStar_Util.print_string
                                                     (Prims.strcat " " x))
                                                core;
                                              FStar_Util.print_string "\n")))
                                     else ());
                                    (let uu____3497 =
                                       used_hint &&
                                         (FStar_Options.detail_hint_replay ()) in
                                     if uu____3497
                                     then
                                       let ask_z3 label_assumptions =
                                         let res =
                                           FStar_Util.mk_ref
                                             FStar_Pervasives_Native.None in
                                         (let uu____3514 =
                                            with_fuel label_assumptions p1
                                              initial_config in
                                          FStar_SMTEncoding_Z3.ask
                                            (filter_assertions env unsat_core)
                                            all_labels uu____3514
                                            FStar_Pervasives_Native.None
                                            (fun r  ->
                                               FStar_ST.op_Colon_Equals res
                                                 (FStar_Pervasives_Native.Some
                                                    r)));
                                         (let uu____3551 =
                                            FStar_ST.op_Bang res in
                                          FStar_Option.get uu____3551) in
                                       FStar_SMTEncoding_ErrorReporting.detail_errors
                                         true env all_labels ask_z3
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope))) in
                       ((let uu____3588 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ()) in
                         if uu____3588
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config in
                         let uu____3595 =
                           let uu____3596 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope () in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____3596 in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____3595)) in
                 let process_query q = check q in
                 let uu____3605 =
                   let uu____3612 = FStar_Options.admit_smt_queries () in
                   let uu____3613 = FStar_Options.admit_except () in
                   (uu____3612, uu____3613) in
                 (match uu____3605 with
                  | (true ,uu____3618) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      process_query query
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let cur_id =
                        let uu____3629 =
                          let uu____3630 =
                            let uu____3631 =
                              let uu____3632 =
                                FStar_Util.string_of_int query_index in
                              Prims.strcat uu____3632 ")" in
                            Prims.strcat ", " uu____3631 in
                          Prims.strcat query_name uu____3630 in
                        Prims.strcat "(" uu____3629 in
                      if cur_id = id then process_query query else ()))
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____3656 =
           let uu____3657 =
             let uu____3658 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3658 in
           FStar_Util.format1 "Starting query at %s" uu____3657 in
         FStar_SMTEncoding_Encode.push uu____3656);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____3660 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____3660 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____3694 =
               let uu____3695 =
                 let uu____3696 =
                   let uu____3697 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3697 in
                 FStar_Util.format1 "Ending query at %s" uu____3696 in
               FStar_SMTEncoding_Encode.pop uu____3695 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____3698);
                        FStar_SMTEncoding_Term.freevars = uu____3699;
                        FStar_SMTEncoding_Term.rng = uu____3700;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____3701;
                    FStar_SMTEncoding_Term.assumption_name = uu____3702;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____3703;_}
                  -> pop1 ()
              | uu____3718 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____3719 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____3721 -> failwith "Impossible"))
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
           let uu____3727 =
             let uu____3734 = FStar_Options.peek () in (e, g, uu____3734) in
           [uu____3727]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____3749  -> ());
    FStar_TypeChecker_Env.push = (fun uu____3751  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3753  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____3755  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____3757  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____3759  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____3762  -> fun uu____3763  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3766  -> fun uu____3767  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3773 =
             let uu____3780 = FStar_Options.peek () in (e, g, uu____3780) in
           [uu____3773]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3796  -> fun uu____3797  -> fun uu____3798  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____3805  -> fun uu____3806  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____3808  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3810  -> ())
  }
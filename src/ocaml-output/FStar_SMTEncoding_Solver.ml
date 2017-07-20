open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels,FStar_SMTEncoding_Z3.error_kind)
    FStar_Pervasives_Native.tuple2
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____21 'Auu____22 'Auu____23 .
    ('Auu____23,('Auu____22,'Auu____21) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____23,'Auu____22) FStar_Util.either
  =
  fun uu___84_39  ->
    match uu___84_39 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____54) -> FStar_Util.Inr r
  
type hint_stat =
  {
  hint: FStar_Util.hint FStar_Pervasives_Native.option ;
  replay_result: z3_replay_result ;
  elapsed_time: Prims.int ;
  source_location: FStar_Range.range }
let __proj__Mkhint_stat__item__hint :
  hint_stat -> FStar_Util.hint FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} -> __fname__hint
  
let __proj__Mkhint_stat__item__replay_result : hint_stat -> z3_replay_result
  =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__replay_result
  
let __proj__Mkhint_stat__item__elapsed_time : hint_stat -> Prims.int =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__elapsed_time
  
let __proj__Mkhint_stat__item__source_location :
  hint_stat -> FStar_Range.range =
  fun projectee  ->
    match projectee with
    | { hint = __fname__hint; replay_result = __fname__replay_result;
        elapsed_time = __fname__elapsed_time;
        source_location = __fname__source_location;_} ->
        __fname__source_location
  
type hint_stats_t = hint_stat Prims.list
let recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let hint_stats : hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let format_hints_file_name : Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____154 . Prims.string -> 'Auu____154 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      FStar_ST.write hint_stats [];
      (let uu____167 = FStar_Options.record_hints ()  in
       if uu____167
       then FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____177 = FStar_Options.use_hints ()  in
       if uu____177
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____180 = FStar_Options.hint_file ()  in
           match uu____180 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____184 = FStar_Util.read_hints val_filename  in
         match uu____184 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____190 = FStar_Options.hint_info ()  in
               if uu____190
               then
                 let uu____191 =
                   let uu____192 = FStar_Options.hint_file ()  in
                   match uu____192 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____196 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____191
               else ());
              FStar_ST.write replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____203 = FStar_Options.hint_info ()  in
             (if uu____203
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let finalize_hints_db : Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____211 = FStar_Options.record_hints ()  in
     if uu____211
     then
       let hints =
         let uu____213 = FStar_ST.read recorded_hints  in
         FStar_Option.get uu____213  in
       let hints_db =
         let uu____219 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____219; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____222 = FStar_Options.hint_file ()  in
         match uu____222 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename
          in
       FStar_Util.write_hints val_filename hints_db
     else ());
    (let uu____228 = FStar_Options.hint_info ()  in
     if uu____228
     then
       let stats =
         let uu____232 = FStar_ST.read hint_stats  in
         FStar_All.pipe_right uu____232 FStar_List.rev  in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               let uu____247 = FStar_Range.string_of_range s.source_location
                  in
               let uu____248 = FStar_Util.string_of_int s.elapsed_time  in
               FStar_Util.print3
                 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____247
                 (match s.replay_result with
                  | FStar_Util.Inl uu____250 -> "succeeded"
                  | FStar_Util.Inr uu____251 -> "failed") uu____248))
     else ());
    FStar_ST.write recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.write replaying_hints FStar_Pervasives_Native.None;
    FStar_ST.write hint_stats []
  
let with_hints_db : 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f ()  in finalize_hints_db fname; result)
  
let next_hint :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____294 = FStar_ST.read replaying_hints  in
      match uu____294 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___85_306  ->
               match uu___85_306 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____312 -> FStar_Pervasives_Native.None)
      | uu____315 -> FStar_Pervasives_Native.None
  
let record_hint :
  FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___89_333 = h  in
             {
               FStar_Util.hint_name = (uu___89_333.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_333.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_333.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_333.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_333.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             })
       in
    let uu____334 = FStar_ST.read recorded_hints  in
    match uu____334 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.write recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____352 -> ()
  
let record_hint_stat :
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
            }  in
          let uu____376 =
            let uu____379 = FStar_ST.read hint_stats  in s :: uu____379  in
          FStar_ST.write hint_stats uu____376
  
let filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____401 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____413 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid)))
         in
      let theory_rev = FStar_List.rev theory  in
      let uu____423 =
        FStar_List.fold_left
          (fun uu____446  ->
             fun d  ->
               match uu____446 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____483 =
                          matches_fact_ids include_assumption_names a  in
                        if uu____483
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____508 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev
         in
      match uu____423 with | (pruned_theory,uu____520) -> pruned_theory
  
let filter_assertions :
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
            let uu____555 = filter_using_facts_from e theory  in
            (uu____555, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____565 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____589  ->
                     match uu____589 with
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
                          | uu____646 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____565 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____680 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____690 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___86_695  ->
                                         match uu___86_695 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____697 -> false))
                                  in
                               FStar_All.pipe_right uu____690
                                 Prims.op_Negation))
                        in
                     FStar_All.pipe_right uu____680
                       (FStar_String.concat ", ")
                      in
                   let included =
                     let uu____701 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___87_710  ->
                               match uu___87_710 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____714 -> []))
                        in
                     FStar_All.pipe_right uu____701
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included
                    in
                 ((let uu____718 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ())
                      in
                   if uu____718
                   then
                     let n1 = FStar_List.length core1  in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else ""  in
                     let uu____726 = FStar_Util.string_of_int n_retained  in
                     let uu____727 =
                       if n1 <> n_retained
                       then
                         let uu____732 = FStar_Util.string_of_int n1  in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____732 missed
                       else ""  in
                     let uu____740 = FStar_Util.string_of_int n_pruned  in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____726 uu____727 uu____740
                   else ());
                  (let uu____742 =
                     let uu____745 =
                       let uu____748 =
                         let uu____749 =
                           let uu____750 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ")
                              in
                           Prims.strcat "UNSAT CORE: " uu____750  in
                         FStar_SMTEncoding_Term.Caption uu____749  in
                       [uu____748]  in
                     FStar_List.append theory' uu____745  in
                   (uu____742, true))))
  
let filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____769 = filter_using_facts_from e x  in (uu____769, false)
  
let ask_and_report_errors :
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
            (let uu____803 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1)
                in
             match uu____803 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                 let set_minimum_workable_fuel f uu___88_901 =
                   match uu___88_901 with
                   | ([],uu____914) -> ()
                   | errs ->
                       let uu____924 = FStar_ST.read minimum_workable_fuel
                          in
                       (match uu____924 with
                        | FStar_Pervasives_Native.Some uu____963 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.write minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs)))
                    in
                 let with_fuel label_assumptions p uu____1079 =
                   match uu____1079 with
                   | (n1,i,rlimit) ->
                       let uu____1093 =
                         let uu____1096 =
                           let uu____1097 =
                             let uu____1098 = FStar_Util.string_of_int n1  in
                             let uu____1099 = FStar_Util.string_of_int i  in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____1098 uu____1099
                              in
                           FStar_SMTEncoding_Term.Caption uu____1097  in
                         let uu____1100 =
                           let uu____1103 =
                             let uu____1104 =
                               let uu____1111 =
                                 let uu____1112 =
                                   let uu____1117 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", [])
                                      in
                                   let uu____1120 =
                                     FStar_SMTEncoding_Term.n_fuel n1  in
                                   (uu____1117, uu____1120)  in
                                 FStar_SMTEncoding_Util.mkEq uu____1112  in
                               (uu____1111, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption")
                                in
                             FStar_SMTEncoding_Util.mkAssume uu____1104  in
                           let uu____1123 =
                             let uu____1126 =
                               let uu____1127 =
                                 let uu____1134 =
                                   let uu____1135 =
                                     let uu____1140 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", [])
                                        in
                                     let uu____1143 =
                                       FStar_SMTEncoding_Term.n_fuel i  in
                                     (uu____1140, uu____1143)  in
                                   FStar_SMTEncoding_Util.mkEq uu____1135  in
                                 (uu____1134, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption")
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____1127  in
                             [uu____1126; p]  in
                           uu____1103 :: uu____1123  in
                         uu____1096 :: uu____1100  in
                       let uu____1146 =
                         let uu____1149 =
                           let uu____1152 =
                             let uu____1155 =
                               let uu____1156 =
                                 let uu____1161 =
                                   FStar_Util.string_of_int rlimit  in
                                 ("rlimit", uu____1161)  in
                               FStar_SMTEncoding_Term.SetOption uu____1156
                                in
                             [uu____1155]  in
                           let uu____1162 =
                             let uu____1165 =
                               let uu____1168 =
                                 let uu____1171 =
                                   FStar_Options.record_hints ()  in
                                 if uu____1171
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else []  in
                               let uu____1175 =
                                 let uu____1178 =
                                   let uu____1181 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ())
                                      in
                                   if uu____1181
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics;
                                     FStar_SMTEncoding_Term.GetReasonUnknown]
                                   else []  in
                                 FStar_List.append uu____1178 suffix  in
                               FStar_List.append uu____1168 uu____1175  in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____1165
                              in
                           FStar_List.append uu____1152 uu____1162  in
                         FStar_List.append label_assumptions uu____1149  in
                       FStar_List.append uu____1093 uu____1146
                    in
                 let check p =
                   let rlimit =
                     let uu____1190 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____1191 =
                       let uu____1192 = FStar_Options.z3_rlimit ()  in
                       uu____1192 * (Prims.parse_int "544656")  in
                     uu____1190 * uu____1191  in
                   let default_initial_config =
                     let uu____1200 = FStar_Options.initial_fuel ()  in
                     let uu____1201 = FStar_Options.initial_ifuel ()  in
                     (uu____1200, uu____1201, rlimit)  in
                   let hint_opt = next_hint query_name query_index  in
                   let uu____1205 =
                     match hint_opt with
                     | FStar_Pervasives_Native.None  ->
                         (FStar_Pervasives_Native.None,
                           default_initial_config)
                     | FStar_Pervasives_Native.Some hint ->
                         let uu____1247 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (FStar_Pervasives_Native.None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656")))
                            in
                         (match uu____1247 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout)))
                      in
                   match uu____1205 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____1342 =
                           let uu____1353 =
                             let uu____1364 =
                               let uu____1373 =
                                 let uu____1374 = FStar_Options.max_ifuel ()
                                    in
                                 let uu____1375 =
                                   FStar_Options.initial_ifuel ()  in
                                 uu____1374 > uu____1375  in
                               if uu____1373
                               then
                                 let uu____1384 =
                                   let uu____1391 =
                                     FStar_Options.initial_fuel ()  in
                                   let uu____1392 =
                                     FStar_Options.max_ifuel ()  in
                                   (uu____1391, uu____1392, rlimit)  in
                                 [uu____1384]
                               else []  in
                             let uu____1412 =
                               let uu____1423 =
                                 let uu____1432 =
                                   let uu____1433 =
                                     let uu____1434 =
                                       FStar_Options.max_fuel ()  in
                                     uu____1434 / (Prims.parse_int "2")  in
                                   let uu____1441 =
                                     FStar_Options.initial_fuel ()  in
                                   uu____1433 > uu____1441  in
                                 if uu____1432
                                 then
                                   let uu____1450 =
                                     let uu____1457 =
                                       let uu____1458 =
                                         FStar_Options.max_fuel ()  in
                                       uu____1458 / (Prims.parse_int "2")  in
                                     let uu____1465 =
                                       FStar_Options.max_ifuel ()  in
                                     (uu____1457, uu____1465, rlimit)  in
                                   [uu____1450]
                                 else []  in
                               let uu____1485 =
                                 let uu____1496 =
                                   let uu____1505 =
                                     (let uu____1510 =
                                        FStar_Options.max_fuel ()  in
                                      let uu____1511 =
                                        FStar_Options.initial_fuel ()  in
                                      uu____1510 > uu____1511) &&
                                       (let uu____1514 =
                                          FStar_Options.max_ifuel ()  in
                                        let uu____1515 =
                                          FStar_Options.initial_ifuel ()  in
                                        uu____1514 >= uu____1515)
                                      in
                                   if uu____1505
                                   then
                                     let uu____1524 =
                                       let uu____1531 =
                                         FStar_Options.max_fuel ()  in
                                       let uu____1532 =
                                         FStar_Options.max_ifuel ()  in
                                       (uu____1531, uu____1532, rlimit)  in
                                     [uu____1524]
                                   else []  in
                                 let uu____1552 =
                                   let uu____1563 =
                                     let uu____1572 =
                                       let uu____1573 =
                                         FStar_Options.min_fuel ()  in
                                       let uu____1574 =
                                         FStar_Options.initial_fuel ()  in
                                       uu____1573 < uu____1574  in
                                     if uu____1572
                                     then
                                       let uu____1583 =
                                         let uu____1590 =
                                           FStar_Options.min_fuel ()  in
                                         (uu____1590, (Prims.parse_int "1"),
                                           rlimit)
                                          in
                                       [uu____1583]
                                     else []  in
                                   [uu____1563]  in
                                 uu____1496 :: uu____1552  in
                               uu____1423 :: uu____1485  in
                             uu____1364 :: uu____1412  in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____1353
                            in
                         FStar_List.flatten uu____1342  in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1707 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1709 = FStar_Options.n_cores ()  in
                                uu____1709 = (Prims.parse_int "1"))
                              in
                           if uu____1707
                           then
                             let uu____1710 =
                               let uu____1727 =
                                 FStar_ST.read minimum_workable_fuel  in
                               match uu____1727 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____1852 =
                                     let uu____1859 =
                                       FStar_Options.min_fuel ()  in
                                     (uu____1859, (Prims.parse_int "1"),
                                       rlimit)
                                      in
                                   (uu____1852, errs)
                                in
                             match uu____1710 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (let uu____1908 =
                                      with_fuel label_assumptions p1
                                        min_fuel1
                                       in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1908
                                      FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.write res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____1917 = FStar_ST.read res  in
                                    FStar_Option.get uu____1917)
                                    in
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
                              | (uu____2004,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____2041 -> errs)
                            in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____2044 = FStar_Options.print_fuels ()  in
                          if uu____2044
                          then
                            let uu____2045 =
                              let uu____2046 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Range.string_of_range uu____2046  in
                            let uu____2047 =
                              let uu____2048 = FStar_Options.max_fuel ()  in
                              FStar_All.pipe_right uu____2048
                                FStar_Util.string_of_int
                               in
                            let uu____2049 =
                              let uu____2050 = FStar_Options.max_ifuel ()  in
                              FStar_All.pipe_right uu____2050
                                FStar_Util.string_of_int
                               in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____2045 uu____2047 uu____2049
                          else ());
                         (let uu____2052 =
                            FStar_All.pipe_right
                              (FStar_Pervasives_Native.fst errs1)
                              (FStar_List.map
                                 (fun uu____2079  ->
                                    match uu____2079 with
                                    | (uu____2090,x,y) -> (x, y)))
                             in
                          FStar_TypeChecker_Err.add_errors env uu____2052)
                          in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____2112),uu____2113) -> result
                         | (uu____2122,FStar_Util.Inl uu____2123) -> result
                         | (uu____2136,FStar_Util.Inr uu____2137) ->
                             FStar_Util.Inr errs
                          in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____2240) -> report1 p1 errs
                          | (uu____2255,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____2274) ->
                              let uu____2303 = with_fuel [] p1 mi  in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____2303
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____2311  ->
                                   match uu____2311 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____2331 =
                                         let uu____2338 =
                                           use_errors errs result  in
                                         (uu____2338, elapsed_time,
                                           statistics)
                                          in
                                       cb false mi p1 tl1 scope uu____2331))
                       
                       and cb used_hint uu____2340 p1 alt scope uu____2344 =
                         match (uu____2340, uu____2344) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____2397 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____2397))
                              else ();
                              (let uu____2400 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ())
                                  in
                               if uu____2400
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____2423 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ())
                                    in
                                 if uu____2423
                                 then
                                   let uu____2424 =
                                     let uu____2427 =
                                       let uu____2430 =
                                         match env1 with
                                         | FStar_Pervasives_Native.Some e ->
                                             let uu____2432 =
                                               let uu____2433 =
                                                 let uu____2434 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e
                                                    in
                                                 FStar_Range.string_of_range
                                                   uu____2434
                                                  in
                                               let uu____2435 =
                                                 let uu____2436 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     ()
                                                    in
                                                 Prims.strcat uu____2436 ")"
                                                  in
                                               Prims.strcat uu____2433
                                                 uu____2435
                                                in
                                             Prims.strcat "(" uu____2432
                                         | FStar_Pervasives_Native.None  ->
                                             ""
                                          in
                                       let uu____2437 =
                                         let uu____2440 =
                                           let uu____2443 =
                                             let uu____2446 =
                                               FStar_Util.string_of_int
                                                 query_index
                                                in
                                             let uu____2447 =
                                               let uu____2450 =
                                                 let uu____2453 =
                                                   let uu____2456 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time
                                                      in
                                                   let uu____2457 =
                                                     let uu____2460 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel
                                                        in
                                                     let uu____2461 =
                                                       let uu____2464 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel
                                                          in
                                                       let uu____2465 =
                                                         let uu____2468 =
                                                           FStar_Util.string_of_int
                                                             rlimit
                                                            in
                                                         [uu____2468]  in
                                                       uu____2464 ::
                                                         uu____2465
                                                        in
                                                     uu____2460 :: uu____2461
                                                      in
                                                   uu____2456 :: uu____2457
                                                    in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____2453
                                                  in
                                               tag :: uu____2450  in
                                             uu____2446 :: uu____2447  in
                                           query_name :: uu____2443  in
                                         name :: uu____2440  in
                                       uu____2430 :: uu____2437  in
                                     let uu____2472 =
                                       let uu____2475 =
                                         let uu____2476 =
                                           FStar_Options.print_z3_statistics
                                             ()
                                            in
                                         if uu____2476
                                         then
                                           let f k v1 a =
                                             Prims.strcat a
                                               (Prims.strcat k
                                                  (Prims.strcat "="
                                                     (Prims.strcat v1 " ")))
                                              in
                                           let str =
                                             FStar_Util.smap_fold statistics1
                                               f "statistics={"
                                              in
                                           let uu____2488 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1"))
                                              in
                                           Prims.strcat uu____2488 "}"
                                         else
                                           (let uu____2490 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown"
                                               in
                                            match uu____2490 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____2494 -> "")
                                          in
                                       [uu____2475]  in
                                     FStar_List.append uu____2427 uu____2472
                                      in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____2424
                                 else ()  in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1  in
                                 let hint_worked = FStar_Util.mk_ref false
                                    in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____2515 =
                                     let uu____2516 =
                                       FStar_ST.read hint_worked  in
                                     Prims.op_Negation uu____2516  in
                                   if uu____2515
                                   then
                                     let hint_check_cb uu____2538 =
                                       match uu____2538 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____2579 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____2587 ->
                                                 "failed"
                                              in
                                           let uu____2596 =
                                             FStar_Options.hint_info ()  in
                                           if uu____2596
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else ()
                                        in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____2600 =
                                         let uu____2607 =
                                           FStar_ST.read current_core  in
                                         filter_assertions env uu____2607  in
                                       let uu____2610 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit)
                                          in
                                       FStar_SMTEncoding_Z3.ask uu____2600
                                         all_labels uu____2610
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____2613 =
                                         let uu____2614 =
                                           FStar_ST.read hint_worked  in
                                         Prims.op_Negation uu____2614  in
                                       if uu____2613
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false  in
                                         ((let uu____2621 =
                                             let uu____2622 =
                                               let uu____2625 =
                                                 let uu____2628 =
                                                   let uu____2629 =
                                                     let uu____2630 =
                                                       let uu____2633 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist
                                                          in
                                                       [uu____2633]  in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____2630
                                                      in
                                                   FStar_Options.String
                                                     uu____2629
                                                    in
                                                 [uu____2628]  in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____2625
                                                in
                                             FStar_Options.List uu____2622
                                              in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____2621);
                                          (let hint_refinement_cb uu____2653
                                             =
                                             match uu____2653 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____2693 =
                                                   FStar_Options.hint_info ()
                                                    in
                                                 if uu____2693
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____2706 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist
                                                              in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____2706))
                                                     | FStar_Util.Inr errs ->
                                                         "failed"
                                                      in
                                                   query_info
                                                     FStar_Pervasives_Native.None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else ()
                                              in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____2719 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit)
                                               in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____2719
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____2722 =
                                              FStar_ST.read refinement_ok  in
                                            if uu____2722
                                            then
                                              let cutoff =
                                                (Prims.parse_int "10")  in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____2727 =
                                                     let uu____2730 =
                                                       FStar_Util.string_of_int
                                                         cutoff
                                                        in
                                                     [uu____2730]  in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____2727);
                                                  FStar_ST.write current_core
                                                    FStar_Pervasives_Native.None)
                                               else
                                                 refine_hint
                                                   (core_ext_max_dist +
                                                      (Prims.parse_int "1")))
                                            else ())))
                                       else ()))
                                   else ()  in
                                 (let z3cliopts_before =
                                    FStar_Options.z3_cliopt ()  in
                                  let log_queries_before =
                                    FStar_Options.log_queries ()  in
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool false);
                                  refine_hint (Prims.parse_int "1");
                                  (let uu____2747 =
                                     let uu____2748 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before
                                        in
                                     FStar_Options.List uu____2748  in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____2747);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____2753 = FStar_ST.read current_core
                                     in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____2753;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  })
                                  in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____2762 =
                                       let uu____2765 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ())
                                          in
                                       if uu____2765
                                       then
                                         let uu____2768 =
                                           let uu____2769 =
                                             FStar_Options.check_hints ()  in
                                           if uu____2769
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
                                             }
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____2768
                                       else hint_opt  in
                                     record_hint uu____2762))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____2775 =
                                       used_hint &&
                                         (FStar_Options.hint_info ())
                                        in
                                     if uu____2775
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
                                    (let uu____2789 =
                                       used_hint &&
                                         (FStar_Options.detail_hint_replay ())
                                        in
                                     if uu____2789
                                     then
                                       let ask_z3 label_assumptions =
                                         let res =
                                           FStar_Util.mk_ref
                                             FStar_Pervasives_Native.None
                                            in
                                         (let uu____2806 =
                                            with_fuel label_assumptions p1
                                              initial_config
                                             in
                                          FStar_SMTEncoding_Z3.ask
                                            (filter_assertions env unsat_core)
                                            all_labels uu____2806
                                            FStar_Pervasives_Native.None
                                            (fun r  ->
                                               FStar_ST.write res
                                                 (FStar_Pervasives_Native.Some
                                                    r)));
                                         (let uu____2815 = FStar_ST.read res
                                             in
                                          FStar_Option.get uu____2815)
                                          in
                                       FStar_SMTEncoding_ErrorReporting.detail_errors
                                         true env all_labels ask_z3
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope)))
                        in
                       ((let uu____2824 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ())
                            in
                         if uu____2824
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config  in
                         let uu____2831 =
                           let uu____2832 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____2832
                            in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____2831))
                    in
                 let process_query q = check q  in
                 let uu____2841 =
                   let uu____2848 = FStar_Options.admit_smt_queries ()  in
                   let uu____2849 = FStar_Options.admit_except ()  in
                   (uu____2848, uu____2849)  in
                 (match uu____2841 with
                  | (true ,uu____2854) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      process_query query
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let cur_id =
                        let uu____2865 =
                          let uu____2866 =
                            let uu____2867 =
                              let uu____2868 =
                                FStar_Util.string_of_int query_index  in
                              Prims.strcat uu____2868 ")"  in
                            Prims.strcat ", " uu____2867  in
                          Prims.strcat query_name uu____2866  in
                        Prims.strcat "(" uu____2865  in
                      if cur_id = id then process_query query else ()))
  
let solve :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2892 =
           let uu____2893 =
             let uu____2894 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2894  in
           FStar_Util.format1 "Starting query at %s" uu____2893  in
         FStar_SMTEncoding_Encode.push uu____2892);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____2896 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____2896 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2930 =
               let uu____2931 =
                 let uu____2932 =
                   let uu____2933 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2933
                    in
                 FStar_Util.format1 "Ending query at %s" uu____2932  in
               FStar_SMTEncoding_Encode.pop uu____2931  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2934);
                        FStar_SMTEncoding_Term.freevars = uu____2935;
                        FStar_SMTEncoding_Term.rng = uu____2936;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2937;
                    FStar_SMTEncoding_Term.assumption_name = uu____2938;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2939;_}
                  -> pop1 ()
              | uu____2954 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2955 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2957 -> failwith "Impossible"))
  
let solver : FStar_TypeChecker_Env.solver_t =
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
           let uu____2963 =
             let uu____2970 = FStar_Options.peek ()  in (e, g, uu____2970)
              in
           [uu____2963]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2985  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2987  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2989  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____2991  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____2993  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____2995  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2998  -> fun uu____2999  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3002  -> fun uu____3003  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3009 =
             let uu____3016 = FStar_Options.peek ()  in (e, g, uu____3016)
              in
           [uu____3009]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3032  -> fun uu____3033  -> fun uu____3034  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____3041  -> fun uu____3042  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____3044  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3046  -> ())
  } 
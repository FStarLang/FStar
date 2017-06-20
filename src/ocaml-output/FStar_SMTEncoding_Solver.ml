open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___84_23 =
  match uu___84_23 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____32) -> FStar_Util.Inr r 
type hint_stat =
  {
  hint: FStar_Util.hint option ;
  replay_result: z3_replay_result ;
  elapsed_time: Prims.int ;
  source_location: FStar_Range.range }
type hint_stats_t = hint_stat Prims.list
let recorded_hints : FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None 
let replaying_hints : FStar_Util.hints option FStar_ST.ref =
  FStar_Util.mk_ref None 
let hint_stats : hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let format_hints_file_name : Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____106 = FStar_Options.record_hints ()  in
   if uu____106 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____114 = FStar_Options.use_hints ()  in
   if uu____114
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename  in
     let val_filename = format_hints_file_name norm_src_filename  in
     let uu____117 = FStar_Util.read_hints val_filename  in
     match uu____117 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename
            in
         ((let uu____122 = FStar_Options.hint_info ()  in
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
         let uu____128 = FStar_Options.hint_info ()  in
         (if uu____128
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
  
let finalize_hints_db : Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____135 = FStar_Options.record_hints ()  in
     if uu____135
     then
       let hints =
         let uu____137 = FStar_ST.read recorded_hints  in
         FStar_Option.get uu____137  in
       let hints_db =
         let uu____143 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____143; FStar_Util.hints = hints }
          in
       let hints_file_name = format_hints_file_name src_filename  in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____147 = FStar_Options.hint_info ()  in
     if uu____147
     then
       let stats =
         let uu____150 = FStar_ST.read hint_stats  in
         FStar_All.pipe_right uu____150 FStar_List.rev  in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____160 =
                     FStar_Range.string_of_range s.source_location  in
                   let uu____161 = FStar_Util.string_of_int s.elapsed_time
                      in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____160 uu____161
               | FStar_Util.Inr _error ->
                   let uu____163 =
                     FStar_Range.string_of_range s.source_location  in
                   let uu____164 = FStar_Util.string_of_int s.elapsed_time
                      in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____163 uu____164))
     else ());
    FStar_ST.write recorded_hints None;
    FStar_ST.write replaying_hints None;
    FStar_ST.write hint_stats []
  
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f ()  in finalize_hints_db fname; result) 
let next_hint : Prims.string -> Prims.int -> FStar_Util.hint option =
  fun qname  ->
    fun qindex  ->
      let uu____204 = FStar_ST.read replaying_hints  in
      match uu____204 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___85_212  ->
               match uu___85_212 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____216 -> None)
      | uu____218 -> None
  
let record_hint : FStar_Util.hint option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___89_229 = h  in
             {
               FStar_Util.hint_name = (uu___89_229.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___89_229.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___89_229.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___89_229.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___89_229.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             })
       in
    let uu____230 = FStar_ST.read recorded_hints  in
    match uu____230 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____244 -> ()
  
let record_hint_stat :
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
            }  in
          let uu____261 =
            let uu____263 = FStar_ST.read hint_stats  in s :: uu____263  in
          FStar_ST.write hint_stats uu____261
  
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
        | uu____283 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____293 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid)))
         in
      let theory_rev = FStar_List.rev theory  in
      let uu____299 =
        FStar_List.fold_left
          (fun uu____308  ->
             fun d  ->
               match uu____308 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
                        let uu____329 =
                          matches_fact_ids include_assumption_names a  in
                        if uu____329
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
                    | uu____343 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev
         in
      match uu____299 with | (pruned_theory,uu____350) -> pruned_theory
  
let filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool)
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | None  ->
            let uu____371 = filter_using_facts_from e theory  in
            (uu____371, false)
        | Some core1 ->
            let uu____377 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____387  ->
                     match uu____387 with
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
                          | uu____419 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____377 with
             | (theory',n_retained,n_pruned) ->
                 let missed_assertions th core2 =
                   let missed =
                     let uu____442 =
                       FStar_All.pipe_right core2
                         (FStar_List.filter
                            (fun nm  ->
                               let uu____447 =
                                 FStar_All.pipe_right th
                                   (FStar_Util.for_some
                                      (fun uu___86_449  ->
                                         match uu___86_449 with
                                         | FStar_SMTEncoding_Term.Assume a ->
                                             nm =
                                               a.FStar_SMTEncoding_Term.assumption_name
                                         | uu____451 -> false))
                                  in
                               FStar_All.pipe_right uu____447
                                 Prims.op_Negation))
                        in
                     FStar_All.pipe_right uu____442
                       (FStar_String.concat ", ")
                      in
                   let included =
                     let uu____454 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___87_458  ->
                               match uu___87_458 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____461 -> []))
                        in
                     FStar_All.pipe_right uu____454
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included
                    in
                 ((let uu____464 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ())
                      in
                   if uu____464
                   then
                     let n1 = FStar_List.length core1  in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else ""  in
                     let uu____471 = FStar_Util.string_of_int n_retained  in
                     let uu____472 =
                       if n1 <> n_retained
                       then
                         let uu____475 = FStar_Util.string_of_int n1  in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____475 missed
                       else ""  in
                     let uu____480 = FStar_Util.string_of_int n_pruned  in
                     FStar_Util.print3
                       "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n"
                       uu____471 uu____472 uu____480
                   else ());
                  (let uu____482 =
                     let uu____484 =
                       let uu____486 =
                         let uu____487 =
                           let uu____488 =
                             FStar_All.pipe_right core1
                               (FStar_String.concat ", ")
                              in
                           Prims.strcat "UNSAT CORE: " uu____488  in
                         FStar_SMTEncoding_Term.Caption uu____487  in
                       [uu____486]  in
                     FStar_List.append theory' uu____484  in
                   (uu____482, true))))
  
let filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool)
  =
  fun e  ->
    fun x  ->
      let uu____500 = filter_using_facts_from e x  in (uu____500, false)
  
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
            (let uu____523 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1)  in
             match uu____523 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None  in
                 let set_minimum_workable_fuel f uu___88_579 =
                   match uu___88_579 with
                   | ([],uu____586) -> ()
                   | errs ->
                       let uu____592 = FStar_ST.read minimum_workable_fuel
                          in
                       (match uu____592 with
                        | Some uu____613 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs)))
                    in
                 let with_fuel label_assumptions p uu____677 =
                   match uu____677 with
                   | (n1,i,rlimit) ->
                       let uu____686 =
                         let uu____688 =
                           let uu____689 =
                             let uu____690 = FStar_Util.string_of_int n1  in
                             let uu____691 = FStar_Util.string_of_int i  in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____690 uu____691
                              in
                           FStar_SMTEncoding_Term.Caption uu____689  in
                         let uu____692 =
                           let uu____694 =
                             let uu____695 =
                               let uu____699 =
                                 let uu____700 =
                                   let uu____703 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", [])
                                      in
                                   let uu____705 =
                                     FStar_SMTEncoding_Term.n_fuel n1  in
                                   (uu____703, uu____705)  in
                                 FStar_SMTEncoding_Util.mkEq uu____700  in
                               (uu____699, None, "@MaxFuel_assumption")  in
                             FStar_SMTEncoding_Util.mkAssume uu____695  in
                           let uu____707 =
                             let uu____709 =
                               let uu____710 =
                                 let uu____714 =
                                   let uu____715 =
                                     let uu____718 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", [])
                                        in
                                     let uu____720 =
                                       FStar_SMTEncoding_Term.n_fuel i  in
                                     (uu____718, uu____720)  in
                                   FStar_SMTEncoding_Util.mkEq uu____715  in
                                 (uu____714, None, "@MaxIFuel_assumption")
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____710  in
                             [uu____709; p]  in
                           uu____694 :: uu____707  in
                         uu____688 :: uu____692  in
                       let uu____722 =
                         let uu____724 =
                           let uu____726 =
                             let uu____728 =
                               let uu____729 =
                                 let uu____732 =
                                   FStar_Util.string_of_int rlimit  in
                                 ("rlimit", uu____732)  in
                               FStar_SMTEncoding_Term.SetOption uu____729  in
                             [uu____728]  in
                           let uu____733 =
                             let uu____735 =
                               let uu____737 =
                                 let uu____739 =
                                   FStar_Options.record_hints ()  in
                                 if uu____739
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else []  in
                               let uu____742 =
                                 let uu____744 =
                                   let uu____746 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ())
                                      in
                                   if uu____746
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics]
                                   else []  in
                                 let uu____749 =
                                   let uu____751 =
                                     let uu____753 =
                                       FStar_Options.check_hints ()  in
                                     if uu____753
                                     then
                                       [FStar_SMTEncoding_Term.GetReasonUnknown]
                                     else []  in
                                   FStar_List.append uu____751 suffix  in
                                 FStar_List.append uu____744 uu____749  in
                               FStar_List.append uu____737 uu____742  in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____735
                              in
                           FStar_List.append uu____726 uu____733  in
                         FStar_List.append label_assumptions uu____724  in
                       FStar_List.append uu____686 uu____722
                    in
                 let check p =
                   let rlimit =
                     let uu____761 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____762 =
                       let uu____763 = FStar_Options.z3_rlimit ()  in
                       uu____763 * (Prims.parse_int "544656")  in
                     uu____761 * uu____762  in
                   let default_initial_config =
                     let uu____768 = FStar_Options.initial_fuel ()  in
                     let uu____769 = FStar_Options.initial_ifuel ()  in
                     (uu____768, uu____769, rlimit)  in
                   let hint_opt = next_hint query_name query_index  in
                   let uu____772 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____794 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656")))
                            in
                         (match uu____794 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout)))
                      in
                   match uu____772 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____845 =
                           let uu____851 =
                             let uu____857 =
                               let uu____862 =
                                 let uu____863 = FStar_Options.max_ifuel ()
                                    in
                                 let uu____864 =
                                   FStar_Options.initial_ifuel ()  in
                                 uu____863 > uu____864  in
                               if uu____862
                               then
                                 let uu____869 =
                                   let uu____873 =
                                     FStar_Options.initial_fuel ()  in
                                   let uu____874 = FStar_Options.max_ifuel ()
                                      in
                                   (uu____873, uu____874, rlimit)  in
                                 [uu____869]
                               else []  in
                             let uu____885 =
                               let uu____891 =
                                 let uu____896 =
                                   let uu____897 =
                                     let uu____898 =
                                       FStar_Options.max_fuel ()  in
                                     uu____898 / (Prims.parse_int "2")  in
                                   let uu____902 =
                                     FStar_Options.initial_fuel ()  in
                                   uu____897 > uu____902  in
                                 if uu____896
                                 then
                                   let uu____907 =
                                     let uu____911 =
                                       let uu____912 =
                                         FStar_Options.max_fuel ()  in
                                       uu____912 / (Prims.parse_int "2")  in
                                     let uu____916 =
                                       FStar_Options.max_ifuel ()  in
                                     (uu____911, uu____916, rlimit)  in
                                   [uu____907]
                                 else []  in
                               let uu____927 =
                                 let uu____933 =
                                   let uu____938 =
                                     (let uu____939 =
                                        FStar_Options.max_fuel ()  in
                                      let uu____940 =
                                        FStar_Options.initial_fuel ()  in
                                      uu____939 > uu____940) &&
                                       (let uu____941 =
                                          FStar_Options.max_ifuel ()  in
                                        let uu____942 =
                                          FStar_Options.initial_ifuel ()  in
                                        uu____941 >= uu____942)
                                      in
                                   if uu____938
                                   then
                                     let uu____947 =
                                       let uu____951 =
                                         FStar_Options.max_fuel ()  in
                                       let uu____952 =
                                         FStar_Options.max_ifuel ()  in
                                       (uu____951, uu____952, rlimit)  in
                                     [uu____947]
                                   else []  in
                                 let uu____963 =
                                   let uu____969 =
                                     let uu____974 =
                                       let uu____975 =
                                         FStar_Options.min_fuel ()  in
                                       let uu____976 =
                                         FStar_Options.initial_fuel ()  in
                                       uu____975 < uu____976  in
                                     if uu____974
                                     then
                                       let uu____981 =
                                         let uu____985 =
                                           FStar_Options.min_fuel ()  in
                                         (uu____985, (Prims.parse_int "1"),
                                           rlimit)
                                          in
                                       [uu____981]
                                     else []  in
                                   [uu____969]  in
                                 uu____933 :: uu____963  in
                               uu____891 :: uu____927  in
                             uu____857 :: uu____885  in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____851
                            in
                         FStar_List.flatten uu____845  in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____1049 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____1050 = FStar_Options.n_cores ()  in
                                uu____1050 = (Prims.parse_int "1"))
                              in
                           if uu____1049
                           then
                             let uu____1051 =
                               let uu____1060 =
                                 FStar_ST.read minimum_workable_fuel  in
                               match uu____1060 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____1125 =
                                     let uu____1129 =
                                       FStar_Options.min_fuel ()  in
                                     (uu____1129, (Prims.parse_int "1"),
                                       rlimit)
                                      in
                                   (uu____1125, errs)
                                in
                             match uu____1051 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None  in
                                   (let uu____1159 =
                                      with_fuel label_assumptions p1
                                        min_fuel1
                                       in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____1159 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____1165 = FStar_ST.read res  in
                                    FStar_Option.get uu____1165)
                                    in
                                 let uu____1170 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3
                                    in
                                 (uu____1170, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1210,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)], (snd errs))
                              | uu____1229 -> errs)
                            in
                         record_hint None;
                         (let uu____1232 = FStar_Options.print_fuels ()  in
                          if uu____1232
                          then
                            let uu____1233 =
                              let uu____1234 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Range.string_of_range uu____1234  in
                            let uu____1235 =
                              let uu____1236 = FStar_Options.max_fuel ()  in
                              FStar_All.pipe_right uu____1236
                                FStar_Util.string_of_int
                               in
                            let uu____1237 =
                              let uu____1238 = FStar_Options.max_ifuel ()  in
                              FStar_All.pipe_right uu____1238
                                FStar_Util.string_of_int
                               in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1233 uu____1235 uu____1237
                          else ());
                         (let uu____1240 =
                            FStar_All.pipe_right (fst errs1)
                              (FStar_List.map
                                 (fun uu____1252  ->
                                    match uu____1252 with
                                    | (uu____1258,x,y) -> (x, y)))
                             in
                          FStar_TypeChecker_Err.add_errors env uu____1240)
                          in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____1274),uu____1275) -> result
                         | (uu____1280,FStar_Util.Inl uu____1281) -> result
                         | (uu____1288,FStar_Util.Inr uu____1289) ->
                             FStar_Util.Inr errs
                          in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (snd errs)) with
                          | ([],uu____1356) -> report1 p1 errs
                          | (uu____1364,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____1375) ->
                              let uu____1390 = with_fuel [] p1 mi  in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____1390 (Some scope)
                                (fun uu____1392  ->
                                   match uu____1392 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____1404 =
                                         let uu____1408 =
                                           use_errors errs result  in
                                         (uu____1408, elapsed_time,
                                           statistics)
                                          in
                                       cb false mi p1 tl1 scope uu____1404))
                       
                       and cb used_hint uu____1410 p1 alt scope uu____1414 =
                         match (uu____1410, uu____1414) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1445 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1445))
                              else ();
                              (let uu____1448 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ())
                                  in
                               if uu____1448
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____1467 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ())
                                    in
                                 if uu____1467
                                 then
                                   let uu____1468 =
                                     let uu____1470 =
                                       let uu____1472 =
                                         match env1 with
                                         | Some e ->
                                             let uu____1474 =
                                               let uu____1475 =
                                                 let uu____1476 =
                                                   FStar_TypeChecker_Env.get_range
                                                     e
                                                    in
                                                 FStar_Range.string_of_range
                                                   uu____1476
                                                  in
                                               let uu____1477 =
                                                 let uu____1478 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     ()
                                                    in
                                                 Prims.strcat uu____1478 ")"
                                                  in
                                               Prims.strcat uu____1475
                                                 uu____1477
                                                in
                                             Prims.strcat "(" uu____1474
                                         | None  -> ""  in
                                       let uu____1479 =
                                         let uu____1481 =
                                           let uu____1483 =
                                             let uu____1485 =
                                               FStar_Util.string_of_int
                                                 query_index
                                                in
                                             let uu____1486 =
                                               let uu____1488 =
                                                 let uu____1490 =
                                                   let uu____1492 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time
                                                      in
                                                   let uu____1493 =
                                                     let uu____1495 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel
                                                        in
                                                     let uu____1496 =
                                                       let uu____1498 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel
                                                          in
                                                       let uu____1499 =
                                                         let uu____1501 =
                                                           FStar_Util.string_of_int
                                                             rlimit
                                                            in
                                                         [uu____1501]  in
                                                       uu____1498 ::
                                                         uu____1499
                                                        in
                                                     uu____1495 :: uu____1496
                                                      in
                                                   uu____1492 :: uu____1493
                                                    in
                                                 (match env1 with
                                                  | Some e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | None  -> "") ::
                                                   uu____1490
                                                  in
                                               tag :: uu____1488  in
                                             uu____1485 :: uu____1486  in
                                           query_name :: uu____1483  in
                                         name :: uu____1481  in
                                       uu____1472 :: uu____1479  in
                                     let uu____1504 =
                                       let uu____1506 =
                                         let uu____1507 =
                                           FStar_Options.print_z3_statistics
                                             ()
                                            in
                                         if uu____1507
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
                                           let uu____1519 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1"))
                                              in
                                           Prims.strcat uu____1519 "}"
                                         else
                                           (let uu____1524 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown"
                                               in
                                            match uu____1524 with
                                            | Some v1 ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____1527 -> "")
                                          in
                                       [uu____1506]  in
                                     FStar_List.append uu____1470 uu____1504
                                      in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____1468
                                 else ()  in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1  in
                                 let hint_worked = FStar_Util.mk_ref false
                                    in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____1547 =
                                     let uu____1548 =
                                       FStar_ST.read hint_worked  in
                                     Prims.op_Negation uu____1548  in
                                   if uu____1547
                                   then
                                     let hint_check_cb uu____1562 =
                                       match uu____1562 with
                                       | (result1,elapsed_time1,statistics1)
                                           ->
                                           let tag =
                                             match result1 with
                                             | FStar_Util.Inl uu____1585 ->
                                                 (FStar_ST.write hint_worked
                                                    true;
                                                  "succeeded")
                                             | FStar_Util.Inr uu____1591 ->
                                                 "failed"
                                              in
                                           let uu____1596 =
                                             FStar_Options.hint_info ()  in
                                           if uu____1596
                                           then
                                             query_info None "Hint-check" tag
                                               statistics1
                                           else ()
                                        in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____1600 =
                                         let uu____1605 =
                                           FStar_ST.read current_core  in
                                         filter_assertions env uu____1605  in
                                       let uu____1608 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit)
                                          in
                                       FStar_SMTEncoding_Z3.ask uu____1600
                                         all_labels uu____1608 (Some scope1)
                                         hint_check_cb);
                                      (let uu____1610 =
                                         let uu____1611 =
                                           FStar_ST.read hint_worked  in
                                         Prims.op_Negation uu____1611  in
                                       if uu____1610
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false  in
                                         ((let uu____1618 =
                                             let uu____1619 =
                                               let uu____1621 =
                                                 let uu____1623 =
                                                   let uu____1624 =
                                                     let uu____1625 =
                                                       let uu____1627 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist
                                                          in
                                                       [uu____1627]  in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____1625
                                                      in
                                                   FStar_Options.String
                                                     uu____1624
                                                    in
                                                 [uu____1623]  in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____1621
                                                in
                                             FStar_Options.List uu____1619
                                              in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____1618);
                                          (let hint_refinement_cb uu____1639
                                             =
                                             match uu____1639 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____1661 =
                                                   FStar_Options.hint_info ()
                                                    in
                                                 if uu____1661
                                                 then
                                                   let tag =
                                                     match result1 with
                                                     | FStar_Util.Inl uc ->
                                                         (FStar_ST.write
                                                            refinement_ok
                                                            true;
                                                          FStar_ST.write
                                                            current_core uc;
                                                          (let uu____1672 =
                                                             FStar_Util.string_of_int
                                                               core_ext_max_dist
                                                              in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____1672))
                                                     | FStar_Util.Inr errs ->
                                                         "failed"
                                                      in
                                                   query_info None
                                                     "Hint-refinement" tag
                                                     statistics1
                                                 else ()
                                              in
                                           FStar_SMTEncoding_Z3.refresh ();
                                           (let uu____1681 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit)
                                               in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____1681
                                              (Some scope1)
                                              hint_refinement_cb);
                                           (let uu____1683 =
                                              FStar_ST.read refinement_ok  in
                                            if uu____1683
                                            then
                                              let cutoff =
                                                (Prims.parse_int "10")  in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____1688 =
                                                     let uu____1690 =
                                                       FStar_Util.string_of_int
                                                         cutoff
                                                        in
                                                     [uu____1690]  in
                                                   FStar_Util.print
                                                     "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement."
                                                     uu____1688);
                                                  FStar_ST.write current_core
                                                    None)
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
                                  (let uu____1705 =
                                     let uu____1706 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before
                                        in
                                     FStar_Options.List uu____1706  in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____1705);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____1709 = FStar_ST.read current_core
                                     in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____1709;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  })
                                  in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info (Some env) "Query-stats"
                                      "succeeded" statistics;
                                    (let uu____1716 =
                                       let uu____1718 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ())
                                          in
                                       if uu____1718
                                       then
                                         let uu____1720 =
                                           let uu____1721 =
                                             FStar_Options.check_hints ()  in
                                           if uu____1721
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
                                         Some uu____1720
                                       else hint_opt  in
                                     record_hint uu____1716))
                               | FStar_Util.Inr errs ->
                                   (query_info (Some env) "Query-stats"
                                      "failed" statistics;
                                    (let uu____1727 =
                                       used_hint &&
                                         (FStar_Options.hint_info ())
                                        in
                                     if uu____1727
                                     then
                                       (FStar_Util.print_string
                                          "Failed hint:\n";
                                        (match unsat_core with
                                         | None  ->
                                             FStar_Util.print_string
                                               "<empty>"
                                         | Some core ->
                                             ((let uu____1734 =
                                                 FStar_List.map
                                                   (fun x  ->
                                                      FStar_Util.print_string
                                                        (Prims.strcat " " x))
                                                   core
                                                  in
                                               ());
                                              FStar_Util.print_string "\n")))
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope)))
                        in
                       ((let uu____1740 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ())
                            in
                         if uu____1740
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config  in
                         let uu____1745 =
                           let uu____1746 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1746
                            in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           None uu____1745))
                    in
                 let process_query q = check q  in
                 let uu____1754 = FStar_Options.admit_smt_queries ()  in
                 if uu____1754 then () else process_query query)
  
let solve :
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1773 =
           let uu____1774 =
             let uu____1775 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1775  in
           FStar_Util.format1 "Starting query at %s" uu____1774  in
         FStar_SMTEncoding_Encode.push uu____1773);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____1777 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____1777 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1798 =
               let uu____1799 =
                 let uu____1800 =
                   let uu____1801 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1801
                    in
                 FStar_Util.format1 "Ending query at %s" uu____1800  in
               FStar_SMTEncoding_Encode.pop uu____1799  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____1802);
                        FStar_SMTEncoding_Term.freevars = uu____1803;
                        FStar_SMTEncoding_Term.rng = uu____1804;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____1805;
                    FStar_SMTEncoding_Term.assumption_name = uu____1806;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____1807;_}
                  -> pop1 ()
              | uu____1815 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____1816 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1818 -> failwith "Impossible"))
  
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
           let uu____1821 =
             let uu____1825 = FStar_Options.peek ()  in (e, g, uu____1825)
              in
           [uu____1821]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1832  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1833  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1834  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1835  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1836  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1837  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1838  -> fun uu____1839  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1840  -> fun uu____1841  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____1844 =
             let uu____1848 = FStar_Options.peek ()  in (e, g, uu____1848)
              in
           [uu____1844]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1855  -> fun uu____1856  -> fun uu____1857  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1861  -> fun uu____1862  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1863  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1864  -> ())
  } 
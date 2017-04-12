open Prims
type z3_err =
  (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)
type z3_result = (FStar_SMTEncoding_Z3.unsat_core,z3_err) FStar_Util.either
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result uu___91_23 =
  match uu___91_23 with
  | FStar_Util.Inl l -> FStar_Util.Inl l
  | FStar_Util.Inr (r,uu____32) -> FStar_Util.Inr r 
type hint_stat =
  {
  hint: FStar_Util.hint Prims.option ;
  replay_result: z3_replay_result ;
  elapsed_time: Prims.int ;
  source_location: FStar_Range.range }
type hint_stats_t = hint_stat Prims.list
let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None 
let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref =
  FStar_Util.mk_ref None 
let hint_stats : hint_stat Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let format_hints_file_name : Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db src_filename force_record =
  FStar_ST.write hint_stats [];
  (let uu____102 = FStar_Options.record_hints ()  in
   if uu____102 then FStar_ST.write recorded_hints (Some []) else ());
  (let uu____110 = FStar_Options.use_hints ()  in
   if uu____110
   then
     let norm_src_filename = FStar_Util.normalize_file_path src_filename  in
     let val_filename = format_hints_file_name norm_src_filename  in
     let uu____113 = FStar_Util.read_hints val_filename  in
     match uu____113 with
     | Some hints ->
         let expected_digest = FStar_Util.digest_of_file norm_src_filename
            in
         ((let uu____118 = FStar_Options.hint_info ()  in
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
         let uu____124 = FStar_Options.hint_info ()  in
         (if uu____124
          then
            FStar_Util.print1 "(%s) Unable to read hints db.\n"
              norm_src_filename
          else ())
   else ())
  
let finalize_hints_db : Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____131 = FStar_Options.record_hints ()  in
     if uu____131
     then
       let hints =
         let uu____133 = FStar_ST.read recorded_hints  in
         FStar_Option.get uu____133  in
       let hints_db =
         let uu____139 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____139; FStar_Util.hints = hints }
          in
       let hints_file_name = format_hints_file_name src_filename  in
       FStar_Util.write_hints hints_file_name hints_db
     else ());
    (let uu____143 = FStar_Options.hint_info ()  in
     if uu____143
     then
       let stats =
         let uu____146 = FStar_ST.read hint_stats  in
         FStar_All.pipe_right uu____146 FStar_List.rev  in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               match s.replay_result with
               | FStar_Util.Inl _unsat_core ->
                   let uu____156 =
                     FStar_Range.string_of_range s.source_location  in
                   let uu____157 = FStar_Util.string_of_int s.elapsed_time
                      in
                   FStar_Util.print2
                     "Hint-info (%s): Replay succeeded in %s milliseconds\n"
                     uu____156 uu____157
               | FStar_Util.Inr _error ->
                   let uu____159 =
                     FStar_Range.string_of_range s.source_location  in
                   let uu____160 = FStar_Util.string_of_int s.elapsed_time
                      in
                   FStar_Util.print2
                     "Hint-info (%s): Replay failed in %s milliseconds\n"
                     uu____159 uu____160))
     else ());
    FStar_ST.write recorded_hints None;
    FStar_ST.write replaying_hints None;
    FStar_ST.write hint_stats []
  
let with_hints_db fname f =
  initialize_hints_db fname false;
  (let result = f ()  in finalize_hints_db fname; result) 
let next_hint : Prims.string -> Prims.int -> FStar_Util.hint Prims.option =
  fun qname  ->
    fun qindex  ->
      let uu____200 = FStar_ST.read replaying_hints  in
      match uu____200 with
      | Some hints ->
          FStar_Util.find_map hints
            (fun uu___92_208  ->
               match uu___92_208 with
               | Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> Some hint
               | uu____212 -> None)
      | uu____214 -> None
  
let record_hint : FStar_Util.hint Prims.option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | None  -> None
      | Some h ->
          Some
            (let uu___94_225 = h  in
             {
               FStar_Util.hint_name = (uu___94_225.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___94_225.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___94_225.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___94_225.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___94_225.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             })
       in
    let uu____226 = FStar_ST.read recorded_hints  in
    match uu____226 with
    | Some l ->
        FStar_ST.write recorded_hints (Some (FStar_List.append l [hint1]))
    | uu____240 -> ()
  
let record_hint_stat :
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
            }  in
          let uu____257 =
            let uu____259 = FStar_ST.read hint_stats  in s :: uu____259  in
          FStar_ST.write hint_stats uu____257
  
let ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) *
      Prims.string * FStar_Range.range) Prims.list ->
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
            (let uu____299 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | None  -> failwith "No query name set!"
               | Some (q,n1) -> ((FStar_Ident.text_of_lid q), n1)  in
             match uu____299 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel = FStar_Util.mk_ref None  in
                 let set_minimum_workable_fuel f uu___93_355 =
                   match uu___93_355 with
                   | ([],uu____362) -> ()
                   | errs ->
                       let uu____368 = FStar_ST.read minimum_workable_fuel
                          in
                       (match uu____368 with
                        | Some uu____389 -> ()
                        | None  ->
                            FStar_ST.write minimum_workable_fuel
                              (Some (f, errs)))
                    in
                 let with_fuel label_assumptions p uu____453 =
                   match uu____453 with
                   | (n1,i,rlimit) ->
                       let uu____462 =
                         let uu____464 =
                           let uu____465 =
                             let uu____466 = FStar_Util.string_of_int n1  in
                             let uu____467 = FStar_Util.string_of_int i  in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____466 uu____467
                              in
                           FStar_SMTEncoding_Term.Caption uu____465  in
                         let uu____468 =
                           let uu____470 =
                             let uu____471 =
                               let uu____476 =
                                 let uu____477 =
                                   let uu____480 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", [])
                                      in
                                   let uu____482 =
                                     FStar_SMTEncoding_Term.n_fuel n1  in
                                   (uu____480, uu____482)  in
                                 FStar_SMTEncoding_Util.mkEq uu____477  in
                               (uu____476, None, None)  in
                             FStar_SMTEncoding_Term.Assume uu____471  in
                           let uu____485 =
                             let uu____487 =
                               let uu____488 =
                                 let uu____493 =
                                   let uu____494 =
                                     let uu____497 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", [])
                                        in
                                     let uu____499 =
                                       FStar_SMTEncoding_Term.n_fuel i  in
                                     (uu____497, uu____499)  in
                                   FStar_SMTEncoding_Util.mkEq uu____494  in
                                 (uu____493, None, None)  in
                               FStar_SMTEncoding_Term.Assume uu____488  in
                             [uu____487; p]  in
                           uu____470 :: uu____485  in
                         uu____464 :: uu____468  in
                       let uu____502 =
                         let uu____504 =
                           let uu____506 =
                             let uu____508 =
                               let uu____509 =
                                 let uu____512 =
                                   FStar_Util.string_of_int rlimit  in
                                 ("rlimit", uu____512)  in
                               FStar_SMTEncoding_Term.SetOption uu____509  in
                             [uu____508]  in
                           let uu____513 =
                             let uu____515 =
                               let uu____517 =
                                 let uu____519 =
                                   FStar_Options.record_hints ()  in
                                 if uu____519
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else []  in
                               FStar_List.append uu____517 suffix  in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____515
                              in
                           FStar_List.append uu____506 uu____513  in
                         FStar_List.append label_assumptions uu____504  in
                       FStar_List.append uu____462 uu____502
                    in
                 let check p =
                   let rlimit =
                     let uu____527 = FStar_Options.z3_rlimit ()  in
                     uu____527 * (Prims.parse_int "544656")  in
                   let default_initial_config =
                     let uu____532 = FStar_Options.initial_fuel ()  in
                     let uu____533 = FStar_Options.initial_ifuel ()  in
                     (uu____532, uu____533, rlimit)  in
                   let hint_opt = next_hint query_name query_index  in
                   let uu____536 =
                     match hint_opt with
                     | None  -> (None, default_initial_config)
                     | Some hint ->
                         let uu____558 =
                           if FStar_Option.isSome hint.FStar_Util.unsat_core
                           then ((hint.FStar_Util.unsat_core), rlimit)
                           else
                             (None,
                               ((Prims.parse_int "60") *
                                  (Prims.parse_int "544656")))
                            in
                         (match uu____558 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout)))
                      in
                   match uu____536 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____609 =
                           let uu____615 =
                             let uu____621 =
                               let uu____626 =
                                 let uu____627 = FStar_Options.max_ifuel ()
                                    in
                                 let uu____628 =
                                   FStar_Options.initial_ifuel ()  in
                                 uu____627 > uu____628  in
                               if uu____626
                               then
                                 let uu____633 =
                                   let uu____637 =
                                     FStar_Options.initial_fuel ()  in
                                   let uu____638 = FStar_Options.max_ifuel ()
                                      in
                                   (uu____637, uu____638, rlimit)  in
                                 [uu____633]
                               else []  in
                             let uu____649 =
                               let uu____655 =
                                 let uu____660 =
                                   let uu____661 =
                                     let uu____662 =
                                       FStar_Options.max_fuel ()  in
                                     uu____662 / (Prims.parse_int "2")  in
                                   let uu____666 =
                                     FStar_Options.initial_fuel ()  in
                                   uu____661 > uu____666  in
                                 if uu____660
                                 then
                                   let uu____671 =
                                     let uu____675 =
                                       let uu____676 =
                                         FStar_Options.max_fuel ()  in
                                       uu____676 / (Prims.parse_int "2")  in
                                     let uu____680 =
                                       FStar_Options.max_ifuel ()  in
                                     (uu____675, uu____680, rlimit)  in
                                   [uu____671]
                                 else []  in
                               let uu____691 =
                                 let uu____697 =
                                   let uu____702 =
                                     (let uu____703 =
                                        FStar_Options.max_fuel ()  in
                                      let uu____704 =
                                        FStar_Options.initial_fuel ()  in
                                      uu____703 > uu____704) &&
                                       (let uu____705 =
                                          FStar_Options.max_ifuel ()  in
                                        let uu____706 =
                                          FStar_Options.initial_ifuel ()  in
                                        uu____705 > uu____706)
                                      in
                                   if uu____702
                                   then
                                     let uu____711 =
                                       let uu____715 =
                                         FStar_Options.max_fuel ()  in
                                       let uu____716 =
                                         FStar_Options.max_ifuel ()  in
                                       (uu____715, uu____716, rlimit)  in
                                     [uu____711]
                                   else []  in
                                 let uu____727 =
                                   let uu____733 =
                                     let uu____738 =
                                       let uu____739 =
                                         FStar_Options.min_fuel ()  in
                                       let uu____740 =
                                         FStar_Options.initial_fuel ()  in
                                       uu____739 < uu____740  in
                                     if uu____738
                                     then
                                       let uu____745 =
                                         let uu____749 =
                                           FStar_Options.min_fuel ()  in
                                         (uu____749, (Prims.parse_int "1"),
                                           rlimit)
                                          in
                                       [uu____745]
                                     else []  in
                                   [uu____733]  in
                                 uu____697 :: uu____727  in
                               uu____655 :: uu____691  in
                             uu____621 :: uu____649  in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____615
                            in
                         FStar_List.flatten uu____609  in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____813 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____814 = FStar_Options.n_cores ()  in
                                uu____814 = (Prims.parse_int "1"))
                              in
                           if uu____813
                           then
                             let uu____815 =
                               let uu____824 =
                                 FStar_ST.read minimum_workable_fuel  in
                               match uu____824 with
                               | Some (f,errs1) -> (f, errs1)
                               | None  ->
                                   let uu____889 =
                                     let uu____893 =
                                       FStar_Options.min_fuel ()  in
                                     (uu____893, (Prims.parse_int "1"),
                                       rlimit)
                                      in
                                   (uu____889, errs)
                                in
                             match uu____815 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res = FStar_Util.mk_ref None  in
                                   (let uu____947 =
                                      with_fuel label_assumptions p1
                                        min_fuel1
                                       in
                                    FStar_SMTEncoding_Z3.ask None all_labels
                                      uu____947 None
                                      (fun r  -> FStar_ST.write res (Some r)));
                                   (let uu____972 = FStar_ST.read res  in
                                    FStar_Option.get uu____972)
                                    in
                                 let uu____995 =
                                   FStar_SMTEncoding_ErrorReporting.detail_errors
                                     env all_labels ask_z3
                                    in
                                 (uu____995, FStar_SMTEncoding_Z3.Default)
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
                              | (uu____1035,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (Prims.snd errs))
                              | uu____1054 -> errs)
                            in
                         record_hint None;
                         (let uu____1057 = FStar_Options.print_fuels ()  in
                          if uu____1057
                          then
                            let uu____1058 =
                              let uu____1059 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Range.string_of_range uu____1059  in
                            let uu____1060 =
                              let uu____1061 = FStar_Options.max_fuel ()  in
                              FStar_All.pipe_right uu____1061
                                FStar_Util.string_of_int
                               in
                            let uu____1062 =
                              let uu____1063 = FStar_Options.max_ifuel ()  in
                              FStar_All.pipe_right uu____1063
                                FStar_Util.string_of_int
                               in
                            FStar_Util.print3
                              "(%s) Query failed with maximum fuel %s and ifuel %s\n"
                              uu____1058 uu____1060 uu____1062
                          else ());
                         (let uu____1065 =
                            FStar_All.pipe_right (Prims.fst errs1)
                              (FStar_List.map
                                 (fun uu____1077  ->
                                    match uu____1077 with
                                    | (uu____1083,x,y) -> (x, y)))
                             in
                          FStar_TypeChecker_Err.add_errors env uu____1065)
                          in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],_),_)|(_,FStar_Util.Inl _) -> result
                         | (uu____1111,FStar_Util.Inr uu____1112) ->
                             FStar_Util.Inr errs
                          in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (Prims.snd errs)) with
                          | ([],_)|(_,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::[],uu____1196) ->
                              (match errs with
                               | ([],uu____1210) ->
                                   let uu____1212 = with_fuel [] p1 mi  in
                                   FStar_SMTEncoding_Z3.ask None all_labels
                                     uu____1212 (Some scope)
                                     (cb false mi p1 [] scope)
                               | uu____1218 ->
                                   (set_minimum_workable_fuel prev_f errs;
                                    report1 p1 errs))
                          | (mi::tl1,uu____1222) ->
                              let uu____1237 = with_fuel [] p1 mi  in
                              FStar_SMTEncoding_Z3.ask None all_labels
                                uu____1237 (Some scope)
                                (fun uu____1240  ->
                                   match uu____1240 with
                                   | (result,elapsed_time) ->
                                       let uu____1257 =
                                         let uu____1264 =
                                           use_errors errs result  in
                                         (uu____1264, elapsed_time)  in
                                       cb false mi p1 tl1 scope uu____1257))
                       
                       and cb used_hint uu____1266 p1 alt scope uu____1270 =
                         match (uu____1266, uu____1270) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____1317 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____1317))
                              else ();
                              (let uu____1320 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.print_z3_statistics ())
                                  in
                               if uu____1320
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info tag =
                                 let uu____1326 =
                                   let uu____1328 =
                                     let uu____1329 =
                                       FStar_TypeChecker_Env.get_range env
                                        in
                                     FStar_Range.string_of_range uu____1329
                                      in
                                   let uu____1330 =
                                     let uu____1332 =
                                       FStar_SMTEncoding_Z3.at_log_file ()
                                        in
                                     let uu____1333 =
                                       let uu____1335 =
                                         let uu____1337 =
                                           FStar_Util.string_of_int
                                             query_index
                                            in
                                         let uu____1338 =
                                           let uu____1340 =
                                             let uu____1342 =
                                               let uu____1344 =
                                                 FStar_Util.string_of_int
                                                   elapsed_time
                                                  in
                                               let uu____1345 =
                                                 let uu____1347 =
                                                   FStar_Util.string_of_int
                                                     prev_fuel
                                                    in
                                                 let uu____1348 =
                                                   let uu____1350 =
                                                     FStar_Util.string_of_int
                                                       prev_ifuel
                                                      in
                                                   [uu____1350]  in
                                                 uu____1347 :: uu____1348  in
                                               uu____1344 :: uu____1345  in
                                             (if used_hint
                                              then " (with hint)"
                                              else "") :: uu____1342
                                              in
                                           tag :: uu____1340  in
                                         uu____1337 :: uu____1338  in
                                       query_name :: uu____1335  in
                                     uu____1332 :: uu____1333  in
                                   uu____1328 :: uu____1330  in
                                 FStar_Util.print
                                   "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n"
                                   uu____1326
                                  in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (if Prims.op_Negation used_hint
                                    then
                                      (let hint =
                                         {
                                           FStar_Util.hint_name = query_name;
                                           FStar_Util.hint_index =
                                             query_index;
                                           FStar_Util.fuel = prev_fuel;
                                           FStar_Util.ifuel = prev_ifuel;
                                           FStar_Util.unsat_core =
                                             unsat_core1;
                                           FStar_Util.query_elapsed_time =
                                             elapsed_time
                                         }  in
                                       record_hint (Some hint))
                                    else record_hint hint_opt;
                                    (let uu____1358 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ())
                                        in
                                     if uu____1358
                                     then query_info "succeeded"
                                     else ()))
                               | FStar_Util.Inr errs ->
                                   ((let uu____1366 =
                                       (FStar_Options.print_fuels ()) ||
                                         (FStar_Options.hint_info ())
                                        in
                                     if uu____1366
                                     then query_info "failed"
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope)))
                        in
                       (if FStar_Option.isSome unsat_core
                        then FStar_SMTEncoding_Z3.refresh ()
                        else ();
                        (let uu____1371 = with_fuel [] p initial_config  in
                         let uu____1373 =
                           let uu____1382 =
                             FStar_ST.read FStar_SMTEncoding_Z3.fresh_scope
                              in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____1382
                            in
                         FStar_SMTEncoding_Z3.ask unsat_core all_labels
                           uu____1371 None uu____1373))
                    in
                 let process_query q =
                   let uu____1392 =
                     let uu____1393 = FStar_Options.split_cases ()  in
                     uu____1393 > (Prims.parse_int "0")  in
                   if uu____1392
                   then
                     let uu____1394 =
                       let uu____1403 = FStar_Options.split_cases ()  in
                       FStar_SMTEncoding_SplitQueryCases.can_handle_query
                         uu____1403 q
                        in
                     match uu____1394 with
                     | (b,cb) ->
                         (if b
                          then
                            FStar_SMTEncoding_SplitQueryCases.handle_query cb
                              check
                          else check q)
                   else check q  in
                 let uu____1420 = FStar_Options.admit_smt_queries ()  in
                 if uu____1420 then () else process_query query)
  
let solve :
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____1439 =
           let uu____1440 =
             let uu____1441 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____1441  in
           FStar_Util.format1 "Starting query at %s" uu____1440  in
         FStar_SMTEncoding_Encode.push uu____1439);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____1443 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____1443 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____1464 =
               let uu____1465 =
                 let uu____1466 =
                   let uu____1467 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____1467
                    in
                 FStar_Util.format1 "Ending query at %s" uu____1466  in
               FStar_SMTEncoding_Encode.pop uu____1465  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  ({
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.FalseOp ,uu____1468);
                     FStar_SMTEncoding_Term.freevars = uu____1469;
                     FStar_SMTEncoding_Term.rng = uu____1470;_},uu____1471,uu____1472)
                  -> pop1 ()
              | uu____1482 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume (q1,uu____1485,uu____1486) ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____1490 -> failwith "Impossible"))
  
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
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____1497  -> ());
    FStar_TypeChecker_Env.push = (fun uu____1498  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____1499  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____1500  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____1501  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____1502  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____1503  -> fun uu____1504  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____1505  -> fun uu____1506  -> ());
    FStar_TypeChecker_Env.preprocess = (fun e  -> fun g  -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu____1513  -> fun uu____1514  -> fun uu____1515  -> ());
    FStar_TypeChecker_Env.is_trivial =
      (fun uu____1519  -> fun uu____1520  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____1521  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____1522  -> ())
  } 
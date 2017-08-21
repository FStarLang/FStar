open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
<<<<<<< HEAD
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
  'Auu____172 . Prims.string -> 'Auu____172 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      FStar_ST.op_Colon_Equals hint_stats [];
      (let uu____201 = FStar_Options.record_hints ()  in
       if uu____201
=======
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____15,('Auu____14,'Auu____13) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____15,'Auu____14) FStar_Util.either=
  fun uu___85_31  ->
    match uu___85_31 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____46) -> FStar_Util.Inr r
let (recorded_hints
  :FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref)=
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints
  :FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref)=
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (format_hints_file_name :Prims.string -> Prims.string)=
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db :
  'Auu____87 . Prims.string -> 'Auu____87 -> Prims.unit=
  fun src_filename  ->
    fun format_filename  ->
      (let uu____97 = FStar_Options.record_hints () in
       if uu____97
>>>>>>> taramana_pointers_with_codes_modifies
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
<<<<<<< HEAD
      (let uu____227 = FStar_Options.use_hints ()  in
       if uu____227
=======
      (let uu____123 = FStar_Options.use_hints () in
       if uu____123
>>>>>>> taramana_pointers_with_codes_modifies
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
<<<<<<< HEAD
           let uu____230 = FStar_Options.hint_file ()  in
           match uu____230 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____234 = FStar_Util.read_hints val_filename  in
         match uu____234 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____240 = FStar_Options.hint_info ()  in
               if uu____240
               then
                 let uu____241 =
                   let uu____242 = FStar_Options.hint_file ()  in
                   match uu____242 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____246 -> ""  in
=======
           let uu____126 = FStar_Options.hint_file () in
           match uu____126 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____130 = FStar_Util.read_hints val_filename in
         match uu____130 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____136 = FStar_Options.hint_info () in
               if uu____136
               then
                 let uu____137 =
                   let uu____138 = FStar_Options.hint_file () in
                   match uu____138 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____142 -> "" in
>>>>>>> taramana_pointers_with_codes_modifies
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____137
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
<<<<<<< HEAD
             let uu____269 = FStar_Options.hint_info ()  in
             (if uu____269
=======
             let uu____165 = FStar_Options.hint_info () in
             (if uu____165
>>>>>>> taramana_pointers_with_codes_modifies
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
<<<<<<< HEAD
  
let finalize_hints_db : Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____277 = FStar_Options.record_hints ()  in
     if uu____277
     then
       let hints =
         let uu____279 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____279  in
       let hints_db =
         let uu____301 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____301; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____304 = FStar_Options.hint_file ()  in
         match uu____304 with
=======
let (finalize_hints_db :Prims.string -> Prims.unit)=
  fun src_filename  ->
    (let uu____173 = FStar_Options.record_hints () in
     if uu____173
     then
       let hints =
         let uu____175 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____175 in
       let hints_db =
         let uu____197 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____197; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____200 = FStar_Options.hint_file () in
         match uu____200 with
>>>>>>> taramana_pointers_with_codes_modifies
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename
          in
       FStar_Util.write_hints val_filename hints_db
     else ());
<<<<<<< HEAD
    (let uu____310 = FStar_Options.hint_info ()  in
     if uu____310
     then
       let stats =
         let uu____314 = FStar_ST.op_Bang hint_stats  in
         FStar_All.pipe_right uu____314 FStar_List.rev  in
       FStar_All.pipe_right stats
         (FStar_List.iter
            (fun s  ->
               let uu____345 = FStar_Range.string_of_range s.source_location
                  in
               let uu____346 = FStar_Util.string_of_int s.elapsed_time  in
               FStar_Util.print3
                 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____345
                 (match s.replay_result with
                  | FStar_Util.Inl uu____348 -> "succeeded"
                  | FStar_Util.Inr uu____349 -> "failed") uu____346))
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals hint_stats []
  
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
      let uu____440 = FStar_ST.op_Bang replaying_hints  in
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
  
let record_hint :
  FStar_Util.hint FStar_Pervasives_Native.option -> Prims.unit =
  fun hint  ->
    let hint1 =
      match hint with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some h ->
          FStar_Pervasives_Native.Some
            (let uu___93_495 = h  in
             {
               FStar_Util.hint_name = (uu___93_495.FStar_Util.hint_name);
               FStar_Util.hint_index = (uu___93_495.FStar_Util.hint_index);
               FStar_Util.fuel = (uu___93_495.FStar_Util.fuel);
               FStar_Util.ifuel = (uu___93_495.FStar_Util.ifuel);
               FStar_Util.unsat_core = (uu___93_495.FStar_Util.unsat_core);
               FStar_Util.query_elapsed_time = (Prims.parse_int "0")
             })
       in
    let uu____496 = FStar_ST.op_Bang recorded_hints  in
    match uu____496 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some (FStar_List.append l [hint1]))
    | uu____546 -> ()
  
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
          let uu____570 =
            let uu____573 = FStar_ST.op_Bang hint_stats  in s :: uu____573
             in
          FStar_ST.op_Colon_Equals hint_stats uu____570
  
let filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
  =
=======
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db : 'a . Prims.string -> (Prims.unit -> 'a) -> 'a=
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let (filter_using_facts_from
  :FStar_TypeChecker_Env.env ->
     FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
<<<<<<< HEAD
        | uu____627 -> false  in
=======
        | uu____280 -> false in
>>>>>>> taramana_pointers_with_codes_modifies
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____292 ->
            (FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name
               include_assumption_names)
              ||
              (FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
<<<<<<< HEAD
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid)))
         in
      let theory_rev = FStar_List.rev theory  in
      let uu____649 =
=======
                 (FStar_Util.for_some (fun fid  -> should_enc_fid fid))) in
      let theory_rev = FStar_List.rev theory in
      let uu____302 =
>>>>>>> taramana_pointers_with_codes_modifies
        FStar_List.fold_left
          (fun uu____325  ->
             fun d  ->
               match uu____325 with
               | (out,include_assumption_names) ->
                   (match d with
                    | FStar_SMTEncoding_Term.Assume a ->
<<<<<<< HEAD
                        let uu____709 =
                          matches_fact_ids include_assumption_names a  in
                        if uu____709
=======
                        let uu____362 =
                          matches_fact_ids include_assumption_names a in
                        if uu____362
>>>>>>> taramana_pointers_with_codes_modifies
                        then ((d :: out), include_assumption_names)
                        else (out, include_assumption_names)
                    | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                        ((d :: out),
                          (FStar_List.append names1 include_assumption_names))
<<<<<<< HEAD
                    | uu____734 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev
         in
      match uu____649 with | (pruned_theory,uu____746) -> pruned_theory
  
let filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2
  =
=======
                    | uu____387 -> ((d :: out), include_assumption_names)))
          ([], []) theory_rev in
      match uu____302 with | (pruned_theory,uu____399) -> pruned_theory
let (filter_assertions
  :FStar_TypeChecker_Env.env ->
     FStar_SMTEncoding_Z3.unsat_core ->
       FStar_SMTEncoding_Term.decls_t ->
         (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
           FStar_Pervasives_Native.tuple2)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
<<<<<<< HEAD
            let uu____781 = filter_using_facts_from e theory  in
            (uu____781, false)
=======
            let uu____434 = filter_using_facts_from e theory in
            (uu____434, false)
>>>>>>> taramana_pointers_with_codes_modifies
        | FStar_Pervasives_Native.Some core1 ->
            let uu____444 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____468  ->
                     match uu____468 with
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
                          | uu____525 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
<<<<<<< HEAD
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
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
                                         | uu____923 -> false))
                                  in
                               FStar_All.pipe_right uu____916
                                 Prims.op_Negation))
                        in
                     FStar_All.pipe_right uu____906
                       (FStar_String.concat ", ")
                      in
                   let included =
                     let uu____927 =
                       FStar_All.pipe_right th
                         (FStar_List.collect
                            (fun uu___91_936  ->
                               match uu___91_936 with
                               | FStar_SMTEncoding_Term.Assume a ->
                                   [a.FStar_SMTEncoding_Term.assumption_name]
                               | uu____940 -> []))
                        in
                     FStar_All.pipe_right uu____927
                       (FStar_String.concat ", ")
                      in
                   FStar_Util.format2 "missed={%s}; included={%s}" missed
                     included
                    in
                 ((let uu____944 =
                     (FStar_Options.hint_info ()) &&
                       (FStar_Options.debug_any ())
                      in
                   if uu____944
                   then
                     let n1 = FStar_List.length core1  in
                     let missed =
                       if n1 <> n_retained
                       then missed_assertions theory' core1
                       else ""  in
                     let uu____952 = FStar_Util.string_of_int n_retained  in
                     let uu____953 =
                       if n1 <> n_retained
                       then
                         let uu____958 = FStar_Util.string_of_int n1  in
                         FStar_Util.format2
                           " (expected %s (%s); replay may be inaccurate)"
                           uu____958 missed
                       else ""  in
                     let uu____966 = FStar_Util.string_of_int n_pruned  in
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
                               (FStar_String.concat ", ")
                              in
                           Prims.strcat "UNSAT CORE: " uu____976  in
                         FStar_SMTEncoding_Term.Caption uu____975  in
                       [uu____974]  in
                     FStar_List.append theory' uu____971  in
                   (uu____968, true))))
  
let filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____995 = filter_using_facts_from e x  in (uu____995, false)
  
let ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit
  =
=======
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____444 with
             | (theory',n_retained,n_pruned) ->
                 let uu____543 =
                   let uu____546 =
                     let uu____549 =
                       let uu____550 =
                         let uu____551 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____551 in
                       FStar_SMTEncoding_Term.Caption uu____550 in
                     [uu____549] in
                   FStar_List.append theory' uu____546 in
                 (uu____543, true))
let (filter_facts_without_core
  :FStar_TypeChecker_Env.env ->
     FStar_SMTEncoding_Term.decls_t ->
       (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
         FStar_Pervasives_Native.tuple2)=
  fun e  ->
    fun x  ->
      let uu____570 = filter_using_facts_from e x in (uu____570, false)
type errors =
  {
  error_reason: Prims.string;
  error_fuel: Prims.int;
  error_ifuel: Prims.int;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  error_messages:
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list;}
let (__proj__Mkerrors__item__error_reason :errors -> Prims.string)=
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
let (__proj__Mkerrors__item__error_fuel :errors -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
let (__proj__Mkerrors__item__error_ifuel :errors -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
let (__proj__Mkerrors__item__error_hint
  :errors -> Prims.string Prims.list FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
let (__proj__Mkerrors__item__error_messages
  :errors ->
     (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
       Prims.list)=
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
let (error_to_short_string :errors -> Prims.string)=
  fun err1  ->
    let uu____724 = FStar_Util.string_of_int err1.error_fuel in
    let uu____725 = FStar_Util.string_of_int err1.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason
      uu____724 uu____725
      (if FStar_Option.isSome err1.error_hint then "with hint" else "")
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env;
  query_decl: FStar_SMTEncoding_Term.decl;
  query_name: Prims.string;
  query_index: Prims.int;
  query_range: FStar_Range.range;
  query_fuel: Prims.int;
  query_ifuel: Prims.int;
  query_rlimit: Prims.int;
  query_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  query_errors: errors Prims.list;
  query_all_labels: FStar_SMTEncoding_Term.error_labels;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list;}
let (__proj__Mkquery_settings__item__query_env
  :query_settings -> FStar_TypeChecker_Env.env)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_env
let (__proj__Mkquery_settings__item__query_decl
  :query_settings -> FStar_SMTEncoding_Term.decl)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_decl
let (__proj__Mkquery_settings__item__query_name
  :query_settings -> Prims.string)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_name
let (__proj__Mkquery_settings__item__query_index
  :query_settings -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_index
let (__proj__Mkquery_settings__item__query_range
  :query_settings -> FStar_Range.range)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_range
let (__proj__Mkquery_settings__item__query_fuel
  :query_settings -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_fuel
let (__proj__Mkquery_settings__item__query_ifuel
  :query_settings -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_ifuel
let (__proj__Mkquery_settings__item__query_rlimit
  :query_settings -> Prims.int)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_rlimit
let (__proj__Mkquery_settings__item__query_hint
  :query_settings -> Prims.string Prims.list FStar_Pervasives_Native.option)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_hint
let (__proj__Mkquery_settings__item__query_errors
  :query_settings -> errors Prims.list)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_errors
let (__proj__Mkquery_settings__item__query_all_labels
  :query_settings -> FStar_SMTEncoding_Term.error_labels)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_all_labels
let (__proj__Mkquery_settings__item__query_suffix
  :query_settings -> FStar_SMTEncoding_Term.decl Prims.list)=
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;_} -> __fname__query_suffix
let (with_fuel_and_diagnostics
  :query_settings ->
     FStar_SMTEncoding_Term.decl Prims.list ->
       FStar_SMTEncoding_Term.decl Prims.list)=
  fun settings  ->
    fun label_assumptions  ->
      let n1 = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1106 =
        let uu____1109 =
          let uu____1110 =
            let uu____1111 = FStar_Util.string_of_int n1 in
            let uu____1112 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1111 uu____1112 in
          FStar_SMTEncoding_Term.Caption uu____1110 in
        let uu____1113 =
          let uu____1116 =
            let uu____1117 =
              let uu____1124 =
                let uu____1125 =
                  let uu____1130 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1133 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1130, uu____1133) in
                FStar_SMTEncoding_Util.mkEq uu____1125 in
              (uu____1124, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1117 in
          let uu____1136 =
            let uu____1139 =
              let uu____1140 =
                let uu____1147 =
                  let uu____1148 =
                    let uu____1153 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1156 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1153, uu____1156) in
                  FStar_SMTEncoding_Util.mkEq uu____1148 in
                (uu____1147, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1140 in
            [uu____1139; settings.query_decl] in
          uu____1116 :: uu____1136 in
        uu____1109 :: uu____1113 in
      let uu____1159 =
        let uu____1162 =
          let uu____1165 =
            let uu____1168 =
              let uu____1169 =
                let uu____1174 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1174) in
              FStar_SMTEncoding_Term.SetOption uu____1169 in
            [uu____1168;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1175 =
            let uu____1178 =
              let uu____1181 = FStar_Options.record_hints () in
              if uu____1181
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1185 =
              let uu____1188 =
                let uu____1191 = FStar_Options.print_z3_statistics () in
                if uu____1191
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1188 settings.query_suffix in
            FStar_List.append uu____1178 uu____1185 in
          FStar_List.append uu____1165 uu____1175 in
        FStar_List.append label_assumptions uu____1162 in
      FStar_List.append uu____1106 uu____1159
let (used_hint :query_settings -> Prims.bool)=
  fun s  -> FStar_Option.isSome s.query_hint
let (next_hint
  :query_settings -> FStar_Util.hint FStar_Pervasives_Native.option)=
  fun uu____1206  ->
    match uu____1206 with
    | { query_env = uu____1209; query_decl = uu____1210; query_name = qname;
        query_index = qindex; query_range = uu____1213;
        query_fuel = uu____1214; query_ifuel = uu____1215;
        query_rlimit = uu____1216; query_hint = uu____1217;
        query_errors = uu____1218; query_all_labels = uu____1219;
        query_suffix = uu____1220;_} ->
        let uu____1229 = FStar_ST.op_Bang replaying_hints in
        (match uu____1229 with
         | FStar_Pervasives_Native.Some hints ->
             FStar_Util.find_map hints
               (fun uu___86_1257  ->
                  match uu___86_1257 with
                  | FStar_Pervasives_Native.Some hint when
                      (hint.FStar_Util.hint_name = qname) &&
                        (hint.FStar_Util.hint_index = qindex)
                      -> FStar_Pervasives_Native.Some hint
                  | uu____1263 -> FStar_Pervasives_Native.None)
         | uu____1266 -> FStar_Pervasives_Native.None)
let query_errors :
  'Auu____1277 'Auu____1278 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1278,'Auu____1277)
        FStar_Pervasives_Native.tuple3 ->
        errors FStar_Pervasives_Native.option=
  fun settings  ->
    fun uu____1294  ->
      match uu____1294 with
      | (z3status,elapsed_time,stats) ->
          (match z3status with
           | FStar_SMTEncoding_Z3.UNSAT uu____1306 ->
               FStar_Pervasives_Native.None
           | uu____1307 ->
               let uu____1308 =
                 FStar_SMTEncoding_Z3.status_string_and_errors z3status in
               (match uu____1308 with
                | (msg,error_labels) ->
                    let err1 =
                      let uu____1318 =
                        FStar_List.map
                          (fun uu____1339  ->
                             match uu____1339 with
                             | (uu____1350,x,y) -> (x, y)) error_labels in
                      {
                        error_reason = msg;
                        error_fuel = (settings.query_fuel);
                        error_ifuel = (settings.query_ifuel);
                        error_hint = (settings.query_hint);
                        error_messages = uu____1318
                      } in
                    FStar_Pervasives_Native.Some err1))
let detail_hint_replay :
  'Auu____1361 'Auu____1362 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1362,'Auu____1361)
        FStar_Pervasives_Native.tuple3 -> Prims.unit=
  fun settings  ->
    fun uu____1376  ->
      match uu____1376 with
      | (z3status,uu____1384,uu____1385) ->
          let uu____1386 =
            (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
          if uu____1386
          then
            (match z3status with
             | FStar_SMTEncoding_Z3.UNSAT uu____1387 -> ()
             | _failed ->
                 let ask_z3 label_assumptions =
                   let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   (let uu____1405 =
                      with_fuel_and_diagnostics settings label_assumptions in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions settings.query_env
                         settings.query_hint) settings.query_all_labels
                      uu____1405 FStar_Pervasives_Native.None
                      (fun r  ->
                         FStar_ST.op_Colon_Equals res
                           (FStar_Pervasives_Native.Some r)));
                   (let uu____1442 = FStar_ST.op_Bang res in
                    FStar_Option.get uu____1442) in
                 FStar_SMTEncoding_ErrorReporting.detail_errors true
                   settings.query_env settings.query_all_labels ask_z3)
          else ()
let (find_localized_errors
  :errors Prims.list -> errors FStar_Pervasives_Native.option)=
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err1  ->
            match err1.error_messages with | [] -> false | uu____1498 -> true))
let (has_localized_errors :errors Prims.list -> Prims.bool)=
  fun errs  ->
    let uu____1513 = find_localized_errors errs in
    FStar_Option.isSome uu____1513
let (report_errors :query_settings -> Prims.unit)=
  fun settings  ->
    let uu____1520 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1522 = FStar_Options.n_cores () in
         uu____1522 = (Prims.parse_int "1")) in
    if uu____1520
    then
      let initial_fuel1 =
        let uu___87_1524 = settings in
        let uu____1525 = FStar_Options.initial_fuel () in
        let uu____1526 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___87_1524.query_env);
          query_decl = (uu___87_1524.query_decl);
          query_name = (uu___87_1524.query_name);
          query_index = (uu___87_1524.query_index);
          query_range = (uu___87_1524.query_range);
          query_fuel = uu____1525;
          query_ifuel = uu____1526;
          query_rlimit = (uu___87_1524.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___87_1524.query_errors);
          query_all_labels = (uu___87_1524.query_all_labels);
          query_suffix = (uu___87_1524.query_suffix)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1545 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env)
           settings.query_all_labels uu____1545 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1582 = FStar_ST.op_Bang res in FStar_Option.get uu____1582) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1618 = find_localized_errors settings.query_errors in
       match uu____1618 with
       | FStar_Pervasives_Native.Some err1 ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1628 =
                      let uu____1629 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1629 in
                    FStar_Errors.diag settings.query_range uu____1628));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err1.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1631 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1641 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1641)) in
             FStar_All.pipe_right uu____1631 (FStar_String.concat "; ") in
           let uu____1644 =
             let uu____1651 =
               let uu____1656 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (uu____1656, (settings.query_range)) in
             [uu____1651] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1644)
let (query_info
  :query_settings ->
     (FStar_SMTEncoding_Z3.z3status,Prims.int,Prims.string FStar_Util.smap)
       FStar_Pervasives_Native.tuple3 -> Prims.unit)=
  fun settings  ->
    fun z3result  ->
      let uu____1689 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1689
      then
        let uu____1690 = z3result in
        match uu____1690 with
        | (z3status,elapsed_time,statistics) ->
            let uu____1706 =
              FStar_SMTEncoding_Z3.status_string_and_errors z3status in
            (match uu____1706 with
             | (status_string,errs) ->
                 let tag =
                   match z3status with
                   | FStar_SMTEncoding_Z3.UNSAT uu____1714 -> "succeeded"
                   | uu____1715 ->
                       Prims.strcat "failed {reason-unknown="
                         (Prims.strcat status_string "}") in
                 let range =
                   let uu____1717 =
                     let uu____1718 =
                       FStar_Range.string_of_range settings.query_range in
                     let uu____1719 =
                       let uu____1720 = FStar_SMTEncoding_Z3.at_log_file () in
                       Prims.strcat uu____1720 ")" in
                     Prims.strcat uu____1718 uu____1719 in
                   Prims.strcat "(" uu____1717 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu____1724 = FStar_Options.print_z3_statistics () in
                   if uu____1724
                   then
                     let f k v1 a =
                       Prims.strcat a
                         (Prims.strcat k
                            (Prims.strcat "=" (Prims.strcat v1 " "))) in
                     let str =
                       FStar_Util.smap_fold statistics f "statistics={" in
                     let uu____1736 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1")) in
                     Prims.strcat uu____1736 "}"
                   else "" in
                 ((let uu____1739 =
                     let uu____1742 =
                       let uu____1745 =
                         let uu____1748 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu____1749 =
                           let uu____1752 =
                             let uu____1755 =
                               let uu____1758 =
                                 FStar_Util.string_of_int elapsed_time in
                               let uu____1759 =
                                 let uu____1762 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu____1763 =
                                   let uu____1766 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu____1767 =
                                     let uu____1770 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu____1770; stats] in
                                   uu____1766 :: uu____1767 in
                                 uu____1762 :: uu____1763 in
                               uu____1758 :: uu____1759 in
                             used_hint_tag :: uu____1755 in
                           tag :: uu____1752 in
                         uu____1748 :: uu____1749 in
                       (settings.query_name) :: uu____1745 in
                     range :: uu____1742 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____1739);
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____1784  ->
                          match uu____1784 with
                          | (uu____1791,msg,range1) ->
                              let e =
                                FStar_Errors.mk_issue FStar_Errors.EInfo
                                  (FStar_Pervasives_Native.Some range1) msg in
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              let uu____1797 = FStar_Errors.format_issue e in
                              FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1797))))
      else ()
let record_hint :
  'Auu____1807 'Auu____1808 .
    query_settings ->
      (FStar_SMTEncoding_Z3.z3status,'Auu____1808,'Auu____1807)
        FStar_Pervasives_Native.tuple3 -> Prims.unit=
  fun settings  ->
    fun z3result  ->
      let uu____1829 =
        let uu____1830 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1830 in
      if uu____1829
      then ()
      else
        (let uu____1832 = z3result in
         match uu____1832 with
         | (z3status,uu____1840,uu____1841) ->
             let mk_hint core =
               {
                 FStar_Util.hint_name = (settings.query_name);
                 FStar_Util.hint_index = (settings.query_index);
                 FStar_Util.fuel = (settings.query_fuel);
                 FStar_Util.ifuel = (settings.query_ifuel);
                 FStar_Util.unsat_core = core;
                 FStar_Util.query_elapsed_time = (Prims.parse_int "0")
               } in
             let store_hint hint =
               let uu____1858 = FStar_ST.op_Bang recorded_hints in
               match uu____1858 with
               | FStar_Pervasives_Native.Some l ->
                   FStar_ST.op_Colon_Equals recorded_hints
                     (FStar_Pervasives_Native.Some
                        (FStar_List.append l
                           [FStar_Pervasives_Native.Some hint]))
               | uu____1908 -> () in
             (match z3status with
              | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
                  if used_hint settings
                  then store_hint (mk_hint settings.query_hint)
                  else store_hint (mk_hint unsat_core)
              | uu____1916 -> ()))
let (process_result
  :query_settings ->
     (FStar_SMTEncoding_Z3.z3status,Prims.int,Prims.string FStar_Util.smap)
       FStar_Pervasives_Native.tuple3 ->
       errors FStar_Pervasives_Native.option)=
  fun settings  ->
    fun result  ->
      (let uu____1946 =
         (used_hint settings) &&
           (let uu____1948 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____1948) in
       if uu____1946 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
let (fold_queries
  :query_settings Prims.list ->
     (query_settings ->
        (FStar_SMTEncoding_Z3.z3result -> Prims.unit) -> Prims.unit)
       ->
       (query_settings ->
          FStar_SMTEncoding_Z3.z3result ->
            errors FStar_Pervasives_Native.option)
         -> (errors Prims.list -> Prims.unit) -> Prims.unit)=
  fun qs  ->
    fun ask1  ->
      fun f  ->
        fun report1  ->
          let rec aux acc qs1 =
            match qs1 with
            | [] -> report1 acc
            | q::qs2 ->
                ask1 q
                  (fun res  ->
                     let uu____2044 = f q res in
                     match uu____2044 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2) in
          aux [] qs
let (ask_and_report_errors
  :FStar_TypeChecker_Env.env ->
     FStar_SMTEncoding_Term.error_labels ->
       FStar_SMTEncoding_Term.decl Prims.list ->
         FStar_SMTEncoding_Term.decl ->
           FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit)=
>>>>>>> taramana_pointers_with_codes_modifies
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
<<<<<<< HEAD
            (let uu____1029 =
               match env.FStar_TypeChecker_Env.qname_and_index with
               | FStar_Pervasives_Native.None  ->
                   failwith "No query name set!"
               | FStar_Pervasives_Native.Some (q,n1) ->
                   ((FStar_Ident.text_of_lid q), n1)
                in
             match uu____1029 with
             | (query_name,query_index) ->
                 let minimum_workable_fuel =
                   FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                 let set_minimum_workable_fuel f uu___92_1127 =
                   match uu___92_1127 with
                   | ([],uu____1140) -> ()
                   | errs ->
                       let uu____1150 =
                         FStar_ST.op_Bang minimum_workable_fuel  in
                       (match uu____1150 with
                        | FStar_Pervasives_Native.Some uu____1265 -> ()
                        | FStar_Pervasives_Native.None  ->
                            FStar_ST.op_Colon_Equals minimum_workable_fuel
                              (FStar_Pervasives_Native.Some (f, errs)))
                    in
                 let with_fuel label_assumptions p uu____1457 =
                   match uu____1457 with
                   | (n1,i,rlimit) ->
                       let uu____1471 =
                         let uu____1474 =
                           let uu____1475 =
                             let uu____1476 = FStar_Util.string_of_int n1  in
                             let uu____1477 = FStar_Util.string_of_int i  in
                             FStar_Util.format2 "<fuel='%s' ifuel='%s'>"
                               uu____1476 uu____1477
                              in
                           FStar_SMTEncoding_Term.Caption uu____1475  in
                         let uu____1478 =
                           let uu____1481 =
                             let uu____1482 =
                               let uu____1489 =
                                 let uu____1490 =
                                   let uu____1495 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("MaxFuel", [])
                                      in
                                   let uu____1498 =
                                     FStar_SMTEncoding_Term.n_fuel n1  in
                                   (uu____1495, uu____1498)  in
                                 FStar_SMTEncoding_Util.mkEq uu____1490  in
                               (uu____1489, FStar_Pervasives_Native.None,
                                 "@MaxFuel_assumption")
                                in
                             FStar_SMTEncoding_Util.mkAssume uu____1482  in
                           let uu____1501 =
                             let uu____1504 =
                               let uu____1505 =
                                 let uu____1512 =
                                   let uu____1513 =
                                     let uu____1518 =
                                       FStar_SMTEncoding_Util.mkApp
                                         ("MaxIFuel", [])
                                        in
                                     let uu____1521 =
                                       FStar_SMTEncoding_Term.n_fuel i  in
                                     (uu____1518, uu____1521)  in
                                   FStar_SMTEncoding_Util.mkEq uu____1513  in
                                 (uu____1512, FStar_Pervasives_Native.None,
                                   "@MaxIFuel_assumption")
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____1505  in
                             [uu____1504; p]  in
                           uu____1481 :: uu____1501  in
                         uu____1474 :: uu____1478  in
                       let uu____1524 =
                         let uu____1527 =
                           let uu____1530 =
                             let uu____1533 =
                               let uu____1534 =
                                 let uu____1539 =
                                   FStar_Util.string_of_int rlimit  in
                                 ("rlimit", uu____1539)  in
                               FStar_SMTEncoding_Term.SetOption uu____1534
                                in
                             [uu____1533]  in
                           let uu____1540 =
                             let uu____1543 =
                               let uu____1546 =
                                 let uu____1549 =
                                   FStar_Options.record_hints ()  in
                                 if uu____1549
                                 then [FStar_SMTEncoding_Term.GetUnsatCore]
                                 else []  in
                               let uu____1553 =
                                 let uu____1556 =
                                   let uu____1559 =
                                     (FStar_Options.print_z3_statistics ())
                                       || (FStar_Options.check_hints ())
                                      in
                                   if uu____1559
                                   then
                                     [FStar_SMTEncoding_Term.GetStatistics;
                                     FStar_SMTEncoding_Term.GetReasonUnknown]
                                   else []  in
                                 FStar_List.append uu____1556 suffix  in
                               FStar_List.append uu____1546 uu____1553  in
                             FStar_List.append
                               [FStar_SMTEncoding_Term.CheckSat] uu____1543
                              in
                           FStar_List.append uu____1530 uu____1540  in
                         FStar_List.append label_assumptions uu____1527  in
                       FStar_List.append uu____1471 uu____1524
                    in
                 let check p =
                   let rlimit =
                     let uu____1568 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____1569 =
                       let uu____1570 = FStar_Options.z3_rlimit ()  in
                       uu____1570 * (Prims.parse_int "544656")  in
                     uu____1568 * uu____1569  in
                   let default_initial_config =
                     let uu____1578 = FStar_Options.initial_fuel ()  in
                     let uu____1579 = FStar_Options.initial_ifuel ()  in
                     (uu____1578, uu____1579, rlimit)  in
                   let hint_opt = next_hint query_name query_index  in
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
                                  (Prims.parse_int "544656")))
                            in
                         (match uu____1625 with
                          | (core,timeout) ->
                              (core,
                                ((hint.FStar_Util.fuel),
                                  (hint.FStar_Util.ifuel), timeout)))
                      in
                   match uu____1583 with
                   | (unsat_core,initial_config) ->
                       let alt_configs =
                         let uu____1720 =
                           let uu____1731 =
                             let uu____1742 =
                               let uu____1751 =
                                 let uu____1752 = FStar_Options.max_ifuel ()
                                    in
                                 let uu____1753 =
                                   FStar_Options.initial_ifuel ()  in
                                 uu____1752 > uu____1753  in
                               if uu____1751
                               then
                                 let uu____1762 =
                                   let uu____1769 =
                                     FStar_Options.initial_fuel ()  in
                                   let uu____1770 =
                                     FStar_Options.max_ifuel ()  in
                                   (uu____1769, uu____1770, rlimit)  in
                                 [uu____1762]
                               else []  in
                             let uu____1790 =
                               let uu____1801 =
                                 let uu____1810 =
                                   let uu____1811 =
                                     let uu____1812 =
                                       FStar_Options.max_fuel ()  in
                                     uu____1812 / (Prims.parse_int "2")  in
                                   let uu____1819 =
                                     FStar_Options.initial_fuel ()  in
                                   uu____1811 > uu____1819  in
                                 if uu____1810
                                 then
                                   let uu____1828 =
                                     let uu____1835 =
                                       let uu____1836 =
                                         FStar_Options.max_fuel ()  in
                                       uu____1836 / (Prims.parse_int "2")  in
                                     let uu____1843 =
                                       FStar_Options.max_ifuel ()  in
                                     (uu____1835, uu____1843, rlimit)  in
                                   [uu____1828]
                                 else []  in
                               let uu____1863 =
                                 let uu____1874 =
                                   let uu____1883 =
                                     (let uu____1888 =
                                        FStar_Options.max_fuel ()  in
                                      let uu____1889 =
                                        FStar_Options.initial_fuel ()  in
                                      uu____1888 > uu____1889) &&
                                       (let uu____1892 =
                                          FStar_Options.max_ifuel ()  in
                                        let uu____1893 =
                                          FStar_Options.initial_ifuel ()  in
                                        uu____1892 >= uu____1893)
                                      in
                                   if uu____1883
                                   then
                                     let uu____1902 =
                                       let uu____1909 =
                                         FStar_Options.max_fuel ()  in
                                       let uu____1910 =
                                         FStar_Options.max_ifuel ()  in
                                       (uu____1909, uu____1910, rlimit)  in
                                     [uu____1902]
                                   else []  in
                                 let uu____1930 =
                                   let uu____1941 =
                                     let uu____1950 =
                                       let uu____1951 =
                                         FStar_Options.min_fuel ()  in
                                       let uu____1952 =
                                         FStar_Options.initial_fuel ()  in
                                       uu____1951 < uu____1952  in
                                     if uu____1950
                                     then
                                       let uu____1961 =
                                         let uu____1968 =
                                           FStar_Options.min_fuel ()  in
                                         (uu____1968, (Prims.parse_int "1"),
                                           rlimit)
                                          in
                                       [uu____1961]
                                     else []  in
                                   [uu____1941]  in
                                 uu____1874 :: uu____1930  in
                               uu____1801 :: uu____1863  in
                             uu____1742 :: uu____1790  in
                           (if
                              (default_initial_config <> initial_config) ||
                                (FStar_Option.isSome unsat_core)
                            then [default_initial_config]
                            else []) :: uu____1731
                            in
                         FStar_List.flatten uu____1720  in
                       let report1 p1 errs =
                         let errs1 =
                           let uu____2085 =
                             (FStar_Options.detail_errors ()) &&
                               (let uu____2087 = FStar_Options.n_cores ()  in
                                uu____2087 = (Prims.parse_int "1"))
                              in
                           if uu____2085
                           then
                             let uu____2088 =
                               let uu____2105 =
                                 FStar_ST.op_Bang minimum_workable_fuel  in
                               match uu____2105 with
                               | FStar_Pervasives_Native.Some (f,errs1) ->
                                   (f, errs1)
                               | FStar_Pervasives_Native.None  ->
                                   let uu____2306 =
                                     let uu____2313 =
                                       FStar_Options.min_fuel ()  in
                                     (uu____2313, (Prims.parse_int "1"),
                                       rlimit)
                                      in
                                   (uu____2306, errs)
                                in
                             match uu____2088 with
                             | (min_fuel1,potential_errors) ->
                                 let ask_z3 label_assumptions =
                                   let res =
                                     FStar_Util.mk_ref
                                       FStar_Pervasives_Native.None
                                      in
                                   (let uu____2362 =
                                      with_fuel label_assumptions p1
                                        min_fuel1
                                       in
                                    FStar_SMTEncoding_Z3.ask
                                      (filter_facts_without_core env)
                                      all_labels uu____2362
                                      FStar_Pervasives_Native.None
                                      (fun r  ->
                                         FStar_ST.op_Colon_Equals res
                                           (FStar_Pervasives_Native.Some r)));
                                   (let uu____2399 = FStar_ST.op_Bang res  in
                                    FStar_Option.get uu____2399)
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
                              | (uu____2514,FStar_SMTEncoding_Z3.Kill ) ->
                                  ([(("", FStar_SMTEncoding_Term.Term_sort),
                                      "Killed: Unknown assertion failed",
                                      FStar_Range.dummyRange)],
                                    (FStar_Pervasives_Native.snd errs))
                              | uu____2551 -> errs)
                            in
                         record_hint FStar_Pervasives_Native.None;
                         (let uu____2554 = FStar_Options.print_fuels ()  in
                          if uu____2554
                          then
                            let uu____2555 =
                              let uu____2556 =
                                FStar_TypeChecker_Env.get_range env  in
                              FStar_Range.string_of_range uu____2556  in
                            let uu____2557 =
                              let uu____2558 = FStar_Options.max_fuel ()  in
                              FStar_All.pipe_right uu____2558
                                FStar_Util.string_of_int
                               in
                            let uu____2559 =
                              let uu____2560 = FStar_Options.max_ifuel ()  in
                              FStar_All.pipe_right uu____2560
                                FStar_Util.string_of_int
                               in
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
                                    | (uu____2600,x,y) -> (x, y)))
                             in
                          FStar_TypeChecker_Err.add_errors env uu____2562)
                          in
                       let use_errors errs result =
                         match (errs, result) with
                         | (([],uu____2622),uu____2623) -> result
                         | (uu____2632,FStar_Util.Inl uu____2633) -> result
                         | (uu____2646,FStar_Util.Inr uu____2647) ->
                             FStar_Util.Inr errs
                          in
                       let rec try_alt_configs prev_f p1 errs cfgs scope =
                         set_minimum_workable_fuel prev_f errs;
                         (match (cfgs, (FStar_Pervasives_Native.snd errs))
                          with
                          | ([],uu____2750) -> report1 p1 errs
                          | (uu____2765,FStar_SMTEncoding_Z3.Kill ) ->
                              report1 p1 errs
                          | (mi::tl1,uu____2784) ->
                              let uu____2813 = with_fuel [] p1 mi  in
                              FStar_SMTEncoding_Z3.ask
                                (filter_facts_without_core env) all_labels
                                uu____2813
                                (FStar_Pervasives_Native.Some scope)
                                (fun uu____2821  ->
                                   match uu____2821 with
                                   | (result,elapsed_time,statistics) ->
                                       let uu____2841 =
                                         let uu____2848 =
                                           use_errors errs result  in
                                         (uu____2848, elapsed_time,
                                           statistics)
                                          in
                                       cb false mi p1 tl1 scope uu____2841))
                       
                       and cb used_hint uu____2850 p1 alt scope uu____2854 =
                         match (uu____2850, uu____2854) with
                         | ((prev_fuel,prev_ifuel,timeout),(result,elapsed_time,statistics))
                             ->
                             (if used_hint
                              then
                                (FStar_SMTEncoding_Z3.refresh ();
                                 (let uu____2907 =
                                    FStar_TypeChecker_Env.get_range env  in
                                  record_hint_stat hint_opt result
                                    elapsed_time uu____2907))
                              else ();
                              (let uu____2910 =
                                 (FStar_Options.z3_refresh ()) ||
                                   (FStar_Options.check_hints ())
                                  in
                               if uu____2910
                               then FStar_SMTEncoding_Z3.refresh ()
                               else ());
                              (let query_info env1 name tag statistics1 =
                                 let uu____2933 =
                                   ((FStar_Options.print_fuels ()) ||
                                      (FStar_Options.hint_info ()))
                                     ||
                                     (FStar_Options.print_z3_statistics ())
                                    in
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
                                                     e
                                                    in
                                                 FStar_Range.string_of_range
                                                   uu____2944
                                                  in
                                               let uu____2945 =
                                                 let uu____2946 =
                                                   FStar_SMTEncoding_Z3.at_log_file
                                                     ()
                                                    in
                                                 Prims.strcat uu____2946 ")"
                                                  in
                                               Prims.strcat uu____2943
                                                 uu____2945
                                                in
                                             Prims.strcat "(" uu____2942
                                         | FStar_Pervasives_Native.None  ->
                                             ""
                                          in
                                       let uu____2947 =
                                         let uu____2950 =
                                           let uu____2953 =
                                             let uu____2956 =
                                               FStar_Util.string_of_int
                                                 query_index
                                                in
                                             let uu____2957 =
                                               let uu____2960 =
                                                 let uu____2963 =
                                                   let uu____2966 =
                                                     FStar_Util.string_of_int
                                                       elapsed_time
                                                      in
                                                   let uu____2967 =
                                                     let uu____2970 =
                                                       FStar_Util.string_of_int
                                                         prev_fuel
                                                        in
                                                     let uu____2971 =
                                                       let uu____2974 =
                                                         FStar_Util.string_of_int
                                                           prev_ifuel
                                                          in
                                                       let uu____2975 =
                                                         let uu____2978 =
                                                           FStar_Util.string_of_int
                                                             rlimit
                                                            in
                                                         [uu____2978]  in
                                                       uu____2974 ::
                                                         uu____2975
                                                        in
                                                     uu____2970 :: uu____2971
                                                      in
                                                   uu____2966 :: uu____2967
                                                    in
                                                 (match env1 with
                                                  | FStar_Pervasives_Native.Some
                                                      e ->
                                                      if used_hint
                                                      then " (with hint)"
                                                      else ""
                                                  | FStar_Pervasives_Native.None
                                                       -> "")
                                                   :: uu____2963
                                                  in
                                               tag :: uu____2960  in
                                             uu____2956 :: uu____2957  in
                                           query_name :: uu____2953  in
                                         name :: uu____2950  in
                                       uu____2940 :: uu____2947  in
                                     let uu____2982 =
                                       let uu____2985 =
                                         let uu____2986 =
                                           FStar_Options.print_z3_statistics
                                             ()
                                            in
                                         if uu____2986
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
                                           let uu____2998 =
                                             FStar_Util.substring str
                                               (Prims.parse_int "0")
                                               ((FStar_String.length str) -
                                                  (Prims.parse_int "1"))
                                              in
                                           Prims.strcat uu____2998 "}"
                                         else
                                           (let uu____3000 =
                                              FStar_Util.smap_try_find
                                                statistics1 "reason-unknown"
                                               in
                                            match uu____3000 with
                                            | FStar_Pervasives_Native.Some v1
                                                ->
                                                Prims.strcat
                                                  "(reason-unknown="
                                                  (Prims.strcat v1 ")")
                                            | uu____3004 -> "")
                                          in
                                       [uu____2985]  in
                                     FStar_List.append uu____2937 uu____2982
                                      in
                                   FStar_Util.print
                                     "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                                     uu____2934
                                 else ()  in
                               let refine_hint unsat_core1 scope1 =
                                 let current_core =
                                   FStar_Util.mk_ref unsat_core1  in
                                 let hint_worked = FStar_Util.mk_ref false
                                    in
                                 let rec refine_hint core_ext_max_dist =
                                   let uu____3025 =
                                     let uu____3026 =
                                       FStar_ST.op_Bang hint_worked  in
                                     Prims.op_Negation uu____3026  in
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
                                                 "failed"
                                              in
                                           let uu____3150 =
                                             FStar_Options.hint_info ()  in
                                           if uu____3150
                                           then
                                             query_info
                                               FStar_Pervasives_Native.None
                                               "Hint-check" tag statistics1
                                           else ()
                                        in
                                     (FStar_SMTEncoding_Z3.refresh ();
                                      (let uu____3154 =
                                         let uu____3161 =
                                           FStar_ST.op_Bang current_core  in
                                         filter_assertions env uu____3161  in
                                       let uu____3186 =
                                         with_fuel [] p1
                                           (prev_fuel, prev_ifuel, rlimit)
                                          in
                                       FStar_SMTEncoding_Z3.ask uu____3154
                                         all_labels uu____3186
                                         (FStar_Pervasives_Native.Some scope1)
                                         hint_check_cb);
                                      (let uu____3189 =
                                         let uu____3190 =
                                           FStar_ST.op_Bang hint_worked  in
                                         Prims.op_Negation uu____3190  in
                                       if uu____3189
                                       then
                                         let refinement_ok =
                                           FStar_Util.mk_ref false  in
                                         ((let uu____3219 =
                                             let uu____3220 =
                                               let uu____3223 =
                                                 let uu____3226 =
                                                   let uu____3227 =
                                                     let uu____3228 =
                                                       let uu____3231 =
                                                         FStar_Util.string_of_int
                                                           core_ext_max_dist
                                                          in
                                                       [uu____3231]  in
                                                     FStar_Util.format
                                                       "smt.core.extend_patterns.max_distance=%s"
                                                       uu____3228
                                                      in
                                                   FStar_Options.String
                                                     uu____3227
                                                    in
                                                 [uu____3226]  in
                                               (FStar_Options.String
                                                  "smt.core.extend_patterns=true")
                                                 :: uu____3223
                                                in
                                             FStar_Options.List uu____3220
                                              in
                                           FStar_Options.set_option
                                             "z3cliopt" uu____3219);
                                          (let hint_refinement_cb uu____3251
                                             =
                                             match uu____3251 with
                                             | (result1,elapsed_time1,statistics1)
                                                 ->
                                                 let uu____3291 =
                                                   FStar_Options.hint_info ()
                                                    in
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
                                                               core_ext_max_dist
                                                              in
                                                           FStar_Util.format1
                                                             "succeeded (with smt.core.extend_patterns.max_distance=%s)"
                                                             uu____3348))
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
                                           (let uu____3361 =
                                              with_fuel [] p1
                                                (prev_fuel, prev_ifuel,
                                                  rlimit)
                                               in
                                            FStar_SMTEncoding_Z3.ask
                                              (filter_facts_without_core env)
                                              all_labels uu____3361
                                              (FStar_Pervasives_Native.Some
                                                 scope1) hint_refinement_cb);
                                           (let uu____3364 =
                                              FStar_ST.op_Bang refinement_ok
                                               in
                                            if uu____3364
                                            then
                                              let cutoff =
                                                (Prims.parse_int "10")  in
                                              (if core_ext_max_dist >= cutoff
                                               then
                                                 ((let uu____3391 =
                                                     let uu____3394 =
                                                       FStar_Util.string_of_int
                                                         cutoff
                                                        in
                                                     [uu____3394]  in
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
                                   else ()  in
                                 (let z3cliopts_before =
                                    FStar_Options.z3_cliopt ()  in
                                  let log_queries_before =
                                    FStar_Options.log_queries ()  in
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool false);
                                  refine_hint (Prims.parse_int "1");
                                  (let uu____3433 =
                                     let uu____3434 =
                                       FStar_List.map
                                         (fun x  -> FStar_Options.String x)
                                         z3cliopts_before
                                        in
                                     FStar_Options.List uu____3434  in
                                   FStar_Options.set_option "z3cliopt"
                                     uu____3433);
                                  FStar_Options.set_option "log_queries"
                                    (FStar_Options.Bool log_queries_before));
                                 (let uu____3439 =
                                    FStar_ST.op_Bang current_core  in
                                  {
                                    FStar_Util.hint_name = query_name;
                                    FStar_Util.hint_index = query_index;
                                    FStar_Util.fuel = prev_fuel;
                                    FStar_Util.ifuel = prev_ifuel;
                                    FStar_Util.unsat_core = uu____3439;
                                    FStar_Util.query_elapsed_time =
                                      elapsed_time
                                  })
                                  in
                               match result with
                               | FStar_Util.Inl unsat_core1 ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "succeeded" statistics;
                                    (let uu____3470 =
                                       let uu____3473 =
                                         (Prims.op_Negation used_hint) &&
                                           (FStar_Options.record_hints ())
                                          in
                                       if uu____3473
                                       then
                                         let uu____3476 =
                                           let uu____3477 =
                                             FStar_Options.check_hints ()  in
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
                                             }
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____3476
                                       else hint_opt  in
                                     record_hint uu____3470))
                               | FStar_Util.Inr errs ->
                                   (query_info
                                      (FStar_Pervasives_Native.Some env)
                                      "Query-stats" "failed" statistics;
                                    (let uu____3483 =
                                       used_hint &&
                                         (FStar_Options.hint_info ())
                                        in
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
                                         (FStar_Options.detail_hint_replay ())
                                        in
                                     if uu____3497
                                     then
                                       let ask_z3 label_assumptions =
                                         let res =
                                           FStar_Util.mk_ref
                                             FStar_Pervasives_Native.None
                                            in
                                         (let uu____3514 =
                                            with_fuel label_assumptions p1
                                              initial_config
                                             in
                                          FStar_SMTEncoding_Z3.ask
                                            (filter_assertions env unsat_core)
                                            all_labels uu____3514
                                            FStar_Pervasives_Native.None
                                            (fun r  ->
                                               FStar_ST.op_Colon_Equals res
                                                 (FStar_Pervasives_Native.Some
                                                    r)));
                                         (let uu____3551 =
                                            FStar_ST.op_Bang res  in
                                          FStar_Option.get uu____3551)
                                          in
                                       FStar_SMTEncoding_ErrorReporting.detail_errors
                                         true env all_labels ask_z3
                                     else ());
                                    try_alt_configs
                                      (prev_fuel, prev_ifuel, timeout) p1
                                      errs alt scope)))
                        in
                       ((let uu____3588 =
                           (FStar_Option.isSome unsat_core) ||
                             (FStar_Options.z3_refresh ())
                            in
                         if uu____3588
                         then FStar_SMTEncoding_Z3.refresh ()
                         else ());
                        (let wf = with_fuel [] p initial_config  in
                         let uu____3595 =
                           let uu____3596 =
                             FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                           cb (FStar_Option.isSome unsat_core) initial_config
                             p alt_configs uu____3596
                            in
                         FStar_SMTEncoding_Z3.ask
                           (filter_assertions env unsat_core) all_labels wf
                           FStar_Pervasives_Native.None uu____3595))
                    in
                 let process_query q = check q  in
                 let uu____3605 =
                   let uu____3612 = FStar_Options.admit_smt_queries ()  in
                   let uu____3613 = FStar_Options.admit_except ()  in
                   (uu____3612, uu____3613)  in
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
                                FStar_Util.string_of_int query_index  in
                              Prims.strcat uu____3632 ")"  in
                            Prims.strcat ", " uu____3631  in
                          Prims.strcat query_name uu____3630  in
                        Prims.strcat "(" uu____3629  in
                      if cur_id = id then process_query query else ()))
  
let solve :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____3656 =
           let uu____3657 =
             let uu____3658 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3658  in
           FStar_Util.format1 "Starting query at %s" uu____3657  in
         FStar_SMTEncoding_Encode.push uu____3656);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____3660 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____3660 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____3694 =
               let uu____3695 =
                 let uu____3696 =
                   let uu____3697 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3697
                    in
                 FStar_Util.format1 "Ending query at %s" uu____3696  in
               FStar_SMTEncoding_Encode.pop uu____3695  in
=======
            (let default_settings =
               let uu____2078 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2078 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2104 = FStar_Options.z3_rlimit_factor () in
                     let uu____2105 =
                       let uu____2106 = FStar_Options.z3_rlimit () in
                       uu____2106 * (Prims.parse_int "544656") in
                     uu____2104 * uu____2105 in
                   let uu____2107 = FStar_TypeChecker_Env.get_range env in
                   let uu____2108 = FStar_Options.initial_fuel () in
                   let uu____2109 = FStar_Options.initial_ifuel () in
                   {
                     query_env = env;
                     query_decl = query;
                     query_name = qname;
                     query_index = index1;
                     query_range = uu____2107;
                     query_fuel = uu____2108;
                     query_ifuel = uu____2109;
                     query_rlimit = rlimit;
                     query_hint = FStar_Pervasives_Native.None;
                     query_errors = [];
                     query_all_labels = all_labels;
                     query_suffix = suffix
                   } in
             let use_hints_setting =
               let uu____2115 = next_hint default_settings in
               match uu____2115 with
               | FStar_Pervasives_Native.Some
                   { FStar_Util.hint_name = uu____2120;
                     FStar_Util.hint_index = uu____2121; FStar_Util.fuel = i;
                     FStar_Util.ifuel = j;
                     FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                       core;
                     FStar_Util.query_elapsed_time = uu____2125;_}
                   ->
                   [(let uu___88_2131 = default_settings in
                     {
                       query_env = (uu___88_2131.query_env);
                       query_decl = (uu___88_2131.query_decl);
                       query_name = (uu___88_2131.query_name);
                       query_index = (uu___88_2131.query_index);
                       query_range = (uu___88_2131.query_range);
                       query_fuel = i;
                       query_ifuel = j;
                       query_rlimit = (uu___88_2131.query_rlimit);
                       query_hint = (FStar_Pervasives_Native.Some core);
                       query_errors = (uu___88_2131.query_errors);
                       query_all_labels = (uu___88_2131.query_all_labels);
                       query_suffix = (uu___88_2131.query_suffix)
                     })]
               | uu____2134 -> [] in
             let initial_fuel_max_ifuel =
               let uu____2140 =
                 let uu____2141 = FStar_Options.max_ifuel () in
                 let uu____2142 = FStar_Options.initial_ifuel () in
                 uu____2141 > uu____2142 in
               if uu____2140
               then
                 let uu____2145 =
                   let uu___89_2146 = default_settings in
                   let uu____2147 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___89_2146.query_env);
                     query_decl = (uu___89_2146.query_decl);
                     query_name = (uu___89_2146.query_name);
                     query_index = (uu___89_2146.query_index);
                     query_range = (uu___89_2146.query_range);
                     query_fuel = (uu___89_2146.query_fuel);
                     query_ifuel = uu____2147;
                     query_rlimit = (uu___89_2146.query_rlimit);
                     query_hint = (uu___89_2146.query_hint);
                     query_errors = (uu___89_2146.query_errors);
                     query_all_labels = (uu___89_2146.query_all_labels);
                     query_suffix = (uu___89_2146.query_suffix)
                   } in
                 [uu____2145]
               else [] in
             let half_max_fuel_max_ifuel =
               let uu____2152 =
                 let uu____2153 =
                   let uu____2154 = FStar_Options.max_fuel () in
                   uu____2154 / (Prims.parse_int "2") in
                 let uu____2161 = FStar_Options.initial_fuel () in
                 uu____2153 > uu____2161 in
               if uu____2152
               then
                 let uu____2164 =
                   let uu___90_2165 = default_settings in
                   let uu____2166 =
                     let uu____2167 = FStar_Options.max_fuel () in
                     uu____2167 / (Prims.parse_int "2") in
                   let uu____2174 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___90_2165.query_env);
                     query_decl = (uu___90_2165.query_decl);
                     query_name = (uu___90_2165.query_name);
                     query_index = (uu___90_2165.query_index);
                     query_range = (uu___90_2165.query_range);
                     query_fuel = uu____2166;
                     query_ifuel = uu____2174;
                     query_rlimit = (uu___90_2165.query_rlimit);
                     query_hint = (uu___90_2165.query_hint);
                     query_errors = (uu___90_2165.query_errors);
                     query_all_labels = (uu___90_2165.query_all_labels);
                     query_suffix = (uu___90_2165.query_suffix)
                   } in
                 [uu____2164]
               else [] in
             let max_fuel_max_ifuel =
               let uu____2179 =
                 (let uu____2184 = FStar_Options.max_fuel () in
                  let uu____2185 = FStar_Options.initial_fuel () in
                  uu____2184 > uu____2185) &&
                   (let uu____2188 = FStar_Options.max_ifuel () in
                    let uu____2189 = FStar_Options.initial_ifuel () in
                    uu____2188 >= uu____2189) in
               if uu____2179
               then
                 let uu____2192 =
                   let uu___91_2193 = default_settings in
                   let uu____2194 = FStar_Options.max_fuel () in
                   let uu____2195 = FStar_Options.max_ifuel () in
                   {
                     query_env = (uu___91_2193.query_env);
                     query_decl = (uu___91_2193.query_decl);
                     query_name = (uu___91_2193.query_name);
                     query_index = (uu___91_2193.query_index);
                     query_range = (uu___91_2193.query_range);
                     query_fuel = uu____2194;
                     query_ifuel = uu____2195;
                     query_rlimit = (uu___91_2193.query_rlimit);
                     query_hint = (uu___91_2193.query_hint);
                     query_errors = (uu___91_2193.query_errors);
                     query_all_labels = (uu___91_2193.query_all_labels);
                     query_suffix = (uu___91_2193.query_suffix)
                   } in
                 [uu____2192]
               else [] in
             let min_fuel1 =
               let uu____2200 =
                 let uu____2201 = FStar_Options.min_fuel () in
                 let uu____2202 = FStar_Options.initial_fuel () in
                 uu____2201 < uu____2202 in
               if uu____2200
               then
                 let uu____2205 =
                   let uu___92_2206 = default_settings in
                   let uu____2207 = FStar_Options.min_fuel () in
                   {
                     query_env = (uu___92_2206.query_env);
                     query_decl = (uu___92_2206.query_decl);
                     query_name = (uu___92_2206.query_name);
                     query_index = (uu___92_2206.query_index);
                     query_range = (uu___92_2206.query_range);
                     query_fuel = uu____2207;
                     query_ifuel = (Prims.parse_int "1");
                     query_rlimit = (uu___92_2206.query_rlimit);
                     query_hint = (uu___92_2206.query_hint);
                     query_errors = (uu___92_2206.query_errors);
                     query_all_labels = (uu___92_2206.query_all_labels);
                     query_suffix = (uu___92_2206.query_suffix)
                   } in
                 [uu____2205]
               else [] in
             let all_configs =
               FStar_List.append use_hints_setting
                 (FStar_List.append [default_settings]
                    (FStar_List.append initial_fuel_max_ifuel
                       (FStar_List.append half_max_fuel_max_ifuel
                          max_fuel_max_ifuel))) in
             let check_one_config config k =
               (let uu____2225 =
                  (used_hint config) || (FStar_Options.z3_refresh ()) in
                if uu____2225 then FStar_SMTEncoding_Z3.refresh () else ());
               (let uu____2227 = with_fuel_and_diagnostics config [] in
                let uu____2230 =
                  let uu____2233 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                  FStar_Pervasives_Native.Some uu____2233 in
                FStar_SMTEncoding_Z3.ask
                  (filter_assertions config.query_env config.query_hint)
                  config.query_all_labels uu____2227 uu____2230 k) in
             let check_all_configs configs =
               let report1 errs =
                 report_errors
                   (let uu___93_2252 = default_settings in
                    {
                      query_env = (uu___93_2252.query_env);
                      query_decl = (uu___93_2252.query_decl);
                      query_name = (uu___93_2252.query_name);
                      query_index = (uu___93_2252.query_index);
                      query_range = (uu___93_2252.query_range);
                      query_fuel = (uu___93_2252.query_fuel);
                      query_ifuel = (uu___93_2252.query_ifuel);
                      query_rlimit = (uu___93_2252.query_rlimit);
                      query_hint = (uu___93_2252.query_hint);
                      query_errors = errs;
                      query_all_labels = (uu___93_2252.query_all_labels);
                      query_suffix = (uu___93_2252.query_suffix)
                    }) in
               fold_queries configs check_one_config process_result report1 in
             let uu____2253 =
               let uu____2260 = FStar_Options.admit_smt_queries () in
               let uu____2261 = FStar_Options.admit_except () in
               (uu____2260, uu____2261) in
             match uu____2253 with
             | (true ,uu____2266) -> ()
             | (false ,FStar_Pervasives_Native.None ) ->
                 check_all_configs all_configs
             | (false ,FStar_Pervasives_Native.Some id) ->
                 let skip =
                   if FStar_Util.starts_with id "("
                   then
                     let full_query_id =
                       let uu____2278 =
                         let uu____2279 =
                           let uu____2280 =
                             let uu____2281 =
                               FStar_Util.string_of_int
                                 default_settings.query_index in
                             Prims.strcat uu____2281 ")" in
                           Prims.strcat ", " uu____2280 in
                         Prims.strcat default_settings.query_name uu____2279 in
                       Prims.strcat "(" uu____2278 in
                     full_query_id <> id
                   else default_settings.query_name <> id in
                 if Prims.op_Negation skip
                 then check_all_configs all_configs
                 else ())
let (solve
  :(Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
     FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)=
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2306 =
           let uu____2307 =
             let uu____2308 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2308 in
           FStar_Util.format1 "Starting query at %s" uu____2307 in
         FStar_SMTEncoding_Encode.push uu____2306);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2310 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2310 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2344 =
               let uu____2345 =
                 let uu____2346 =
                   let uu____2347 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2347 in
                 FStar_Util.format1 "Ending query at %s" uu____2346 in
               FStar_SMTEncoding_Encode.pop uu____2345 in
>>>>>>> taramana_pointers_with_codes_modifies
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2348);
                        FStar_SMTEncoding_Term.freevars = uu____2349;
                        FStar_SMTEncoding_Term.rng = uu____2350;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2351;
                    FStar_SMTEncoding_Term.assumption_name = uu____2352;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2353;_}
                  -> pop1 ()
              | uu____2368 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2369 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
<<<<<<< HEAD
              | uu____3721 -> failwith "Impossible"))
  
let solver : FStar_TypeChecker_Env.solver_t =
=======
              | uu____2371 -> failwith "Impossible"))
let (solver :FStar_TypeChecker_Env.solver_t)=
>>>>>>> taramana_pointers_with_codes_modifies
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
<<<<<<< HEAD
           let uu____3727 =
             let uu____3734 = FStar_Options.peek ()  in (e, g, uu____3734)
              in
           [uu____3727]);
=======
           let uu____2377 =
             let uu____2384 = FStar_Options.peek () in (e, g, uu____2384) in
           [uu____2377]);
>>>>>>> taramana_pointers_with_codes_modifies
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
<<<<<<< HEAD
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
=======
  }
let (dummy :FStar_TypeChecker_Env.solver_t)=
>>>>>>> taramana_pointers_with_codes_modifies
  {
    FStar_TypeChecker_Env.init = (fun uu____2399  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2401  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2403  -> ());
    FStar_TypeChecker_Env.mark = (fun uu____2405  -> ());
    FStar_TypeChecker_Env.reset_mark = (fun uu____2407  -> ());
    FStar_TypeChecker_Env.commit_mark = (fun uu____2409  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2412  -> fun uu____2413  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2416  -> fun uu____2417  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
<<<<<<< HEAD
           let uu____3773 =
             let uu____3780 = FStar_Options.peek ()  in (e, g, uu____3780)
              in
           [uu____3773]);
=======
           let uu____2423 =
             let uu____2430 = FStar_Options.peek () in (e, g, uu____2430) in
           [uu____2423]);
>>>>>>> taramana_pointers_with_codes_modifies
    FStar_TypeChecker_Env.solve =
      (fun uu____2446  -> fun uu____2447  -> fun uu____2448  -> ());
    FStar_TypeChecker_Env.is_trivial =
<<<<<<< HEAD
      (fun uu____3805  -> fun uu____3806  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____3808  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3810  -> ())
  } 
=======
      (fun uu____2455  -> fun uu____2456  -> false);
    FStar_TypeChecker_Env.finish = (fun uu____2458  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2460  -> ())
  }
>>>>>>> taramana_pointers_with_codes_modifies

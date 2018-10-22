open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14,'Auu____15) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___373_32  ->
    match uu___373_32 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____47) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db : 'Auu____105 . Prims.string -> 'Auu____105 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____119 = FStar_Options.record_hints ()  in
       if uu____119
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____149 = FStar_Options.use_hints ()  in
       if uu____149
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____156 = FStar_Options.hint_file ()  in
           match uu____156 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____165 = FStar_Util.read_hints val_filename  in
         match uu____165 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____172 = FStar_Options.hint_info ()  in
               if uu____172
               then
                 let uu____175 =
                   let uu____177 = FStar_Options.hint_file ()  in
                   match uu____177 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____187 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____175
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____225 = FStar_Options.hint_info ()  in
             (if uu____225
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____242 = FStar_Options.record_hints ()  in
     if uu____242
     then
       let hints =
         let uu____246 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____246  in
       let hints_db =
         let uu____273 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____273; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____279 = FStar_Options.hint_file ()  in
         match uu____279 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename
          in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
  
let with_hints_db : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f ()  in finalize_hints_db fname; result)
  
let (filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____389 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____411 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____418 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____418)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____449 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____449 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____467 -> d :: out) [] theory_rev
         in
      pruned_theory
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____501 = filter_using_facts_from e theory  in
            (uu____501, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____515 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____543  ->
                     match uu____543 with
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
                          | uu____628 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____515 with
             | (theory',n_retained,n_pruned) ->
                 let uu____657 =
                   let uu____660 =
                     let uu____663 =
                       let uu____664 =
                         let uu____666 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____666  in
                       FStar_SMTEncoding_Term.Caption uu____664  in
                     [uu____663]  in
                   FStar_List.append theory' uu____660  in
                 (uu____657, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____696 = filter_using_facts_from e x  in (uu____696, false)
  
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
    }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_reason
  
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_fuel
  
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_ifuel
  
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_hint
  
let (__proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
  
let (error_to_short_string : errors -> Prims.string) =
  fun err  ->
    let uu____926 = FStar_Util.string_of_int err.error_fuel  in
    let uu____928 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____926 uu____928
      (if FStar_Option.isSome err.error_hint then "with hint" else "")
  
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env ;
  query_decl: FStar_SMTEncoding_Term.decl ;
  query_name: Prims.string ;
  query_index: Prims.int ;
  query_range: FStar_Range.range ;
  query_fuel: Prims.int ;
  query_ifuel: Prims.int ;
  query_rlimit: Prims.int ;
  query_hint: FStar_SMTEncoding_Z3.unsat_core ;
  query_errors: errors Prims.list ;
  query_all_labels: FStar_SMTEncoding_Term.error_labels ;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list ;
  query_hash: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkquery_settings__item__query_env :
  query_settings -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_env
  
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_decl
  
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_name
  
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_index
  
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_range
  
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_fuel
  
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_ifuel
  
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_rlimit
  
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hint
  
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_errors
  
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_all_labels
  
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_suffix
  
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hash
  
let (with_fuel_and_diagnostics :
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun settings  ->
    fun label_assumptions  ->
      let n1 = settings.query_fuel  in
      let i = settings.query_ifuel  in
      let rlimit = settings.query_rlimit  in
      let uu____1467 =
        let uu____1470 =
          let uu____1471 =
            let uu____1473 = FStar_Util.string_of_int n1  in
            let uu____1475 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1473 uu____1475
             in
          FStar_SMTEncoding_Term.Caption uu____1471  in
        let uu____1478 =
          let uu____1481 =
            let uu____1482 =
              let uu____1490 =
                let uu____1491 =
                  let uu____1496 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1501 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1496, uu____1501)  in
                FStar_SMTEncoding_Util.mkEq uu____1491  in
              (uu____1490, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1482  in
          let uu____1505 =
            let uu____1508 =
              let uu____1509 =
                let uu____1517 =
                  let uu____1518 =
                    let uu____1523 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1528 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1523, uu____1528)  in
                  FStar_SMTEncoding_Util.mkEq uu____1518  in
                (uu____1517, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1509  in
            [uu____1508; settings.query_decl]  in
          uu____1481 :: uu____1505  in
        uu____1470 :: uu____1478  in
      let uu____1532 =
        let uu____1535 =
          let uu____1538 =
            let uu____1541 =
              let uu____1542 =
                let uu____1549 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1549)  in
              FStar_SMTEncoding_Term.SetOption uu____1542  in
            [uu____1541;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1554 =
            let uu____1557 =
              let uu____1560 = FStar_Options.record_hints ()  in
              if uu____1560
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1567 =
              let uu____1570 =
                let uu____1573 = FStar_Options.print_z3_statistics ()  in
                if uu____1573
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1570 settings.query_suffix  in
            FStar_List.append uu____1557 uu____1567  in
          FStar_List.append uu____1538 uu____1554  in
        FStar_List.append label_assumptions uu____1535  in
      FStar_List.append uu____1467 uu____1532
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1607 = FStar_ST.op_Bang replaying_hints  in
      match uu____1607 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___374_1640  ->
               match uu___374_1640 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1648 -> FStar_Pervasives_Native.None)
      | uu____1651 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1669 -> FStar_Pervasives_Native.None
      | uu____1670 ->
          let uu____1671 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1671 with
           | (msg,error_labels) ->
               let err =
                 let uu____1684 =
                   FStar_List.map
                     (fun uu____1712  ->
                        match uu____1712 with
                        | (uu____1727,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1684
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1744 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1744
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1747 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1767 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1767
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1817 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1817)
               in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
  
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err  ->
            match err.error_messages with | [] -> false | uu____1895 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1917 = find_localized_errors errs  in
    FStar_Option.isSome uu____1917
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____1927 = find_localized_errors settings.query_errors  in
     match uu____1927 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____1937 =
                    let uu____1939 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____1939  in
                  FStar_Errors.diag settings.query_range uu____1937));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____1944 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____1957 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____1957))
              in
           FStar_All.pipe_right uu____1944 (FStar_String.concat "; ")  in
         let uu____1965 =
           let uu____1975 =
             let uu____1983 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1983,
               (settings.query_range))
              in
           [uu____1975]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____1965);
    (let uu____2001 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2004 = FStar_Options.n_cores ()  in
          uu____2004 = (Prims.parse_int "1"))
        in
     if uu____2001
     then
       let initial_fuel1 =
         let uu___375_2010 = settings  in
         let uu____2011 = FStar_Options.initial_fuel ()  in
         let uu____2013 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___375_2010.query_env);
           query_decl = (uu___375_2010.query_decl);
           query_name = (uu___375_2010.query_name);
           query_index = (uu___375_2010.query_index);
           query_range = (uu___375_2010.query_range);
           query_fuel = uu____2011;
           query_ifuel = uu____2013;
           query_rlimit = (uu___375_2010.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___375_2010.query_errors);
           query_all_labels = (uu___375_2010.query_all_labels);
           query_suffix = (uu___375_2010.query_suffix);
           query_hash = (uu___375_2010.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2036 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2036
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
         (let uu____2086 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2086)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2148 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____2148
      then
        let uu____2151 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2151 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____2164 -> "succeeded"
              | uu____2166 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____2171 =
                let uu____2173 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____2175 =
                  let uu____2177 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____2177 ")"  in
                Prims.strcat uu____2173 uu____2175  in
              Prims.strcat "(" uu____2171  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____2191 = FStar_Options.print_z3_statistics ()  in
              if uu____2191
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))
                   in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={"
                   in
                let uu____2225 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____2225 "}"
              else ""  in
            ((let uu____2234 =
                let uu____2238 =
                  let uu____2242 =
                    let uu____2246 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____2248 =
                      let uu____2252 =
                        let uu____2256 =
                          let uu____2260 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____2262 =
                            let uu____2266 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____2268 =
                              let uu____2272 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____2274 =
                                let uu____2278 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____2278; stats]  in
                              uu____2272 :: uu____2274  in
                            uu____2266 :: uu____2268  in
                          uu____2260 :: uu____2262  in
                        used_hint_tag :: uu____2256  in
                      tag :: uu____2252  in
                    uu____2246 :: uu____2248  in
                  (settings.query_name) :: uu____2242  in
                range :: uu____2238  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____2234);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____2313  ->
                     match uu____2313 with
                     | (uu____2321,msg,range1) ->
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else ""  in
                         FStar_Errors.log_issue range1
                           (FStar_Errors.Warning_HitReplayFailed,
                             (Prims.strcat tag1 msg)))))
      else ()
  
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2348 =
        let uu____2350 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____2350  in
      if uu____2348
      then ()
      else
        (let mk_hint core =
           {
             FStar_Util.hint_name = (settings.query_name);
             FStar_Util.hint_index = (settings.query_index);
             FStar_Util.fuel = (settings.query_fuel);
             FStar_Util.ifuel = (settings.query_ifuel);
             FStar_Util.unsat_core = core;
             FStar_Util.query_elapsed_time = (Prims.parse_int "0");
             FStar_Util.hash =
               (match z3result.FStar_SMTEncoding_Z3.z3result_status with
                | FStar_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStar_SMTEncoding_Z3.z3result_query_hash
                | uu____2377 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____2385 = FStar_ST.op_Bang recorded_hints  in
           match uu____2385 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2441 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2448 =
               let uu____2449 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2449  in
             store_hint uu____2448
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2456 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2473 =
         (used_hint settings) &&
           (let uu____2476 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2476)
          in
       if uu____2473 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result  in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
  
let (fold_queries :
  query_settings Prims.list ->
    (query_settings -> (FStar_SMTEncoding_Z3.z3result -> unit) -> unit) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> unit) -> unit)
  =
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
                     let uu____2576 = f q res  in
                     match uu____2576 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2)
             in
          aux [] qs
  
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit)
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____2615 =
               let uu____2622 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2635,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2661,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2684 = FStar_Ident.text_of_lid q  in
                     (uu____2684, n1)
                  in
               match uu____2622 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2702 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2704 =
                       let uu____2706 = FStar_Options.z3_rlimit ()  in
                       uu____2706 * (Prims.parse_int "544656")  in
                     uu____2702 * uu____2704  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2713 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2714 = FStar_Options.initial_fuel ()  in
                     let uu____2716 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2713;
                       query_fuel = uu____2714;
                       query_ifuel = uu____2716;
                       query_rlimit = rlimit;
                       query_hint = FStar_Pervasives_Native.None;
                       query_errors = [];
                       query_all_labels = all_labels;
                       query_suffix = suffix;
                       query_hash =
                         (match next_hint with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              { FStar_Util.hint_name = uu____2725;
                                FStar_Util.hint_index = uu____2726;
                                FStar_Util.fuel = uu____2727;
                                FStar_Util.ifuel = uu____2728;
                                FStar_Util.unsat_core = uu____2729;
                                FStar_Util.query_elapsed_time = uu____2730;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2615 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2758;
                         FStar_Util.hint_index = uu____2759;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2763;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___376_2780 = default_settings  in
                         {
                           query_env = (uu___376_2780.query_env);
                           query_decl = (uu___376_2780.query_decl);
                           query_name = (uu___376_2780.query_name);
                           query_index = (uu___376_2780.query_index);
                           query_range = (uu___376_2780.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___376_2780.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___376_2780.query_errors);
                           query_all_labels =
                             (uu___376_2780.query_all_labels);
                           query_suffix = (uu___376_2780.query_suffix);
                           query_hash = (uu___376_2780.query_hash)
                         })]
                   | uu____2784 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2790 =
                     let uu____2792 = FStar_Options.max_ifuel ()  in
                     let uu____2794 = FStar_Options.initial_ifuel ()  in
                     uu____2792 > uu____2794  in
                   if uu____2790
                   then
                     let uu____2799 =
                       let uu___377_2800 = default_settings  in
                       let uu____2801 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___377_2800.query_env);
                         query_decl = (uu___377_2800.query_decl);
                         query_name = (uu___377_2800.query_name);
                         query_index = (uu___377_2800.query_index);
                         query_range = (uu___377_2800.query_range);
                         query_fuel = (uu___377_2800.query_fuel);
                         query_ifuel = uu____2801;
                         query_rlimit = (uu___377_2800.query_rlimit);
                         query_hint = (uu___377_2800.query_hint);
                         query_errors = (uu___377_2800.query_errors);
                         query_all_labels = (uu___377_2800.query_all_labels);
                         query_suffix = (uu___377_2800.query_suffix);
                         query_hash = (uu___377_2800.query_hash)
                       }  in
                     [uu____2799]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2808 =
                     let uu____2810 =
                       let uu____2812 = FStar_Options.max_fuel ()  in
                       uu____2812 / (Prims.parse_int "2")  in
                     let uu____2815 = FStar_Options.initial_fuel ()  in
                     uu____2810 > uu____2815  in
                   if uu____2808
                   then
                     let uu____2820 =
                       let uu___378_2821 = default_settings  in
                       let uu____2822 =
                         let uu____2824 = FStar_Options.max_fuel ()  in
                         uu____2824 / (Prims.parse_int "2")  in
                       let uu____2827 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___378_2821.query_env);
                         query_decl = (uu___378_2821.query_decl);
                         query_name = (uu___378_2821.query_name);
                         query_index = (uu___378_2821.query_index);
                         query_range = (uu___378_2821.query_range);
                         query_fuel = uu____2822;
                         query_ifuel = uu____2827;
                         query_rlimit = (uu___378_2821.query_rlimit);
                         query_hint = (uu___378_2821.query_hint);
                         query_errors = (uu___378_2821.query_errors);
                         query_all_labels = (uu___378_2821.query_all_labels);
                         query_suffix = (uu___378_2821.query_suffix);
                         query_hash = (uu___378_2821.query_hash)
                       }  in
                     [uu____2820]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2834 =
                     (let uu____2840 = FStar_Options.max_fuel ()  in
                      let uu____2842 = FStar_Options.initial_fuel ()  in
                      uu____2840 > uu____2842) &&
                       (let uu____2846 = FStar_Options.max_ifuel ()  in
                        let uu____2848 = FStar_Options.initial_ifuel ()  in
                        uu____2846 >= uu____2848)
                      in
                   if uu____2834
                   then
                     let uu____2853 =
                       let uu___379_2854 = default_settings  in
                       let uu____2855 = FStar_Options.max_fuel ()  in
                       let uu____2857 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___379_2854.query_env);
                         query_decl = (uu___379_2854.query_decl);
                         query_name = (uu___379_2854.query_name);
                         query_index = (uu___379_2854.query_index);
                         query_range = (uu___379_2854.query_range);
                         query_fuel = uu____2855;
                         query_ifuel = uu____2857;
                         query_rlimit = (uu___379_2854.query_rlimit);
                         query_hint = (uu___379_2854.query_hint);
                         query_errors = (uu___379_2854.query_errors);
                         query_all_labels = (uu___379_2854.query_all_labels);
                         query_suffix = (uu___379_2854.query_suffix);
                         query_hash = (uu___379_2854.query_hash)
                       }  in
                     [uu____2853]
                   else []  in
                 let min_fuel1 =
                   let uu____2864 =
                     let uu____2866 = FStar_Options.min_fuel ()  in
                     let uu____2868 = FStar_Options.initial_fuel ()  in
                     uu____2866 < uu____2868  in
                   if uu____2864
                   then
                     let uu____2873 =
                       let uu___380_2874 = default_settings  in
                       let uu____2875 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___380_2874.query_env);
                         query_decl = (uu___380_2874.query_decl);
                         query_name = (uu___380_2874.query_name);
                         query_index = (uu___380_2874.query_index);
                         query_range = (uu___380_2874.query_range);
                         query_fuel = uu____2875;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___380_2874.query_rlimit);
                         query_hint = (uu___380_2874.query_hint);
                         query_errors = (uu___380_2874.query_errors);
                         query_all_labels = (uu___380_2874.query_all_labels);
                         query_suffix = (uu___380_2874.query_suffix);
                         query_hash = (uu___380_2874.query_hash)
                       }  in
                     [uu____2873]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____2900 =
                      (used_hint config1) || (FStar_Options.z3_refresh ())
                       in
                    if uu____2900
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2905 = with_fuel_and_diagnostics config1 []  in
                    let uu____2908 =
                      let uu____2911 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2911  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____2905
                      uu____2908 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___381_2934 = default_settings  in
                        {
                          query_env = (uu___381_2934.query_env);
                          query_decl = (uu___381_2934.query_decl);
                          query_name = (uu___381_2934.query_name);
                          query_index = (uu___381_2934.query_index);
                          query_range = (uu___381_2934.query_range);
                          query_fuel = (uu___381_2934.query_fuel);
                          query_ifuel = (uu___381_2934.query_ifuel);
                          query_rlimit = (uu___381_2934.query_rlimit);
                          query_hint = (uu___381_2934.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___381_2934.query_all_labels);
                          query_suffix = (uu___381_2934.query_suffix);
                          query_hash = (uu___381_2934.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2935 =
                   let uu____2944 = FStar_Options.admit_smt_queries ()  in
                   let uu____2946 = FStar_Options.admit_except ()  in
                   (uu____2944, uu____2946)  in
                 (match uu____2935 with
                  | (true ,uu____2954) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2984 =
                              let uu____2986 =
                                let uu____2988 =
                                  let uu____2990 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2990 ")"  in
                                Prims.strcat ", " uu____2988  in
                              Prims.strcat default_settings.query_name
                                uu____2986
                               in
                            Prims.strcat "(" uu____2984  in
                          full_query_id <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____3030 =
           let uu____3032 =
             let uu____3034 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3034  in
           FStar_Util.format1 "Starting query at %s" uu____3032  in
         FStar_SMTEncoding_Encode.push uu____3030);
        (let uu____3037 = FStar_Options.no_smt ()  in
         if uu____3037
         then
           let uu____3040 =
             let uu____3050 =
               let uu____3058 =
                 let uu____3060 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3060
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3058,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3050]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3040
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3081 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3081 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3117 =
                  let uu____3118 =
                    let uu____3120 =
                      let uu____3122 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3122
                       in
                    FStar_Util.format1 "Ending query at %s" uu____3120  in
                  FStar_SMTEncoding_Encode.pop uu____3118  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____3125);
                           FStar_SMTEncoding_Term.freevars = uu____3126;
                           FStar_SMTEncoding_Term.rng = uu____3127;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3128;
                       FStar_SMTEncoding_Term.assumption_name = uu____3129;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3130;_}
                     -> pop1 ()
                 | uu____3147 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3148 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3150 -> failwith "Impossible")))
  
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_modul =
      FStar_SMTEncoding_Encode.encode_modul;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3158 =
             let uu____3165 = FStar_Options.peek ()  in (e, g, uu____3165)
              in
           [uu____3158]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3181  -> ());
    FStar_TypeChecker_Env.push = (fun uu____3183  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3186  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3189  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____3208  -> fun uu____3209  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____3224  -> fun uu____3225  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3228  -> fun uu____3229  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3235 =
             let uu____3242 = FStar_Options.peek ()  in (e, g, uu____3242)
              in
           [uu____3235]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3258  -> fun uu____3259  -> fun uu____3260  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____3267  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3269  -> ())
  } 
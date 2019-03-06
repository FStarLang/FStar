open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____66774 'Auu____66775 'Auu____66776 .
    ('Auu____66774,('Auu____66775 * 'Auu____66776)) FStar_Util.either ->
      ('Auu____66774,'Auu____66775) FStar_Util.either
  =
  fun uu___633_66793  ->
    match uu___633_66793 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____66808) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____66844 . Prims.string -> 'Auu____66844 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____66858 = FStar_Options.record_hints ()  in
       if uu____66858
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____66888 = FStar_Options.use_hints ()  in
       if uu____66888
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____66895 = FStar_Options.hint_file ()  in
           match uu____66895 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____66904 = FStar_Util.read_hints val_filename  in
         match uu____66904 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____66911 = FStar_Options.hint_info ()  in
               if uu____66911
               then
                 let uu____66914 =
                   let uu____66916 = FStar_Options.hint_file ()  in
                   match uu____66916 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____66926 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   uu____66914
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____66964 = FStar_Options.hint_info ()  in
             (if uu____66964
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____66981 = FStar_Options.record_hints ()  in
     if uu____66981
     then
       let hints =
         let uu____66985 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____66985  in
       let hints_db =
         let uu____67012 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____67012; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____67018 = FStar_Options.hint_file ()  in
         match uu____67018 with
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
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e  ->
    fun theory  ->
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____67143 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___634_67151  ->
                     match uu___634_67151 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____67154 -> false)))
              ||
              (let uu____67157 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____67157)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___635_67181 =
          match uu___635_67181 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____67196 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____67206 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____67229 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____67229
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____67247 ->
                   let uu____67248 = keep_decl d  in
                   if uu____67248 then d :: out else out) [] theory_rev
         in
      pruned_theory
  
let rec (filter_assertions_with_stats :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int *
          Prims.int))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____67304 = filter_using_facts_from e theory  in
            (uu____67304, false, (Prims.parse_int "0"),
              (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____67325 =
              let uu____67336 =
                let uu____67347 =
                  let uu____67350 =
                    let uu____67351 =
                      let uu____67353 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____67353  in
                    FStar_SMTEncoding_Term.Caption uu____67351  in
                  [uu____67350]  in
                (uu____67347, (Prims.parse_int "0"), (Prims.parse_int "0"))
                 in
              FStar_List.fold_left
                (fun uu____67383  ->
                   fun d  ->
                     match uu____67383 with
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
                          | FStar_SMTEncoding_Term.Module (name,decls) ->
                              let uu____67477 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____67477
                                (fun uu____67537  ->
                                   match uu____67537 with
                                   | (decls1,uu____67562,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____67582 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____67336 theory_rev
               in
            (match uu____67325 with
             | (theory',n_retained,n_pruned) ->
                 (theory', true, n_retained, n_pruned))
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        let uu____67644 = filter_assertions_with_stats e core theory  in
        match uu____67644 with
        | (theory1,b,uu____67667,uu____67668) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____67704 = filter_using_facts_from e x  in (uu____67704, false)
  
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list }
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
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
  
let (error_to_short_string : errors -> Prims.string) =
  fun err  ->
    let uu____67934 = FStar_Util.string_of_int err.error_fuel  in
    let uu____67936 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____67934 uu____67936
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
      let uu____68475 =
        let uu____68478 =
          let uu____68479 =
            let uu____68481 = FStar_Util.string_of_int n1  in
            let uu____68483 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____68481
              uu____68483
             in
          FStar_SMTEncoding_Term.Caption uu____68479  in
        let uu____68486 =
          let uu____68489 =
            let uu____68490 =
              let uu____68498 =
                let uu____68499 =
                  let uu____68504 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____68509 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____68504, uu____68509)  in
                FStar_SMTEncoding_Util.mkEq uu____68499  in
              (uu____68498, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____68490  in
          let uu____68513 =
            let uu____68516 =
              let uu____68517 =
                let uu____68525 =
                  let uu____68526 =
                    let uu____68531 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____68536 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____68531, uu____68536)  in
                  FStar_SMTEncoding_Util.mkEq uu____68526  in
                (uu____68525, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____68517  in
            [uu____68516; settings.query_decl]  in
          uu____68489 :: uu____68513  in
        uu____68478 :: uu____68486  in
      let uu____68540 =
        let uu____68543 =
          let uu____68546 =
            let uu____68549 =
              let uu____68550 =
                let uu____68557 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____68557)  in
              FStar_SMTEncoding_Term.SetOption uu____68550  in
            [uu____68549;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____68562 =
            let uu____68565 =
              let uu____68568 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____68568
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____68565 settings.query_suffix  in
          FStar_List.append uu____68546 uu____68562  in
        FStar_List.append label_assumptions uu____68543  in
      FStar_List.append uu____68475 uu____68540
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____68602 = FStar_ST.op_Bang replaying_hints  in
      match uu____68602 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___636_68635  ->
               match uu___636_68635 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____68643 -> FStar_Pervasives_Native.None)
      | uu____68646 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____68664 ->
          FStar_Pervasives_Native.None
      | uu____68665 ->
          let uu____68666 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____68666 with
           | (msg,error_labels) ->
               let err =
                 let uu____68679 =
                   FStar_List.map
                     (fun uu____68707  ->
                        match uu____68707 with
                        | (uu____68722,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____68679
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____68739 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____68739
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____68742 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____68762 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____68762
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____68791 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____68791)
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
            match err.error_messages with | [] -> false | uu____68847 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____68869 = find_localized_errors errs  in
    FStar_Option.isSome uu____68869
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____68879 = find_localized_errors settings.query_errors  in
     match uu____68879 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____68889 =
                    let uu____68891 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____68891  in
                  FStar_Errors.diag settings.query_range uu____68889));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____68896 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____68909 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____68909))
              in
           FStar_All.pipe_right uu____68896 (FStar_String.concat "; ")  in
         let uu____68917 =
           let uu____68927 =
             let uu____68935 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____68935,
               (settings.query_range))
              in
           [uu____68927]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____68917);
    (let uu____68953 =
       (FStar_Options.detail_errors ()) &&
         (let uu____68956 = FStar_Options.n_cores ()  in
          uu____68956 = (Prims.parse_int "1"))
        in
     if uu____68953
     then
       let initial_fuel1 =
         let uu___868_68962 = settings  in
         let uu____68963 = FStar_Options.initial_fuel ()  in
         let uu____68965 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___868_68962.query_env);
           query_decl = (uu___868_68962.query_decl);
           query_name = (uu___868_68962.query_name);
           query_index = (uu___868_68962.query_index);
           query_range = (uu___868_68962.query_range);
           query_fuel = uu____68963;
           query_ifuel = uu____68965;
           query_rlimit = (uu___868_68962.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___868_68962.query_errors);
           query_all_labels = (uu___868_68962.query_all_labels);
           query_suffix = (uu___868_68962.query_suffix);
           query_hash = (uu___868_68962.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____68988 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____68988
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____69017 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____69017)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____69082 =
          let r = FStar_Util.mk_ref []  in
          let uu____69093 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____69193  ->
                 let uu____69194 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____69194
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____69093 with | (add1,get1) -> (add1, get1)  in
        let uu____69276 = accumulator ()  in
        match uu____69276 with
        | (add_module_name,get_module_names) ->
            let uu____69313 = accumulator ()  in
            (match uu____69313 with
             | (add_discarded_name,get_discarded_names) ->
                 let parse_axiom_name s =
                   let chars = FStar_String.list_of_string s  in
                   let first_upper_index =
                     FStar_Util.try_find_index FStar_Util.is_upper chars  in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None  ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStar_Util.substring_from s first_upper_index1  in
                       let components =
                         FStar_String.split [46] name_and_suffix  in
                       let excluded_suffixes =
                         ["fuel_instrumented";
                         "_pretyping";
                         "_Tm_refine";
                         "_Tm_abs";
                         "@";
                         "_interpretation_Tm_arrow";
                         "MaxFuel_assumption";
                         "MaxIFuel_assumption"]  in
                       let exclude_suffix s1 =
                         let s2 = FStar_Util.trim_string s1  in
                         let sopt =
                           FStar_Util.find_map excluded_suffixes
                             (fun sfx  ->
                                if FStar_Util.contains s2 sfx
                                then
                                  let uu____69436 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____69436
                                else FStar_Pervasives_Native.None)
                            in
                         match sopt with
                         | FStar_Pervasives_Native.None  ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3]
                          in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu____69481 ->
                             let uu____69485 = FStar_Util.prefix components
                                in
                             (match uu____69485 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____69512 = exclude_suffix last1
                                       in
                                    FStar_List.append module_name uu____69512
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____69519::[] -> ()
                                    | uu____69523 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____69540 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____69540])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____69567 =
                          let uu____69569 = get_module_names ()  in
                          FStar_All.pipe_right uu____69569
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____69567);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____69582 =
                          let uu____69584 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____69584
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____69582))))
         in
      let uu____69594 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____69594
      then
        let uu____69597 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____69597 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____69616 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____69630 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____69616 with
             | (tag,core) ->
                 let range =
                   let uu____69643 =
                     let uu____69645 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____69645 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____69643  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____69659 = FStar_Options.query_stats ()  in
                   if uu____69659
                   then
                     let f k v1 a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v1 " ")))
                        in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={"
                        in
                     let uu____69693 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____69693 "}"
                   else ""  in
                 ((let uu____69702 =
                     let uu____69706 =
                       let uu____69710 =
                         let uu____69714 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____69716 =
                           let uu____69720 =
                             let uu____69724 =
                               let uu____69728 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____69730 =
                                 let uu____69734 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____69736 =
                                   let uu____69740 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____69742 =
                                     let uu____69746 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____69746; stats]  in
                                   uu____69740 :: uu____69742  in
                                 uu____69734 :: uu____69736  in
                               uu____69728 :: uu____69730  in
                             used_hint_tag :: uu____69724  in
                           tag :: uu____69720  in
                         uu____69714 :: uu____69716  in
                       (settings.query_name) :: uu____69710  in
                     range :: uu____69706  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____69702);
                  (let uu____69761 = FStar_Options.print_z3_statistics ()  in
                   if uu____69761 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____69787  ->
                          match uu____69787 with
                          | (uu____69795,msg,range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else ""  in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
  
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____69822 =
        let uu____69824 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____69824  in
      if uu____69822
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
                | uu____69851 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____69859 = FStar_ST.op_Bang recorded_hints  in
           match uu____69859 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____69915 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____69922 =
               let uu____69923 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____69923  in
             store_hint uu____69922
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____69930 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      let errs = query_errors settings result  in
      query_info settings result;
      record_hint settings result;
      detail_hint_replay settings result;
      errs
  
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
                     let uu____70041 = f q res  in
                     match uu____70041 with
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
            (let uu____70080 =
               let uu____70087 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____70100,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____70126,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____70149 = FStar_Ident.text_of_lid q  in
                     (uu____70149, n1)
                  in
               match uu____70087 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____70167 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____70169 =
                       let uu____70171 = FStar_Options.z3_rlimit ()  in
                       uu____70171 * (Prims.parse_int "544656")  in
                     uu____70167 * uu____70169  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____70178 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____70179 = FStar_Options.initial_fuel ()  in
                     let uu____70181 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____70178;
                       query_fuel = uu____70179;
                       query_ifuel = uu____70181;
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
                              { FStar_Util.hint_name = uu____70190;
                                FStar_Util.hint_index = uu____70191;
                                FStar_Util.fuel = uu____70192;
                                FStar_Util.ifuel = uu____70193;
                                FStar_Util.unsat_core = uu____70194;
                                FStar_Util.query_elapsed_time = uu____70195;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____70080 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____70223;
                         FStar_Util.hint_index = uu____70224;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____70228;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___1057_70245 = default_settings  in
                         {
                           query_env = (uu___1057_70245.query_env);
                           query_decl = (uu___1057_70245.query_decl);
                           query_name = (uu___1057_70245.query_name);
                           query_index = (uu___1057_70245.query_index);
                           query_range = (uu___1057_70245.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___1057_70245.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___1057_70245.query_errors);
                           query_all_labels =
                             (uu___1057_70245.query_all_labels);
                           query_suffix = (uu___1057_70245.query_suffix);
                           query_hash = (uu___1057_70245.query_hash)
                         })]
                   | uu____70249 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____70255 =
                     let uu____70257 = FStar_Options.max_ifuel ()  in
                     let uu____70259 = FStar_Options.initial_ifuel ()  in
                     uu____70257 > uu____70259  in
                   if uu____70255
                   then
                     let uu____70264 =
                       let uu___1062_70265 = default_settings  in
                       let uu____70266 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1062_70265.query_env);
                         query_decl = (uu___1062_70265.query_decl);
                         query_name = (uu___1062_70265.query_name);
                         query_index = (uu___1062_70265.query_index);
                         query_range = (uu___1062_70265.query_range);
                         query_fuel = (uu___1062_70265.query_fuel);
                         query_ifuel = uu____70266;
                         query_rlimit = (uu___1062_70265.query_rlimit);
                         query_hint = (uu___1062_70265.query_hint);
                         query_errors = (uu___1062_70265.query_errors);
                         query_all_labels =
                           (uu___1062_70265.query_all_labels);
                         query_suffix = (uu___1062_70265.query_suffix);
                         query_hash = (uu___1062_70265.query_hash)
                       }  in
                     [uu____70264]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____70273 =
                     let uu____70275 =
                       let uu____70277 = FStar_Options.max_fuel ()  in
                       uu____70277 / (Prims.parse_int "2")  in
                     let uu____70280 = FStar_Options.initial_fuel ()  in
                     uu____70275 > uu____70280  in
                   if uu____70273
                   then
                     let uu____70285 =
                       let uu___1066_70286 = default_settings  in
                       let uu____70287 =
                         let uu____70289 = FStar_Options.max_fuel ()  in
                         uu____70289 / (Prims.parse_int "2")  in
                       let uu____70292 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1066_70286.query_env);
                         query_decl = (uu___1066_70286.query_decl);
                         query_name = (uu___1066_70286.query_name);
                         query_index = (uu___1066_70286.query_index);
                         query_range = (uu___1066_70286.query_range);
                         query_fuel = uu____70287;
                         query_ifuel = uu____70292;
                         query_rlimit = (uu___1066_70286.query_rlimit);
                         query_hint = (uu___1066_70286.query_hint);
                         query_errors = (uu___1066_70286.query_errors);
                         query_all_labels =
                           (uu___1066_70286.query_all_labels);
                         query_suffix = (uu___1066_70286.query_suffix);
                         query_hash = (uu___1066_70286.query_hash)
                       }  in
                     [uu____70285]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____70299 =
                     (let uu____70305 = FStar_Options.max_fuel ()  in
                      let uu____70307 = FStar_Options.initial_fuel ()  in
                      uu____70305 > uu____70307) &&
                       (let uu____70311 = FStar_Options.max_ifuel ()  in
                        let uu____70313 = FStar_Options.initial_ifuel ()  in
                        uu____70311 >= uu____70313)
                      in
                   if uu____70299
                   then
                     let uu____70318 =
                       let uu___1070_70319 = default_settings  in
                       let uu____70320 = FStar_Options.max_fuel ()  in
                       let uu____70322 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1070_70319.query_env);
                         query_decl = (uu___1070_70319.query_decl);
                         query_name = (uu___1070_70319.query_name);
                         query_index = (uu___1070_70319.query_index);
                         query_range = (uu___1070_70319.query_range);
                         query_fuel = uu____70320;
                         query_ifuel = uu____70322;
                         query_rlimit = (uu___1070_70319.query_rlimit);
                         query_hint = (uu___1070_70319.query_hint);
                         query_errors = (uu___1070_70319.query_errors);
                         query_all_labels =
                           (uu___1070_70319.query_all_labels);
                         query_suffix = (uu___1070_70319.query_suffix);
                         query_hash = (uu___1070_70319.query_hash)
                       }  in
                     [uu____70318]
                   else []  in
                 let min_fuel1 =
                   let uu____70329 =
                     let uu____70331 = FStar_Options.min_fuel ()  in
                     let uu____70333 = FStar_Options.initial_fuel ()  in
                     uu____70331 < uu____70333  in
                   if uu____70329
                   then
                     let uu____70338 =
                       let uu___1074_70339 = default_settings  in
                       let uu____70340 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___1074_70339.query_env);
                         query_decl = (uu___1074_70339.query_decl);
                         query_name = (uu___1074_70339.query_name);
                         query_index = (uu___1074_70339.query_index);
                         query_range = (uu___1074_70339.query_range);
                         query_fuel = uu____70340;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___1074_70339.query_rlimit);
                         query_hint = (uu___1074_70339.query_hint);
                         query_errors = (uu___1074_70339.query_errors);
                         query_all_labels =
                           (uu___1074_70339.query_all_labels);
                         query_suffix = (uu___1074_70339.query_suffix);
                         query_hash = (uu___1074_70339.query_hash)
                       }  in
                     [uu____70338]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____70365 = FStar_Options.z3_refresh ()  in
                    if uu____70365
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____70370 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____70373 =
                      let uu____70376 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____70376  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____70370
                      uu____70373 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___1087_70399 = default_settings  in
                        {
                          query_env = (uu___1087_70399.query_env);
                          query_decl = (uu___1087_70399.query_decl);
                          query_name = (uu___1087_70399.query_name);
                          query_index = (uu___1087_70399.query_index);
                          query_range = (uu___1087_70399.query_range);
                          query_fuel = (uu___1087_70399.query_fuel);
                          query_ifuel = (uu___1087_70399.query_ifuel);
                          query_rlimit = (uu___1087_70399.query_rlimit);
                          query_hint = (uu___1087_70399.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___1087_70399.query_all_labels);
                          query_suffix = (uu___1087_70399.query_suffix);
                          query_hash = (uu___1087_70399.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____70400 =
                   let uu____70409 = FStar_Options.admit_smt_queries ()  in
                   let uu____70411 = FStar_Options.admit_except ()  in
                   (uu____70409, uu____70411)  in
                 (match uu____70400 with
                  | (true ,uu____70419) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____70449 =
                              let uu____70451 =
                                let uu____70453 =
                                  let uu____70455 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____70455 ")"  in
                                Prims.op_Hat ", " uu____70453  in
                              Prims.op_Hat default_settings.query_name
                                uu____70451
                               in
                            Prims.op_Hat "(" uu____70449  in
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
        (let uu____70495 =
           let uu____70497 =
             let uu____70499 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____70499  in
           FStar_Util.format1 "Starting query at %s" uu____70497  in
         FStar_SMTEncoding_Encode.push uu____70495);
        (let uu____70502 = FStar_Options.no_smt ()  in
         if uu____70502
         then
           let uu____70505 =
             let uu____70515 =
               let uu____70523 =
                 let uu____70525 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____70525
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____70523,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____70515]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____70505
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____70546 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____70546 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____70582 =
                  let uu____70583 =
                    let uu____70585 =
                      let uu____70587 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____70587
                       in
                    FStar_Util.format1 "Ending query at %s" uu____70585  in
                  FStar_SMTEncoding_Encode.pop uu____70583  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____70590);
                           FStar_SMTEncoding_Term.freevars = uu____70591;
                           FStar_SMTEncoding_Term.rng = uu____70592;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____70593;
                       FStar_SMTEncoding_Term.assumption_name = uu____70594;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____70595;_}
                     -> pop1 ()
                 | uu____70615 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____70616 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____70618 -> failwith "Impossible")))
  
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____70626 =
             let uu____70633 = FStar_Options.peek ()  in (e, g, uu____70633)
              in
           [uu____70626]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____70649  -> ());
    FStar_TypeChecker_Env.push = (fun uu____70651  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____70654  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____70657  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____70676  -> fun uu____70677  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____70692  -> fun uu____70693  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____70699 =
             let uu____70706 = FStar_Options.peek ()  in (e, g, uu____70706)
              in
           [uu____70699]);
    FStar_TypeChecker_Env.solve =
      (fun uu____70722  -> fun uu____70723  -> fun uu____70724  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____70731  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____70733  -> ())
  } 
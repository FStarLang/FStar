open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____35 'Auu____36 'Auu____37 .
    ('Auu____35,('Auu____36 * 'Auu____37)) FStar_Util.either ->
      ('Auu____35,'Auu____36) FStar_Util.either
  =
  fun uu___0_54  ->
    match uu___0_54 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____69) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let initialize_hints_db : 'Auu____95 . Prims.string -> 'Auu____95 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____109 = FStar_Options.record_hints ()  in
       if uu____109
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename
          in
       let uu____143 =
         let uu____146 = FStar_Options.use_hints ()  in
         FStar_Util.read_hints val_filename uu____146  in
       match uu____143 with
       | FStar_Pervasives_Native.Some hints ->
           let expected_digest = FStar_Util.digest_of_file norm_src_filename
              in
           ((let uu____152 = FStar_Options.hint_info ()  in
             if uu____152
             then
               FStar_Util.print3 "(%s) digest is %s from %s.\n"
                 norm_src_filename
                 (if hints.FStar_Util.module_digest = expected_digest
                  then "valid; using hints"
                  else "invalid; using potentially stale hints") val_filename
             else ());
            FStar_ST.op_Colon_Equals replaying_hints
              (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
       | FStar_Pervasives_Native.None  ->
           let uu____188 = FStar_Options.hint_info ()  in
           if uu____188
           then
             FStar_Util.print1 "(%s) Unable to read hint file.\n"
               norm_src_filename
           else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____203 = FStar_Options.record_hints ()  in
     if uu____203
     then
       let hints =
         let uu____207 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____207  in
       let hints_db =
         let uu____234 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____234; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename
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
        | uu____356 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_364  ->
                     match uu___1_364 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____367 -> false)))
              ||
              (let uu____370 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____370)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.of_int (10000))  in
        let keep_decl uu___2_394 =
          match uu___2_394 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____409 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____419 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____442 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____442
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____460 ->
                   let uu____461 = keep_decl d  in
                   if uu____461 then d :: out else out) [] theory_rev
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
            let uu____517 = filter_using_facts_from e theory  in
            (uu____517, false, Prims.int_zero, Prims.int_zero)
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____538 =
              let uu____549 =
                let uu____560 =
                  let uu____563 =
                    let uu____564 =
                      let uu____566 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____566  in
                    FStar_SMTEncoding_Term.Caption uu____564  in
                  [uu____563]  in
                (uu____560, Prims.int_zero, Prims.int_zero)  in
              FStar_List.fold_left
                (fun uu____596  ->
                   fun d  ->
                     match uu____596 with
                     | (theory1,n_retained,n_pruned) ->
                         (match d with
                          | FStar_SMTEncoding_Term.Assume a ->
                              if
                                FStar_List.contains
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  core1
                              then
                                ((d :: theory1),
                                  (n_retained + Prims.int_one), n_pruned)
                              else
                                if
                                  FStar_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + Prims.int_one))
                          | FStar_SMTEncoding_Term.Module (name,decls) ->
                              let uu____690 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____690
                                (fun uu____750  ->
                                   match uu____750 with
                                   | (decls1,uu____775,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____795 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____549 theory_rev
               in
            (match uu____538 with
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
        let uu____857 = filter_assertions_with_stats e core theory  in
        match uu____857 with
        | (theory1,b,uu____880,uu____881) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____917 = filter_using_facts_from e x  in (uu____917, false)
  
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
    let uu____1147 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1149 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____1147
      uu____1149
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
  
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err  ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____1175 =
        let uu____1177 = FStar_Util.string_of_int err.error_fuel  in
        let uu____1179 = FStar_Util.string_of_int err.error_ifuel  in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____1177 uu____1179
          (if FStar_Option.isSome err.error_hint then "with hint" else "")
         in
      [uu____1175]
    else []
  
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
      let uu____1723 =
        let uu____1726 =
          let uu____1727 =
            let uu____1729 = FStar_Util.string_of_int n1  in
            let uu____1731 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1729 uu____1731
             in
          FStar_SMTEncoding_Term.Caption uu____1727  in
        let uu____1734 =
          let uu____1737 =
            let uu____1738 =
              let uu____1746 =
                let uu____1747 =
                  let uu____1752 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1757 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1752, uu____1757)  in
                FStar_SMTEncoding_Util.mkEq uu____1747  in
              (uu____1746, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1738  in
          let uu____1761 =
            let uu____1764 =
              let uu____1765 =
                let uu____1773 =
                  let uu____1774 =
                    let uu____1779 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1784 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1779, uu____1784)  in
                  FStar_SMTEncoding_Util.mkEq uu____1774  in
                (uu____1773, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1765  in
            [uu____1764; settings.query_decl]  in
          uu____1737 :: uu____1761  in
        uu____1726 :: uu____1734  in
      let uu____1788 =
        let uu____1791 =
          let uu____1794 =
            let uu____1797 =
              let uu____1798 =
                let uu____1805 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1805)  in
              FStar_SMTEncoding_Term.SetOption uu____1798  in
            [uu____1797;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1814 =
            let uu____1817 =
              let uu____1820 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1820
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1817 settings.query_suffix  in
          FStar_List.append uu____1794 uu____1814  in
        FStar_List.append label_assumptions uu____1791  in
      FStar_List.append uu____1723 uu____1788
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1854 = FStar_ST.op_Bang replaying_hints  in
      match uu____1854 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1887  ->
               match uu___3_1887 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1895 -> FStar_Pervasives_Native.None)
      | uu____1898 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1916 -> FStar_Pervasives_Native.None
      | uu____1917 ->
          let uu____1918 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1918 with
           | (msg,error_labels) ->
               let err =
                 let uu____1931 =
                   FStar_List.map
                     (fun uu____1959  ->
                        match uu____1959 with
                        | (uu____1974,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1931
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1991 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1991
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1994 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let uu____2006 =
                with_fuel_and_diagnostics settings label_assumptions  in
              FStar_SMTEncoding_Z3.ask settings.query_range
                (filter_assertions settings.query_env settings.query_hint)
                settings.query_hash settings.query_all_labels uu____2006
                FStar_Pervasives_Native.None false
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
            match err.error_messages with | [] -> false | uu____2040 -> true))
  
let (errors_to_report : query_settings -> FStar_Errors.error Prims.list) =
  fun settings  ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg
       in
    let basic_errors =
      let smt_error =
        let uu____2081 = FStar_Options.query_stats ()  in
        if uu____2081
        then
          let uu____2090 =
            let uu____2092 =
              let uu____2094 =
                FStar_All.pipe_right settings.query_errors
                  (FStar_List.map error_to_short_string)
                 in
              FStar_All.pipe_right uu____2094 (FStar_String.concat ";\n\t")
               in
            FStar_All.pipe_right uu____2092 format_smt_error  in
          FStar_All.pipe_right uu____2090
            (fun _2120  -> FStar_Util.Inr _2120)
        else
          (let uu____2123 =
             FStar_List.fold_left
               (fun uu____2148  ->
                  fun err  ->
                    match uu____2148 with
                    | (ic,cc,uc) ->
                        let err1 =
                          FStar_Util.substring_from err.error_reason
                            (FStar_String.length "unknown because ")
                           in
                        if
                          ((FStar_Util.starts_with err1 "canceled") ||
                             (FStar_Util.starts_with err1 "(resource"))
                            || (FStar_Util.starts_with err1 "timeout")
                        then (ic, (cc + Prims.int_one), uc)
                        else
                          if FStar_Util.starts_with err1 "(incomplete"
                          then ((ic + Prims.int_one), cc, uc)
                          else (ic, cc, (uc + Prims.int_one)))
               (Prims.int_zero, Prims.int_zero, Prims.int_zero)
               settings.query_errors
              in
           match uu____2123 with
           | (incomplete_count,canceled_count,unknown_count) ->
               FStar_All.pipe_right
                 (match (incomplete_count, canceled_count, unknown_count)
                  with
                  | (uu____2253,_2258,_2259) when
                      ((_2258 = Prims.int_zero) && (_2259 = Prims.int_zero))
                        && (incomplete_count > Prims.int_zero)
                      ->
                      "The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
                  | (_2266,uu____2262,_2268) when
                      ((_2266 = Prims.int_zero) && (_2268 = Prims.int_zero))
                        && (canceled_count > Prims.int_zero)
                      ->
                      "The SMT query timed out, you might want to increase the rlimit"
                  | (uu____2271,uu____2272,uu____2273) ->
                      "Try with --query_stats to get more details")
                 (fun _2283  -> FStar_Util.Inl _2283))
         in
      let uu____2284 = find_localized_errors settings.query_errors  in
      match uu____2284 with
      | FStar_Pervasives_Native.Some err ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            err.error_messages smt_error
      | FStar_Pervasives_Native.None  ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
               "Unknown assertion failed", (settings.query_range))] smt_error
       in
    (let uu____2307 = FStar_Options.detail_errors ()  in
     if uu____2307
     then
       let initial_fuel1 =
         let uu___248_2311 = settings  in
         let uu____2312 = FStar_Options.initial_fuel ()  in
         let uu____2314 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___248_2311.query_env);
           query_decl = (uu___248_2311.query_decl);
           query_name = (uu___248_2311.query_name);
           query_index = (uu___248_2311.query_index);
           query_range = (uu___248_2311.query_range);
           query_fuel = uu____2312;
           query_ifuel = uu____2314;
           query_rlimit = (uu___248_2311.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___248_2311.query_errors);
           query_all_labels = (uu___248_2311.query_all_labels);
           query_suffix = (uu___248_2311.query_suffix);
           query_hash = (uu___248_2311.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let uu____2329 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____2329 FStar_Pervasives_Native.None
           false
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ());
    basic_errors
  
let (report_errors : query_settings -> unit) =
  fun qry_settings  ->
    let uu____2342 = errors_to_report qry_settings  in
    FStar_Errors.add_errors uu____2342
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2388 =
          let r = FStar_Util.mk_ref []  in
          let uu____2399 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2499  ->
                 let uu____2500 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2500
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2399 with | (add1,get1) -> (add1, get1)  in
        let uu____2582 = accumulator ()  in
        match uu____2582 with
        | (add_module_name,get_module_names) ->
            let uu____2619 = accumulator ()  in
            (match uu____2619 with
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
                                  let uu____2742 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2742
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
                         | uu____2787 ->
                             let uu____2791 = FStar_Util.prefix components
                                in
                             (match uu____2791 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2818 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2818
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2825::[] -> ()
                                    | uu____2829 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2846 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2846])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2873 =
                          let uu____2875 = get_module_names ()  in
                          FStar_All.pipe_right uu____2875
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2873);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2888 =
                          let uu____2890 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2890
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2888))))
         in
      let uu____2900 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____2900
      then
        let uu____2903 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2903 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____2922 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2936 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____2922 with
             | (tag,core) ->
                 let range =
                   let uu____2949 =
                     let uu____2951 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____2951 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____2949  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____2965 = FStar_Options.query_stats ()  in
                   if uu____2965
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
                     let uu____2999 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one)
                        in
                     Prims.op_Hat uu____2999 "}"
                   else ""  in
                 ((let uu____3008 =
                     let uu____3012 =
                       let uu____3016 =
                         let uu____3020 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3022 =
                           let uu____3026 =
                             let uu____3030 =
                               let uu____3034 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3036 =
                                 let uu____3040 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3042 =
                                   let uu____3046 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3048 =
                                     let uu____3052 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3052; stats]  in
                                   uu____3046 :: uu____3048  in
                                 uu____3040 :: uu____3042  in
                               uu____3034 :: uu____3036  in
                             used_hint_tag :: uu____3030  in
                           tag :: uu____3026  in
                         uu____3020 :: uu____3022  in
                       (settings.query_name) :: uu____3016  in
                     range :: uu____3012  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____3008);
                  (let uu____3067 = FStar_Options.print_z3_statistics ()  in
                   if uu____3067 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3093  ->
                          match uu____3093 with
                          | (uu____3101,msg,range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else ""  in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
  
let (store_hint : FStar_Util.hint -> unit) =
  fun hint  ->
    let uu____3123 = FStar_ST.op_Bang recorded_hints  in
    match uu____3123 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
    | uu____3179 -> ()
  
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____3194 =
        let uu____3196 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3196  in
      if uu____3194
      then ()
      else
        (let mk_hint core =
           {
             FStar_Util.hint_name = (settings.query_name);
             FStar_Util.hint_index = (settings.query_index);
             FStar_Util.fuel = (settings.query_fuel);
             FStar_Util.ifuel = (settings.query_ifuel);
             FStar_Util.unsat_core = core;
             FStar_Util.query_elapsed_time = Prims.int_zero;
             FStar_Util.hash =
               (match z3result.FStar_SMTEncoding_Z3.z3result_status with
                | FStar_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStar_SMTEncoding_Z3.z3result_query_hash
                | uu____3223 -> FStar_Pervasives_Native.None)
           }  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3228 =
               let uu____3229 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3229  in
             store_hint uu____3228
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3236 -> ())
  
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
    (query_settings -> FStar_SMTEncoding_Z3.z3result) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list,query_settings) FStar_Util.either)
  =
  fun qs  ->
    fun ask1  ->
      fun f  ->
        let rec aux acc qs1 =
          match qs1 with
          | [] -> FStar_Util.Inl acc
          | q::qs2 ->
              let res = ask1 q  in
              let uu____3347 = f q res  in
              (match uu____3347 with
               | FStar_Pervasives_Native.None  -> FStar_Util.Inr q
               | FStar_Pervasives_Native.Some errs -> aux (errs :: acc) qs2)
           in
        aux [] qs
  
let (full_query_id : query_settings -> Prims.string) =
  fun settings  ->
    let uu____3366 =
      let uu____3368 =
        let uu____3370 =
          let uu____3372 = FStar_Util.string_of_int settings.query_index  in
          Prims.op_Hat uu____3372 ")"  in
        Prims.op_Hat ", " uu____3370  in
      Prims.op_Hat settings.query_name uu____3368  in
    Prims.op_Hat "(" uu____3366
  
let collect : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l  ->
    let acc = []  in
    let rec add_one1 acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h,n1)::t ->
          if h = x
          then (h, (n1 + Prims.int_one)) :: t
          else (let uu____3502 = add_one1 t x  in (h, n1) :: uu____3502)
       in
    FStar_List.fold_left add_one1 acc l
  
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
            (let uu____3558 =
               let uu____3565 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3578,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3604,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3627 = FStar_Ident.text_of_lid q  in
                     (uu____3627, n1)
                  in
               match uu____3565 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3645 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3647 =
                       let uu____3649 = FStar_Options.z3_rlimit ()  in
                       uu____3649 * (Prims.parse_int "544656")  in
                     uu____3645 * uu____3647  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3656 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3657 = FStar_Options.initial_fuel ()  in
                     let uu____3659 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3656;
                       query_fuel = uu____3657;
                       query_ifuel = uu____3659;
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
                              { FStar_Util.hint_name = uu____3668;
                                FStar_Util.hint_index = uu____3669;
                                FStar_Util.fuel = uu____3670;
                                FStar_Util.ifuel = uu____3671;
                                FStar_Util.unsat_core = uu____3672;
                                FStar_Util.query_elapsed_time = uu____3673;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3558 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   let uu____3699 =
                     (FStar_Options.use_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some)
                      in
                   if uu____3699
                   then
                     let uu____3707 =
                       FStar_All.pipe_right next_hint FStar_Util.must  in
                     match uu____3707 with
                     | { FStar_Util.hint_name = uu____3712;
                         FStar_Util.hint_index = uu____3713;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3717;
                         FStar_Util.hash = h;_} ->
                         [(let uu___448_3734 = default_settings  in
                           {
                             query_env = (uu___448_3734.query_env);
                             query_decl = (uu___448_3734.query_decl);
                             query_name = (uu___448_3734.query_name);
                             query_index = (uu___448_3734.query_index);
                             query_range = (uu___448_3734.query_range);
                             query_fuel = i;
                             query_ifuel = j;
                             query_rlimit = (uu___448_3734.query_rlimit);
                             query_hint = (FStar_Pervasives_Native.Some core);
                             query_errors = (uu___448_3734.query_errors);
                             query_all_labels =
                               (uu___448_3734.query_all_labels);
                             query_suffix = (uu___448_3734.query_suffix);
                             query_hash = (uu___448_3734.query_hash)
                           })]
                   else []  in
                 let initial_fuel_max_ifuel =
                   let uu____3743 =
                     let uu____3745 = FStar_Options.max_ifuel ()  in
                     let uu____3747 = FStar_Options.initial_ifuel ()  in
                     uu____3745 > uu____3747  in
                   if uu____3743
                   then
                     let uu____3752 =
                       let uu___452_3753 = default_settings  in
                       let uu____3754 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___452_3753.query_env);
                         query_decl = (uu___452_3753.query_decl);
                         query_name = (uu___452_3753.query_name);
                         query_index = (uu___452_3753.query_index);
                         query_range = (uu___452_3753.query_range);
                         query_fuel = (uu___452_3753.query_fuel);
                         query_ifuel = uu____3754;
                         query_rlimit = (uu___452_3753.query_rlimit);
                         query_hint = (uu___452_3753.query_hint);
                         query_errors = (uu___452_3753.query_errors);
                         query_all_labels = (uu___452_3753.query_all_labels);
                         query_suffix = (uu___452_3753.query_suffix);
                         query_hash = (uu___452_3753.query_hash)
                       }  in
                     [uu____3752]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3761 =
                     let uu____3763 =
                       let uu____3765 = FStar_Options.max_fuel ()  in
                       uu____3765 / (Prims.of_int (2))  in
                     let uu____3768 = FStar_Options.initial_fuel ()  in
                     uu____3763 > uu____3768  in
                   if uu____3761
                   then
                     let uu____3773 =
                       let uu___456_3774 = default_settings  in
                       let uu____3775 =
                         let uu____3777 = FStar_Options.max_fuel ()  in
                         uu____3777 / (Prims.of_int (2))  in
                       let uu____3780 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___456_3774.query_env);
                         query_decl = (uu___456_3774.query_decl);
                         query_name = (uu___456_3774.query_name);
                         query_index = (uu___456_3774.query_index);
                         query_range = (uu___456_3774.query_range);
                         query_fuel = uu____3775;
                         query_ifuel = uu____3780;
                         query_rlimit = (uu___456_3774.query_rlimit);
                         query_hint = (uu___456_3774.query_hint);
                         query_errors = (uu___456_3774.query_errors);
                         query_all_labels = (uu___456_3774.query_all_labels);
                         query_suffix = (uu___456_3774.query_suffix);
                         query_hash = (uu___456_3774.query_hash)
                       }  in
                     [uu____3773]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3787 =
                     (let uu____3793 = FStar_Options.max_fuel ()  in
                      let uu____3795 = FStar_Options.initial_fuel ()  in
                      uu____3793 > uu____3795) &&
                       (let uu____3799 = FStar_Options.max_ifuel ()  in
                        let uu____3801 = FStar_Options.initial_ifuel ()  in
                        uu____3799 >= uu____3801)
                      in
                   if uu____3787
                   then
                     let uu____3806 =
                       let uu___460_3807 = default_settings  in
                       let uu____3808 = FStar_Options.max_fuel ()  in
                       let uu____3810 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___460_3807.query_env);
                         query_decl = (uu___460_3807.query_decl);
                         query_name = (uu___460_3807.query_name);
                         query_index = (uu___460_3807.query_index);
                         query_range = (uu___460_3807.query_range);
                         query_fuel = uu____3808;
                         query_ifuel = uu____3810;
                         query_rlimit = (uu___460_3807.query_rlimit);
                         query_hint = (uu___460_3807.query_hint);
                         query_errors = (uu___460_3807.query_errors);
                         query_all_labels = (uu___460_3807.query_all_labels);
                         query_suffix = (uu___460_3807.query_suffix);
                         query_hash = (uu___460_3807.query_hash)
                       }  in
                     [uu____3806]
                   else []  in
                 let min_fuel1 =
                   let uu____3817 =
                     let uu____3819 = FStar_Options.min_fuel ()  in
                     let uu____3821 = FStar_Options.initial_fuel ()  in
                     uu____3819 < uu____3821  in
                   if uu____3817
                   then
                     let uu____3826 =
                       let uu___464_3827 = default_settings  in
                       let uu____3828 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___464_3827.query_env);
                         query_decl = (uu___464_3827.query_decl);
                         query_name = (uu___464_3827.query_name);
                         query_index = (uu___464_3827.query_index);
                         query_range = (uu___464_3827.query_range);
                         query_fuel = uu____3828;
                         query_ifuel = Prims.int_one;
                         query_rlimit = (uu___464_3827.query_rlimit);
                         query_hint = (uu___464_3827.query_hint);
                         query_errors = (uu___464_3827.query_errors);
                         query_all_labels = (uu___464_3827.query_all_labels);
                         query_suffix = (uu___464_3827.query_suffix);
                         query_hash = (uu___464_3827.query_hash)
                       }  in
                     [uu____3826]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 =
                   (let uu____3843 = FStar_Options.z3_refresh ()  in
                    if uu____3843
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3848 = with_fuel_and_diagnostics config1 []  in
                    let uu____3851 =
                      let uu____3854 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3854  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3848
                      uu____3851 (used_hint config1))
                    in
                 let check_all_configs configs =
                   fold_queries configs check_one_config process_result  in
                 let quake_and_check_all_configs configs =
                   let lo = FStar_Options.quake_lo ()  in
                   let hi = FStar_Options.quake_hi ()  in
                   let seed = FStar_Options.z3_seed ()  in
                   let name = full_query_id default_settings  in
                   let quaking =
                     (hi > Prims.int_one) &&
                       (let uu____3899 = FStar_Options.retry ()  in
                        Prims.op_Negation uu____3899)
                      in
                   let quaking_or_retrying = hi > Prims.int_one  in
                   let hi1 = if hi < Prims.int_one then Prims.int_one else hi
                      in
                   let lo1 =
                     if lo < Prims.int_one
                     then Prims.int_one
                     else if lo > hi1 then hi1 else lo  in
                   let run_one seed1 =
                     let uu____3938 = FStar_Options.z3_refresh ()  in
                     if uu____3938
                     then
                       FStar_Options.with_saved_options
                         (fun uu____3955  ->
                            FStar_Options.set_option "z3seed"
                              (FStar_Options.Int seed1);
                            check_all_configs configs)
                     else check_all_configs configs  in
                   let rec fold_nat' f acc lo2 hi2 =
                     if lo2 > hi2
                     then acc
                     else
                       (let uu____4011 = f acc lo2  in
                        fold_nat' f uu____4011 (lo2 + Prims.int_one) hi2)
                      in
                   let best_fuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                   let best_ifuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                   let maybe_improve r n1 =
                     let uu____4134 = FStar_ST.op_Bang r  in
                     match uu____4134 with
                     | FStar_Pervasives_Native.None  ->
                         FStar_ST.op_Colon_Equals r
                           (FStar_Pervasives_Native.Some n1)
                     | FStar_Pervasives_Native.Some m ->
                         if n1 < m
                         then
                           FStar_ST.op_Colon_Equals r
                             (FStar_Pervasives_Native.Some n1)
                         else ()
                      in
                   let uu____4222 =
                     fold_nat'
                       (fun uu____4261  ->
                          fun n1  ->
                            match uu____4261 with
                            | (nsucc,nfail,rs) ->
                                let uu____4319 =
                                  (let uu____4323 =
                                     FStar_Options.quake_keep ()  in
                                   Prims.op_Negation uu____4323) &&
                                    ((nsucc >= lo1) || (nfail > (hi1 - lo1)))
                                   in
                                if uu____4319
                                then (nsucc, nfail, rs)
                                else
                                  ((let uu____4355 =
                                      (quaking_or_retrying &&
                                         ((FStar_Options.interactive ()) ||
                                            (FStar_Options.debug_any ())))
                                        && (n1 > Prims.int_zero)
                                       in
                                    if uu____4355
                                    then
                                      let uu____4359 =
                                        if quaking
                                        then
                                          let uu____4363 =
                                            FStar_Util.string_of_int nsucc
                                             in
                                          FStar_Util.format1
                                            "succeeded %s times and "
                                            uu____4363
                                        else ""  in
                                      let uu____4369 =
                                        if quaking
                                        then FStar_Util.string_of_int nfail
                                        else
                                          (let uu____4375 =
                                             FStar_Util.string_of_int nfail
                                              in
                                           Prims.op_Hat uu____4375 " times")
                                         in
                                      let uu____4378 =
                                        FStar_Util.string_of_int (hi1 - n1)
                                         in
                                      FStar_Util.print5
                                        "%s: so far query %s %sfailed %s (%s runs remain)\n"
                                        (if quaking then "Quake" else "Retry")
                                        name uu____4359 uu____4369 uu____4378
                                    else ());
                                   (let r = run_one (seed + n1)  in
                                    let uu____4396 =
                                      match r with
                                      | FStar_Util.Inr cfg ->
                                          (maybe_improve best_fuel
                                             cfg.query_fuel;
                                           maybe_improve best_ifuel
                                             cfg.query_ifuel;
                                           ((nsucc + Prims.int_one), nfail))
                                      | uu____4417 ->
                                          (nsucc, (nfail + Prims.int_one))
                                       in
                                    match uu____4396 with
                                    | (nsucc1,nfail1) ->
                                        (nsucc1, nfail1, (r :: rs)))))
                       (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
                       (hi1 - Prims.int_one)
                      in
                   match uu____4222 with
                   | (nsuccess,nfailures,rs) ->
                       let total_ran = nsuccess + nfailures  in
                       (if quaking
                        then
                          (let fuel_msg =
                             let uu____4514 =
                               let uu____4525 = FStar_ST.op_Bang best_fuel
                                  in
                               let uu____4554 = FStar_ST.op_Bang best_ifuel
                                  in
                               (uu____4525, uu____4554)  in
                             match uu____4514 with
                             | (FStar_Pervasives_Native.Some
                                f,FStar_Pervasives_Native.Some i) ->
                                 let uu____4602 = FStar_Util.string_of_int f
                                    in
                                 let uu____4604 = FStar_Util.string_of_int i
                                    in
                                 FStar_Util.format2
                                   " (best fuel=%s, best ifuel=%s)"
                                   uu____4602 uu____4604
                             | (uu____4607,uu____4608) -> ""  in
                           let uu____4622 = FStar_Util.string_of_int nsuccess
                              in
                           let uu____4624 =
                             FStar_Util.string_of_int total_ran  in
                           FStar_Util.print5
                             "Quake: query %s succeeded %s/%s times%s%s\n"
                             name uu____4622 uu____4624
                             (if total_ran < hi1
                              then " (early finish)"
                              else "") fuel_msg)
                        else ();
                        if nsuccess < lo1
                        then
                          (let all_errs =
                             FStar_List.concatMap
                               (fun uu___4_4651  ->
                                  match uu___4_4651 with
                                  | FStar_Util.Inr uu____4662 -> []
                                  | FStar_Util.Inl es -> [es]) rs
                              in
                           let uu____4676 =
                             quaking_or_retrying &&
                               (let uu____4679 = FStar_Options.query_stats ()
                                   in
                                Prims.op_Negation uu____4679)
                              in
                           if uu____4676
                           then
                             let errors_to_report1 errs =
                               errors_to_report
                                 (let uu___555_4696 = default_settings  in
                                  {
                                    query_env = (uu___555_4696.query_env);
                                    query_decl = (uu___555_4696.query_decl);
                                    query_name = (uu___555_4696.query_name);
                                    query_index = (uu___555_4696.query_index);
                                    query_range = (uu___555_4696.query_range);
                                    query_fuel = (uu___555_4696.query_fuel);
                                    query_ifuel = (uu___555_4696.query_ifuel);
                                    query_rlimit =
                                      (uu___555_4696.query_rlimit);
                                    query_hint = (uu___555_4696.query_hint);
                                    query_errors = errs;
                                    query_all_labels =
                                      (uu___555_4696.query_all_labels);
                                    query_suffix =
                                      (uu___555_4696.query_suffix);
                                    query_hash = (uu___555_4696.query_hash)
                                  })
                                in
                             let errs =
                               FStar_List.map errors_to_report1 all_errs  in
                             let errs1 =
                               let uu____4721 =
                                 FStar_All.pipe_right errs FStar_List.flatten
                                  in
                               FStar_All.pipe_right uu____4721 collect  in
                             let errs2 =
                               FStar_All.pipe_right errs1
                                 (FStar_List.map
                                    (fun uu____4804  ->
                                       match uu____4804 with
                                       | ((e,m,r),n1) ->
                                           if n1 > Prims.int_one
                                           then
                                             let uu____4848 =
                                               let uu____4850 =
                                                 let uu____4852 =
                                                   FStar_Util.string_of_int
                                                     n1
                                                    in
                                                 FStar_Util.format1
                                                   " (%s times)" uu____4852
                                                  in
                                               Prims.op_Hat m uu____4850  in
                                             (e, uu____4848, r)
                                           else (e, m, r)))
                                in
                             (FStar_Errors.add_errors errs2;
                              (let rng =
                                 match FStar_Pervasives_Native.snd
                                         env.FStar_TypeChecker_Env.qtbl_name_and_index
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (l,uu____4872) ->
                                     FStar_Ident.range_of_lid l
                                 | uu____4880 -> FStar_Range.dummyRange  in
                               if quaking
                               then
                                 let uu____4889 =
                                   let uu____4899 =
                                     let uu____4907 =
                                       let uu____4909 =
                                         FStar_Util.string_of_int nsuccess
                                          in
                                       let uu____4911 =
                                         FStar_Util.string_of_int total_ran
                                          in
                                       let uu____4913 =
                                         FStar_Util.string_of_int lo1  in
                                       let uu____4915 =
                                         FStar_Util.string_of_int hi1  in
                                       FStar_Util.format6
                                         "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                                         name uu____4909 uu____4911
                                         uu____4913 uu____4915
                                         (if total_ran < hi1
                                          then " (early abort)"
                                          else "")
                                        in
                                     (FStar_Errors.Error_QuakeFailed,
                                       uu____4907, rng)
                                      in
                                   [uu____4899]  in
                                 FStar_TypeChecker_Err.add_errors env
                                   uu____4889
                               else ()))
                           else
                             (let report1 errs =
                                report_errors
                                  (let uu___578_4955 = default_settings  in
                                   {
                                     query_env = (uu___578_4955.query_env);
                                     query_decl = (uu___578_4955.query_decl);
                                     query_name = (uu___578_4955.query_name);
                                     query_index =
                                       (uu___578_4955.query_index);
                                     query_range =
                                       (uu___578_4955.query_range);
                                     query_fuel = (uu___578_4955.query_fuel);
                                     query_ifuel =
                                       (uu___578_4955.query_ifuel);
                                     query_rlimit =
                                       (uu___578_4955.query_rlimit);
                                     query_hint = (uu___578_4955.query_hint);
                                     query_errors = errs;
                                     query_all_labels =
                                       (uu___578_4955.query_all_labels);
                                     query_suffix =
                                       (uu___578_4955.query_suffix);
                                     query_hash = (uu___578_4955.query_hash)
                                   })
                                 in
                              FStar_List.iter report1 all_errs))
                        else ())
                    in
                 let skip =
                   (FStar_Options.admit_smt_queries ()) ||
                     (let uu____4965 = FStar_Options.admit_except ()  in
                      match uu____4965 with
                      | FStar_Pervasives_Native.Some id1 ->
                          if FStar_Util.starts_with id1 "("
                          then
                            let uu____4976 = full_query_id default_settings
                               in
                            uu____4976 <> id1
                          else default_settings.query_name <> id1
                      | FStar_Pervasives_Native.None  -> false)
                    in
                 if skip
                 then
                   let uu____4985 =
                     (FStar_Options.record_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some)
                      in
                   (if uu____4985
                    then
                      let uu____4991 =
                        FStar_All.pipe_right next_hint FStar_Util.must  in
                      FStar_All.pipe_right uu____4991 store_hint
                    else ())
                 else quake_and_check_all_configs all_configs)
  
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  valid_intro: Prims.bool ;
  valid_elim: Prims.bool }
let (__proj__Mksolver_cfg__item__seed : solver_cfg -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> seed
  
let (__proj__Mksolver_cfg__item__cliopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> cliopt
  
let (__proj__Mksolver_cfg__item__facts :
  solver_cfg -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun projectee  ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> facts
  
let (__proj__Mksolver_cfg__item__valid_intro : solver_cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_intro
  
let (__proj__Mksolver_cfg__item__valid_elim : solver_cfg -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_elim
  
let (_last_cfg : solver_cfg FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (get_cfg : FStar_TypeChecker_Env.env -> solver_cfg) =
  fun env  ->
    let uu____5219 = FStar_Options.z3_seed ()  in
    let uu____5221 = FStar_Options.z3_cliopt ()  in
    let uu____5225 = FStar_Options.smtencoding_valid_intro ()  in
    let uu____5227 = FStar_Options.smtencoding_valid_elim ()  in
    {
      seed = uu____5219;
      cliopt = uu____5221;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____5225;
      valid_elim = uu____5227
    }
  
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____5235 =
      let uu____5238 = get_cfg env  in
      FStar_Pervasives_Native.Some uu____5238  in
    FStar_ST.op_Colon_Equals _last_cfg uu____5235
  
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    let uu____5269 = FStar_ST.op_Bang _last_cfg  in
    match uu____5269 with
    | FStar_Pervasives_Native.None  -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____5299 = let uu____5301 = get_cfg env  in cfg = uu____5301
           in
        Prims.op_Negation uu____5299
  
let (do_solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____5330 = should_refresh tcenv  in
         if uu____5330
         then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
         else ());
        (let uu____5337 =
           let uu____5339 =
             let uu____5341 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____5341  in
           FStar_Util.format1 "Starting query at %s" uu____5339  in
         FStar_SMTEncoding_Encode.push uu____5337);
        (let pop1 uu____5349 =
           let uu____5350 =
             let uu____5352 =
               let uu____5354 = FStar_TypeChecker_Env.get_range tcenv  in
               FStar_All.pipe_left FStar_Range.string_of_range uu____5354  in
             FStar_Util.format1 "Ending query at %s" uu____5352  in
           FStar_SMTEncoding_Encode.pop uu____5350  in
         try
           (fun uu___619_5370  ->
              match () with
              | () ->
                  let uu____5371 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q
                     in
                  (match uu____5371 with
                   | (prefix1,labels,qry,suffix) ->
                       let tcenv1 =
                         FStar_TypeChecker_Env.incr_query_index tcenv  in
                       (match qry with
                        | FStar_SMTEncoding_Term.Assume
                            {
                              FStar_SMTEncoding_Term.assumption_term =
                                {
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.FalseOp
                                     ,uu____5403);
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____5404;
                                  FStar_SMTEncoding_Term.rng = uu____5405;_};
                              FStar_SMTEncoding_Term.assumption_caption =
                                uu____5406;
                              FStar_SMTEncoding_Term.assumption_name =
                                uu____5407;
                              FStar_SMTEncoding_Term.assumption_fact_ids =
                                uu____5408;_}
                            -> pop1 ()
                        | uu____5428 when tcenv1.FStar_TypeChecker_Env.admit
                            -> pop1 ()
                        | FStar_SMTEncoding_Term.Assume uu____5429 ->
                            (ask_and_report_errors tcenv1 labels prefix1 qry
                               suffix;
                             pop1 ())
                        | uu____5431 -> failwith "Impossible"))) ()
         with
         | FStar_SMTEncoding_Env.Inner_let_rec names1 ->
             (pop1 ();
              (let uu____5447 =
                 let uu____5457 =
                   let uu____5465 =
                     let uu____5467 =
                       let uu____5469 =
                         FStar_List.map FStar_Pervasives_Native.fst names1
                          in
                       FStar_String.concat "," uu____5469  in
                     FStar_Util.format1
                       "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                       uu____5467
                      in
                   (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                     uu____5465, (tcenv.FStar_TypeChecker_Env.range))
                    in
                 [uu____5457]  in
               FStar_TypeChecker_Err.add_errors tcenv uu____5447)))
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        let uu____5524 = FStar_Options.no_smt ()  in
        if uu____5524
        then
          let uu____5527 =
            let uu____5537 =
              let uu____5545 =
                let uu____5547 = FStar_Syntax_Print.term_to_string q  in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____5547
                 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____5545,
                (tcenv.FStar_TypeChecker_Env.range))
               in
            [uu____5537]  in
          FStar_TypeChecker_Err.add_errors tcenv uu____5527
        else
          (let uu____5567 =
             let uu____5571 =
               let uu____5573 = FStar_TypeChecker_Env.current_module tcenv
                  in
               FStar_Ident.string_of_lid uu____5573  in
             FStar_Pervasives_Native.Some uu____5571  in
           FStar_Profiling.profile
             (fun uu____5576  -> do_solve use_env_msg tcenv q) uu____5567
             "FStar.TypeChecker.SMTEncoding.solve_top_level")
  
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init =
      (fun e  -> save_cfg e; FStar_SMTEncoding_Encode.init e);
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____5590 =
             let uu____5597 = FStar_Options.peek ()  in (e, g, uu____5597)
              in
           [uu____5590]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____5613  -> ());
    FStar_TypeChecker_Env.push = (fun uu____5615  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____5618  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____5621  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____5640  -> fun uu____5641  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____5656  -> fun uu____5657  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____5663 =
             let uu____5670 = FStar_Options.peek ()  in (e, g, uu____5670)
              in
           [uu____5663]);
    FStar_TypeChecker_Env.solve =
      (fun uu____5686  -> fun uu____5687  -> fun uu____5688  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____5695  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____5697  -> ())
  } 
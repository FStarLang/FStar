open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____30 'Auu____31 'Auu____32 .
    ('Auu____30,('Auu____31 * 'Auu____32)) FStar_Util.either ->
      ('Auu____30,'Auu____31) FStar_Util.either
  =
  fun uu___0_49  ->
    match uu___0_49 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____64) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db : 'Auu____100 . Prims.string -> 'Auu____100 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____114 = FStar_Options.record_hints ()  in
       if uu____114
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____144 = FStar_Options.use_hints ()  in
       if uu____144
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____151 = FStar_Options.hint_file ()  in
           match uu____151 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____160 = FStar_Util.read_hints val_filename  in
         match uu____160 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____167 = FStar_Options.hint_info ()  in
               if uu____167
               then
                 let uu____170 =
                   let uu____172 = FStar_Options.hint_file ()  in
                   match uu____172 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____182 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____170
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____220 = FStar_Options.hint_info ()  in
             (if uu____220
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____237 = FStar_Options.record_hints ()  in
     if uu____237
     then
       let hints =
         let uu____241 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____241  in
       let hints_db =
         let uu____268 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____268; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____274 = FStar_Options.hint_file ()  in
         match uu____274 with
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
        | uu____399 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_407  ->
                     match uu___1_407 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____410 -> false)))
              ||
              (let uu____413 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____413)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___2_437 =
          match uu___2_437 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____452 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____462 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____485 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____485
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____503 ->
                   let uu____504 = keep_decl d  in
                   if uu____504 then d :: out else out) [] theory_rev
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
            let uu____560 = filter_using_facts_from e theory  in
            (uu____560, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____581 =
              let uu____592 =
                let uu____603 =
                  let uu____606 =
                    let uu____607 =
                      let uu____609 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____609  in
                    FStar_SMTEncoding_Term.Caption uu____607  in
                  [uu____606]  in
                (uu____603, (Prims.parse_int "0"), (Prims.parse_int "0"))  in
              FStar_List.fold_left
                (fun uu____639  ->
                   fun d  ->
                     match uu____639 with
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
                              let uu____733 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____733
                                (fun uu____793  ->
                                   match uu____793 with
                                   | (decls1,uu____818,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____838 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____592 theory_rev
               in
            (match uu____581 with
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
        let uu____900 = filter_assertions_with_stats e core theory  in
        match uu____900 with
        | (theory1,b,uu____923,uu____924) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____960 = filter_using_facts_from e x  in (uu____960, false)
  
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
    let uu____1190 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1192 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____1190
      uu____1192
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
  
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err  ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____1218 =
        let uu____1220 = FStar_Util.string_of_int err.error_fuel  in
        let uu____1222 = FStar_Util.string_of_int err.error_ifuel  in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____1220 uu____1222
          (if FStar_Option.isSome err.error_hint then "with hint" else "")
         in
      [uu____1218]
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
      let uu____1766 =
        let uu____1769 =
          let uu____1770 =
            let uu____1772 = FStar_Util.string_of_int n1  in
            let uu____1774 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1772 uu____1774
             in
          FStar_SMTEncoding_Term.Caption uu____1770  in
        let uu____1777 =
          let uu____1780 =
            let uu____1781 =
              let uu____1789 =
                let uu____1790 =
                  let uu____1795 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1800 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1795, uu____1800)  in
                FStar_SMTEncoding_Util.mkEq uu____1790  in
              (uu____1789, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1781  in
          let uu____1804 =
            let uu____1807 =
              let uu____1808 =
                let uu____1816 =
                  let uu____1817 =
                    let uu____1822 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1827 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1822, uu____1827)  in
                  FStar_SMTEncoding_Util.mkEq uu____1817  in
                (uu____1816, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1808  in
            [uu____1807; settings.query_decl]  in
          uu____1780 :: uu____1804  in
        uu____1769 :: uu____1777  in
      let uu____1831 =
        let uu____1834 =
          let uu____1837 =
            let uu____1840 =
              let uu____1841 =
                let uu____1848 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1848)  in
              FStar_SMTEncoding_Term.SetOption uu____1841  in
            [uu____1840;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1857 =
            let uu____1860 =
              let uu____1863 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1863
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1860 settings.query_suffix  in
          FStar_List.append uu____1837 uu____1857  in
        FStar_List.append label_assumptions uu____1834  in
      FStar_List.append uu____1766 uu____1831
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1897 = FStar_ST.op_Bang replaying_hints  in
      match uu____1897 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1930  ->
               match uu___3_1930 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1938 -> FStar_Pervasives_Native.None)
      | uu____1941 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1959 -> FStar_Pervasives_Native.None
      | uu____1960 ->
          let uu____1961 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1961 with
           | (msg,error_labels) ->
               let err =
                 let uu____1974 =
                   FStar_List.map
                     (fun uu____2002  ->
                        match uu____2002 with
                        | (uu____2017,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1974
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2034 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____2034
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____2037 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____2057 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2057
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2086 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2086)
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
            match err.error_messages with | [] -> false | uu____2142 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2164 = find_localized_errors errs  in
    FStar_Option.isSome uu____2164
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg
       in
    (let smt_error =
       let uu____2186 =
         let uu____2188 =
           FStar_All.pipe_right settings.query_errors
             (FStar_List.map error_to_short_string)
            in
         FStar_All.pipe_right uu____2188 (FStar_String.concat ";\n\t")  in
       FStar_All.pipe_right uu____2186 format_smt_error  in
     let uu____2205 = find_localized_errors settings.query_errors  in
     match uu____2205 with
     | FStar_Pervasives_Native.Some err ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           err.error_messages (FStar_Pervasives_Native.Some smt_error)
     | FStar_Pervasives_Native.None  ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
              "Unknown assertion failed", (settings.query_range))]
           (FStar_Pervasives_Native.Some smt_error));
    (let uu____2227 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2230 = FStar_Options.n_cores ()  in
          uu____2230 = (Prims.parse_int "1"))
        in
     if uu____2227
     then
       let initial_fuel1 =
         let uu___237_2236 = settings  in
         let uu____2237 = FStar_Options.initial_fuel ()  in
         let uu____2239 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___237_2236.query_env);
           query_decl = (uu___237_2236.query_decl);
           query_name = (uu___237_2236.query_name);
           query_index = (uu___237_2236.query_index);
           query_range = (uu___237_2236.query_range);
           query_fuel = uu____2237;
           query_ifuel = uu____2239;
           query_rlimit = (uu___237_2236.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___237_2236.query_errors);
           query_all_labels = (uu___237_2236.query_all_labels);
           query_suffix = (uu___237_2236.query_suffix);
           query_hash = (uu___237_2236.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2262 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2262
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2291 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2291)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2356 =
          let r = FStar_Util.mk_ref []  in
          let uu____2367 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2467  ->
                 let uu____2468 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2468
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2367 with | (add1,get1) -> (add1, get1)  in
        let uu____2550 = accumulator ()  in
        match uu____2550 with
        | (add_module_name,get_module_names) ->
            let uu____2587 = accumulator ()  in
            (match uu____2587 with
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
                                  let uu____2710 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2710
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
                         | uu____2755 ->
                             let uu____2759 = FStar_Util.prefix components
                                in
                             (match uu____2759 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2786 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2786
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2793::[] -> ()
                                    | uu____2797 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2814 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2814])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2841 =
                          let uu____2843 = get_module_names ()  in
                          FStar_All.pipe_right uu____2843
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2841);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2856 =
                          let uu____2858 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2858
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2856))))
         in
      let uu____2868 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____2868
      then
        let uu____2871 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2871 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____2890 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2904 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____2890 with
             | (tag,core) ->
                 let range =
                   let uu____2917 =
                     let uu____2919 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____2919 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____2917  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____2933 = FStar_Options.query_stats ()  in
                   if uu____2933
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
                     let uu____2967 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____2967 "}"
                   else ""  in
                 ((let uu____2976 =
                     let uu____2980 =
                       let uu____2984 =
                         let uu____2988 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____2990 =
                           let uu____2994 =
                             let uu____2998 =
                               let uu____3002 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3004 =
                                 let uu____3008 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3010 =
                                   let uu____3014 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3016 =
                                     let uu____3020 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3020; stats]  in
                                   uu____3014 :: uu____3016  in
                                 uu____3008 :: uu____3010  in
                               uu____3002 :: uu____3004  in
                             used_hint_tag :: uu____2998  in
                           tag :: uu____2994  in
                         uu____2988 :: uu____2990  in
                       (settings.query_name) :: uu____2984  in
                     range :: uu____2980  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2976);
                  (let uu____3035 = FStar_Options.print_z3_statistics ()  in
                   if uu____3035 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3061  ->
                          match uu____3061 with
                          | (uu____3069,msg,range1) ->
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
      let uu____3096 =
        let uu____3098 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3098  in
      if uu____3096
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
                | uu____3125 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3133 = FStar_ST.op_Bang recorded_hints  in
           match uu____3133 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3189 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3196 =
               let uu____3197 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3197  in
             store_hint uu____3196
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3204 -> ())
  
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
                     let uu____3315 = f q res  in
                     match uu____3315 with
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
            (let uu____3354 =
               let uu____3361 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3374,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3400,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3423 = FStar_Ident.text_of_lid q  in
                     (uu____3423, n1)
                  in
               match uu____3361 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3441 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3443 =
                       let uu____3445 = FStar_Options.z3_rlimit ()  in
                       uu____3445 * (Prims.parse_int "544656")  in
                     uu____3441 * uu____3443  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3452 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3453 = FStar_Options.initial_fuel ()  in
                     let uu____3455 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3452;
                       query_fuel = uu____3453;
                       query_ifuel = uu____3455;
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
                              { FStar_Util.hint_name = uu____3464;
                                FStar_Util.hint_index = uu____3465;
                                FStar_Util.fuel = uu____3466;
                                FStar_Util.ifuel = uu____3467;
                                FStar_Util.unsat_core = uu____3468;
                                FStar_Util.query_elapsed_time = uu____3469;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3354 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3497;
                         FStar_Util.hint_index = uu____3498;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3502;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___426_3519 = default_settings  in
                         {
                           query_env = (uu___426_3519.query_env);
                           query_decl = (uu___426_3519.query_decl);
                           query_name = (uu___426_3519.query_name);
                           query_index = (uu___426_3519.query_index);
                           query_range = (uu___426_3519.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___426_3519.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___426_3519.query_errors);
                           query_all_labels =
                             (uu___426_3519.query_all_labels);
                           query_suffix = (uu___426_3519.query_suffix);
                           query_hash = (uu___426_3519.query_hash)
                         })]
                   | uu____3523 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3529 =
                     let uu____3531 = FStar_Options.max_ifuel ()  in
                     let uu____3533 = FStar_Options.initial_ifuel ()  in
                     uu____3531 > uu____3533  in
                   if uu____3529
                   then
                     let uu____3538 =
                       let uu___431_3539 = default_settings  in
                       let uu____3540 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___431_3539.query_env);
                         query_decl = (uu___431_3539.query_decl);
                         query_name = (uu___431_3539.query_name);
                         query_index = (uu___431_3539.query_index);
                         query_range = (uu___431_3539.query_range);
                         query_fuel = (uu___431_3539.query_fuel);
                         query_ifuel = uu____3540;
                         query_rlimit = (uu___431_3539.query_rlimit);
                         query_hint = (uu___431_3539.query_hint);
                         query_errors = (uu___431_3539.query_errors);
                         query_all_labels = (uu___431_3539.query_all_labels);
                         query_suffix = (uu___431_3539.query_suffix);
                         query_hash = (uu___431_3539.query_hash)
                       }  in
                     [uu____3538]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3547 =
                     let uu____3549 =
                       let uu____3551 = FStar_Options.max_fuel ()  in
                       uu____3551 / (Prims.parse_int "2")  in
                     let uu____3554 = FStar_Options.initial_fuel ()  in
                     uu____3549 > uu____3554  in
                   if uu____3547
                   then
                     let uu____3559 =
                       let uu___435_3560 = default_settings  in
                       let uu____3561 =
                         let uu____3563 = FStar_Options.max_fuel ()  in
                         uu____3563 / (Prims.parse_int "2")  in
                       let uu____3566 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___435_3560.query_env);
                         query_decl = (uu___435_3560.query_decl);
                         query_name = (uu___435_3560.query_name);
                         query_index = (uu___435_3560.query_index);
                         query_range = (uu___435_3560.query_range);
                         query_fuel = uu____3561;
                         query_ifuel = uu____3566;
                         query_rlimit = (uu___435_3560.query_rlimit);
                         query_hint = (uu___435_3560.query_hint);
                         query_errors = (uu___435_3560.query_errors);
                         query_all_labels = (uu___435_3560.query_all_labels);
                         query_suffix = (uu___435_3560.query_suffix);
                         query_hash = (uu___435_3560.query_hash)
                       }  in
                     [uu____3559]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3573 =
                     (let uu____3579 = FStar_Options.max_fuel ()  in
                      let uu____3581 = FStar_Options.initial_fuel ()  in
                      uu____3579 > uu____3581) &&
                       (let uu____3585 = FStar_Options.max_ifuel ()  in
                        let uu____3587 = FStar_Options.initial_ifuel ()  in
                        uu____3585 >= uu____3587)
                      in
                   if uu____3573
                   then
                     let uu____3592 =
                       let uu___439_3593 = default_settings  in
                       let uu____3594 = FStar_Options.max_fuel ()  in
                       let uu____3596 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___439_3593.query_env);
                         query_decl = (uu___439_3593.query_decl);
                         query_name = (uu___439_3593.query_name);
                         query_index = (uu___439_3593.query_index);
                         query_range = (uu___439_3593.query_range);
                         query_fuel = uu____3594;
                         query_ifuel = uu____3596;
                         query_rlimit = (uu___439_3593.query_rlimit);
                         query_hint = (uu___439_3593.query_hint);
                         query_errors = (uu___439_3593.query_errors);
                         query_all_labels = (uu___439_3593.query_all_labels);
                         query_suffix = (uu___439_3593.query_suffix);
                         query_hash = (uu___439_3593.query_hash)
                       }  in
                     [uu____3592]
                   else []  in
                 let min_fuel1 =
                   let uu____3603 =
                     let uu____3605 = FStar_Options.min_fuel ()  in
                     let uu____3607 = FStar_Options.initial_fuel ()  in
                     uu____3605 < uu____3607  in
                   if uu____3603
                   then
                     let uu____3612 =
                       let uu___443_3613 = default_settings  in
                       let uu____3614 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___443_3613.query_env);
                         query_decl = (uu___443_3613.query_decl);
                         query_name = (uu___443_3613.query_name);
                         query_index = (uu___443_3613.query_index);
                         query_range = (uu___443_3613.query_range);
                         query_fuel = uu____3614;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___443_3613.query_rlimit);
                         query_hint = (uu___443_3613.query_hint);
                         query_errors = (uu___443_3613.query_errors);
                         query_all_labels = (uu___443_3613.query_all_labels);
                         query_suffix = (uu___443_3613.query_suffix);
                         query_hash = (uu___443_3613.query_hash)
                       }  in
                     [uu____3612]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3639 = FStar_Options.z3_refresh ()  in
                    if uu____3639
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3644 = with_fuel_and_diagnostics config1 []  in
                    let uu____3647 =
                      let uu____3650 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3650  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3644
                      uu____3647 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___456_3673 = default_settings  in
                        {
                          query_env = (uu___456_3673.query_env);
                          query_decl = (uu___456_3673.query_decl);
                          query_name = (uu___456_3673.query_name);
                          query_index = (uu___456_3673.query_index);
                          query_range = (uu___456_3673.query_range);
                          query_fuel = (uu___456_3673.query_fuel);
                          query_ifuel = (uu___456_3673.query_ifuel);
                          query_rlimit = (uu___456_3673.query_rlimit);
                          query_hint = (uu___456_3673.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___456_3673.query_all_labels);
                          query_suffix = (uu___456_3673.query_suffix);
                          query_hash = (uu___456_3673.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3674 =
                   let uu____3683 = FStar_Options.admit_smt_queries ()  in
                   let uu____3685 = FStar_Options.admit_except ()  in
                   (uu____3683, uu____3685)  in
                 (match uu____3674 with
                  | (true ,uu____3693) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3723 =
                              let uu____3725 =
                                let uu____3727 =
                                  let uu____3729 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____3729 ")"  in
                                Prims.op_Hat ", " uu____3727  in
                              Prims.op_Hat default_settings.query_name
                                uu____3725
                               in
                            Prims.op_Hat "(" uu____3723  in
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
        (let uu____3769 =
           let uu____3771 =
             let uu____3773 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3773  in
           FStar_Util.format1 "Starting query at %s" uu____3771  in
         FStar_SMTEncoding_Encode.push uu____3769);
        (let uu____3776 = FStar_Options.no_smt ()  in
         if uu____3776
         then
           let uu____3779 =
             let uu____3789 =
               let uu____3797 =
                 let uu____3799 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3799
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3797,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3789]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3779
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3820 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3820 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3856 =
                  let uu____3857 =
                    let uu____3859 =
                      let uu____3861 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3861
                       in
                    FStar_Util.format1 "Ending query at %s" uu____3859  in
                  FStar_SMTEncoding_Encode.pop uu____3857  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____3864);
                           FStar_SMTEncoding_Term.freevars = uu____3865;
                           FStar_SMTEncoding_Term.rng = uu____3866;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3867;
                       FStar_SMTEncoding_Term.assumption_name = uu____3868;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3869;_}
                     -> pop1 ()
                 | uu____3889 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3890 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3892 -> failwith "Impossible")))
  
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
           let uu____3900 =
             let uu____3907 = FStar_Options.peek ()  in (e, g, uu____3907)
              in
           [uu____3900]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3923  -> ());
    FStar_TypeChecker_Env.push = (fun uu____3925  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3928  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3931  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____3950  -> fun uu____3951  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3966  -> fun uu____3967  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3973 =
             let uu____3980 = FStar_Options.peek ()  in (e, g, uu____3980)
              in
           [uu____3973]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3996  -> fun uu____3997  -> fun uu____3998  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4005  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4007  -> ())
  } 
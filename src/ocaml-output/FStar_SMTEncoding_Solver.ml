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
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
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
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e  ->
    fun theory  ->
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____404 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_412  ->
                     match uu___1_412 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____415 -> false)))
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
        let keep_decl uu___2_442 =
          match uu___2_442 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____457 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____467 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____490 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____490
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____508 ->
                   let uu____509 = keep_decl d  in
                   if uu____509 then d :: out else out) [] theory_rev
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
            let uu____565 = filter_using_facts_from e theory  in
            (uu____565, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____586 =
              let uu____597 =
                let uu____608 =
                  let uu____611 =
                    let uu____612 =
                      let uu____614 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____614  in
                    FStar_SMTEncoding_Term.Caption uu____612  in
                  [uu____611]  in
                (uu____608, (Prims.parse_int "0"), (Prims.parse_int "0"))  in
              FStar_List.fold_left
                (fun uu____644  ->
                   fun d  ->
                     match uu____644 with
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
                              let uu____738 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____738
                                (fun uu____798  ->
                                   match uu____798 with
                                   | (decls1,uu____823,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____843 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____597 theory_rev
               in
            (match uu____586 with
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
        let uu____905 = filter_assertions_with_stats e core theory  in
        match uu____905 with
        | (theory1,b,uu____928,uu____929) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____965 = filter_using_facts_from e x  in (uu____965, false)
  
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
    let uu____1195 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1197 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____1195
      uu____1197
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
  
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err  ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____1223 =
        let uu____1225 = FStar_Util.string_of_int err.error_fuel  in
        let uu____1227 = FStar_Util.string_of_int err.error_ifuel  in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____1225 uu____1227
          (if FStar_Option.isSome err.error_hint then "with hint" else "")
         in
      [uu____1223]
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
      let uu____1771 =
        let uu____1774 =
          let uu____1775 =
            let uu____1777 = FStar_Util.string_of_int n1  in
            let uu____1779 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1777 uu____1779
             in
          FStar_SMTEncoding_Term.Caption uu____1775  in
        let uu____1782 =
          let uu____1785 =
            let uu____1786 =
              let uu____1794 =
                let uu____1795 =
                  let uu____1800 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1805 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1800, uu____1805)  in
                FStar_SMTEncoding_Util.mkEq uu____1795  in
              (uu____1794, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1786  in
          let uu____1809 =
            let uu____1812 =
              let uu____1813 =
                let uu____1821 =
                  let uu____1822 =
                    let uu____1827 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1832 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1827, uu____1832)  in
                  FStar_SMTEncoding_Util.mkEq uu____1822  in
                (uu____1821, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1813  in
            [uu____1812; settings.query_decl]  in
          uu____1785 :: uu____1809  in
        uu____1774 :: uu____1782  in
      let uu____1836 =
        let uu____1839 =
          let uu____1842 =
            let uu____1845 =
              let uu____1846 =
                let uu____1853 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1853)  in
              FStar_SMTEncoding_Term.SetOption uu____1846  in
            [uu____1845;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1862 =
            let uu____1865 =
              let uu____1868 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1868
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1865 settings.query_suffix  in
          FStar_List.append uu____1842 uu____1862  in
        FStar_List.append label_assumptions uu____1839  in
      FStar_List.append uu____1771 uu____1836
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1902 = FStar_ST.op_Bang replaying_hints  in
      match uu____1902 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1935  ->
               match uu___3_1935 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1943 -> FStar_Pervasives_Native.None)
      | uu____1946 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1964 -> FStar_Pervasives_Native.None
      | uu____1965 ->
          let uu____1966 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1966 with
           | (msg,error_labels) ->
               let err =
                 let uu____1979 =
                   FStar_List.map
                     (fun uu____2007  ->
                        match uu____2007 with
                        | (uu____2022,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1979
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2039 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____2039
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____2042 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____2062 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2062
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2091 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2091)
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
            match err.error_messages with | [] -> false | uu____2147 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2169 = find_localized_errors errs  in
    FStar_Option.isSome uu____2169
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg
       in
    (let smt_error =
       let uu____2191 =
         let uu____2193 =
           FStar_All.pipe_right settings.query_errors
             (FStar_List.map error_to_short_string)
            in
         FStar_All.pipe_right uu____2193 (FStar_String.concat ";\n\t")  in
       FStar_All.pipe_right uu____2191 format_smt_error  in
     let uu____2210 = find_localized_errors settings.query_errors  in
     match uu____2210 with
     | FStar_Pervasives_Native.Some err ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           err.error_messages (FStar_Pervasives_Native.Some smt_error)
     | FStar_Pervasives_Native.None  ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
              "Unknown assertion failed", (settings.query_range))]
           (FStar_Pervasives_Native.Some smt_error));
    (let uu____2232 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2235 = FStar_Options.n_cores ()  in
          uu____2235 = (Prims.parse_int "1"))
        in
     if uu____2232
     then
       let initial_fuel1 =
         let uu___237_2241 = settings  in
         let uu____2242 = FStar_Options.initial_fuel ()  in
         let uu____2244 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___237_2241.query_env);
           query_decl = (uu___237_2241.query_decl);
           query_name = (uu___237_2241.query_name);
           query_index = (uu___237_2241.query_index);
           query_range = (uu___237_2241.query_range);
           query_fuel = uu____2242;
           query_ifuel = uu____2244;
           query_rlimit = (uu___237_2241.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___237_2241.query_errors);
           query_all_labels = (uu___237_2241.query_all_labels);
           query_suffix = (uu___237_2241.query_suffix);
           query_hash = (uu___237_2241.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2267 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2267
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2296 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2296)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2361 =
          let r = FStar_Util.mk_ref []  in
          let uu____2372 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2472  ->
                 let uu____2473 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2473
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2372 with | (add1,get1) -> (add1, get1)  in
        let uu____2555 = accumulator ()  in
        match uu____2555 with
        | (add_module_name,get_module_names) ->
            let uu____2592 = accumulator ()  in
            (match uu____2592 with
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
                                  let uu____2715 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2715
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
                         | uu____2760 ->
                             let uu____2764 = FStar_Util.prefix components
                                in
                             (match uu____2764 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2791 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2791
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2798::[] -> ()
                                    | uu____2802 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2819 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2819])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2846 =
                          let uu____2848 = get_module_names ()  in
                          FStar_All.pipe_right uu____2848
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2846);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2861 =
                          let uu____2863 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2863
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2861))))
         in
      let uu____2873 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____2873
      then
        let uu____2876 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2876 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____2895 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2909 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____2895 with
             | (tag,core) ->
                 let range =
                   let uu____2922 =
                     let uu____2924 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____2924 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____2922  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____2938 = FStar_Options.query_stats ()  in
                   if uu____2938
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
                     let uu____2972 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____2972 "}"
                   else ""  in
                 ((let uu____2981 =
                     let uu____2985 =
                       let uu____2989 =
                         let uu____2993 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____2995 =
                           let uu____2999 =
                             let uu____3003 =
                               let uu____3007 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3009 =
                                 let uu____3013 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3015 =
                                   let uu____3019 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3021 =
                                     let uu____3025 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3025; stats]  in
                                   uu____3019 :: uu____3021  in
                                 uu____3013 :: uu____3015  in
                               uu____3007 :: uu____3009  in
                             used_hint_tag :: uu____3003  in
                           tag :: uu____2999  in
                         uu____2993 :: uu____2995  in
                       (settings.query_name) :: uu____2989  in
                     range :: uu____2985  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2981);
                  (let uu____3040 = FStar_Options.print_z3_statistics ()  in
                   if uu____3040 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3066  ->
                          match uu____3066 with
                          | (uu____3074,msg,range1) ->
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
      let uu____3101 =
        let uu____3103 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3103  in
      if uu____3101
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
                | uu____3130 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3138 = FStar_ST.op_Bang recorded_hints  in
           match uu____3138 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3194 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3201 =
               let uu____3202 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3202  in
             store_hint uu____3201
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3209 -> ())
  
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
                     let uu____3320 = f q res  in
                     match uu____3320 with
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
            (let uu____3359 =
               let uu____3366 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3379,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3405,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3428 = FStar_Ident.text_of_lid q  in
                     (uu____3428, n1)
                  in
               match uu____3366 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3446 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3448 =
                       let uu____3450 = FStar_Options.z3_rlimit ()  in
                       uu____3450 * (Prims.parse_int "544656")  in
                     uu____3446 * uu____3448  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3457 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3458 = FStar_Options.initial_fuel ()  in
                     let uu____3460 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3457;
                       query_fuel = uu____3458;
                       query_ifuel = uu____3460;
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
                              { FStar_Util.hint_name = uu____3469;
                                FStar_Util.hint_index = uu____3470;
                                FStar_Util.fuel = uu____3471;
                                FStar_Util.ifuel = uu____3472;
                                FStar_Util.unsat_core = uu____3473;
                                FStar_Util.query_elapsed_time = uu____3474;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3359 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3502;
                         FStar_Util.hint_index = uu____3503;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3507;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___426_3524 = default_settings  in
                         {
                           query_env = (uu___426_3524.query_env);
                           query_decl = (uu___426_3524.query_decl);
                           query_name = (uu___426_3524.query_name);
                           query_index = (uu___426_3524.query_index);
                           query_range = (uu___426_3524.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___426_3524.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___426_3524.query_errors);
                           query_all_labels =
                             (uu___426_3524.query_all_labels);
                           query_suffix = (uu___426_3524.query_suffix);
                           query_hash = (uu___426_3524.query_hash)
                         })]
                   | uu____3528 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3534 =
                     let uu____3536 = FStar_Options.max_ifuel ()  in
                     let uu____3538 = FStar_Options.initial_ifuel ()  in
                     uu____3536 > uu____3538  in
                   if uu____3534
                   then
                     let uu____3543 =
                       let uu___431_3544 = default_settings  in
                       let uu____3545 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___431_3544.query_env);
                         query_decl = (uu___431_3544.query_decl);
                         query_name = (uu___431_3544.query_name);
                         query_index = (uu___431_3544.query_index);
                         query_range = (uu___431_3544.query_range);
                         query_fuel = (uu___431_3544.query_fuel);
                         query_ifuel = uu____3545;
                         query_rlimit = (uu___431_3544.query_rlimit);
                         query_hint = (uu___431_3544.query_hint);
                         query_errors = (uu___431_3544.query_errors);
                         query_all_labels = (uu___431_3544.query_all_labels);
                         query_suffix = (uu___431_3544.query_suffix);
                         query_hash = (uu___431_3544.query_hash)
                       }  in
                     [uu____3543]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3552 =
                     let uu____3554 =
                       let uu____3556 = FStar_Options.max_fuel ()  in
                       uu____3556 / (Prims.parse_int "2")  in
                     let uu____3559 = FStar_Options.initial_fuel ()  in
                     uu____3554 > uu____3559  in
                   if uu____3552
                   then
                     let uu____3564 =
                       let uu___435_3565 = default_settings  in
                       let uu____3566 =
                         let uu____3568 = FStar_Options.max_fuel ()  in
                         uu____3568 / (Prims.parse_int "2")  in
                       let uu____3571 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___435_3565.query_env);
                         query_decl = (uu___435_3565.query_decl);
                         query_name = (uu___435_3565.query_name);
                         query_index = (uu___435_3565.query_index);
                         query_range = (uu___435_3565.query_range);
                         query_fuel = uu____3566;
                         query_ifuel = uu____3571;
                         query_rlimit = (uu___435_3565.query_rlimit);
                         query_hint = (uu___435_3565.query_hint);
                         query_errors = (uu___435_3565.query_errors);
                         query_all_labels = (uu___435_3565.query_all_labels);
                         query_suffix = (uu___435_3565.query_suffix);
                         query_hash = (uu___435_3565.query_hash)
                       }  in
                     [uu____3564]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3578 =
                     (let uu____3584 = FStar_Options.max_fuel ()  in
                      let uu____3586 = FStar_Options.initial_fuel ()  in
                      uu____3584 > uu____3586) &&
                       (let uu____3590 = FStar_Options.max_ifuel ()  in
                        let uu____3592 = FStar_Options.initial_ifuel ()  in
                        uu____3590 >= uu____3592)
                      in
                   if uu____3578
                   then
                     let uu____3597 =
                       let uu___439_3598 = default_settings  in
                       let uu____3599 = FStar_Options.max_fuel ()  in
                       let uu____3601 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___439_3598.query_env);
                         query_decl = (uu___439_3598.query_decl);
                         query_name = (uu___439_3598.query_name);
                         query_index = (uu___439_3598.query_index);
                         query_range = (uu___439_3598.query_range);
                         query_fuel = uu____3599;
                         query_ifuel = uu____3601;
                         query_rlimit = (uu___439_3598.query_rlimit);
                         query_hint = (uu___439_3598.query_hint);
                         query_errors = (uu___439_3598.query_errors);
                         query_all_labels = (uu___439_3598.query_all_labels);
                         query_suffix = (uu___439_3598.query_suffix);
                         query_hash = (uu___439_3598.query_hash)
                       }  in
                     [uu____3597]
                   else []  in
                 let min_fuel1 =
                   let uu____3608 =
                     let uu____3610 = FStar_Options.min_fuel ()  in
                     let uu____3612 = FStar_Options.initial_fuel ()  in
                     uu____3610 < uu____3612  in
                   if uu____3608
                   then
                     let uu____3617 =
                       let uu___443_3618 = default_settings  in
                       let uu____3619 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___443_3618.query_env);
                         query_decl = (uu___443_3618.query_decl);
                         query_name = (uu___443_3618.query_name);
                         query_index = (uu___443_3618.query_index);
                         query_range = (uu___443_3618.query_range);
                         query_fuel = uu____3619;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___443_3618.query_rlimit);
                         query_hint = (uu___443_3618.query_hint);
                         query_errors = (uu___443_3618.query_errors);
                         query_all_labels = (uu___443_3618.query_all_labels);
                         query_suffix = (uu___443_3618.query_suffix);
                         query_hash = (uu___443_3618.query_hash)
                       }  in
                     [uu____3617]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3644 = FStar_Options.z3_refresh ()  in
                    if uu____3644
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3649 = with_fuel_and_diagnostics config1 []  in
                    let uu____3652 =
                      let uu____3655 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3655  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3649
                      uu____3652 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___456_3678 = default_settings  in
                        {
                          query_env = (uu___456_3678.query_env);
                          query_decl = (uu___456_3678.query_decl);
                          query_name = (uu___456_3678.query_name);
                          query_index = (uu___456_3678.query_index);
                          query_range = (uu___456_3678.query_range);
                          query_fuel = (uu___456_3678.query_fuel);
                          query_ifuel = (uu___456_3678.query_ifuel);
                          query_rlimit = (uu___456_3678.query_rlimit);
                          query_hint = (uu___456_3678.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___456_3678.query_all_labels);
                          query_suffix = (uu___456_3678.query_suffix);
                          query_hash = (uu___456_3678.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3679 =
                   let uu____3688 = FStar_Options.admit_smt_queries ()  in
                   let uu____3690 = FStar_Options.admit_except ()  in
                   (uu____3688, uu____3690)  in
                 (match uu____3679 with
                  | (true ,uu____3698) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3728 =
                              let uu____3730 =
                                let uu____3732 =
                                  let uu____3734 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____3734 ")"  in
                                Prims.op_Hat ", " uu____3732  in
                              Prims.op_Hat default_settings.query_name
                                uu____3730
                               in
                            Prims.op_Hat "(" uu____3728  in
                          full_query_id <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
  
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
    let uu____3967 = FStar_Options.z3_seed ()  in
    let uu____3969 = FStar_Options.z3_cliopt ()  in
    let uu____3973 = FStar_Options.smtencoding_valid_intro ()  in
    let uu____3975 = FStar_Options.smtencoding_valid_elim ()  in
    {
      seed = uu____3967;
      cliopt = uu____3969;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____3973;
      valid_elim = uu____3975
    }
  
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____3983 =
      let uu____3986 = get_cfg env  in
      FStar_Pervasives_Native.Some uu____3986  in
    FStar_ST.op_Colon_Equals _last_cfg uu____3983
  
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    let uu____4017 = FStar_ST.op_Bang _last_cfg  in
    match uu____4017 with
    | FStar_Pervasives_Native.None  -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____4047 = let uu____4049 = get_cfg env  in cfg = uu____4049
           in
        Prims.op_Negation uu____4047
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        let uu____4077 = FStar_Options.no_smt ()  in
        if uu____4077
        then
          let uu____4080 =
            let uu____4090 =
              let uu____4098 =
                let uu____4100 = FStar_Syntax_Print.term_to_string q  in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____4100
                 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____4098,
                (tcenv.FStar_TypeChecker_Env.range))
               in
            [uu____4090]  in
          FStar_TypeChecker_Err.add_errors tcenv uu____4080
        else
          ((let uu____4121 = should_refresh tcenv  in
            if uu____4121
            then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
            else ());
           (let uu____4128 =
              let uu____4130 =
                let uu____4132 = FStar_TypeChecker_Env.get_range tcenv  in
                FStar_All.pipe_left FStar_Range.string_of_range uu____4132
                 in
              FStar_Util.format1 "Starting query at %s" uu____4130  in
            FStar_SMTEncoding_Encode.push uu____4128);
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____4136 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____4136 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____4172 =
                  let uu____4173 =
                    let uu____4175 =
                      let uu____4177 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____4177
                       in
                    FStar_Util.format1 "Ending query at %s" uu____4175  in
                  FStar_SMTEncoding_Encode.pop uu____4173  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____4180);
                           FStar_SMTEncoding_Term.freevars = uu____4181;
                           FStar_SMTEncoding_Term.rng = uu____4182;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____4183;
                       FStar_SMTEncoding_Term.assumption_name = uu____4184;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____4185;_}
                     -> pop1 ()
                 | uu____4205 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____4206 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____4208 -> failwith "Impossible")))
  
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
           let uu____4222 =
             let uu____4229 = FStar_Options.peek ()  in (e, g, uu____4229)
              in
           [uu____4222]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____4245  -> ());
    FStar_TypeChecker_Env.push = (fun uu____4247  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____4250  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____4253  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____4272  -> fun uu____4273  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4288  -> fun uu____4289  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____4295 =
             let uu____4302 = FStar_Options.peek ()  in (e, g, uu____4302)
              in
           [uu____4295]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4318  -> fun uu____4319  -> fun uu____4320  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4327  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4329  -> ())
  } 
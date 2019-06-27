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
       let uu____2196 = FStar_Options.query_stats ()  in
       if uu____2196
       then
         let uu____2205 =
           let uu____2207 =
             let uu____2209 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map error_to_short_string)
                in
             FStar_All.pipe_right uu____2209 (FStar_String.concat ";\n\t")
              in
           FStar_All.pipe_right uu____2207 format_smt_error  in
         FStar_All.pipe_right uu____2205 (fun _2235  -> FStar_Util.Inr _2235)
       else
         (let uu____2238 =
            FStar_List.fold_left
              (fun uu____2263  ->
                 fun err  ->
                   match uu____2263 with
                   | (ic,cc,uc) ->
                       let err1 =
                         FStar_Util.substring_from err.error_reason
                           (FStar_String.length "unknown because ")
                          in
                       if
                         ((FStar_Util.starts_with err1 "canceled") ||
                            (FStar_Util.starts_with err1 "(resource"))
                           || (FStar_Util.starts_with err1 "timeout")
                       then (ic, (cc + (Prims.parse_int "1")), uc)
                       else
                         if FStar_Util.starts_with err1 "(incomplete"
                         then ((ic + (Prims.parse_int "1")), cc, uc)
                         else (ic, cc, (uc + (Prims.parse_int "1"))))
              ((Prims.parse_int "0"), (Prims.parse_int "0"),
                (Prims.parse_int "0")) settings.query_errors
             in
          match uu____2238 with
          | (incomplete_count,canceled_count,unknown_count) ->
              FStar_All.pipe_right
                (match (incomplete_count, canceled_count, unknown_count) with
                 | (uu____2368,_2373,_2374) when
                     ((_2373 = (Prims.parse_int "0")) &&
                        (_2374 = (Prims.parse_int "0")))
                       && (incomplete_count > (Prims.parse_int "0"))
                     ->
                     "The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
                 | (_2381,uu____2377,_2383) when
                     ((_2381 = (Prims.parse_int "0")) &&
                        (_2383 = (Prims.parse_int "0")))
                       && (canceled_count > (Prims.parse_int "0"))
                     ->
                     "The SMT query timed out, you might want to increase the rlimit"
                 | (uu____2386,uu____2387,uu____2388) ->
                     "Try with --query_stats to get more details")
                (fun _2398  -> FStar_Util.Inl _2398))
        in
     let uu____2399 = find_localized_errors settings.query_errors  in
     match uu____2399 with
     | FStar_Pervasives_Native.Some err ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           err.error_messages smt_error
     | FStar_Pervasives_Native.None  ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
              "Unknown assertion failed", (settings.query_range))] smt_error);
    (let uu____2419 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2422 = FStar_Options.n_cores ()  in
          uu____2422 = (Prims.parse_int "1"))
        in
     if uu____2419
     then
       let initial_fuel1 =
         let uu___262_2428 = settings  in
         let uu____2429 = FStar_Options.initial_fuel ()  in
         let uu____2431 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___262_2428.query_env);
           query_decl = (uu___262_2428.query_decl);
           query_name = (uu___262_2428.query_name);
           query_index = (uu___262_2428.query_index);
           query_range = (uu___262_2428.query_range);
           query_fuel = uu____2429;
           query_ifuel = uu____2431;
           query_rlimit = (uu___262_2428.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___262_2428.query_errors);
           query_all_labels = (uu___262_2428.query_all_labels);
           query_suffix = (uu___262_2428.query_suffix);
           query_hash = (uu___262_2428.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2454 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2454
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2483 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2483)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2548 =
          let r = FStar_Util.mk_ref []  in
          let uu____2559 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2659  ->
                 let uu____2660 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2660
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2559 with | (add1,get1) -> (add1, get1)  in
        let uu____2742 = accumulator ()  in
        match uu____2742 with
        | (add_module_name,get_module_names) ->
            let uu____2779 = accumulator ()  in
            (match uu____2779 with
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
                                  let uu____2902 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2902
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
                         | uu____2947 ->
                             let uu____2951 = FStar_Util.prefix components
                                in
                             (match uu____2951 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2978 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2978
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2985::[] -> ()
                                    | uu____2989 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____3006 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____3006])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____3033 =
                          let uu____3035 = get_module_names ()  in
                          FStar_All.pipe_right uu____3035
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____3033);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____3048 =
                          let uu____3050 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____3050
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____3048))))
         in
      let uu____3060 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____3060
      then
        let uu____3063 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____3063 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____3082 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____3096 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____3082 with
             | (tag,core) ->
                 let range =
                   let uu____3109 =
                     let uu____3111 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____3111 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____3109  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____3125 = FStar_Options.query_stats ()  in
                   if uu____3125
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
                     let uu____3159 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____3159 "}"
                   else ""  in
                 ((let uu____3168 =
                     let uu____3172 =
                       let uu____3176 =
                         let uu____3180 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3182 =
                           let uu____3186 =
                             let uu____3190 =
                               let uu____3194 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3196 =
                                 let uu____3200 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3202 =
                                   let uu____3206 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3208 =
                                     let uu____3212 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3212; stats]  in
                                   uu____3206 :: uu____3208  in
                                 uu____3200 :: uu____3202  in
                               uu____3194 :: uu____3196  in
                             used_hint_tag :: uu____3190  in
                           tag :: uu____3186  in
                         uu____3180 :: uu____3182  in
                       (settings.query_name) :: uu____3176  in
                     range :: uu____3172  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____3168);
                  (let uu____3227 = FStar_Options.print_z3_statistics ()  in
                   if uu____3227 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3253  ->
                          match uu____3253 with
                          | (uu____3261,msg,range1) ->
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
      let uu____3288 =
        let uu____3290 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3290  in
      if uu____3288
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
                | uu____3317 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3325 = FStar_ST.op_Bang recorded_hints  in
           match uu____3325 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3381 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3388 =
               let uu____3389 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3389  in
             store_hint uu____3388
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3396 -> ())
  
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
                     let uu____3507 = f q res  in
                     match uu____3507 with
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
            (let uu____3546 =
               let uu____3553 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3566,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3592,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3615 = FStar_Ident.text_of_lid q  in
                     (uu____3615, n1)
                  in
               match uu____3553 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3633 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3635 =
                       let uu____3637 = FStar_Options.z3_rlimit ()  in
                       uu____3637 * (Prims.parse_int "544656")  in
                     uu____3633 * uu____3635  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3644 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3645 = FStar_Options.initial_fuel ()  in
                     let uu____3647 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3644;
                       query_fuel = uu____3645;
                       query_ifuel = uu____3647;
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
                              { FStar_Util.hint_name = uu____3656;
                                FStar_Util.hint_index = uu____3657;
                                FStar_Util.fuel = uu____3658;
                                FStar_Util.ifuel = uu____3659;
                                FStar_Util.unsat_core = uu____3660;
                                FStar_Util.query_elapsed_time = uu____3661;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3546 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3689;
                         FStar_Util.hint_index = uu____3690;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3694;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___451_3711 = default_settings  in
                         {
                           query_env = (uu___451_3711.query_env);
                           query_decl = (uu___451_3711.query_decl);
                           query_name = (uu___451_3711.query_name);
                           query_index = (uu___451_3711.query_index);
                           query_range = (uu___451_3711.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___451_3711.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___451_3711.query_errors);
                           query_all_labels =
                             (uu___451_3711.query_all_labels);
                           query_suffix = (uu___451_3711.query_suffix);
                           query_hash = (uu___451_3711.query_hash)
                         })]
                   | uu____3715 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3721 =
                     let uu____3723 = FStar_Options.max_ifuel ()  in
                     let uu____3725 = FStar_Options.initial_ifuel ()  in
                     uu____3723 > uu____3725  in
                   if uu____3721
                   then
                     let uu____3730 =
                       let uu___456_3731 = default_settings  in
                       let uu____3732 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___456_3731.query_env);
                         query_decl = (uu___456_3731.query_decl);
                         query_name = (uu___456_3731.query_name);
                         query_index = (uu___456_3731.query_index);
                         query_range = (uu___456_3731.query_range);
                         query_fuel = (uu___456_3731.query_fuel);
                         query_ifuel = uu____3732;
                         query_rlimit = (uu___456_3731.query_rlimit);
                         query_hint = (uu___456_3731.query_hint);
                         query_errors = (uu___456_3731.query_errors);
                         query_all_labels = (uu___456_3731.query_all_labels);
                         query_suffix = (uu___456_3731.query_suffix);
                         query_hash = (uu___456_3731.query_hash)
                       }  in
                     [uu____3730]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3739 =
                     let uu____3741 =
                       let uu____3743 = FStar_Options.max_fuel ()  in
                       uu____3743 / (Prims.parse_int "2")  in
                     let uu____3746 = FStar_Options.initial_fuel ()  in
                     uu____3741 > uu____3746  in
                   if uu____3739
                   then
                     let uu____3751 =
                       let uu___460_3752 = default_settings  in
                       let uu____3753 =
                         let uu____3755 = FStar_Options.max_fuel ()  in
                         uu____3755 / (Prims.parse_int "2")  in
                       let uu____3758 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___460_3752.query_env);
                         query_decl = (uu___460_3752.query_decl);
                         query_name = (uu___460_3752.query_name);
                         query_index = (uu___460_3752.query_index);
                         query_range = (uu___460_3752.query_range);
                         query_fuel = uu____3753;
                         query_ifuel = uu____3758;
                         query_rlimit = (uu___460_3752.query_rlimit);
                         query_hint = (uu___460_3752.query_hint);
                         query_errors = (uu___460_3752.query_errors);
                         query_all_labels = (uu___460_3752.query_all_labels);
                         query_suffix = (uu___460_3752.query_suffix);
                         query_hash = (uu___460_3752.query_hash)
                       }  in
                     [uu____3751]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3765 =
                     (let uu____3771 = FStar_Options.max_fuel ()  in
                      let uu____3773 = FStar_Options.initial_fuel ()  in
                      uu____3771 > uu____3773) &&
                       (let uu____3777 = FStar_Options.max_ifuel ()  in
                        let uu____3779 = FStar_Options.initial_ifuel ()  in
                        uu____3777 >= uu____3779)
                      in
                   if uu____3765
                   then
                     let uu____3784 =
                       let uu___464_3785 = default_settings  in
                       let uu____3786 = FStar_Options.max_fuel ()  in
                       let uu____3788 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___464_3785.query_env);
                         query_decl = (uu___464_3785.query_decl);
                         query_name = (uu___464_3785.query_name);
                         query_index = (uu___464_3785.query_index);
                         query_range = (uu___464_3785.query_range);
                         query_fuel = uu____3786;
                         query_ifuel = uu____3788;
                         query_rlimit = (uu___464_3785.query_rlimit);
                         query_hint = (uu___464_3785.query_hint);
                         query_errors = (uu___464_3785.query_errors);
                         query_all_labels = (uu___464_3785.query_all_labels);
                         query_suffix = (uu___464_3785.query_suffix);
                         query_hash = (uu___464_3785.query_hash)
                       }  in
                     [uu____3784]
                   else []  in
                 let min_fuel1 =
                   let uu____3795 =
                     let uu____3797 = FStar_Options.min_fuel ()  in
                     let uu____3799 = FStar_Options.initial_fuel ()  in
                     uu____3797 < uu____3799  in
                   if uu____3795
                   then
                     let uu____3804 =
                       let uu___468_3805 = default_settings  in
                       let uu____3806 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___468_3805.query_env);
                         query_decl = (uu___468_3805.query_decl);
                         query_name = (uu___468_3805.query_name);
                         query_index = (uu___468_3805.query_index);
                         query_range = (uu___468_3805.query_range);
                         query_fuel = uu____3806;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___468_3805.query_rlimit);
                         query_hint = (uu___468_3805.query_hint);
                         query_errors = (uu___468_3805.query_errors);
                         query_all_labels = (uu___468_3805.query_all_labels);
                         query_suffix = (uu___468_3805.query_suffix);
                         query_hash = (uu___468_3805.query_hash)
                       }  in
                     [uu____3804]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3831 = FStar_Options.z3_refresh ()  in
                    if uu____3831
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3836 = with_fuel_and_diagnostics config1 []  in
                    let uu____3839 =
                      let uu____3842 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3842  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3836
                      uu____3839 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___481_3865 = default_settings  in
                        {
                          query_env = (uu___481_3865.query_env);
                          query_decl = (uu___481_3865.query_decl);
                          query_name = (uu___481_3865.query_name);
                          query_index = (uu___481_3865.query_index);
                          query_range = (uu___481_3865.query_range);
                          query_fuel = (uu___481_3865.query_fuel);
                          query_ifuel = (uu___481_3865.query_ifuel);
                          query_rlimit = (uu___481_3865.query_rlimit);
                          query_hint = (uu___481_3865.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___481_3865.query_all_labels);
                          query_suffix = (uu___481_3865.query_suffix);
                          query_hash = (uu___481_3865.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3866 =
                   let uu____3875 = FStar_Options.admit_smt_queries ()  in
                   let uu____3877 = FStar_Options.admit_except ()  in
                   (uu____3875, uu____3877)  in
                 (match uu____3866 with
                  | (true ,uu____3885) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3915 =
                              let uu____3917 =
                                let uu____3919 =
                                  let uu____3921 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____3921 ")"  in
                                Prims.op_Hat ", " uu____3919  in
                              Prims.op_Hat default_settings.query_name
                                uu____3917
                               in
                            Prims.op_Hat "(" uu____3915  in
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
    let uu____4154 = FStar_Options.z3_seed ()  in
    let uu____4156 = FStar_Options.z3_cliopt ()  in
    let uu____4160 = FStar_Options.smtencoding_valid_intro ()  in
    let uu____4162 = FStar_Options.smtencoding_valid_elim ()  in
    {
      seed = uu____4154;
      cliopt = uu____4156;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____4160;
      valid_elim = uu____4162
    }
  
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____4170 =
      let uu____4173 = get_cfg env  in
      FStar_Pervasives_Native.Some uu____4173  in
    FStar_ST.op_Colon_Equals _last_cfg uu____4170
  
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    let uu____4204 = FStar_ST.op_Bang _last_cfg  in
    match uu____4204 with
    | FStar_Pervasives_Native.None  -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____4234 = let uu____4236 = get_cfg env  in cfg = uu____4236
           in
        Prims.op_Negation uu____4234
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        let uu____4264 = FStar_Options.no_smt ()  in
        if uu____4264
        then
          let uu____4267 =
            let uu____4277 =
              let uu____4285 =
                let uu____4287 = FStar_Syntax_Print.term_to_string q  in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____4287
                 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____4285,
                (tcenv.FStar_TypeChecker_Env.range))
               in
            [uu____4277]  in
          FStar_TypeChecker_Err.add_errors tcenv uu____4267
        else
          ((let uu____4308 = should_refresh tcenv  in
            if uu____4308
            then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
            else ());
           (let uu____4315 =
              let uu____4317 =
                let uu____4319 = FStar_TypeChecker_Env.get_range tcenv  in
                FStar_All.pipe_left FStar_Range.string_of_range uu____4319
                 in
              FStar_Util.format1 "Starting query at %s" uu____4317  in
            FStar_SMTEncoding_Encode.push uu____4315);
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____4323 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____4323 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____4359 =
                  let uu____4360 =
                    let uu____4362 =
                      let uu____4364 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____4364
                       in
                    FStar_Util.format1 "Ending query at %s" uu____4362  in
                  FStar_SMTEncoding_Encode.pop uu____4360  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____4367);
                           FStar_SMTEncoding_Term.freevars = uu____4368;
                           FStar_SMTEncoding_Term.rng = uu____4369;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____4370;
                       FStar_SMTEncoding_Term.assumption_name = uu____4371;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____4372;_}
                     -> pop1 ()
                 | uu____4392 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____4393 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____4395 -> failwith "Impossible")))
  
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
           let uu____4409 =
             let uu____4416 = FStar_Options.peek ()  in (e, g, uu____4416)
              in
           [uu____4409]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____4432  -> ());
    FStar_TypeChecker_Env.push = (fun uu____4434  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____4437  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____4440  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____4459  -> fun uu____4460  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4475  -> fun uu____4476  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____4482 =
             let uu____4489 = FStar_Options.peek ()  in (e, g, uu____4489)
              in
           [uu____4482]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4505  -> fun uu____4506  -> fun uu____4507  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4514  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4516  -> ())
  } 
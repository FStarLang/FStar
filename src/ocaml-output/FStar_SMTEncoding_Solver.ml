open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14 * 'Auu____15)) FStar_Util.either ->
      ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___63_32  ->
    match uu___63_32 with
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
                  (fun uu___64_412  ->
                     match uu___64_412 with
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
        let keep_decl uu___65_442 =
          match uu___65_442 with
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
                      Prims.strcat "UNSAT CORE: " uu____614  in
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
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____1195 uu____1197
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
      let uu____1736 =
        let uu____1739 =
          let uu____1740 =
            let uu____1742 = FStar_Util.string_of_int n1  in
            let uu____1744 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1742 uu____1744
             in
          FStar_SMTEncoding_Term.Caption uu____1740  in
        let uu____1747 =
          let uu____1750 =
            let uu____1751 =
              let uu____1759 =
                let uu____1760 =
                  let uu____1765 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1770 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1765, uu____1770)  in
                FStar_SMTEncoding_Util.mkEq uu____1760  in
              (uu____1759, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1751  in
          let uu____1774 =
            let uu____1777 =
              let uu____1778 =
                let uu____1786 =
                  let uu____1787 =
                    let uu____1792 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1797 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1792, uu____1797)  in
                  FStar_SMTEncoding_Util.mkEq uu____1787  in
                (uu____1786, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1778  in
            [uu____1777; settings.query_decl]  in
          uu____1750 :: uu____1774  in
        uu____1739 :: uu____1747  in
      let uu____1801 =
        let uu____1804 =
          let uu____1807 =
            let uu____1810 =
              let uu____1811 =
                let uu____1818 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1818)  in
              FStar_SMTEncoding_Term.SetOption uu____1811  in
            [uu____1810;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1823 =
            let uu____1826 =
              let uu____1829 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1829
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1826 settings.query_suffix  in
          FStar_List.append uu____1807 uu____1823  in
        FStar_List.append label_assumptions uu____1804  in
      FStar_List.append uu____1736 uu____1801
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1863 = FStar_ST.op_Bang replaying_hints  in
      match uu____1863 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___66_1896  ->
               match uu___66_1896 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1904 -> FStar_Pervasives_Native.None)
      | uu____1907 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1925 -> FStar_Pervasives_Native.None
      | uu____1926 ->
          let uu____1927 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1927 with
           | (msg,error_labels) ->
               let err =
                 let uu____1940 =
                   FStar_List.map
                     (fun uu____1968  ->
                        match uu____1968 with
                        | (uu____1983,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1940
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2000 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____2000
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____2003 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____2023 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2023
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2074 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2074)
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
            match err.error_messages with | [] -> false | uu____2152 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2174 = find_localized_errors errs  in
    FStar_Option.isSome uu____2174
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____2184 = find_localized_errors settings.query_errors  in
     match uu____2184 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____2194 =
                    let uu____2196 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____2196  in
                  FStar_Errors.diag settings.query_range uu____2194));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____2201 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____2214 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____2214))
              in
           FStar_All.pipe_right uu____2201 (FStar_String.concat "; ")  in
         let uu____2222 =
           let uu____2232 =
             let uu____2240 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____2240,
               (settings.query_range))
              in
           [uu____2232]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____2222);
    (let uu____2258 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2261 = FStar_Options.n_cores ()  in
          uu____2261 = (Prims.parse_int "1"))
        in
     if uu____2258
     then
       let initial_fuel1 =
         let uu___67_2267 = settings  in
         let uu____2268 = FStar_Options.initial_fuel ()  in
         let uu____2270 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___67_2267.query_env);
           query_decl = (uu___67_2267.query_decl);
           query_name = (uu___67_2267.query_name);
           query_index = (uu___67_2267.query_index);
           query_range = (uu___67_2267.query_range);
           query_fuel = uu____2268;
           query_ifuel = uu____2270;
           query_rlimit = (uu___67_2267.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___67_2267.query_errors);
           query_all_labels = (uu___67_2267.query_all_labels);
           query_suffix = (uu___67_2267.query_suffix);
           query_hash = (uu___67_2267.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2293 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2293
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2344 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2344)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2431 =
          let r = FStar_Util.mk_ref []  in
          let uu____2442 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2586  ->
                 let uu____2587 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2587
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2442 with | (add1,get1) -> (add1, get1)  in
        let uu____2691 = accumulator ()  in
        match uu____2691 with
        | (add_module_name,get_module_names) ->
            let uu____2728 = accumulator ()  in
            (match uu____2728 with
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
                                  let uu____2851 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2851
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
                         | uu____2896 ->
                             let uu____2900 = FStar_Util.prefix components
                                in
                             (match uu____2900 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2927 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2927
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2934::[] -> ()
                                    | uu____2938 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2955 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2955])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2982 =
                          let uu____2984 = get_module_names ()  in
                          FStar_All.pipe_right uu____2984
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2982);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2997 =
                          let uu____2999 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2999
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2997))))
         in
      let uu____3009 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____3009
      then
        let uu____3012 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____3012 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.strcat "@" s  in
            let uu____3031 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____3045 ->
                  ((Prims.strcat "failed {reason-unknown="
                      (Prims.strcat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____3031 with
             | (tag,core) ->
                 let range =
                   let uu____3058 =
                     let uu____3060 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.strcat uu____3060 (Prims.strcat at_log_file ")")
                      in
                   Prims.strcat "(" uu____3058  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____3074 = FStar_Options.query_stats ()  in
                   if uu____3074
                   then
                     let f k v1 a =
                       Prims.strcat a
                         (Prims.strcat k
                            (Prims.strcat "=" (Prims.strcat v1 " ")))
                        in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={"
                        in
                     let uu____3108 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.strcat uu____3108 "}"
                   else ""  in
                 ((let uu____3117 =
                     let uu____3121 =
                       let uu____3125 =
                         let uu____3129 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3131 =
                           let uu____3135 =
                             let uu____3139 =
                               let uu____3143 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3145 =
                                 let uu____3149 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3151 =
                                   let uu____3155 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3157 =
                                     let uu____3161 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3161; stats]  in
                                   uu____3155 :: uu____3157  in
                                 uu____3149 :: uu____3151  in
                               uu____3143 :: uu____3145  in
                             used_hint_tag :: uu____3139  in
                           tag :: uu____3135  in
                         uu____3129 :: uu____3131  in
                       (settings.query_name) :: uu____3125  in
                     range :: uu____3121  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____3117);
                  (let uu____3176 = FStar_Options.print_z3_statistics ()  in
                   if uu____3176 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3202  ->
                          match uu____3202 with
                          | (uu____3210,msg,range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else ""  in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.strcat tag1 msg))))))
      else ()
  
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____3237 =
        let uu____3239 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3239  in
      if uu____3237
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
                | uu____3266 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3274 = FStar_ST.op_Bang recorded_hints  in
           match uu____3274 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3330 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3337 =
               let uu____3338 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3338  in
             store_hint uu____3337
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3345 -> ())
  
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
                     let uu____3456 = f q res  in
                     match uu____3456 with
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
            (let uu____3495 =
               let uu____3502 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3515,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3541,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3564 = FStar_Ident.text_of_lid q  in
                     (uu____3564, n1)
                  in
               match uu____3502 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3582 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3584 =
                       let uu____3586 = FStar_Options.z3_rlimit ()  in
                       uu____3586 * (Prims.parse_int "544656")  in
                     uu____3582 * uu____3584  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3593 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3594 = FStar_Options.initial_fuel ()  in
                     let uu____3596 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3593;
                       query_fuel = uu____3594;
                       query_ifuel = uu____3596;
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
                              { FStar_Util.hint_name = uu____3605;
                                FStar_Util.hint_index = uu____3606;
                                FStar_Util.fuel = uu____3607;
                                FStar_Util.ifuel = uu____3608;
                                FStar_Util.unsat_core = uu____3609;
                                FStar_Util.query_elapsed_time = uu____3610;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3495 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3638;
                         FStar_Util.hint_index = uu____3639;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3643;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___68_3660 = default_settings  in
                         {
                           query_env = (uu___68_3660.query_env);
                           query_decl = (uu___68_3660.query_decl);
                           query_name = (uu___68_3660.query_name);
                           query_index = (uu___68_3660.query_index);
                           query_range = (uu___68_3660.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___68_3660.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___68_3660.query_errors);
                           query_all_labels = (uu___68_3660.query_all_labels);
                           query_suffix = (uu___68_3660.query_suffix);
                           query_hash = (uu___68_3660.query_hash)
                         })]
                   | uu____3664 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3670 =
                     let uu____3672 = FStar_Options.max_ifuel ()  in
                     let uu____3674 = FStar_Options.initial_ifuel ()  in
                     uu____3672 > uu____3674  in
                   if uu____3670
                   then
                     let uu____3679 =
                       let uu___69_3680 = default_settings  in
                       let uu____3681 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___69_3680.query_env);
                         query_decl = (uu___69_3680.query_decl);
                         query_name = (uu___69_3680.query_name);
                         query_index = (uu___69_3680.query_index);
                         query_range = (uu___69_3680.query_range);
                         query_fuel = (uu___69_3680.query_fuel);
                         query_ifuel = uu____3681;
                         query_rlimit = (uu___69_3680.query_rlimit);
                         query_hint = (uu___69_3680.query_hint);
                         query_errors = (uu___69_3680.query_errors);
                         query_all_labels = (uu___69_3680.query_all_labels);
                         query_suffix = (uu___69_3680.query_suffix);
                         query_hash = (uu___69_3680.query_hash)
                       }  in
                     [uu____3679]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3688 =
                     let uu____3690 =
                       let uu____3692 = FStar_Options.max_fuel ()  in
                       uu____3692 / (Prims.parse_int "2")  in
                     let uu____3695 = FStar_Options.initial_fuel ()  in
                     uu____3690 > uu____3695  in
                   if uu____3688
                   then
                     let uu____3700 =
                       let uu___70_3701 = default_settings  in
                       let uu____3702 =
                         let uu____3704 = FStar_Options.max_fuel ()  in
                         uu____3704 / (Prims.parse_int "2")  in
                       let uu____3707 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___70_3701.query_env);
                         query_decl = (uu___70_3701.query_decl);
                         query_name = (uu___70_3701.query_name);
                         query_index = (uu___70_3701.query_index);
                         query_range = (uu___70_3701.query_range);
                         query_fuel = uu____3702;
                         query_ifuel = uu____3707;
                         query_rlimit = (uu___70_3701.query_rlimit);
                         query_hint = (uu___70_3701.query_hint);
                         query_errors = (uu___70_3701.query_errors);
                         query_all_labels = (uu___70_3701.query_all_labels);
                         query_suffix = (uu___70_3701.query_suffix);
                         query_hash = (uu___70_3701.query_hash)
                       }  in
                     [uu____3700]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3714 =
                     (let uu____3720 = FStar_Options.max_fuel ()  in
                      let uu____3722 = FStar_Options.initial_fuel ()  in
                      uu____3720 > uu____3722) &&
                       (let uu____3726 = FStar_Options.max_ifuel ()  in
                        let uu____3728 = FStar_Options.initial_ifuel ()  in
                        uu____3726 >= uu____3728)
                      in
                   if uu____3714
                   then
                     let uu____3733 =
                       let uu___71_3734 = default_settings  in
                       let uu____3735 = FStar_Options.max_fuel ()  in
                       let uu____3737 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___71_3734.query_env);
                         query_decl = (uu___71_3734.query_decl);
                         query_name = (uu___71_3734.query_name);
                         query_index = (uu___71_3734.query_index);
                         query_range = (uu___71_3734.query_range);
                         query_fuel = uu____3735;
                         query_ifuel = uu____3737;
                         query_rlimit = (uu___71_3734.query_rlimit);
                         query_hint = (uu___71_3734.query_hint);
                         query_errors = (uu___71_3734.query_errors);
                         query_all_labels = (uu___71_3734.query_all_labels);
                         query_suffix = (uu___71_3734.query_suffix);
                         query_hash = (uu___71_3734.query_hash)
                       }  in
                     [uu____3733]
                   else []  in
                 let min_fuel1 =
                   let uu____3744 =
                     let uu____3746 = FStar_Options.min_fuel ()  in
                     let uu____3748 = FStar_Options.initial_fuel ()  in
                     uu____3746 < uu____3748  in
                   if uu____3744
                   then
                     let uu____3753 =
                       let uu___72_3754 = default_settings  in
                       let uu____3755 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___72_3754.query_env);
                         query_decl = (uu___72_3754.query_decl);
                         query_name = (uu___72_3754.query_name);
                         query_index = (uu___72_3754.query_index);
                         query_range = (uu___72_3754.query_range);
                         query_fuel = uu____3755;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___72_3754.query_rlimit);
                         query_hint = (uu___72_3754.query_hint);
                         query_errors = (uu___72_3754.query_errors);
                         query_all_labels = (uu___72_3754.query_all_labels);
                         query_suffix = (uu___72_3754.query_suffix);
                         query_hash = (uu___72_3754.query_hash)
                       }  in
                     [uu____3753]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3780 = FStar_Options.z3_refresh ()  in
                    if uu____3780
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3785 = with_fuel_and_diagnostics config1 []  in
                    let uu____3788 =
                      let uu____3791 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3791  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3785
                      uu____3788 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___73_3814 = default_settings  in
                        {
                          query_env = (uu___73_3814.query_env);
                          query_decl = (uu___73_3814.query_decl);
                          query_name = (uu___73_3814.query_name);
                          query_index = (uu___73_3814.query_index);
                          query_range = (uu___73_3814.query_range);
                          query_fuel = (uu___73_3814.query_fuel);
                          query_ifuel = (uu___73_3814.query_ifuel);
                          query_rlimit = (uu___73_3814.query_rlimit);
                          query_hint = (uu___73_3814.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___73_3814.query_all_labels);
                          query_suffix = (uu___73_3814.query_suffix);
                          query_hash = (uu___73_3814.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3815 =
                   let uu____3824 = FStar_Options.admit_smt_queries ()  in
                   let uu____3826 = FStar_Options.admit_except ()  in
                   (uu____3824, uu____3826)  in
                 (match uu____3815 with
                  | (true ,uu____3834) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3864 =
                              let uu____3866 =
                                let uu____3868 =
                                  let uu____3870 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____3870 ")"  in
                                Prims.strcat ", " uu____3868  in
                              Prims.strcat default_settings.query_name
                                uu____3866
                               in
                            Prims.strcat "(" uu____3864  in
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
        (let uu____3910 =
           let uu____3912 =
             let uu____3914 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3914  in
           FStar_Util.format1 "Starting query at %s" uu____3912  in
         FStar_SMTEncoding_Encode.push uu____3910);
        (let uu____3917 = FStar_Options.no_smt ()  in
         if uu____3917
         then
           let uu____3920 =
             let uu____3930 =
               let uu____3938 =
                 let uu____3940 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3940
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3938,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3930]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3920
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3961 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3961 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3997 =
                  let uu____3998 =
                    let uu____4000 =
                      let uu____4002 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____4002
                       in
                    FStar_Util.format1 "Ending query at %s" uu____4000  in
                  FStar_SMTEncoding_Encode.pop uu____3998  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____4005);
                           FStar_SMTEncoding_Term.freevars = uu____4006;
                           FStar_SMTEncoding_Term.rng = uu____4007;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____4008;
                       FStar_SMTEncoding_Term.assumption_name = uu____4009;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____4010;_}
                     -> pop1 ()
                 | uu____4030 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____4031 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____4033 -> failwith "Impossible")))
  
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
           let uu____4041 =
             let uu____4048 = FStar_Options.peek ()  in (e, g, uu____4048)
              in
           [uu____4041]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____4064  -> ());
    FStar_TypeChecker_Env.push = (fun uu____4066  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____4069  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____4072  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____4091  -> fun uu____4092  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4107  -> fun uu____4108  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____4114 =
             let uu____4121 = FStar_Options.peek ()  in (e, g, uu____4121)
              in
           [uu____4114]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4137  -> fun uu____4138  -> fun uu____4139  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4146  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4148  -> ())
  } 
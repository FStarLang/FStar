open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14 * 'Auu____15)) FStar_Util.either ->
      ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___374_32  ->
    match uu___374_32 with
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
        | FStar_SMTEncoding_Term.Name lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____389 ->
            failwith
              "Solver.fs::filter_using_facts_from expected only Name fact ids"
         in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____412 ->
            (let uu____417 =
               FStar_All.pipe_right
                 a.FStar_SMTEncoding_Term.assumption_fact_ids
                 (FStar_List.filter
                    (fun uu___375_426  ->
                       match uu___375_426 with
                       | FStar_SMTEncoding_Term.Name uu____428 -> true
                       | uu____430 -> false))
                in
             FStar_All.pipe_right uu____417
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____436 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____436)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___376_460 =
          match uu___376_460 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____475 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____485 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____508 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____508
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____526 ->
                   let uu____527 = keep_decl d  in
                   if uu____527 then d :: out else out) [] theory_rev
         in
      pruned_theory
  
let rec (filter_assertions_with_stats :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decls_t * Prims.bool * Prims.int * Prims.int))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____575 = filter_using_facts_from e theory  in
            (uu____575, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let uu____589 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____617  ->
                     match uu____617 with
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
                              let uu____710 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____710
                                (fun uu____768  ->
                                   match uu____768 with
                                   | (decls1,uu____793,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____813 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____589 with
             | (theory',n_retained,n_pruned) ->
                 let uu____846 =
                   let uu____847 =
                     let uu____850 =
                       let uu____851 =
                         let uu____853 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____853  in
                       FStar_SMTEncoding_Term.Caption uu____851  in
                     [uu____850]  in
                   FStar_List.append theory' uu____847  in
                 (uu____846, true, n_retained, n_pruned))
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decls_t * Prims.bool))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        let uu____886 = filter_assertions_with_stats e core theory  in
        match uu____886 with
        | (theory1,b,uu____905,uu____906) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____932 = filter_using_facts_from e x  in (uu____932, false)
  
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
    let uu____1162 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1164 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____1162 uu____1164
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
      let uu____1703 =
        let uu____1706 =
          let uu____1707 =
            let uu____1709 = FStar_Util.string_of_int n1  in
            let uu____1711 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1709 uu____1711
             in
          FStar_SMTEncoding_Term.Caption uu____1707  in
        let uu____1714 =
          let uu____1717 =
            let uu____1718 =
              let uu____1726 =
                let uu____1727 =
                  let uu____1732 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1737 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1732, uu____1737)  in
                FStar_SMTEncoding_Util.mkEq uu____1727  in
              (uu____1726, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1718  in
          let uu____1741 =
            let uu____1744 =
              let uu____1745 =
                let uu____1753 =
                  let uu____1754 =
                    let uu____1759 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1764 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1759, uu____1764)  in
                  FStar_SMTEncoding_Util.mkEq uu____1754  in
                (uu____1753, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1745  in
            [uu____1744; settings.query_decl]  in
          uu____1717 :: uu____1741  in
        uu____1706 :: uu____1714  in
      let uu____1768 =
        let uu____1771 =
          let uu____1774 =
            let uu____1777 =
              let uu____1778 =
                let uu____1785 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1785)  in
              FStar_SMTEncoding_Term.SetOption uu____1778  in
            [uu____1777;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1790 =
            let uu____1793 =
              let uu____1796 = FStar_Options.record_hints ()  in
              if uu____1796
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1803 =
              let uu____1806 =
                let uu____1809 = FStar_Options.print_z3_statistics ()  in
                if uu____1809
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1806 settings.query_suffix  in
            FStar_List.append uu____1793 uu____1803  in
          FStar_List.append uu____1774 uu____1790  in
        FStar_List.append label_assumptions uu____1771  in
      FStar_List.append uu____1703 uu____1768
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1843 = FStar_ST.op_Bang replaying_hints  in
      match uu____1843 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___377_1876  ->
               match uu___377_1876 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1884 -> FStar_Pervasives_Native.None)
      | uu____1887 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1905 -> FStar_Pervasives_Native.None
      | uu____1906 ->
          let uu____1907 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1907 with
           | (msg,error_labels) ->
               let err =
                 let uu____1920 =
                   FStar_List.map
                     (fun uu____1948  ->
                        match uu____1948 with
                        | (uu____1963,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1920
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1980 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1980
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1983 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____2003 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2003
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____2053 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2053)
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
            match err.error_messages with | [] -> false | uu____2131 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2153 = find_localized_errors errs  in
    FStar_Option.isSome uu____2153
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____2163 = find_localized_errors settings.query_errors  in
     match uu____2163 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____2173 =
                    let uu____2175 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____2175  in
                  FStar_Errors.diag settings.query_range uu____2173));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____2180 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____2193 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____2193))
              in
           FStar_All.pipe_right uu____2180 (FStar_String.concat "; ")  in
         let uu____2201 =
           let uu____2211 =
             let uu____2219 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____2219,
               (settings.query_range))
              in
           [uu____2211]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____2201);
    (let uu____2237 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2240 = FStar_Options.n_cores ()  in
          uu____2240 = (Prims.parse_int "1"))
        in
     if uu____2237
     then
       let initial_fuel1 =
         let uu___378_2246 = settings  in
         let uu____2247 = FStar_Options.initial_fuel ()  in
         let uu____2249 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___378_2246.query_env);
           query_decl = (uu___378_2246.query_decl);
           query_name = (uu___378_2246.query_name);
           query_index = (uu___378_2246.query_index);
           query_range = (uu___378_2246.query_range);
           query_fuel = uu____2247;
           query_ifuel = uu____2249;
           query_rlimit = (uu___378_2246.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___378_2246.query_errors);
           query_all_labels = (uu___378_2246.query_all_labels);
           query_suffix = (uu___378_2246.query_suffix);
           query_hash = (uu___378_2246.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2272 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2272
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
         (let uu____2322 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2322)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2384 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____2384
      then
        let uu____2387 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2387 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____2400 -> "succeeded"
              | uu____2402 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____2407 =
                let uu____2409 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____2411 =
                  let uu____2413 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____2413 ")"  in
                Prims.strcat uu____2409 uu____2411  in
              Prims.strcat "(" uu____2407  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____2427 = FStar_Options.print_z3_statistics ()  in
              if uu____2427
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
                let uu____2461 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____2461 "}"
              else ""  in
            ((let uu____2470 =
                let uu____2474 =
                  let uu____2478 =
                    let uu____2482 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____2484 =
                      let uu____2488 =
                        let uu____2492 =
                          let uu____2496 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____2498 =
                            let uu____2502 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____2504 =
                              let uu____2508 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____2510 =
                                let uu____2514 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____2514; stats]  in
                              uu____2508 :: uu____2510  in
                            uu____2502 :: uu____2504  in
                          uu____2496 :: uu____2498  in
                        used_hint_tag :: uu____2492  in
                      tag :: uu____2488  in
                    uu____2482 :: uu____2484  in
                  (settings.query_name) :: uu____2478  in
                range :: uu____2474  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____2470);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____2549  ->
                     match uu____2549 with
                     | (uu____2557,msg,range1) ->
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
      let uu____2584 =
        let uu____2586 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____2586  in
      if uu____2584
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
                | uu____2613 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____2621 = FStar_ST.op_Bang recorded_hints  in
           match uu____2621 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2677 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2684 =
               let uu____2685 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2685  in
             store_hint uu____2684
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2692 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2709 =
         (used_hint settings) &&
           (let uu____2712 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2712)
          in
       if uu____2709 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2812 = f q res  in
                     match uu____2812 with
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
            (let uu____2851 =
               let uu____2858 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2871,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2897,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2920 = FStar_Ident.text_of_lid q  in
                     (uu____2920, n1)
                  in
               match uu____2858 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2938 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2940 =
                       let uu____2942 = FStar_Options.z3_rlimit ()  in
                       uu____2942 * (Prims.parse_int "544656")  in
                     uu____2938 * uu____2940  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2949 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2950 = FStar_Options.initial_fuel ()  in
                     let uu____2952 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2949;
                       query_fuel = uu____2950;
                       query_ifuel = uu____2952;
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
                              { FStar_Util.hint_name = uu____2961;
                                FStar_Util.hint_index = uu____2962;
                                FStar_Util.fuel = uu____2963;
                                FStar_Util.ifuel = uu____2964;
                                FStar_Util.unsat_core = uu____2965;
                                FStar_Util.query_elapsed_time = uu____2966;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2851 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2994;
                         FStar_Util.hint_index = uu____2995;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2999;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___379_3016 = default_settings  in
                         {
                           query_env = (uu___379_3016.query_env);
                           query_decl = (uu___379_3016.query_decl);
                           query_name = (uu___379_3016.query_name);
                           query_index = (uu___379_3016.query_index);
                           query_range = (uu___379_3016.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___379_3016.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___379_3016.query_errors);
                           query_all_labels =
                             (uu___379_3016.query_all_labels);
                           query_suffix = (uu___379_3016.query_suffix);
                           query_hash = (uu___379_3016.query_hash)
                         })]
                   | uu____3020 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3026 =
                     let uu____3028 = FStar_Options.max_ifuel ()  in
                     let uu____3030 = FStar_Options.initial_ifuel ()  in
                     uu____3028 > uu____3030  in
                   if uu____3026
                   then
                     let uu____3035 =
                       let uu___380_3036 = default_settings  in
                       let uu____3037 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___380_3036.query_env);
                         query_decl = (uu___380_3036.query_decl);
                         query_name = (uu___380_3036.query_name);
                         query_index = (uu___380_3036.query_index);
                         query_range = (uu___380_3036.query_range);
                         query_fuel = (uu___380_3036.query_fuel);
                         query_ifuel = uu____3037;
                         query_rlimit = (uu___380_3036.query_rlimit);
                         query_hint = (uu___380_3036.query_hint);
                         query_errors = (uu___380_3036.query_errors);
                         query_all_labels = (uu___380_3036.query_all_labels);
                         query_suffix = (uu___380_3036.query_suffix);
                         query_hash = (uu___380_3036.query_hash)
                       }  in
                     [uu____3035]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3044 =
                     let uu____3046 =
                       let uu____3048 = FStar_Options.max_fuel ()  in
                       uu____3048 / (Prims.parse_int "2")  in
                     let uu____3051 = FStar_Options.initial_fuel ()  in
                     uu____3046 > uu____3051  in
                   if uu____3044
                   then
                     let uu____3056 =
                       let uu___381_3057 = default_settings  in
                       let uu____3058 =
                         let uu____3060 = FStar_Options.max_fuel ()  in
                         uu____3060 / (Prims.parse_int "2")  in
                       let uu____3063 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___381_3057.query_env);
                         query_decl = (uu___381_3057.query_decl);
                         query_name = (uu___381_3057.query_name);
                         query_index = (uu___381_3057.query_index);
                         query_range = (uu___381_3057.query_range);
                         query_fuel = uu____3058;
                         query_ifuel = uu____3063;
                         query_rlimit = (uu___381_3057.query_rlimit);
                         query_hint = (uu___381_3057.query_hint);
                         query_errors = (uu___381_3057.query_errors);
                         query_all_labels = (uu___381_3057.query_all_labels);
                         query_suffix = (uu___381_3057.query_suffix);
                         query_hash = (uu___381_3057.query_hash)
                       }  in
                     [uu____3056]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3070 =
                     (let uu____3076 = FStar_Options.max_fuel ()  in
                      let uu____3078 = FStar_Options.initial_fuel ()  in
                      uu____3076 > uu____3078) &&
                       (let uu____3082 = FStar_Options.max_ifuel ()  in
                        let uu____3084 = FStar_Options.initial_ifuel ()  in
                        uu____3082 >= uu____3084)
                      in
                   if uu____3070
                   then
                     let uu____3089 =
                       let uu___382_3090 = default_settings  in
                       let uu____3091 = FStar_Options.max_fuel ()  in
                       let uu____3093 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___382_3090.query_env);
                         query_decl = (uu___382_3090.query_decl);
                         query_name = (uu___382_3090.query_name);
                         query_index = (uu___382_3090.query_index);
                         query_range = (uu___382_3090.query_range);
                         query_fuel = uu____3091;
                         query_ifuel = uu____3093;
                         query_rlimit = (uu___382_3090.query_rlimit);
                         query_hint = (uu___382_3090.query_hint);
                         query_errors = (uu___382_3090.query_errors);
                         query_all_labels = (uu___382_3090.query_all_labels);
                         query_suffix = (uu___382_3090.query_suffix);
                         query_hash = (uu___382_3090.query_hash)
                       }  in
                     [uu____3089]
                   else []  in
                 let min_fuel1 =
                   let uu____3100 =
                     let uu____3102 = FStar_Options.min_fuel ()  in
                     let uu____3104 = FStar_Options.initial_fuel ()  in
                     uu____3102 < uu____3104  in
                   if uu____3100
                   then
                     let uu____3109 =
                       let uu___383_3110 = default_settings  in
                       let uu____3111 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___383_3110.query_env);
                         query_decl = (uu___383_3110.query_decl);
                         query_name = (uu___383_3110.query_name);
                         query_index = (uu___383_3110.query_index);
                         query_range = (uu___383_3110.query_range);
                         query_fuel = uu____3111;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___383_3110.query_rlimit);
                         query_hint = (uu___383_3110.query_hint);
                         query_errors = (uu___383_3110.query_errors);
                         query_all_labels = (uu___383_3110.query_all_labels);
                         query_suffix = (uu___383_3110.query_suffix);
                         query_hash = (uu___383_3110.query_hash)
                       }  in
                     [uu____3109]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3136 =
                      (used_hint config1) || (FStar_Options.z3_refresh ())
                       in
                    if uu____3136
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3141 = with_fuel_and_diagnostics config1 []  in
                    let uu____3144 =
                      let uu____3147 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3147  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3141
                      uu____3144 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___384_3170 = default_settings  in
                        {
                          query_env = (uu___384_3170.query_env);
                          query_decl = (uu___384_3170.query_decl);
                          query_name = (uu___384_3170.query_name);
                          query_index = (uu___384_3170.query_index);
                          query_range = (uu___384_3170.query_range);
                          query_fuel = (uu___384_3170.query_fuel);
                          query_ifuel = (uu___384_3170.query_ifuel);
                          query_rlimit = (uu___384_3170.query_rlimit);
                          query_hint = (uu___384_3170.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___384_3170.query_all_labels);
                          query_suffix = (uu___384_3170.query_suffix);
                          query_hash = (uu___384_3170.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3171 =
                   let uu____3180 = FStar_Options.admit_smt_queries ()  in
                   let uu____3182 = FStar_Options.admit_except ()  in
                   (uu____3180, uu____3182)  in
                 (match uu____3171 with
                  | (true ,uu____3190) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3220 =
                              let uu____3222 =
                                let uu____3224 =
                                  let uu____3226 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____3226 ")"  in
                                Prims.strcat ", " uu____3224  in
                              Prims.strcat default_settings.query_name
                                uu____3222
                               in
                            Prims.strcat "(" uu____3220  in
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
        (let uu____3266 =
           let uu____3268 =
             let uu____3270 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3270  in
           FStar_Util.format1 "Starting query at %s" uu____3268  in
         FStar_SMTEncoding_Encode.push uu____3266);
        (let uu____3273 = FStar_Options.no_smt ()  in
         if uu____3273
         then
           let uu____3276 =
             let uu____3286 =
               let uu____3294 =
                 let uu____3296 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3296
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3294,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3286]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3276
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3317 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3317 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3353 =
                  let uu____3354 =
                    let uu____3356 =
                      let uu____3358 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3358
                       in
                    FStar_Util.format1 "Ending query at %s" uu____3356  in
                  FStar_SMTEncoding_Encode.pop uu____3354  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____3361);
                           FStar_SMTEncoding_Term.freevars = uu____3362;
                           FStar_SMTEncoding_Term.rng = uu____3363;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3364;
                       FStar_SMTEncoding_Term.assumption_name = uu____3365;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3366;_}
                     -> pop1 ()
                 | uu____3383 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3384 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3386 -> failwith "Impossible")))
  
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
           let uu____3394 =
             let uu____3401 = FStar_Options.peek ()  in (e, g, uu____3401)
              in
           [uu____3394]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3417  -> ());
    FStar_TypeChecker_Env.push = (fun uu____3419  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3422  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3425  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____3444  -> fun uu____3445  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____3460  -> fun uu____3461  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3464  -> fun uu____3465  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3471 =
             let uu____3478 = FStar_Options.peek ()  in (e, g, uu____3478)
              in
           [uu____3471]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3494  -> fun uu____3495  -> fun uu____3496  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____3503  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3505  -> ())
  } 
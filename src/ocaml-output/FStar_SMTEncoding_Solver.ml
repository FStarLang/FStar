open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14 * 'Auu____15)) FStar_Util.either ->
      ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___377_32  ->
    match uu___377_32 with
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
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____400 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___378_408  ->
                     match uu___378_408 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____411 -> false)))
              ||
              (let uu____414 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____414)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___379_438 =
          match uu___379_438 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____453 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____463 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____486 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____486
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____504 ->
                   let uu____505 = keep_decl d  in
                   if uu____505 then d :: out else out) [] theory_rev
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
            let uu____553 = filter_using_facts_from e theory  in
            (uu____553, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____570 =
              let uu____581 =
                let uu____592 =
                  let uu____595 =
                    let uu____596 =
                      let uu____598 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.strcat "UNSAT CORE: " uu____598  in
                    FStar_SMTEncoding_Term.Caption uu____596  in
                  [uu____595]  in
                (uu____592, (Prims.parse_int "0"), (Prims.parse_int "0"))  in
              FStar_List.fold_left
                (fun uu____628  ->
                   fun d  ->
                     match uu____628 with
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
                              let uu____722 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____722
                                (fun uu____780  ->
                                   match uu____780 with
                                   | (decls1,uu____805,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____825 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____581 theory_rev
               in
            (match uu____570 with
             | (theory',n_retained,n_pruned) ->
                 (theory', true, n_retained, n_pruned))
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decls_t * Prims.bool))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        let uu____877 = filter_assertions_with_stats e core theory  in
        match uu____877 with
        | (theory1,b,uu____896,uu____897) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____923 = filter_using_facts_from e x  in (uu____923, false)
  
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
    let uu____1153 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1155 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____1153 uu____1155
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
      let uu____1694 =
        let uu____1697 =
          let uu____1698 =
            let uu____1700 = FStar_Util.string_of_int n1  in
            let uu____1702 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1700 uu____1702
             in
          FStar_SMTEncoding_Term.Caption uu____1698  in
        let uu____1705 =
          let uu____1708 =
            let uu____1709 =
              let uu____1717 =
                let uu____1718 =
                  let uu____1723 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1728 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1723, uu____1728)  in
                FStar_SMTEncoding_Util.mkEq uu____1718  in
              (uu____1717, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1709  in
          let uu____1732 =
            let uu____1735 =
              let uu____1736 =
                let uu____1744 =
                  let uu____1745 =
                    let uu____1750 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1755 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1750, uu____1755)  in
                  FStar_SMTEncoding_Util.mkEq uu____1745  in
                (uu____1744, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1736  in
            [uu____1735; settings.query_decl]  in
          uu____1708 :: uu____1732  in
        uu____1697 :: uu____1705  in
      let uu____1759 =
        let uu____1762 =
          let uu____1765 =
            let uu____1768 =
              let uu____1769 =
                let uu____1776 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1776)  in
              FStar_SMTEncoding_Term.SetOption uu____1769  in
            [uu____1768;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1781 =
            let uu____1784 =
              let uu____1787 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1787
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1784 settings.query_suffix  in
          FStar_List.append uu____1765 uu____1781  in
        FStar_List.append label_assumptions uu____1762  in
      FStar_List.append uu____1694 uu____1759
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1821 = FStar_ST.op_Bang replaying_hints  in
      match uu____1821 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___380_1854  ->
               match uu___380_1854 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1862 -> FStar_Pervasives_Native.None)
      | uu____1865 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1883 -> FStar_Pervasives_Native.None
      | uu____1884 ->
          let uu____1885 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1885 with
           | (msg,error_labels) ->
               let err =
                 let uu____1898 =
                   FStar_List.map
                     (fun uu____1926  ->
                        match uu____1926 with
                        | (uu____1941,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1898
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1958 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1958
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1961 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1981 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1981
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2032 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2032)
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
            match err.error_messages with | [] -> false | uu____2110 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2132 = find_localized_errors errs  in
    FStar_Option.isSome uu____2132
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____2142 = find_localized_errors settings.query_errors  in
     match uu____2142 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____2152 =
                    let uu____2154 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____2154  in
                  FStar_Errors.diag settings.query_range uu____2152));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____2159 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____2172 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____2172))
              in
           FStar_All.pipe_right uu____2159 (FStar_String.concat "; ")  in
         let uu____2180 =
           let uu____2190 =
             let uu____2198 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____2198,
               (settings.query_range))
              in
           [uu____2190]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____2180);
    (let uu____2216 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2219 = FStar_Options.n_cores ()  in
          uu____2219 = (Prims.parse_int "1"))
        in
     if uu____2216
     then
       let initial_fuel1 =
         let uu___381_2225 = settings  in
         let uu____2226 = FStar_Options.initial_fuel ()  in
         let uu____2228 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___381_2225.query_env);
           query_decl = (uu___381_2225.query_decl);
           query_name = (uu___381_2225.query_name);
           query_index = (uu___381_2225.query_index);
           query_range = (uu___381_2225.query_range);
           query_fuel = uu____2226;
           query_ifuel = uu____2228;
           query_rlimit = (uu___381_2225.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___381_2225.query_errors);
           query_all_labels = (uu___381_2225.query_all_labels);
           query_suffix = (uu___381_2225.query_suffix);
           query_hash = (uu___381_2225.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2251 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2251
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2302 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2302)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2389 =
          let r = FStar_Util.mk_ref []  in
          let uu____2400 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2544  ->
                 let uu____2545 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2545
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2400 with | (add1,get1) -> (add1, get1)  in
        let uu____2649 = accumulator ()  in
        match uu____2649 with
        | (add_module_name,get_module_names) ->
            let uu____2686 = accumulator ()  in
            (match uu____2686 with
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
                                  let uu____2809 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2809
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
                         | uu____2854 ->
                             let uu____2858 = FStar_Util.prefix components
                                in
                             (match uu____2858 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2885 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2885
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2892::[] -> ()
                                    | uu____2896 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2913 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2913])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2940 =
                          let uu____2942 = get_module_names ()  in
                          FStar_All.pipe_right uu____2942
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2940);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2955 =
                          let uu____2957 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2957
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2955))))
         in
      let uu____2967 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____2967
      then
        let uu____2970 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2970 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.strcat "@" s  in
            let uu____2989 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____3003 ->
                  ((Prims.strcat "failed {reason-unknown="
                      (Prims.strcat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____2989 with
             | (tag,core) ->
                 let range =
                   let uu____3016 =
                     let uu____3018 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.strcat uu____3018 (Prims.strcat at_log_file ")")
                      in
                   Prims.strcat "(" uu____3016  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____3032 = FStar_Options.query_stats ()  in
                   if uu____3032
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
                     let uu____3066 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.strcat uu____3066 "}"
                   else ""  in
                 ((let uu____3075 =
                     let uu____3079 =
                       let uu____3083 =
                         let uu____3087 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3089 =
                           let uu____3093 =
                             let uu____3097 =
                               let uu____3101 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3103 =
                                 let uu____3107 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3109 =
                                   let uu____3113 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3115 =
                                     let uu____3119 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3119; stats]  in
                                   uu____3113 :: uu____3115  in
                                 uu____3107 :: uu____3109  in
                               uu____3101 :: uu____3103  in
                             used_hint_tag :: uu____3097  in
                           tag :: uu____3093  in
                         uu____3087 :: uu____3089  in
                       (settings.query_name) :: uu____3083  in
                     range :: uu____3079  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____3075);
                  (let uu____3134 = FStar_Options.print_z3_statistics ()  in
                   if uu____3134 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3160  ->
                          match uu____3160 with
                          | (uu____3168,msg,range1) ->
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
      let uu____3195 =
        let uu____3197 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3197  in
      if uu____3195
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
                | uu____3224 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3232 = FStar_ST.op_Bang recorded_hints  in
           match uu____3232 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3288 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3295 =
               let uu____3296 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3296  in
             store_hint uu____3295
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3303 -> ())
  
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
                     let uu____3414 = f q res  in
                     match uu____3414 with
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
            (let uu____3453 =
               let uu____3460 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3473,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3499,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3522 = FStar_Ident.text_of_lid q  in
                     (uu____3522, n1)
                  in
               match uu____3460 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3540 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3542 =
                       let uu____3544 = FStar_Options.z3_rlimit ()  in
                       uu____3544 * (Prims.parse_int "544656")  in
                     uu____3540 * uu____3542  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3551 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3552 = FStar_Options.initial_fuel ()  in
                     let uu____3554 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3551;
                       query_fuel = uu____3552;
                       query_ifuel = uu____3554;
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
                              { FStar_Util.hint_name = uu____3563;
                                FStar_Util.hint_index = uu____3564;
                                FStar_Util.fuel = uu____3565;
                                FStar_Util.ifuel = uu____3566;
                                FStar_Util.unsat_core = uu____3567;
                                FStar_Util.query_elapsed_time = uu____3568;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3453 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3596;
                         FStar_Util.hint_index = uu____3597;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3601;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___382_3618 = default_settings  in
                         {
                           query_env = (uu___382_3618.query_env);
                           query_decl = (uu___382_3618.query_decl);
                           query_name = (uu___382_3618.query_name);
                           query_index = (uu___382_3618.query_index);
                           query_range = (uu___382_3618.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___382_3618.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___382_3618.query_errors);
                           query_all_labels =
                             (uu___382_3618.query_all_labels);
                           query_suffix = (uu___382_3618.query_suffix);
                           query_hash = (uu___382_3618.query_hash)
                         })]
                   | uu____3622 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3628 =
                     let uu____3630 = FStar_Options.max_ifuel ()  in
                     let uu____3632 = FStar_Options.initial_ifuel ()  in
                     uu____3630 > uu____3632  in
                   if uu____3628
                   then
                     let uu____3637 =
                       let uu___383_3638 = default_settings  in
                       let uu____3639 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___383_3638.query_env);
                         query_decl = (uu___383_3638.query_decl);
                         query_name = (uu___383_3638.query_name);
                         query_index = (uu___383_3638.query_index);
                         query_range = (uu___383_3638.query_range);
                         query_fuel = (uu___383_3638.query_fuel);
                         query_ifuel = uu____3639;
                         query_rlimit = (uu___383_3638.query_rlimit);
                         query_hint = (uu___383_3638.query_hint);
                         query_errors = (uu___383_3638.query_errors);
                         query_all_labels = (uu___383_3638.query_all_labels);
                         query_suffix = (uu___383_3638.query_suffix);
                         query_hash = (uu___383_3638.query_hash)
                       }  in
                     [uu____3637]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3646 =
                     let uu____3648 =
                       let uu____3650 = FStar_Options.max_fuel ()  in
                       uu____3650 / (Prims.parse_int "2")  in
                     let uu____3653 = FStar_Options.initial_fuel ()  in
                     uu____3648 > uu____3653  in
                   if uu____3646
                   then
                     let uu____3658 =
                       let uu___384_3659 = default_settings  in
                       let uu____3660 =
                         let uu____3662 = FStar_Options.max_fuel ()  in
                         uu____3662 / (Prims.parse_int "2")  in
                       let uu____3665 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___384_3659.query_env);
                         query_decl = (uu___384_3659.query_decl);
                         query_name = (uu___384_3659.query_name);
                         query_index = (uu___384_3659.query_index);
                         query_range = (uu___384_3659.query_range);
                         query_fuel = uu____3660;
                         query_ifuel = uu____3665;
                         query_rlimit = (uu___384_3659.query_rlimit);
                         query_hint = (uu___384_3659.query_hint);
                         query_errors = (uu___384_3659.query_errors);
                         query_all_labels = (uu___384_3659.query_all_labels);
                         query_suffix = (uu___384_3659.query_suffix);
                         query_hash = (uu___384_3659.query_hash)
                       }  in
                     [uu____3658]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3672 =
                     (let uu____3678 = FStar_Options.max_fuel ()  in
                      let uu____3680 = FStar_Options.initial_fuel ()  in
                      uu____3678 > uu____3680) &&
                       (let uu____3684 = FStar_Options.max_ifuel ()  in
                        let uu____3686 = FStar_Options.initial_ifuel ()  in
                        uu____3684 >= uu____3686)
                      in
                   if uu____3672
                   then
                     let uu____3691 =
                       let uu___385_3692 = default_settings  in
                       let uu____3693 = FStar_Options.max_fuel ()  in
                       let uu____3695 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___385_3692.query_env);
                         query_decl = (uu___385_3692.query_decl);
                         query_name = (uu___385_3692.query_name);
                         query_index = (uu___385_3692.query_index);
                         query_range = (uu___385_3692.query_range);
                         query_fuel = uu____3693;
                         query_ifuel = uu____3695;
                         query_rlimit = (uu___385_3692.query_rlimit);
                         query_hint = (uu___385_3692.query_hint);
                         query_errors = (uu___385_3692.query_errors);
                         query_all_labels = (uu___385_3692.query_all_labels);
                         query_suffix = (uu___385_3692.query_suffix);
                         query_hash = (uu___385_3692.query_hash)
                       }  in
                     [uu____3691]
                   else []  in
                 let min_fuel1 =
                   let uu____3702 =
                     let uu____3704 = FStar_Options.min_fuel ()  in
                     let uu____3706 = FStar_Options.initial_fuel ()  in
                     uu____3704 < uu____3706  in
                   if uu____3702
                   then
                     let uu____3711 =
                       let uu___386_3712 = default_settings  in
                       let uu____3713 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___386_3712.query_env);
                         query_decl = (uu___386_3712.query_decl);
                         query_name = (uu___386_3712.query_name);
                         query_index = (uu___386_3712.query_index);
                         query_range = (uu___386_3712.query_range);
                         query_fuel = uu____3713;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___386_3712.query_rlimit);
                         query_hint = (uu___386_3712.query_hint);
                         query_errors = (uu___386_3712.query_errors);
                         query_all_labels = (uu___386_3712.query_all_labels);
                         query_suffix = (uu___386_3712.query_suffix);
                         query_hash = (uu___386_3712.query_hash)
                       }  in
                     [uu____3711]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3738 = FStar_Options.z3_refresh ()  in
                    if uu____3738
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3743 = with_fuel_and_diagnostics config1 []  in
                    let uu____3746 =
                      let uu____3749 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3749  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3743
                      uu____3746 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___387_3772 = default_settings  in
                        {
                          query_env = (uu___387_3772.query_env);
                          query_decl = (uu___387_3772.query_decl);
                          query_name = (uu___387_3772.query_name);
                          query_index = (uu___387_3772.query_index);
                          query_range = (uu___387_3772.query_range);
                          query_fuel = (uu___387_3772.query_fuel);
                          query_ifuel = (uu___387_3772.query_ifuel);
                          query_rlimit = (uu___387_3772.query_rlimit);
                          query_hint = (uu___387_3772.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___387_3772.query_all_labels);
                          query_suffix = (uu___387_3772.query_suffix);
                          query_hash = (uu___387_3772.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3773 =
                   let uu____3782 = FStar_Options.admit_smt_queries ()  in
                   let uu____3784 = FStar_Options.admit_except ()  in
                   (uu____3782, uu____3784)  in
                 (match uu____3773 with
                  | (true ,uu____3792) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3822 =
                              let uu____3824 =
                                let uu____3826 =
                                  let uu____3828 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____3828 ")"  in
                                Prims.strcat ", " uu____3826  in
                              Prims.strcat default_settings.query_name
                                uu____3824
                               in
                            Prims.strcat "(" uu____3822  in
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
        (let uu____3868 =
           let uu____3870 =
             let uu____3872 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3872  in
           FStar_Util.format1 "Starting query at %s" uu____3870  in
         FStar_SMTEncoding_Encode.push uu____3868);
        (let uu____3875 = FStar_Options.no_smt ()  in
         if uu____3875
         then
           let uu____3878 =
             let uu____3888 =
               let uu____3896 =
                 let uu____3898 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3898
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3896,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3888]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3878
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3919 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3919 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3955 =
                  let uu____3956 =
                    let uu____3958 =
                      let uu____3960 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3960
                       in
                    FStar_Util.format1 "Ending query at %s" uu____3958  in
                  FStar_SMTEncoding_Encode.pop uu____3956  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____3963);
                           FStar_SMTEncoding_Term.freevars = uu____3964;
                           FStar_SMTEncoding_Term.rng = uu____3965;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3966;
                       FStar_SMTEncoding_Term.assumption_name = uu____3967;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3968;_}
                     -> pop1 ()
                 | uu____3985 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3986 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3988 -> failwith "Impossible")))
  
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
           let uu____3996 =
             let uu____4003 = FStar_Options.peek ()  in (e, g, uu____4003)
              in
           [uu____3996]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____4019  -> ());
    FStar_TypeChecker_Env.push = (fun uu____4021  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____4024  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____4027  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____4046  -> fun uu____4047  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____4062  -> fun uu____4063  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4066  -> fun uu____4067  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____4073 =
             let uu____4080 = FStar_Options.peek ()  in (e, g, uu____4080)
              in
           [uu____4073]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4096  -> fun uu____4097  -> fun uu____4098  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4105  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4107  -> ())
  } 
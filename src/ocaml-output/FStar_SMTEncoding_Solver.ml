open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14 * 'Auu____15)) FStar_Util.either ->
      ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___375_32  ->
    match uu___375_32 with
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
                  (fun uu___376_408  ->
                     match uu___376_408 with
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
        let keep_decl uu___377_438 =
          match uu___377_438 with
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
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1781 =
            let uu____1784 =
              let uu____1787 = FStar_Options.record_hints ()  in
              if uu____1787
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1794 =
              let uu____1797 =
                let uu____1800 = FStar_Options.print_z3_statistics ()  in
                if uu____1800
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1797 settings.query_suffix  in
            FStar_List.append uu____1784 uu____1794  in
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
      let uu____1834 = FStar_ST.op_Bang replaying_hints  in
      match uu____1834 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___378_1867  ->
               match uu___378_1867 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1875 -> FStar_Pervasives_Native.None)
      | uu____1878 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1896 -> FStar_Pervasives_Native.None
      | uu____1897 ->
          let uu____1898 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1898 with
           | (msg,error_labels) ->
               let err =
                 let uu____1911 =
                   FStar_List.map
                     (fun uu____1939  ->
                        match uu____1939 with
                        | (uu____1954,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1911
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1971 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1971
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1974 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1994 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1994
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____2044 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2044)
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
            match err.error_messages with | [] -> false | uu____2122 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2144 = find_localized_errors errs  in
    FStar_Option.isSome uu____2144
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____2154 = find_localized_errors settings.query_errors  in
     match uu____2154 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____2164 =
                    let uu____2166 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____2166  in
                  FStar_Errors.diag settings.query_range uu____2164));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____2171 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____2184 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____2184))
              in
           FStar_All.pipe_right uu____2171 (FStar_String.concat "; ")  in
         let uu____2192 =
           let uu____2202 =
             let uu____2210 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____2210,
               (settings.query_range))
              in
           [uu____2202]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____2192);
    (let uu____2228 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2231 = FStar_Options.n_cores ()  in
          uu____2231 = (Prims.parse_int "1"))
        in
     if uu____2228
     then
       let initial_fuel1 =
         let uu___379_2237 = settings  in
         let uu____2238 = FStar_Options.initial_fuel ()  in
         let uu____2240 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___379_2237.query_env);
           query_decl = (uu___379_2237.query_decl);
           query_name = (uu___379_2237.query_name);
           query_index = (uu___379_2237.query_index);
           query_range = (uu___379_2237.query_range);
           query_fuel = uu____2238;
           query_ifuel = uu____2240;
           query_rlimit = (uu___379_2237.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___379_2237.query_errors);
           query_all_labels = (uu___379_2237.query_all_labels);
           query_suffix = (uu___379_2237.query_suffix);
           query_hash = (uu___379_2237.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2263 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2263
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
         (let uu____2313 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2313)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____2375 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____2375
      then
        let uu____2378 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2378 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____2391 -> "succeeded"
              | uu____2393 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____2398 =
                let uu____2400 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____2402 =
                  let uu____2404 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____2404 ")"  in
                Prims.strcat uu____2400 uu____2402  in
              Prims.strcat "(" uu____2398  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____2418 = FStar_Options.print_z3_statistics ()  in
              if uu____2418
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
                let uu____2452 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____2452 "}"
              else ""  in
            ((let uu____2461 =
                let uu____2465 =
                  let uu____2469 =
                    let uu____2473 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____2475 =
                      let uu____2479 =
                        let uu____2483 =
                          let uu____2487 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____2489 =
                            let uu____2493 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____2495 =
                              let uu____2499 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____2501 =
                                let uu____2505 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____2505; stats]  in
                              uu____2499 :: uu____2501  in
                            uu____2493 :: uu____2495  in
                          uu____2487 :: uu____2489  in
                        used_hint_tag :: uu____2483  in
                      tag :: uu____2479  in
                    uu____2473 :: uu____2475  in
                  (settings.query_name) :: uu____2469  in
                range :: uu____2465  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____2461);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____2540  ->
                     match uu____2540 with
                     | (uu____2548,msg,range1) ->
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
      let uu____2575 =
        let uu____2577 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____2577  in
      if uu____2575
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
                | uu____2604 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____2612 = FStar_ST.op_Bang recorded_hints  in
           match uu____2612 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2668 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2675 =
               let uu____2676 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2676  in
             store_hint uu____2675
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2683 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2700 =
         (used_hint settings) &&
           (let uu____2703 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2703)
          in
       if uu____2700 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2803 = f q res  in
                     match uu____2803 with
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
            (let uu____2842 =
               let uu____2849 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2862,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2888,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2911 = FStar_Ident.text_of_lid q  in
                     (uu____2911, n1)
                  in
               match uu____2849 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2929 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2931 =
                       let uu____2933 = FStar_Options.z3_rlimit ()  in
                       uu____2933 * (Prims.parse_int "544656")  in
                     uu____2929 * uu____2931  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2940 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2941 = FStar_Options.initial_fuel ()  in
                     let uu____2943 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2940;
                       query_fuel = uu____2941;
                       query_ifuel = uu____2943;
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
                              { FStar_Util.hint_name = uu____2952;
                                FStar_Util.hint_index = uu____2953;
                                FStar_Util.fuel = uu____2954;
                                FStar_Util.ifuel = uu____2955;
                                FStar_Util.unsat_core = uu____2956;
                                FStar_Util.query_elapsed_time = uu____2957;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2842 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2985;
                         FStar_Util.hint_index = uu____2986;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2990;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___380_3007 = default_settings  in
                         {
                           query_env = (uu___380_3007.query_env);
                           query_decl = (uu___380_3007.query_decl);
                           query_name = (uu___380_3007.query_name);
                           query_index = (uu___380_3007.query_index);
                           query_range = (uu___380_3007.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___380_3007.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___380_3007.query_errors);
                           query_all_labels =
                             (uu___380_3007.query_all_labels);
                           query_suffix = (uu___380_3007.query_suffix);
                           query_hash = (uu___380_3007.query_hash)
                         })]
                   | uu____3011 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3017 =
                     let uu____3019 = FStar_Options.max_ifuel ()  in
                     let uu____3021 = FStar_Options.initial_ifuel ()  in
                     uu____3019 > uu____3021  in
                   if uu____3017
                   then
                     let uu____3026 =
                       let uu___381_3027 = default_settings  in
                       let uu____3028 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___381_3027.query_env);
                         query_decl = (uu___381_3027.query_decl);
                         query_name = (uu___381_3027.query_name);
                         query_index = (uu___381_3027.query_index);
                         query_range = (uu___381_3027.query_range);
                         query_fuel = (uu___381_3027.query_fuel);
                         query_ifuel = uu____3028;
                         query_rlimit = (uu___381_3027.query_rlimit);
                         query_hint = (uu___381_3027.query_hint);
                         query_errors = (uu___381_3027.query_errors);
                         query_all_labels = (uu___381_3027.query_all_labels);
                         query_suffix = (uu___381_3027.query_suffix);
                         query_hash = (uu___381_3027.query_hash)
                       }  in
                     [uu____3026]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3035 =
                     let uu____3037 =
                       let uu____3039 = FStar_Options.max_fuel ()  in
                       uu____3039 / (Prims.parse_int "2")  in
                     let uu____3042 = FStar_Options.initial_fuel ()  in
                     uu____3037 > uu____3042  in
                   if uu____3035
                   then
                     let uu____3047 =
                       let uu___382_3048 = default_settings  in
                       let uu____3049 =
                         let uu____3051 = FStar_Options.max_fuel ()  in
                         uu____3051 / (Prims.parse_int "2")  in
                       let uu____3054 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___382_3048.query_env);
                         query_decl = (uu___382_3048.query_decl);
                         query_name = (uu___382_3048.query_name);
                         query_index = (uu___382_3048.query_index);
                         query_range = (uu___382_3048.query_range);
                         query_fuel = uu____3049;
                         query_ifuel = uu____3054;
                         query_rlimit = (uu___382_3048.query_rlimit);
                         query_hint = (uu___382_3048.query_hint);
                         query_errors = (uu___382_3048.query_errors);
                         query_all_labels = (uu___382_3048.query_all_labels);
                         query_suffix = (uu___382_3048.query_suffix);
                         query_hash = (uu___382_3048.query_hash)
                       }  in
                     [uu____3047]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3061 =
                     (let uu____3067 = FStar_Options.max_fuel ()  in
                      let uu____3069 = FStar_Options.initial_fuel ()  in
                      uu____3067 > uu____3069) &&
                       (let uu____3073 = FStar_Options.max_ifuel ()  in
                        let uu____3075 = FStar_Options.initial_ifuel ()  in
                        uu____3073 >= uu____3075)
                      in
                   if uu____3061
                   then
                     let uu____3080 =
                       let uu___383_3081 = default_settings  in
                       let uu____3082 = FStar_Options.max_fuel ()  in
                       let uu____3084 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___383_3081.query_env);
                         query_decl = (uu___383_3081.query_decl);
                         query_name = (uu___383_3081.query_name);
                         query_index = (uu___383_3081.query_index);
                         query_range = (uu___383_3081.query_range);
                         query_fuel = uu____3082;
                         query_ifuel = uu____3084;
                         query_rlimit = (uu___383_3081.query_rlimit);
                         query_hint = (uu___383_3081.query_hint);
                         query_errors = (uu___383_3081.query_errors);
                         query_all_labels = (uu___383_3081.query_all_labels);
                         query_suffix = (uu___383_3081.query_suffix);
                         query_hash = (uu___383_3081.query_hash)
                       }  in
                     [uu____3080]
                   else []  in
                 let min_fuel1 =
                   let uu____3091 =
                     let uu____3093 = FStar_Options.min_fuel ()  in
                     let uu____3095 = FStar_Options.initial_fuel ()  in
                     uu____3093 < uu____3095  in
                   if uu____3091
                   then
                     let uu____3100 =
                       let uu___384_3101 = default_settings  in
                       let uu____3102 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___384_3101.query_env);
                         query_decl = (uu___384_3101.query_decl);
                         query_name = (uu___384_3101.query_name);
                         query_index = (uu___384_3101.query_index);
                         query_range = (uu___384_3101.query_range);
                         query_fuel = uu____3102;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___384_3101.query_rlimit);
                         query_hint = (uu___384_3101.query_hint);
                         query_errors = (uu___384_3101.query_errors);
                         query_all_labels = (uu___384_3101.query_all_labels);
                         query_suffix = (uu___384_3101.query_suffix);
                         query_hash = (uu___384_3101.query_hash)
                       }  in
                     [uu____3100]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3127 =
                      (used_hint config1) || (FStar_Options.z3_refresh ())
                       in
                    if uu____3127
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3132 = with_fuel_and_diagnostics config1 []  in
                    let uu____3135 =
                      let uu____3138 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3138  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3132
                      uu____3135 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___385_3161 = default_settings  in
                        {
                          query_env = (uu___385_3161.query_env);
                          query_decl = (uu___385_3161.query_decl);
                          query_name = (uu___385_3161.query_name);
                          query_index = (uu___385_3161.query_index);
                          query_range = (uu___385_3161.query_range);
                          query_fuel = (uu___385_3161.query_fuel);
                          query_ifuel = (uu___385_3161.query_ifuel);
                          query_rlimit = (uu___385_3161.query_rlimit);
                          query_hint = (uu___385_3161.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___385_3161.query_all_labels);
                          query_suffix = (uu___385_3161.query_suffix);
                          query_hash = (uu___385_3161.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3162 =
                   let uu____3171 = FStar_Options.admit_smt_queries ()  in
                   let uu____3173 = FStar_Options.admit_except ()  in
                   (uu____3171, uu____3173)  in
                 (match uu____3162 with
                  | (true ,uu____3181) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3211 =
                              let uu____3213 =
                                let uu____3215 =
                                  let uu____3217 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____3217 ")"  in
                                Prims.strcat ", " uu____3215  in
                              Prims.strcat default_settings.query_name
                                uu____3213
                               in
                            Prims.strcat "(" uu____3211  in
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
        (let uu____3257 =
           let uu____3259 =
             let uu____3261 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3261  in
           FStar_Util.format1 "Starting query at %s" uu____3259  in
         FStar_SMTEncoding_Encode.push uu____3257);
        (let uu____3264 = FStar_Options.no_smt ()  in
         if uu____3264
         then
           let uu____3267 =
             let uu____3277 =
               let uu____3285 =
                 let uu____3287 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3287
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3285,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____3277]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____3267
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____3308 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____3308 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____3344 =
                  let uu____3345 =
                    let uu____3347 =
                      let uu____3349 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3349
                       in
                    FStar_Util.format1 "Ending query at %s" uu____3347  in
                  FStar_SMTEncoding_Encode.pop uu____3345  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____3352);
                           FStar_SMTEncoding_Term.freevars = uu____3353;
                           FStar_SMTEncoding_Term.rng = uu____3354;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3355;
                       FStar_SMTEncoding_Term.assumption_name = uu____3356;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3357;_}
                     -> pop1 ()
                 | uu____3374 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3375 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3377 -> failwith "Impossible")))
  
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
           let uu____3385 =
             let uu____3392 = FStar_Options.peek ()  in (e, g, uu____3392)
              in
           [uu____3385]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3408  -> ());
    FStar_TypeChecker_Env.push = (fun uu____3410  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3413  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3416  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____3435  -> fun uu____3436  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____3451  -> fun uu____3452  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3455  -> fun uu____3456  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____3462 =
             let uu____3469 = FStar_Options.peek ()  in (e, g, uu____3469)
              in
           [uu____3462]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3485  -> fun uu____3486  -> fun uu____3487  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____3494  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3496  -> ())
  } 
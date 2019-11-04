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
      (let uu____139 = FStar_Options.use_hints ()  in
       if uu____139
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename = FStar_Options.hint_file_for_src norm_src_filename
            in
         let uu____146 = FStar_Util.read_hints val_filename  in
         match uu____146 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____153 = FStar_Options.hint_info ()  in
               if uu____153
               then
                 FStar_Util.print3 "(%s) digest is %s from %s.\n"
                   norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   val_filename
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____189 = FStar_Options.hint_info ()  in
             (if uu____189
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____206 = FStar_Options.record_hints ()  in
     if uu____206
     then
       let hints =
         let uu____210 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____210  in
       let hints_db =
         let uu____237 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____237; FStar_Util.hints = hints }
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
        | uu____359 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_367  ->
                     match uu___1_367 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____370 -> false)))
              ||
              (let uu____373 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____373)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.of_int (10000))  in
        let keep_decl uu___2_397 =
          match uu___2_397 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____412 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____422 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____445 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____445
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____463 ->
                   let uu____464 = keep_decl d  in
                   if uu____464 then d :: out else out) [] theory_rev
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
            let uu____520 = filter_using_facts_from e theory  in
            (uu____520, false, Prims.int_zero, Prims.int_zero)
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____541 =
              let uu____552 =
                let uu____563 =
                  let uu____566 =
                    let uu____567 =
                      let uu____569 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____569  in
                    FStar_SMTEncoding_Term.Caption uu____567  in
                  [uu____566]  in
                (uu____563, Prims.int_zero, Prims.int_zero)  in
              FStar_List.fold_left
                (fun uu____599  ->
                   fun d  ->
                     match uu____599 with
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
                              let uu____693 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____693
                                (fun uu____753  ->
                                   match uu____753 with
                                   | (decls1,uu____778,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____798 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____552 theory_rev
               in
            (match uu____541 with
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
        let uu____860 = filter_assertions_with_stats e core theory  in
        match uu____860 with
        | (theory1,b,uu____883,uu____884) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____920 = filter_using_facts_from e x  in (uu____920, false)
  
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
    let uu____1150 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1152 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____1150
      uu____1152
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
  
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err  ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____1178 =
        let uu____1180 = FStar_Util.string_of_int err.error_fuel  in
        let uu____1182 = FStar_Util.string_of_int err.error_ifuel  in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____1180 uu____1182
          (if FStar_Option.isSome err.error_hint then "with hint" else "")
         in
      [uu____1178]
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
      let uu____1726 =
        let uu____1729 =
          let uu____1730 =
            let uu____1732 = FStar_Util.string_of_int n1  in
            let uu____1734 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1732 uu____1734
             in
          FStar_SMTEncoding_Term.Caption uu____1730  in
        let uu____1737 =
          let uu____1740 =
            let uu____1741 =
              let uu____1749 =
                let uu____1750 =
                  let uu____1755 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1760 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1755, uu____1760)  in
                FStar_SMTEncoding_Util.mkEq uu____1750  in
              (uu____1749, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1741  in
          let uu____1764 =
            let uu____1767 =
              let uu____1768 =
                let uu____1776 =
                  let uu____1777 =
                    let uu____1782 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1787 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1782, uu____1787)  in
                  FStar_SMTEncoding_Util.mkEq uu____1777  in
                (uu____1776, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1768  in
            [uu____1767; settings.query_decl]  in
          uu____1740 :: uu____1764  in
        uu____1729 :: uu____1737  in
      let uu____1791 =
        let uu____1794 =
          let uu____1797 =
            let uu____1800 =
              let uu____1801 =
                let uu____1808 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1808)  in
              FStar_SMTEncoding_Term.SetOption uu____1801  in
            [uu____1800;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____1817 =
            let uu____1820 =
              let uu____1823 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____1823
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____1820 settings.query_suffix  in
          FStar_List.append uu____1797 uu____1817  in
        FStar_List.append label_assumptions uu____1794  in
      FStar_List.append uu____1726 uu____1791
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1857 = FStar_ST.op_Bang replaying_hints  in
      match uu____1857 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1890  ->
               match uu___3_1890 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1898 -> FStar_Pervasives_Native.None)
      | uu____1901 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1919 -> FStar_Pervasives_Native.None
      | uu____1920 ->
          let uu____1921 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1921 with
           | (msg,error_labels) ->
               let err =
                 let uu____1934 =
                   FStar_List.map
                     (fun uu____1962  ->
                        match uu____1962 with
                        | (uu____1977,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1934
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1994 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1994
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1997 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____2017 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2017
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2046 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____2046)
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
            match err.error_messages with | [] -> false | uu____2102 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____2124 = find_localized_errors errs  in
    FStar_Option.isSome uu____2124
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg
       in
    (let smt_error =
       let uu____2151 = FStar_Options.query_stats ()  in
       if uu____2151
       then
         let uu____2160 =
           let uu____2162 =
             let uu____2164 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map error_to_short_string)
                in
             FStar_All.pipe_right uu____2164 (FStar_String.concat ";\n\t")
              in
           FStar_All.pipe_right uu____2162 format_smt_error  in
         FStar_All.pipe_right uu____2160 (fun _2190  -> FStar_Util.Inr _2190)
       else
         (let uu____2193 =
            FStar_List.fold_left
              (fun uu____2218  ->
                 fun err  ->
                   match uu____2218 with
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
          match uu____2193 with
          | (incomplete_count,canceled_count,unknown_count) ->
              FStar_All.pipe_right
                (match (incomplete_count, canceled_count, unknown_count) with
                 | (uu____2323,_2328,_2329) when
                     ((_2328 = Prims.int_zero) && (_2329 = Prims.int_zero))
                       && (incomplete_count > Prims.int_zero)
                     ->
                     "The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
                 | (_2336,uu____2332,_2338) when
                     ((_2336 = Prims.int_zero) && (_2338 = Prims.int_zero))
                       && (canceled_count > Prims.int_zero)
                     ->
                     "The SMT query timed out, you might want to increase the rlimit"
                 | (uu____2341,uu____2342,uu____2343) ->
                     "Try with --query_stats to get more details")
                (fun _2353  -> FStar_Util.Inl _2353))
        in
     let uu____2354 = find_localized_errors settings.query_errors  in
     match uu____2354 with
     | FStar_Pervasives_Native.Some err ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           err.error_messages smt_error
     | FStar_Pervasives_Native.None  ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
              "Unknown assertion failed", (settings.query_range))] smt_error);
    (let uu____2374 = FStar_Options.detail_errors ()  in
     if uu____2374
     then
       let initial_fuel1 =
         let uu___252_2378 = settings  in
         let uu____2379 = FStar_Options.initial_fuel ()  in
         let uu____2381 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___252_2378.query_env);
           query_decl = (uu___252_2378.query_decl);
           query_name = (uu___252_2378.query_name);
           query_index = (uu___252_2378.query_index);
           query_range = (uu___252_2378.query_range);
           query_fuel = uu____2379;
           query_ifuel = uu____2381;
           query_rlimit = (uu___252_2378.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___252_2378.query_errors);
           query_all_labels = (uu___252_2378.query_all_labels);
           query_suffix = (uu___252_2378.query_suffix);
           query_hash = (uu___252_2378.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____2404 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2404
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2433 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____2433)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2498 =
          let r = FStar_Util.mk_ref []  in
          let uu____2509 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2609  ->
                 let uu____2610 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2610
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2509 with | (add1,get1) -> (add1, get1)  in
        let uu____2692 = accumulator ()  in
        match uu____2692 with
        | (add_module_name,get_module_names) ->
            let uu____2729 = accumulator ()  in
            (match uu____2729 with
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
                                  let uu____2852 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2852
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
                         | uu____2897 ->
                             let uu____2901 = FStar_Util.prefix components
                                in
                             (match uu____2901 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2928 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2928
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2935::[] -> ()
                                    | uu____2939 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2956 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2956])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2983 =
                          let uu____2985 = get_module_names ()  in
                          FStar_All.pipe_right uu____2985
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2983);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2998 =
                          let uu____3000 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____3000
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2998))))
         in
      let uu____3010 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____3010
      then
        let uu____3013 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____3013 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____3032 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____3046 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____3032 with
             | (tag,core) ->
                 let range =
                   let uu____3059 =
                     let uu____3061 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____3061 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____3059  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____3075 = FStar_Options.query_stats ()  in
                   if uu____3075
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
                     let uu____3109 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one)
                        in
                     Prims.op_Hat uu____3109 "}"
                   else ""  in
                 ((let uu____3118 =
                     let uu____3122 =
                       let uu____3126 =
                         let uu____3130 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3132 =
                           let uu____3136 =
                             let uu____3140 =
                               let uu____3144 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3146 =
                                 let uu____3150 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3152 =
                                   let uu____3156 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3158 =
                                     let uu____3162 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3162; stats]  in
                                   uu____3156 :: uu____3158  in
                                 uu____3150 :: uu____3152  in
                               uu____3144 :: uu____3146  in
                             used_hint_tag :: uu____3140  in
                           tag :: uu____3136  in
                         uu____3130 :: uu____3132  in
                       (settings.query_name) :: uu____3126  in
                     range :: uu____3122  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____3118);
                  (let uu____3177 = FStar_Options.print_z3_statistics ()  in
                   if uu____3177 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3203  ->
                          match uu____3203 with
                          | (uu____3211,msg,range1) ->
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
      let uu____3238 =
        let uu____3240 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3240  in
      if uu____3238
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
                | uu____3267 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3275 = FStar_ST.op_Bang recorded_hints  in
           match uu____3275 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3331 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3338 =
               let uu____3339 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3339  in
             store_hint uu____3338
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3346 -> ())
  
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
                     let uu____3457 = f q res  in
                     match uu____3457 with
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
            (let uu____3496 =
               let uu____3503 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3516,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3542,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3565 = FStar_Ident.text_of_lid q  in
                     (uu____3565, n1)
                  in
               match uu____3503 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3583 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3585 =
                       let uu____3587 = FStar_Options.z3_rlimit ()  in
                       uu____3587 * (Prims.parse_int "544656")  in
                     uu____3583 * uu____3585  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3594 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3595 = FStar_Options.initial_fuel ()  in
                     let uu____3597 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3594;
                       query_fuel = uu____3595;
                       query_ifuel = uu____3597;
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
                              { FStar_Util.hint_name = uu____3606;
                                FStar_Util.hint_index = uu____3607;
                                FStar_Util.fuel = uu____3608;
                                FStar_Util.ifuel = uu____3609;
                                FStar_Util.unsat_core = uu____3610;
                                FStar_Util.query_elapsed_time = uu____3611;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3496 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3639;
                         FStar_Util.hint_index = uu____3640;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3644;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___441_3661 = default_settings  in
                         {
                           query_env = (uu___441_3661.query_env);
                           query_decl = (uu___441_3661.query_decl);
                           query_name = (uu___441_3661.query_name);
                           query_index = (uu___441_3661.query_index);
                           query_range = (uu___441_3661.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___441_3661.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___441_3661.query_errors);
                           query_all_labels =
                             (uu___441_3661.query_all_labels);
                           query_suffix = (uu___441_3661.query_suffix);
                           query_hash = (uu___441_3661.query_hash)
                         })]
                   | uu____3665 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3671 =
                     let uu____3673 = FStar_Options.max_ifuel ()  in
                     let uu____3675 = FStar_Options.initial_ifuel ()  in
                     uu____3673 > uu____3675  in
                   if uu____3671
                   then
                     let uu____3680 =
                       let uu___446_3681 = default_settings  in
                       let uu____3682 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___446_3681.query_env);
                         query_decl = (uu___446_3681.query_decl);
                         query_name = (uu___446_3681.query_name);
                         query_index = (uu___446_3681.query_index);
                         query_range = (uu___446_3681.query_range);
                         query_fuel = (uu___446_3681.query_fuel);
                         query_ifuel = uu____3682;
                         query_rlimit = (uu___446_3681.query_rlimit);
                         query_hint = (uu___446_3681.query_hint);
                         query_errors = (uu___446_3681.query_errors);
                         query_all_labels = (uu___446_3681.query_all_labels);
                         query_suffix = (uu___446_3681.query_suffix);
                         query_hash = (uu___446_3681.query_hash)
                       }  in
                     [uu____3680]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3689 =
                     let uu____3691 =
                       let uu____3693 = FStar_Options.max_fuel ()  in
                       uu____3693 / (Prims.of_int (2))  in
                     let uu____3696 = FStar_Options.initial_fuel ()  in
                     uu____3691 > uu____3696  in
                   if uu____3689
                   then
                     let uu____3701 =
                       let uu___450_3702 = default_settings  in
                       let uu____3703 =
                         let uu____3705 = FStar_Options.max_fuel ()  in
                         uu____3705 / (Prims.of_int (2))  in
                       let uu____3708 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___450_3702.query_env);
                         query_decl = (uu___450_3702.query_decl);
                         query_name = (uu___450_3702.query_name);
                         query_index = (uu___450_3702.query_index);
                         query_range = (uu___450_3702.query_range);
                         query_fuel = uu____3703;
                         query_ifuel = uu____3708;
                         query_rlimit = (uu___450_3702.query_rlimit);
                         query_hint = (uu___450_3702.query_hint);
                         query_errors = (uu___450_3702.query_errors);
                         query_all_labels = (uu___450_3702.query_all_labels);
                         query_suffix = (uu___450_3702.query_suffix);
                         query_hash = (uu___450_3702.query_hash)
                       }  in
                     [uu____3701]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3715 =
                     (let uu____3721 = FStar_Options.max_fuel ()  in
                      let uu____3723 = FStar_Options.initial_fuel ()  in
                      uu____3721 > uu____3723) &&
                       (let uu____3727 = FStar_Options.max_ifuel ()  in
                        let uu____3729 = FStar_Options.initial_ifuel ()  in
                        uu____3727 >= uu____3729)
                      in
                   if uu____3715
                   then
                     let uu____3734 =
                       let uu___454_3735 = default_settings  in
                       let uu____3736 = FStar_Options.max_fuel ()  in
                       let uu____3738 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___454_3735.query_env);
                         query_decl = (uu___454_3735.query_decl);
                         query_name = (uu___454_3735.query_name);
                         query_index = (uu___454_3735.query_index);
                         query_range = (uu___454_3735.query_range);
                         query_fuel = uu____3736;
                         query_ifuel = uu____3738;
                         query_rlimit = (uu___454_3735.query_rlimit);
                         query_hint = (uu___454_3735.query_hint);
                         query_errors = (uu___454_3735.query_errors);
                         query_all_labels = (uu___454_3735.query_all_labels);
                         query_suffix = (uu___454_3735.query_suffix);
                         query_hash = (uu___454_3735.query_hash)
                       }  in
                     [uu____3734]
                   else []  in
                 let min_fuel1 =
                   let uu____3745 =
                     let uu____3747 = FStar_Options.min_fuel ()  in
                     let uu____3749 = FStar_Options.initial_fuel ()  in
                     uu____3747 < uu____3749  in
                   if uu____3745
                   then
                     let uu____3754 =
                       let uu___458_3755 = default_settings  in
                       let uu____3756 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___458_3755.query_env);
                         query_decl = (uu___458_3755.query_decl);
                         query_name = (uu___458_3755.query_name);
                         query_index = (uu___458_3755.query_index);
                         query_range = (uu___458_3755.query_range);
                         query_fuel = uu____3756;
                         query_ifuel = Prims.int_one;
                         query_rlimit = (uu___458_3755.query_rlimit);
                         query_hint = (uu___458_3755.query_hint);
                         query_errors = (uu___458_3755.query_errors);
                         query_all_labels = (uu___458_3755.query_all_labels);
                         query_suffix = (uu___458_3755.query_suffix);
                         query_hash = (uu___458_3755.query_hash)
                       }  in
                     [uu____3754]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____3781 = FStar_Options.z3_refresh ()  in
                    if uu____3781
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3786 = with_fuel_and_diagnostics config1 []  in
                    let uu____3789 =
                      let uu____3792 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3792  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3786
                      uu____3789 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___471_3815 = default_settings  in
                        {
                          query_env = (uu___471_3815.query_env);
                          query_decl = (uu___471_3815.query_decl);
                          query_name = (uu___471_3815.query_name);
                          query_index = (uu___471_3815.query_index);
                          query_range = (uu___471_3815.query_range);
                          query_fuel = (uu___471_3815.query_fuel);
                          query_ifuel = (uu___471_3815.query_ifuel);
                          query_rlimit = (uu___471_3815.query_rlimit);
                          query_hint = (uu___471_3815.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___471_3815.query_all_labels);
                          query_suffix = (uu___471_3815.query_suffix);
                          query_hash = (uu___471_3815.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____3816 =
                   let uu____3825 = FStar_Options.admit_smt_queries ()  in
                   let uu____3827 = FStar_Options.admit_except ()  in
                   (uu____3825, uu____3827)  in
                 (match uu____3816 with
                  | (true ,uu____3835) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3865 =
                              let uu____3867 =
                                let uu____3869 =
                                  let uu____3871 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____3871 ")"  in
                                Prims.op_Hat ", " uu____3869  in
                              Prims.op_Hat default_settings.query_name
                                uu____3867
                               in
                            Prims.op_Hat "(" uu____3865  in
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
    let uu____4104 = FStar_Options.z3_seed ()  in
    let uu____4106 = FStar_Options.z3_cliopt ()  in
    let uu____4110 = FStar_Options.smtencoding_valid_intro ()  in
    let uu____4112 = FStar_Options.smtencoding_valid_elim ()  in
    {
      seed = uu____4104;
      cliopt = uu____4106;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____4110;
      valid_elim = uu____4112
    }
  
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____4120 =
      let uu____4123 = get_cfg env  in
      FStar_Pervasives_Native.Some uu____4123  in
    FStar_ST.op_Colon_Equals _last_cfg uu____4120
  
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    let uu____4154 = FStar_ST.op_Bang _last_cfg  in
    match uu____4154 with
    | FStar_Pervasives_Native.None  -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____4184 = let uu____4186 = get_cfg env  in cfg = uu____4186
           in
        Prims.op_Negation uu____4184
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        let uu____4214 = FStar_Options.no_smt ()  in
        if uu____4214
        then
          let uu____4217 =
            let uu____4227 =
              let uu____4235 =
                let uu____4237 = FStar_Syntax_Print.term_to_string q  in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____4237
                 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____4235,
                (tcenv.FStar_TypeChecker_Env.range))
               in
            [uu____4227]  in
          FStar_TypeChecker_Err.add_errors tcenv uu____4217
        else
          ((let uu____4258 = should_refresh tcenv  in
            if uu____4258
            then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
            else ());
           (let uu____4265 =
              let uu____4267 =
                let uu____4269 = FStar_TypeChecker_Env.get_range tcenv  in
                FStar_All.pipe_left FStar_Range.string_of_range uu____4269
                 in
              FStar_Util.format1 "Starting query at %s" uu____4267  in
            FStar_SMTEncoding_Encode.push uu____4265);
           (let pop1 uu____4277 =
              let uu____4278 =
                let uu____4280 =
                  let uu____4282 = FStar_TypeChecker_Env.get_range tcenv  in
                  FStar_All.pipe_left FStar_Range.string_of_range uu____4282
                   in
                FStar_Util.format1 "Ending query at %s" uu____4280  in
              FStar_SMTEncoding_Encode.pop uu____4278  in
            try
              (fun uu___520_4298  ->
                 match () with
                 | () ->
                     let uu____4299 =
                       FStar_SMTEncoding_Encode.encode_query use_env_msg
                         tcenv q
                        in
                     (match uu____4299 with
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
                                        ,uu____4331);
                                     FStar_SMTEncoding_Term.freevars =
                                       uu____4332;
                                     FStar_SMTEncoding_Term.rng = uu____4333;_};
                                 FStar_SMTEncoding_Term.assumption_caption =
                                   uu____4334;
                                 FStar_SMTEncoding_Term.assumption_name =
                                   uu____4335;
                                 FStar_SMTEncoding_Term.assumption_fact_ids =
                                   uu____4336;_}
                               -> pop1 ()
                           | uu____4356 when
                               tcenv1.FStar_TypeChecker_Env.admit -> 
                               pop1 ()
                           | FStar_SMTEncoding_Term.Assume uu____4357 ->
                               (ask_and_report_errors tcenv1 labels prefix1
                                  qry suffix;
                                pop1 ())
                           | uu____4359 -> failwith "Impossible"))) ()
            with
            | FStar_SMTEncoding_Env.Inner_let_rec names1 ->
                (pop1 ();
                 (let uu____4375 =
                    let uu____4385 =
                      let uu____4393 =
                        let uu____4395 =
                          let uu____4397 =
                            FStar_List.map FStar_Pervasives_Native.fst names1
                             in
                          FStar_String.concat "," uu____4397  in
                        FStar_Util.format1
                          "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                          uu____4395
                         in
                      (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                        uu____4393, (tcenv.FStar_TypeChecker_Env.range))
                       in
                    [uu____4385]  in
                  FStar_TypeChecker_Err.add_errors tcenv uu____4375))))
  
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
           let uu____4437 =
             let uu____4444 = FStar_Options.peek ()  in (e, g, uu____4444)
              in
           [uu____4437]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____4460  -> ());
    FStar_TypeChecker_Env.push = (fun uu____4462  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____4465  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____4468  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____4487  -> fun uu____4488  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4503  -> fun uu____4504  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____4510 =
             let uu____4517 = FStar_Options.peek ()  in (e, g, uu____4517)
              in
           [uu____4510]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4533  -> fun uu____4534  -> fun uu____4535  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4542  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4544  -> ())
  } 
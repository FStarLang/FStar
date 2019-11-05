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
              let uu____2009 =
                with_fuel_and_diagnostics settings label_assumptions  in
              FStar_SMTEncoding_Z3.ask settings.query_range
                (filter_assertions settings.query_env settings.query_hint)
                settings.query_hash settings.query_all_labels uu____2009
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
            match err.error_messages with | [] -> false | uu____2043 -> true))
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg
       in
    (let smt_error =
       let uu____2078 = FStar_Options.query_stats ()  in
       if uu____2078
       then
         let uu____2087 =
           let uu____2089 =
             let uu____2091 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map error_to_short_string)
                in
             FStar_All.pipe_right uu____2091 (FStar_String.concat ";\n\t")
              in
           FStar_All.pipe_right uu____2089 format_smt_error  in
         FStar_All.pipe_right uu____2087 (fun _2117  -> FStar_Util.Inr _2117)
       else
         (let uu____2120 =
            FStar_List.fold_left
              (fun uu____2145  ->
                 fun err  ->
                   match uu____2145 with
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
          match uu____2120 with
          | (incomplete_count,canceled_count,unknown_count) ->
              FStar_All.pipe_right
                (match (incomplete_count, canceled_count, unknown_count) with
                 | (uu____2250,_2255,_2256) when
                     ((_2255 = Prims.int_zero) && (_2256 = Prims.int_zero))
                       && (incomplete_count > Prims.int_zero)
                     ->
                     "The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
                 | (_2263,uu____2259,_2265) when
                     ((_2263 = Prims.int_zero) && (_2265 = Prims.int_zero))
                       && (canceled_count > Prims.int_zero)
                     ->
                     "The SMT query timed out, you might want to increase the rlimit"
                 | (uu____2268,uu____2269,uu____2270) ->
                     "Try with --query_stats to get more details")
                (fun _2280  -> FStar_Util.Inl _2280))
        in
     let uu____2281 = find_localized_errors settings.query_errors  in
     match uu____2281 with
     | FStar_Pervasives_Native.Some err ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           err.error_messages smt_error
     | FStar_Pervasives_Native.None  ->
         FStar_TypeChecker_Err.add_errors_smt_detail settings.query_env
           [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
              "Unknown assertion failed", (settings.query_range))] smt_error);
    (let uu____2301 = FStar_Options.detail_errors ()  in
     if uu____2301
     then
       let initial_fuel1 =
         let uu___249_2305 = settings  in
         let uu____2306 = FStar_Options.initial_fuel ()  in
         let uu____2308 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___249_2305.query_env);
           query_decl = (uu___249_2305.query_decl);
           query_name = (uu___249_2305.query_name);
           query_index = (uu___249_2305.query_index);
           query_range = (uu___249_2305.query_range);
           query_fuel = uu____2306;
           query_ifuel = uu____2308;
           query_rlimit = (uu___249_2305.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___249_2305.query_errors);
           query_all_labels = (uu___249_2305.query_all_labels);
           query_suffix = (uu___249_2305.query_suffix);
           query_hash = (uu___249_2305.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let uu____2323 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____2323 FStar_Pervasives_Native.None
           false
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____2366 =
          let r = FStar_Util.mk_ref []  in
          let uu____2377 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2477  ->
                 let uu____2478 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____2478
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____2377 with | (add1,get1) -> (add1, get1)  in
        let uu____2560 = accumulator ()  in
        match uu____2560 with
        | (add_module_name,get_module_names) ->
            let uu____2597 = accumulator ()  in
            (match uu____2597 with
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
                                  let uu____2720 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____2720
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
                         | uu____2765 ->
                             let uu____2769 = FStar_Util.prefix components
                                in
                             (match uu____2769 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____2796 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____2796
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2803::[] -> ()
                                    | uu____2807 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2824 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____2824])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____2851 =
                          let uu____2853 = get_module_names ()  in
                          FStar_All.pipe_right uu____2853
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2851);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2866 =
                          let uu____2868 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____2868
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2866))))
         in
      let uu____2878 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____2878
      then
        let uu____2881 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____2881 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____2900 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2914 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____2900 with
             | (tag,core) ->
                 let range =
                   let uu____2927 =
                     let uu____2929 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____2929 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____2927  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____2943 = FStar_Options.query_stats ()  in
                   if uu____2943
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
                     let uu____2977 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one)
                        in
                     Prims.op_Hat uu____2977 "}"
                   else ""  in
                 ((let uu____2986 =
                     let uu____2990 =
                       let uu____2994 =
                         let uu____2998 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____3000 =
                           let uu____3004 =
                             let uu____3008 =
                               let uu____3012 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____3014 =
                                 let uu____3018 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____3020 =
                                   let uu____3024 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____3026 =
                                     let uu____3030 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____3030; stats]  in
                                   uu____3024 :: uu____3026  in
                                 uu____3018 :: uu____3020  in
                               uu____3012 :: uu____3014  in
                             used_hint_tag :: uu____3008  in
                           tag :: uu____3004  in
                         uu____2998 :: uu____3000  in
                       (settings.query_name) :: uu____2994  in
                     range :: uu____2990  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2986);
                  (let uu____3045 = FStar_Options.print_z3_statistics ()  in
                   if uu____3045 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3071  ->
                          match uu____3071 with
                          | (uu____3079,msg,range1) ->
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
      let uu____3106 =
        let uu____3108 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____3108  in
      if uu____3106
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
                | uu____3135 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____3143 = FStar_ST.op_Bang recorded_hints  in
           match uu____3143 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3199 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____3206 =
               let uu____3207 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____3207  in
             store_hint uu____3206
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3214 -> ())
  
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
              let uu____3325 = f q res  in
              (match uu____3325 with
               | FStar_Pervasives_Native.None  -> FStar_Util.Inr q
               | FStar_Pervasives_Native.Some errs -> aux (errs :: acc) qs2)
           in
        aux [] qs
  
let (full_query_id : query_settings -> Prims.string) =
  fun settings  ->
    let uu____3344 =
      let uu____3346 =
        let uu____3348 =
          let uu____3350 = FStar_Util.string_of_int settings.query_index  in
          Prims.op_Hat uu____3350 ")"  in
        Prims.op_Hat ", " uu____3348  in
      Prims.op_Hat settings.query_name uu____3346  in
    Prims.op_Hat "(" uu____3344
  
let rec collect : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l  ->
    let acc = []  in
    let rec add_one1 acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h,n1)::t ->
          if h = x
          then (h, (n1 + Prims.int_one)) :: t
          else (let uu____3480 = add_one1 t x  in (h, n1) :: uu____3480)
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
            (let uu____3536 =
               let uu____3543 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3556,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____3582,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____3605 = FStar_Ident.text_of_lid q  in
                     (uu____3605, n1)
                  in
               match uu____3543 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____3623 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____3625 =
                       let uu____3627 = FStar_Options.z3_rlimit ()  in
                       uu____3627 * (Prims.parse_int "544656")  in
                     uu____3623 * uu____3625  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____3634 = FStar_TypeChecker_Env.get_range env  in
                     let uu____3635 = FStar_Options.initial_fuel ()  in
                     let uu____3637 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3634;
                       query_fuel = uu____3635;
                       query_ifuel = uu____3637;
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
                              { FStar_Util.hint_name = uu____3646;
                                FStar_Util.hint_index = uu____3647;
                                FStar_Util.fuel = uu____3648;
                                FStar_Util.ifuel = uu____3649;
                                FStar_Util.unsat_core = uu____3650;
                                FStar_Util.query_elapsed_time = uu____3651;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____3536 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3679;
                         FStar_Util.hint_index = uu____3680;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3684;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___448_3701 = default_settings  in
                         {
                           query_env = (uu___448_3701.query_env);
                           query_decl = (uu___448_3701.query_decl);
                           query_name = (uu___448_3701.query_name);
                           query_index = (uu___448_3701.query_index);
                           query_range = (uu___448_3701.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___448_3701.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___448_3701.query_errors);
                           query_all_labels =
                             (uu___448_3701.query_all_labels);
                           query_suffix = (uu___448_3701.query_suffix);
                           query_hash = (uu___448_3701.query_hash)
                         })]
                   | uu____3705 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____3711 =
                     let uu____3713 = FStar_Options.max_ifuel ()  in
                     let uu____3715 = FStar_Options.initial_ifuel ()  in
                     uu____3713 > uu____3715  in
                   if uu____3711
                   then
                     let uu____3720 =
                       let uu___453_3721 = default_settings  in
                       let uu____3722 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___453_3721.query_env);
                         query_decl = (uu___453_3721.query_decl);
                         query_name = (uu___453_3721.query_name);
                         query_index = (uu___453_3721.query_index);
                         query_range = (uu___453_3721.query_range);
                         query_fuel = (uu___453_3721.query_fuel);
                         query_ifuel = uu____3722;
                         query_rlimit = (uu___453_3721.query_rlimit);
                         query_hint = (uu___453_3721.query_hint);
                         query_errors = (uu___453_3721.query_errors);
                         query_all_labels = (uu___453_3721.query_all_labels);
                         query_suffix = (uu___453_3721.query_suffix);
                         query_hash = (uu___453_3721.query_hash)
                       }  in
                     [uu____3720]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____3729 =
                     let uu____3731 =
                       let uu____3733 = FStar_Options.max_fuel ()  in
                       uu____3733 / (Prims.of_int (2))  in
                     let uu____3736 = FStar_Options.initial_fuel ()  in
                     uu____3731 > uu____3736  in
                   if uu____3729
                   then
                     let uu____3741 =
                       let uu___457_3742 = default_settings  in
                       let uu____3743 =
                         let uu____3745 = FStar_Options.max_fuel ()  in
                         uu____3745 / (Prims.of_int (2))  in
                       let uu____3748 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___457_3742.query_env);
                         query_decl = (uu___457_3742.query_decl);
                         query_name = (uu___457_3742.query_name);
                         query_index = (uu___457_3742.query_index);
                         query_range = (uu___457_3742.query_range);
                         query_fuel = uu____3743;
                         query_ifuel = uu____3748;
                         query_rlimit = (uu___457_3742.query_rlimit);
                         query_hint = (uu___457_3742.query_hint);
                         query_errors = (uu___457_3742.query_errors);
                         query_all_labels = (uu___457_3742.query_all_labels);
                         query_suffix = (uu___457_3742.query_suffix);
                         query_hash = (uu___457_3742.query_hash)
                       }  in
                     [uu____3741]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____3755 =
                     (let uu____3761 = FStar_Options.max_fuel ()  in
                      let uu____3763 = FStar_Options.initial_fuel ()  in
                      uu____3761 > uu____3763) &&
                       (let uu____3767 = FStar_Options.max_ifuel ()  in
                        let uu____3769 = FStar_Options.initial_ifuel ()  in
                        uu____3767 >= uu____3769)
                      in
                   if uu____3755
                   then
                     let uu____3774 =
                       let uu___461_3775 = default_settings  in
                       let uu____3776 = FStar_Options.max_fuel ()  in
                       let uu____3778 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___461_3775.query_env);
                         query_decl = (uu___461_3775.query_decl);
                         query_name = (uu___461_3775.query_name);
                         query_index = (uu___461_3775.query_index);
                         query_range = (uu___461_3775.query_range);
                         query_fuel = uu____3776;
                         query_ifuel = uu____3778;
                         query_rlimit = (uu___461_3775.query_rlimit);
                         query_hint = (uu___461_3775.query_hint);
                         query_errors = (uu___461_3775.query_errors);
                         query_all_labels = (uu___461_3775.query_all_labels);
                         query_suffix = (uu___461_3775.query_suffix);
                         query_hash = (uu___461_3775.query_hash)
                       }  in
                     [uu____3774]
                   else []  in
                 let min_fuel1 =
                   let uu____3785 =
                     let uu____3787 = FStar_Options.min_fuel ()  in
                     let uu____3789 = FStar_Options.initial_fuel ()  in
                     uu____3787 < uu____3789  in
                   if uu____3785
                   then
                     let uu____3794 =
                       let uu___465_3795 = default_settings  in
                       let uu____3796 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___465_3795.query_env);
                         query_decl = (uu___465_3795.query_decl);
                         query_name = (uu___465_3795.query_name);
                         query_index = (uu___465_3795.query_index);
                         query_range = (uu___465_3795.query_range);
                         query_fuel = uu____3796;
                         query_ifuel = Prims.int_one;
                         query_rlimit = (uu___465_3795.query_rlimit);
                         query_hint = (uu___465_3795.query_hint);
                         query_errors = (uu___465_3795.query_errors);
                         query_all_labels = (uu___465_3795.query_all_labels);
                         query_suffix = (uu___465_3795.query_suffix);
                         query_hash = (uu___465_3795.query_hash)
                       }  in
                     [uu____3794]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 =
                   (let uu____3811 = FStar_Options.z3_refresh ()  in
                    if uu____3811
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3816 = with_fuel_and_diagnostics config1 []  in
                    let uu____3819 =
                      let uu____3822 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____3822  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3816
                      uu____3819 (used_hint config1))
                    in
                 let check_all_configs configs =
                   fold_queries configs check_one_config process_result  in
                 let quake_and_check_all_configs configs =
                   let lo = FStar_Options.quake_lo ()  in
                   let hi = FStar_Options.quake_hi ()  in
                   let seed = FStar_Options.z3_seed ()  in
                   let name = full_query_id default_settings  in
                   let quaking = hi > Prims.int_one  in
                   let hi1 = if hi < Prims.int_one then Prims.int_one else hi
                      in
                   let lo1 =
                     if lo < Prims.int_one
                     then Prims.int_one
                     else if lo > hi1 then hi1 else lo  in
                   let run_one seed1 =
                     let uu____3900 = FStar_Options.z3_refresh ()  in
                     if uu____3900
                     then
                       FStar_Options.with_saved_options
                         (fun uu____3917  ->
                            FStar_Options.set_option "z3seed"
                              (FStar_Options.Int seed1);
                            check_all_configs configs)
                     else check_all_configs configs  in
                   let rec fold_nat' f acc lo2 hi2 =
                     if lo2 > hi2
                     then acc
                     else
                       (let uu____3973 = f acc lo2  in
                        fold_nat' f uu____3973 (lo2 + Prims.int_one) hi2)
                      in
                   let best_fuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                   let best_ifuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None  in
                   let maybe_improve r n1 =
                     let uu____4096 = FStar_ST.op_Bang r  in
                     match uu____4096 with
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
                   let uu____4184 =
                     fold_nat'
                       (fun uu____4218  ->
                          fun n1  ->
                            match uu____4218 with
                            | (nsucc,rs) ->
                                let r = run_one (seed + n1)  in
                                let nsucc1 =
                                  match r with
                                  | FStar_Util.Inr cfg ->
                                      (maybe_improve best_fuel cfg.query_fuel;
                                       maybe_improve best_ifuel
                                         cfg.query_ifuel;
                                       nsucc + Prims.int_one)
                                  | uu____4283 -> nsucc  in
                                ((let uu____4291 =
                                    (quaking &&
                                       ((FStar_Options.interactive ()) ||
                                          (FStar_Options.debug_any ())))
                                      && (n1 < (hi1 - Prims.int_one))
                                     in
                                  if uu____4291
                                  then
                                    let uu____4295 =
                                      FStar_Util.string_of_int nsucc1  in
                                    let uu____4297 =
                                      FStar_Util.string_of_int
                                        ((n1 + Prims.int_one) - nsucc1)
                                       in
                                    let uu____4300 =
                                      FStar_Util.string_of_int
                                        ((hi1 - Prims.int_one) - n1)
                                       in
                                    FStar_Util.print4
                                      "Quake: so far query %s succeeded %s times and failed %s (%s runs remain)\n"
                                      name uu____4295 uu____4297 uu____4300
                                  else ());
                                 (nsucc1, (r :: rs)))) (Prims.int_zero, [])
                       Prims.int_zero (hi1 - Prims.int_one)
                      in
                   match uu____4184 with
                   | (nsuccess,rs) ->
                       (if quaking
                        then
                          (let fuel_msg =
                             let uu____4363 =
                               let uu____4374 = FStar_ST.op_Bang best_fuel
                                  in
                               let uu____4403 = FStar_ST.op_Bang best_ifuel
                                  in
                               (uu____4374, uu____4403)  in
                             match uu____4363 with
                             | (FStar_Pervasives_Native.Some
                                f,FStar_Pervasives_Native.Some i) ->
                                 let uu____4451 = FStar_Util.string_of_int f
                                    in
                                 let uu____4453 = FStar_Util.string_of_int i
                                    in
                                 FStar_Util.format2
                                   " (best fuel=%s, best ifuel=%s)"
                                   uu____4451 uu____4453
                             | (uu____4456,uu____4457) -> ""  in
                           let uu____4471 = FStar_Util.string_of_int nsuccess
                              in
                           let uu____4473 = FStar_Util.string_of_int hi1  in
                           FStar_Util.print4
                             "Quake: query %s succeeded %s/%s times%s\n" name
                             uu____4471 uu____4473 fuel_msg)
                        else ();
                        if nsuccess < lo1
                        then
                          (let report1 errs =
                             report_errors
                               (let uu___538_4491 = default_settings  in
                                {
                                  query_env = (uu___538_4491.query_env);
                                  query_decl = (uu___538_4491.query_decl);
                                  query_name = (uu___538_4491.query_name);
                                  query_index = (uu___538_4491.query_index);
                                  query_range = (uu___538_4491.query_range);
                                  query_fuel = (uu___538_4491.query_fuel);
                                  query_ifuel = (uu___538_4491.query_ifuel);
                                  query_rlimit = (uu___538_4491.query_rlimit);
                                  query_hint = (uu___538_4491.query_hint);
                                  query_errors = errs;
                                  query_all_labels =
                                    (uu___538_4491.query_all_labels);
                                  query_suffix = (uu___538_4491.query_suffix);
                                  query_hash = (uu___538_4491.query_hash)
                                })
                              in
                           let all_errs =
                             FStar_List.concatMap
                               (fun uu___4_4507  ->
                                  match uu___4_4507 with
                                  | FStar_Util.Inr uu____4518 -> []
                                  | FStar_Util.Inl es -> [es]) rs
                              in
                           (let uu____4533 = FStar_Options.query_stats ()  in
                            if uu____4533
                            then FStar_List.iter report1 all_errs
                            else
                              (let errs = FStar_List.flatten all_errs  in
                               let errs1 = collect errs  in
                               let tag_er n1 er =
                                 if n1 <= Prims.int_one
                                 then er
                                 else
                                   (let uu___553_4568 = er  in
                                    let uu____4569 =
                                      FStar_All.pipe_right er.error_messages
                                        (FStar_List.map
                                           (fun uu____4616  ->
                                              match uu____4616 with
                                              | (e,m,r) ->
                                                  let m1 =
                                                    let uu____4638 =
                                                      let uu____4640 =
                                                        FStar_Util.string_of_int
                                                          n1
                                                         in
                                                      FStar_Util.format1
                                                        " (%s times)"
                                                        uu____4640
                                                       in
                                                    Prims.op_Hat m uu____4638
                                                     in
                                                  (e, m1, r)))
                                       in
                                    {
                                      error_reason =
                                        (uu___553_4568.error_reason);
                                      error_fuel = (uu___553_4568.error_fuel);
                                      error_ifuel =
                                        (uu___553_4568.error_ifuel);
                                      error_hint = (uu___553_4568.error_hint);
                                      error_messages = uu____4569
                                    })
                                  in
                               let tag_with_n n1 errs2 =
                                 FStar_List.map (tag_er n1) errs2  in
                               let errs2 =
                                 FStar_List.map
                                   (fun uu____4674  ->
                                      match uu____4674 with
                                      | (errs2,n1) -> tag_er n1 errs2) errs1
                                  in
                               report1 errs2));
                           (match () with
                            | () ->
                                let rng =
                                  match FStar_Pervasives_Native.snd
                                          env.FStar_TypeChecker_Env.qtbl_name_and_index
                                  with
                                  | FStar_Pervasives_Native.Some
                                      (l,uu____4696) ->
                                      FStar_Ident.range_of_lid l
                                  | uu____4704 -> FStar_Range.dummyRange  in
                                if quaking
                                then
                                  let uu____4713 =
                                    let uu____4723 =
                                      let uu____4731 =
                                        let uu____4733 =
                                          FStar_Util.string_of_int nsuccess
                                           in
                                        let uu____4735 =
                                          FStar_Util.string_of_int hi1  in
                                        let uu____4737 =
                                          FStar_Util.string_of_int lo1  in
                                        FStar_Util.format4
                                          "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s"
                                          name uu____4733 uu____4735
                                          uu____4737
                                         in
                                      (FStar_Errors.Error_QuakeFailed,
                                        uu____4731, rng)
                                       in
                                    [uu____4723]  in
                                  FStar_TypeChecker_Err.add_errors env
                                    uu____4713
                                else ()))
                        else ())
                    in
                 let uu____4759 =
                   let uu____4768 = FStar_Options.admit_smt_queries ()  in
                   let uu____4770 = FStar_Options.admit_except ()  in
                   (uu____4768, uu____4770)  in
                 (match uu____4759 with
                  | (true ,uu____4778) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      quake_and_check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let uu____4806 = full_query_id default_settings  in
                          uu____4806 <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then quake_and_check_all_configs all_configs
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
    let uu____5036 = FStar_Options.z3_seed ()  in
    let uu____5038 = FStar_Options.z3_cliopt ()  in
    let uu____5042 = FStar_Options.smtencoding_valid_intro ()  in
    let uu____5044 = FStar_Options.smtencoding_valid_elim ()  in
    {
      seed = uu____5036;
      cliopt = uu____5038;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____5042;
      valid_elim = uu____5044
    }
  
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____5052 =
      let uu____5055 = get_cfg env  in
      FStar_Pervasives_Native.Some uu____5055  in
    FStar_ST.op_Colon_Equals _last_cfg uu____5052
  
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env  ->
    let uu____5086 = FStar_ST.op_Bang _last_cfg  in
    match uu____5086 with
    | FStar_Pervasives_Native.None  -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____5116 = let uu____5118 = get_cfg env  in cfg = uu____5118
           in
        Prims.op_Negation uu____5116
  
let (do_solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____5147 = should_refresh tcenv  in
         if uu____5147
         then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
         else ());
        (let uu____5154 =
           let uu____5156 =
             let uu____5158 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____5158  in
           FStar_Util.format1 "Starting query at %s" uu____5156  in
         FStar_SMTEncoding_Encode.push uu____5154);
        (let pop1 uu____5166 =
           let uu____5167 =
             let uu____5169 =
               let uu____5171 = FStar_TypeChecker_Env.get_range tcenv  in
               FStar_All.pipe_left FStar_Range.string_of_range uu____5171  in
             FStar_Util.format1 "Ending query at %s" uu____5169  in
           FStar_SMTEncoding_Encode.pop uu____5167  in
         try
           (fun uu___620_5187  ->
              match () with
              | () ->
                  let uu____5188 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q
                     in
                  (match uu____5188 with
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
                                     ,uu____5220);
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____5221;
                                  FStar_SMTEncoding_Term.rng = uu____5222;_};
                              FStar_SMTEncoding_Term.assumption_caption =
                                uu____5223;
                              FStar_SMTEncoding_Term.assumption_name =
                                uu____5224;
                              FStar_SMTEncoding_Term.assumption_fact_ids =
                                uu____5225;_}
                            -> pop1 ()
                        | uu____5245 when tcenv1.FStar_TypeChecker_Env.admit
                            -> pop1 ()
                        | FStar_SMTEncoding_Term.Assume uu____5246 ->
                            (ask_and_report_errors tcenv1 labels prefix1 qry
                               suffix;
                             pop1 ())
                        | uu____5248 -> failwith "Impossible"))) ()
         with
         | FStar_SMTEncoding_Env.Inner_let_rec names1 ->
             (pop1 ();
              (let uu____5264 =
                 let uu____5274 =
                   let uu____5282 =
                     let uu____5284 =
                       let uu____5286 =
                         FStar_List.map FStar_Pervasives_Native.fst names1
                          in
                       FStar_String.concat "," uu____5286  in
                     FStar_Util.format1
                       "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                       uu____5284
                      in
                   (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                     uu____5282, (tcenv.FStar_TypeChecker_Env.range))
                    in
                 [uu____5274]  in
               FStar_TypeChecker_Err.add_errors tcenv uu____5264)))
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        let uu____5341 = FStar_Options.no_smt ()  in
        if uu____5341
        then
          let uu____5344 =
            let uu____5354 =
              let uu____5362 =
                let uu____5364 = FStar_Syntax_Print.term_to_string q  in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____5364
                 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____5362,
                (tcenv.FStar_TypeChecker_Env.range))
               in
            [uu____5354]  in
          FStar_TypeChecker_Err.add_errors tcenv uu____5344
        else do_solve use_env_msg tcenv q
  
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
           let uu____5396 =
             let uu____5403 = FStar_Options.peek ()  in (e, g, uu____5403)
              in
           [uu____5396]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____5419  -> ());
    FStar_TypeChecker_Env.push = (fun uu____5421  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____5424  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____5427  ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____5446  -> fun uu____5447  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____5462  -> fun uu____5463  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____5469 =
             let uu____5476 = FStar_Options.peek ()  in (e, g, uu____5476)
              in
           [uu____5469]);
    FStar_TypeChecker_Env.solve =
      (fun uu____5492  -> fun uu____5493  -> fun uu____5494  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____5501  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____5503  -> ())
  } 
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
      (let uu____151 = FStar_Options.use_hints ()  in
       if uu____151
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____158 = FStar_Options.hint_file ()  in
           match uu____158 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____167 = FStar_Util.read_hints val_filename  in
         match uu____167 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____180 = FStar_Options.hint_info ()  in
               if uu____180
               then
                 let uu____183 =
                   let uu____185 = FStar_Options.hint_file ()  in
                   match uu____185 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____195 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____183
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____235 = FStar_Options.hint_info ()  in
             (if uu____235
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____252 = FStar_Options.record_hints ()  in
     if uu____252
     then
       let hints =
         let uu____256 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____256  in
       let hints_db =
         let uu____287 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____287; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____293 = FStar_Options.hint_file ()  in
         match uu____293 with
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
        | uu____540 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_548  ->
                     match uu___1_548 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____555 -> false)))
              ||
              (let uu____558 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____558)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___2_582 =
          match uu___2_582 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____604 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____614 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____637 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____637
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____655 ->
                   let uu____656 = keep_decl d  in
                   if uu____656 then d :: out else out) [] theory_rev
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
            let uu____820 = filter_using_facts_from e theory  in
            (uu____820, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____841 =
              let uu____852 =
                let uu____863 =
                  let uu____866 =
                    let uu____867 =
                      let uu____869 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____869  in
                    FStar_SMTEncoding_Term.Caption uu____867  in
                  [uu____866]  in
                (uu____863, (Prims.parse_int "0"), (Prims.parse_int "0"))  in
              FStar_List.fold_left
                (fun uu____899  ->
                   fun d  ->
                     match uu____899 with
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
                              let uu____1000 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____1000
                                (fun uu____1060  ->
                                   match uu____1060 with
                                   | (decls1,uu____1085,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____1105 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____852 theory_rev
               in
            (match uu____841 with
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
        let uu____1275 = filter_assertions_with_stats e core theory  in
        match uu____1275 with
        | (theory1,b,uu____1298,uu____1299) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____1443 = filter_using_facts_from e x  in (uu____1443, false)
  
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
    let uu____1748 = FStar_Util.string_of_int err.error_fuel  in
    let uu____1750 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____1748 uu____1750
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
      let uu____5418 =
        let uu____5421 =
          let uu____5422 =
            let uu____5424 = FStar_Util.string_of_int n1  in
            let uu____5426 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____5424 uu____5426
             in
          FStar_SMTEncoding_Term.Caption uu____5422  in
        let uu____5429 =
          let uu____5432 =
            let uu____5433 =
              let uu____5444 =
                let uu____5451 =
                  let uu____5462 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____5479 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____5462, uu____5479)  in
                FStar_SMTEncoding_Util.mkEq uu____5451  in
              (uu____5444, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____5433  in
          let uu____5498 =
            let uu____5501 =
              let uu____5502 =
                let uu____5513 =
                  let uu____5520 =
                    let uu____5531 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____5548 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____5531, uu____5548)  in
                  FStar_SMTEncoding_Util.mkEq uu____5520  in
                (uu____5513, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____5502  in
            [uu____5501; settings.query_decl]  in
          uu____5432 :: uu____5498  in
        uu____5421 :: uu____5429  in
      let uu____5567 =
        let uu____5570 =
          let uu____5573 =
            let uu____5576 =
              let uu____5577 =
                let uu____5584 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____5584)  in
              FStar_SMTEncoding_Term.SetOption uu____5577  in
            [uu____5576;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____5589 =
            let uu____5592 =
              let uu____5595 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____5595
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____5592 settings.query_suffix  in
          FStar_List.append uu____5573 uu____5589  in
        FStar_List.append label_assumptions uu____5570  in
      FStar_List.append uu____5418 uu____5567
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____5770 = FStar_ST.op_Bang replaying_hints  in
      match uu____5770 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_5824  ->
               match uu___3_5824 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____5867 -> FStar_Pervasives_Native.None)
      | uu____5884 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____6063 -> FStar_Pervasives_Native.None
      | uu____6069 ->
          let uu____6070 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____6070 with
           | (msg,error_labels) ->
               let err =
                 let uu____6098 =
                   FStar_List.map
                     (fun uu____6126  ->
                        match uu____6126 with
                        | (uu____6141,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____6098
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____6307 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____6307
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____6310 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____6350 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____6350
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____6399 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____6399)
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
            match err.error_messages with | [] -> false | uu____6510 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____6542 = find_localized_errors errs  in
    FStar_Option.isSome uu____6542
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____6696 = find_localized_errors settings.query_errors  in
     match uu____6696 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____6736 =
                    let uu____6738 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____6738  in
                  FStar_Errors.diag settings.query_range uu____6736));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____6748 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____6776 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____6776))
              in
           FStar_All.pipe_right uu____6748 (FStar_String.concat "; ")  in
         let uu____6784 =
           let uu____6794 =
             let uu____6802 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____6802,
               (settings.query_range))
              in
           [uu____6794]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____6784);
    (let uu____6820 =
       (FStar_Options.detail_errors ()) &&
         (let uu____6823 = FStar_Options.n_cores ()  in
          uu____6823 = (Prims.parse_int "1"))
        in
     if uu____6820
     then
       let initial_fuel1 =
         let uu___235_6963 = settings  in
         let uu____7098 = FStar_Options.initial_fuel ()  in
         let uu____7100 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___235_6963.query_env);
           query_decl = (uu___235_6963.query_decl);
           query_name = (uu___235_6963.query_name);
           query_index = (uu___235_6963.query_index);
           query_range = (uu___235_6963.query_range);
           query_fuel = uu____7098;
           query_ifuel = uu____7100;
           query_rlimit = (uu___235_6963.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___235_6963.query_errors);
           query_all_labels = (uu___235_6963.query_all_labels);
           query_suffix = (uu___235_6963.query_suffix);
           query_hash = (uu___235_6963.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____7143 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____7143
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____7192 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____7192)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____7421 =
          let r = FStar_Util.mk_ref []  in
          let uu____7432 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____7532  ->
                 let uu____7533 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____7533
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____7432 with | (add1,get1) -> (add1, get1)  in
        let uu____7615 = accumulator ()  in
        match uu____7615 with
        | (add_module_name,get_module_names) ->
            let uu____7652 = accumulator ()  in
            (match uu____7652 with
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
                                  let uu____7775 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____7775
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
                         | uu____7820 ->
                             let uu____7824 = FStar_Util.prefix components
                                in
                             (match uu____7824 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____7851 = exclude_suffix last1  in
                                    FStar_List.append module_name uu____7851
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____7858::[] -> ()
                                    | uu____7862 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____7879 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____7879])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____7906 =
                          let uu____7908 = get_module_names ()  in
                          FStar_All.pipe_right uu____7908
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____7906);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____7921 =
                          let uu____7923 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____7923
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____7921))))
         in
      let uu____7933 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____7933
      then
        let uu____7936 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____7936 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____7955 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____7969 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____7955 with
             | (tag,core) ->
                 let range =
                   let uu____7982 =
                     let uu____7984 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____7984 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____7982  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____7998 = FStar_Options.query_stats ()  in
                   if uu____7998
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
                     let uu____8032 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____8032 "}"
                   else ""  in
                 ((let uu____8041 =
                     let uu____8045 =
                       let uu____8049 =
                         let uu____8053 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____8055 =
                           let uu____8059 =
                             let uu____8063 =
                               let uu____8067 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____8069 =
                                 let uu____8073 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____8075 =
                                   let uu____8079 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____8081 =
                                     let uu____8085 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____8085; stats]  in
                                   uu____8079 :: uu____8081  in
                                 uu____8073 :: uu____8075  in
                               uu____8067 :: uu____8069  in
                             used_hint_tag :: uu____8063  in
                           tag :: uu____8059  in
                         uu____8053 :: uu____8055  in
                       (settings.query_name) :: uu____8049  in
                     range :: uu____8045  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____8041);
                  (let uu____8100 = FStar_Options.print_z3_statistics ()  in
                   if uu____8100 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____8126  ->
                          match uu____8126 with
                          | (uu____8134,msg,range1) ->
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
      let uu____8305 =
        let uu____8307 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____8307  in
      if uu____8305
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
                | uu____8355 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____8377 = FStar_ST.op_Bang recorded_hints  in
           match uu____8377 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____8461 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____8468 =
               let uu____8483 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____8483  in
             store_hint uu____8468
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____8504 -> ())
  
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
                     let uu____9633 = f q res  in
                     match uu____9633 with
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
            (let uu____9810 =
               let uu____9891 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____9904,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____9938,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____9977 = FStar_Ident.text_of_lid q  in
                     (uu____9977, n1)
                  in
               match uu____9891 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____10069 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____10071 =
                       let uu____10073 = FStar_Options.z3_rlimit ()  in
                       uu____10073 * (Prims.parse_int "544656")  in
                     uu____10069 * uu____10071  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____10221 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____10222 = FStar_Options.initial_fuel ()  in
                     let uu____10224 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____10221;
                       query_fuel = uu____10222;
                       query_ifuel = uu____10224;
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
                              { FStar_Util.hint_name = uu____10245;
                                FStar_Util.hint_index = uu____10246;
                                FStar_Util.fuel = uu____10247;
                                FStar_Util.ifuel = uu____10248;
                                FStar_Util.unsat_core = uu____10249;
                                FStar_Util.query_elapsed_time = uu____10250;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____9810 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____10641;
                         FStar_Util.hint_index = uu____10642;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____10646;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___424_10737 = default_settings  in
                         {
                           query_env = (uu___424_10737.query_env);
                           query_decl = (uu___424_10737.query_decl);
                           query_name = (uu___424_10737.query_name);
                           query_index = (uu___424_10737.query_index);
                           query_range = (uu___424_10737.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___424_10737.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___424_10737.query_errors);
                           query_all_labels =
                             (uu___424_10737.query_all_labels);
                           query_suffix = (uu___424_10737.query_suffix);
                           query_hash = (uu___424_10737.query_hash)
                         })]
                   | uu____10942 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____11089 =
                     let uu____11091 = FStar_Options.max_ifuel ()  in
                     let uu____11093 = FStar_Options.initial_ifuel ()  in
                     uu____11091 > uu____11093  in
                   if uu____11089
                   then
                     let uu____11165 =
                       let uu___429_11300 = default_settings  in
                       let uu____11435 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___429_11300.query_env);
                         query_decl = (uu___429_11300.query_decl);
                         query_name = (uu___429_11300.query_name);
                         query_index = (uu___429_11300.query_index);
                         query_range = (uu___429_11300.query_range);
                         query_fuel = (uu___429_11300.query_fuel);
                         query_ifuel = uu____11435;
                         query_rlimit = (uu___429_11300.query_rlimit);
                         query_hint = (uu___429_11300.query_hint);
                         query_errors = (uu___429_11300.query_errors);
                         query_all_labels = (uu___429_11300.query_all_labels);
                         query_suffix = (uu___429_11300.query_suffix);
                         query_hash = (uu___429_11300.query_hash)
                       }  in
                     [uu____11165]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____11710 =
                     let uu____11712 =
                       let uu____11714 = FStar_Options.max_fuel ()  in
                       uu____11714 / (Prims.parse_int "2")  in
                     let uu____11717 = FStar_Options.initial_fuel ()  in
                     uu____11712 > uu____11717  in
                   if uu____11710
                   then
                     let uu____11789 =
                       let uu___433_11924 = default_settings  in
                       let uu____12059 =
                         let uu____12061 = FStar_Options.max_fuel ()  in
                         uu____12061 / (Prims.parse_int "2")  in
                       let uu____12064 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___433_11924.query_env);
                         query_decl = (uu___433_11924.query_decl);
                         query_name = (uu___433_11924.query_name);
                         query_index = (uu___433_11924.query_index);
                         query_range = (uu___433_11924.query_range);
                         query_fuel = uu____12059;
                         query_ifuel = uu____12064;
                         query_rlimit = (uu___433_11924.query_rlimit);
                         query_hint = (uu___433_11924.query_hint);
                         query_errors = (uu___433_11924.query_errors);
                         query_all_labels = (uu___433_11924.query_all_labels);
                         query_suffix = (uu___433_11924.query_suffix);
                         query_hash = (uu___433_11924.query_hash)
                       }  in
                     [uu____11789]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____12339 =
                     (let uu____12345 = FStar_Options.max_fuel ()  in
                      let uu____12347 = FStar_Options.initial_fuel ()  in
                      uu____12345 > uu____12347) &&
                       (let uu____12351 = FStar_Options.max_ifuel ()  in
                        let uu____12353 = FStar_Options.initial_ifuel ()  in
                        uu____12351 >= uu____12353)
                      in
                   if uu____12339
                   then
                     let uu____12425 =
                       let uu___437_12560 = default_settings  in
                       let uu____12695 = FStar_Options.max_fuel ()  in
                       let uu____12697 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___437_12560.query_env);
                         query_decl = (uu___437_12560.query_decl);
                         query_name = (uu___437_12560.query_name);
                         query_index = (uu___437_12560.query_index);
                         query_range = (uu___437_12560.query_range);
                         query_fuel = uu____12695;
                         query_ifuel = uu____12697;
                         query_rlimit = (uu___437_12560.query_rlimit);
                         query_hint = (uu___437_12560.query_hint);
                         query_errors = (uu___437_12560.query_errors);
                         query_all_labels = (uu___437_12560.query_all_labels);
                         query_suffix = (uu___437_12560.query_suffix);
                         query_hash = (uu___437_12560.query_hash)
                       }  in
                     [uu____12425]
                   else []  in
                 let min_fuel1 =
                   let uu____12972 =
                     let uu____12974 = FStar_Options.min_fuel ()  in
                     let uu____12976 = FStar_Options.initial_fuel ()  in
                     uu____12974 < uu____12976  in
                   if uu____12972
                   then
                     let uu____13048 =
                       let uu___441_13183 = default_settings  in
                       let uu____13318 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___441_13183.query_env);
                         query_decl = (uu___441_13183.query_decl);
                         query_name = (uu___441_13183.query_name);
                         query_index = (uu___441_13183.query_index);
                         query_range = (uu___441_13183.query_range);
                         query_fuel = uu____13318;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___441_13183.query_rlimit);
                         query_hint = (uu___441_13183.query_hint);
                         query_errors = (uu___441_13183.query_errors);
                         query_all_labels = (uu___441_13183.query_all_labels);
                         query_suffix = (uu___441_13183.query_suffix);
                         query_hash = (uu___441_13183.query_hash)
                       }  in
                     [uu____13048]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____14157 = FStar_Options.z3_refresh ()  in
                    if uu____14157
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____14162 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____14165 =
                      let uu____14168 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____14168  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____14162
                      uu____14165 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___454_14335 = default_settings  in
                        {
                          query_env = (uu___454_14335.query_env);
                          query_decl = (uu___454_14335.query_decl);
                          query_name = (uu___454_14335.query_name);
                          query_index = (uu___454_14335.query_index);
                          query_range = (uu___454_14335.query_range);
                          query_fuel = (uu___454_14335.query_fuel);
                          query_ifuel = (uu___454_14335.query_ifuel);
                          query_rlimit = (uu___454_14335.query_rlimit);
                          query_hint = (uu___454_14335.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___454_14335.query_all_labels);
                          query_suffix = (uu___454_14335.query_suffix);
                          query_hash = (uu___454_14335.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____14470 =
                   let uu____14479 = FStar_Options.admit_smt_queries ()  in
                   let uu____14481 = FStar_Options.admit_except ()  in
                   (uu____14479, uu____14481)  in
                 (match uu____14470 with
                  | (true ,uu____14489) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____14519 =
                              let uu____14521 =
                                let uu____14523 =
                                  let uu____14525 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____14525 ")"  in
                                Prims.op_Hat ", " uu____14523  in
                              Prims.op_Hat default_settings.query_name
                                uu____14521
                               in
                            Prims.op_Hat "(" uu____14519  in
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
        (let uu____14681 =
           let uu____14683 =
             let uu____14685 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____14685  in
           FStar_Util.format1 "Starting query at %s" uu____14683  in
         FStar_SMTEncoding_Encode.push uu____14681);
        (let uu____14688 = FStar_Options.no_smt ()  in
         if uu____14688
         then
           let uu____14691 =
             let uu____14701 =
               let uu____14709 =
                 let uu____14711 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____14711
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____14709,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____14701]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____14691
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____14840 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____14840 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____14876 =
                  let uu____14877 =
                    let uu____14879 =
                      let uu____14881 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____14881
                       in
                    FStar_Util.format1 "Ending query at %s" uu____14879  in
                  FStar_SMTEncoding_Encode.pop uu____14877  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____14884);
                           FStar_SMTEncoding_Term.freevars = uu____14885;
                           FStar_SMTEncoding_Term.rng = uu____14886;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____14887;
                       FStar_SMTEncoding_Term.assumption_name = uu____14888;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____14889;_}
                     -> pop1 ()
                 | uu____14915 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____14916 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____14925 -> failwith "Impossible")))
  
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
           let uu____15013 =
             let uu____15078 = FStar_Options.peek ()  in (e, g, uu____15078)
              in
           [uu____15013]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____15290  -> ());
    FStar_TypeChecker_Env.push = (fun uu____15346  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____15349  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____15352  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____15371  -> fun uu____15372  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____15387  -> fun uu____15388  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____15511 =
             let uu____15576 = FStar_Options.peek ()  in (e, g, uu____15576)
              in
           [uu____15511]);
    FStar_TypeChecker_Env.solve =
      (fun uu____15766  -> fun uu____15767  -> fun uu____15768  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____15833  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____15835  -> ())
  } 
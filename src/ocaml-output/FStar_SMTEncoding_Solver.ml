open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____70895 'Auu____70896 'Auu____70897 .
    ('Auu____70895,('Auu____70896 * 'Auu____70897)) FStar_Util.either ->
      ('Auu____70895,'Auu____70896) FStar_Util.either
  =
  fun uu___633_70914  ->
    match uu___633_70914 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____70929) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____70987 . Prims.string -> 'Auu____70987 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____71001 = FStar_Options.record_hints ()  in
       if uu____71001
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____71031 = FStar_Options.use_hints ()  in
       if uu____71031
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____71038 = FStar_Options.hint_file ()  in
           match uu____71038 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____71047 = FStar_Util.read_hints val_filename  in
         match uu____71047 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____71054 = FStar_Options.hint_info ()  in
               if uu____71054
               then
                 let uu____71057 =
                   let uu____71059 = FStar_Options.hint_file ()  in
                   match uu____71059 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____71069 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   uu____71057
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____71107 = FStar_Options.hint_info ()  in
             (if uu____71107
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____71124 = FStar_Options.record_hints ()  in
     if uu____71124
     then
       let hints =
         let uu____71128 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____71128  in
       let hints_db =
         let uu____71155 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____71155; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____71161 = FStar_Options.hint_file ()  in
         match uu____71161 with
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
        | uu____71286 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___634_71294  ->
                     match uu___634_71294 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____71297 -> false)))
              ||
              (let uu____71300 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____71300)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___635_71324 =
          match uu___635_71324 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____71339 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____71349 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____71372 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____71372
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____71390 ->
                   let uu____71391 = keep_decl d  in
                   if uu____71391 then d :: out else out) [] theory_rev
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
            let uu____71447 = filter_using_facts_from e theory  in
            (uu____71447, false, (Prims.parse_int "0"),
              (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____71468 =
              let uu____71479 =
                let uu____71490 =
                  let uu____71493 =
                    let uu____71494 =
                      let uu____71496 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____71496  in
                    FStar_SMTEncoding_Term.Caption uu____71494  in
                  [uu____71493]  in
                (uu____71490, (Prims.parse_int "0"), (Prims.parse_int "0"))
                 in
              FStar_List.fold_left
                (fun uu____71526  ->
                   fun d  ->
                     match uu____71526 with
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
                              let uu____71620 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____71620
                                (fun uu____71680  ->
                                   match uu____71680 with
                                   | (decls1,uu____71705,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____71725 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____71479 theory_rev
               in
            (match uu____71468 with
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
        let uu____71787 = filter_assertions_with_stats e core theory  in
        match uu____71787 with
        | (theory1,b,uu____71810,uu____71811) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____71847 = filter_using_facts_from e x  in (uu____71847, false)
  
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
    let uu____72077 = FStar_Util.string_of_int err.error_fuel  in
    let uu____72079 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____72077 uu____72079
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
      let uu____72618 =
        let uu____72621 =
          let uu____72622 =
            let uu____72624 = FStar_Util.string_of_int n1  in
            let uu____72626 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____72624
              uu____72626
             in
          FStar_SMTEncoding_Term.Caption uu____72622  in
        let uu____72629 =
          let uu____72632 =
            let uu____72633 =
              let uu____72641 =
                let uu____72642 =
                  let uu____72647 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____72652 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____72647, uu____72652)  in
                FStar_SMTEncoding_Util.mkEq uu____72642  in
              (uu____72641, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____72633  in
          let uu____72656 =
            let uu____72659 =
              let uu____72660 =
                let uu____72668 =
                  let uu____72669 =
                    let uu____72674 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____72679 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____72674, uu____72679)  in
                  FStar_SMTEncoding_Util.mkEq uu____72669  in
                (uu____72668, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____72660  in
            [uu____72659; settings.query_decl]  in
          uu____72632 :: uu____72656  in
        uu____72621 :: uu____72629  in
      let uu____72683 =
        let uu____72686 =
          let uu____72689 =
            let uu____72692 =
              let uu____72693 =
                let uu____72700 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____72700)  in
              FStar_SMTEncoding_Term.SetOption uu____72693  in
            [uu____72692;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____72705 =
            let uu____72708 =
              let uu____72711 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____72711
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____72708 settings.query_suffix  in
          FStar_List.append uu____72689 uu____72705  in
        FStar_List.append label_assumptions uu____72686  in
      FStar_List.append uu____72618 uu____72683
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____72745 = FStar_ST.op_Bang replaying_hints  in
      match uu____72745 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___636_72778  ->
               match uu___636_72778 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____72786 -> FStar_Pervasives_Native.None)
      | uu____72789 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____72807 ->
          FStar_Pervasives_Native.None
      | uu____72808 ->
          let uu____72809 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____72809 with
           | (msg,error_labels) ->
               let err =
                 let uu____72822 =
                   FStar_List.map
                     (fun uu____72850  ->
                        match uu____72850 with
                        | (uu____72865,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____72822
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____72882 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____72882
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____72885 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____72905 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____72905
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____72956 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____72956)
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
            match err.error_messages with | [] -> false | uu____73034 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____73056 = find_localized_errors errs  in
    FStar_Option.isSome uu____73056
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____73066 = find_localized_errors settings.query_errors  in
     match uu____73066 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____73076 =
                    let uu____73078 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____73078  in
                  FStar_Errors.diag settings.query_range uu____73076));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____73083 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____73096 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____73096))
              in
           FStar_All.pipe_right uu____73083 (FStar_String.concat "; ")  in
         let uu____73104 =
           let uu____73114 =
             let uu____73122 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____73122,
               (settings.query_range))
              in
           [uu____73114]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____73104);
    (let uu____73140 =
       (FStar_Options.detail_errors ()) &&
         (let uu____73143 = FStar_Options.n_cores ()  in
          uu____73143 = (Prims.parse_int "1"))
        in
     if uu____73140
     then
       let initial_fuel1 =
         let uu___868_73149 = settings  in
         let uu____73150 = FStar_Options.initial_fuel ()  in
         let uu____73152 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___868_73149.query_env);
           query_decl = (uu___868_73149.query_decl);
           query_name = (uu___868_73149.query_name);
           query_index = (uu___868_73149.query_index);
           query_range = (uu___868_73149.query_range);
           query_fuel = uu____73150;
           query_ifuel = uu____73152;
           query_rlimit = (uu___868_73149.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___868_73149.query_errors);
           query_all_labels = (uu___868_73149.query_all_labels);
           query_suffix = (uu___868_73149.query_suffix);
           query_hash = (uu___868_73149.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____73175 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____73175
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____73226 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____73226)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____73313 =
          let r = FStar_Util.mk_ref []  in
          let uu____73324 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____73468  ->
                 let uu____73469 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____73469
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____73324 with | (add1,get1) -> (add1, get1)  in
        let uu____73573 = accumulator ()  in
        match uu____73573 with
        | (add_module_name,get_module_names) ->
            let uu____73610 = accumulator ()  in
            (match uu____73610 with
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
                                  let uu____73733 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____73733
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
                         | uu____73778 ->
                             let uu____73782 = FStar_Util.prefix components
                                in
                             (match uu____73782 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____73809 = exclude_suffix last1
                                       in
                                    FStar_List.append module_name uu____73809
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____73816::[] -> ()
                                    | uu____73820 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____73837 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____73837])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____73864 =
                          let uu____73866 = get_module_names ()  in
                          FStar_All.pipe_right uu____73866
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____73864);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____73879 =
                          let uu____73881 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____73881
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____73879))))
         in
      let uu____73891 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____73891
      then
        let uu____73894 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____73894 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____73913 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____73927 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____73913 with
             | (tag,core) ->
                 let range =
                   let uu____73940 =
                     let uu____73942 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____73942 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____73940  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____73956 = FStar_Options.query_stats ()  in
                   if uu____73956
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
                     let uu____73990 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____73990 "}"
                   else ""  in
                 ((let uu____73999 =
                     let uu____74003 =
                       let uu____74007 =
                         let uu____74011 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____74013 =
                           let uu____74017 =
                             let uu____74021 =
                               let uu____74025 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____74027 =
                                 let uu____74031 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____74033 =
                                   let uu____74037 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____74039 =
                                     let uu____74043 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____74043; stats]  in
                                   uu____74037 :: uu____74039  in
                                 uu____74031 :: uu____74033  in
                               uu____74025 :: uu____74027  in
                             used_hint_tag :: uu____74021  in
                           tag :: uu____74017  in
                         uu____74011 :: uu____74013  in
                       (settings.query_name) :: uu____74007  in
                     range :: uu____74003  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____73999);
                  (let uu____74058 = FStar_Options.print_z3_statistics ()  in
                   if uu____74058 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____74084  ->
                          match uu____74084 with
                          | (uu____74092,msg,range1) ->
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
      let uu____74119 =
        let uu____74121 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____74121  in
      if uu____74119
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
                | uu____74148 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____74156 = FStar_ST.op_Bang recorded_hints  in
           match uu____74156 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____74212 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____74219 =
               let uu____74220 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____74220  in
             store_hint uu____74219
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____74227 -> ())
  
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
                     let uu____74338 = f q res  in
                     match uu____74338 with
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
            (let uu____74377 =
               let uu____74384 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____74397,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____74423,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____74446 = FStar_Ident.text_of_lid q  in
                     (uu____74446, n1)
                  in
               match uu____74384 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____74464 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____74466 =
                       let uu____74468 = FStar_Options.z3_rlimit ()  in
                       uu____74468 * (Prims.parse_int "544656")  in
                     uu____74464 * uu____74466  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____74475 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____74476 = FStar_Options.initial_fuel ()  in
                     let uu____74478 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____74475;
                       query_fuel = uu____74476;
                       query_ifuel = uu____74478;
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
                              { FStar_Util.hint_name = uu____74487;
                                FStar_Util.hint_index = uu____74488;
                                FStar_Util.fuel = uu____74489;
                                FStar_Util.ifuel = uu____74490;
                                FStar_Util.unsat_core = uu____74491;
                                FStar_Util.query_elapsed_time = uu____74492;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____74377 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____74520;
                         FStar_Util.hint_index = uu____74521;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____74525;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___1057_74542 = default_settings  in
                         {
                           query_env = (uu___1057_74542.query_env);
                           query_decl = (uu___1057_74542.query_decl);
                           query_name = (uu___1057_74542.query_name);
                           query_index = (uu___1057_74542.query_index);
                           query_range = (uu___1057_74542.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___1057_74542.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___1057_74542.query_errors);
                           query_all_labels =
                             (uu___1057_74542.query_all_labels);
                           query_suffix = (uu___1057_74542.query_suffix);
                           query_hash = (uu___1057_74542.query_hash)
                         })]
                   | uu____74546 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____74552 =
                     let uu____74554 = FStar_Options.max_ifuel ()  in
                     let uu____74556 = FStar_Options.initial_ifuel ()  in
                     uu____74554 > uu____74556  in
                   if uu____74552
                   then
                     let uu____74561 =
                       let uu___1062_74562 = default_settings  in
                       let uu____74563 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1062_74562.query_env);
                         query_decl = (uu___1062_74562.query_decl);
                         query_name = (uu___1062_74562.query_name);
                         query_index = (uu___1062_74562.query_index);
                         query_range = (uu___1062_74562.query_range);
                         query_fuel = (uu___1062_74562.query_fuel);
                         query_ifuel = uu____74563;
                         query_rlimit = (uu___1062_74562.query_rlimit);
                         query_hint = (uu___1062_74562.query_hint);
                         query_errors = (uu___1062_74562.query_errors);
                         query_all_labels =
                           (uu___1062_74562.query_all_labels);
                         query_suffix = (uu___1062_74562.query_suffix);
                         query_hash = (uu___1062_74562.query_hash)
                       }  in
                     [uu____74561]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____74570 =
                     let uu____74572 =
                       let uu____74574 = FStar_Options.max_fuel ()  in
                       uu____74574 / (Prims.parse_int "2")  in
                     let uu____74577 = FStar_Options.initial_fuel ()  in
                     uu____74572 > uu____74577  in
                   if uu____74570
                   then
                     let uu____74582 =
                       let uu___1066_74583 = default_settings  in
                       let uu____74584 =
                         let uu____74586 = FStar_Options.max_fuel ()  in
                         uu____74586 / (Prims.parse_int "2")  in
                       let uu____74589 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1066_74583.query_env);
                         query_decl = (uu___1066_74583.query_decl);
                         query_name = (uu___1066_74583.query_name);
                         query_index = (uu___1066_74583.query_index);
                         query_range = (uu___1066_74583.query_range);
                         query_fuel = uu____74584;
                         query_ifuel = uu____74589;
                         query_rlimit = (uu___1066_74583.query_rlimit);
                         query_hint = (uu___1066_74583.query_hint);
                         query_errors = (uu___1066_74583.query_errors);
                         query_all_labels =
                           (uu___1066_74583.query_all_labels);
                         query_suffix = (uu___1066_74583.query_suffix);
                         query_hash = (uu___1066_74583.query_hash)
                       }  in
                     [uu____74582]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____74596 =
                     (let uu____74602 = FStar_Options.max_fuel ()  in
                      let uu____74604 = FStar_Options.initial_fuel ()  in
                      uu____74602 > uu____74604) &&
                       (let uu____74608 = FStar_Options.max_ifuel ()  in
                        let uu____74610 = FStar_Options.initial_ifuel ()  in
                        uu____74608 >= uu____74610)
                      in
                   if uu____74596
                   then
                     let uu____74615 =
                       let uu___1070_74616 = default_settings  in
                       let uu____74617 = FStar_Options.max_fuel ()  in
                       let uu____74619 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1070_74616.query_env);
                         query_decl = (uu___1070_74616.query_decl);
                         query_name = (uu___1070_74616.query_name);
                         query_index = (uu___1070_74616.query_index);
                         query_range = (uu___1070_74616.query_range);
                         query_fuel = uu____74617;
                         query_ifuel = uu____74619;
                         query_rlimit = (uu___1070_74616.query_rlimit);
                         query_hint = (uu___1070_74616.query_hint);
                         query_errors = (uu___1070_74616.query_errors);
                         query_all_labels =
                           (uu___1070_74616.query_all_labels);
                         query_suffix = (uu___1070_74616.query_suffix);
                         query_hash = (uu___1070_74616.query_hash)
                       }  in
                     [uu____74615]
                   else []  in
                 let min_fuel1 =
                   let uu____74626 =
                     let uu____74628 = FStar_Options.min_fuel ()  in
                     let uu____74630 = FStar_Options.initial_fuel ()  in
                     uu____74628 < uu____74630  in
                   if uu____74626
                   then
                     let uu____74635 =
                       let uu___1074_74636 = default_settings  in
                       let uu____74637 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___1074_74636.query_env);
                         query_decl = (uu___1074_74636.query_decl);
                         query_name = (uu___1074_74636.query_name);
                         query_index = (uu___1074_74636.query_index);
                         query_range = (uu___1074_74636.query_range);
                         query_fuel = uu____74637;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___1074_74636.query_rlimit);
                         query_hint = (uu___1074_74636.query_hint);
                         query_errors = (uu___1074_74636.query_errors);
                         query_all_labels =
                           (uu___1074_74636.query_all_labels);
                         query_suffix = (uu___1074_74636.query_suffix);
                         query_hash = (uu___1074_74636.query_hash)
                       }  in
                     [uu____74635]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____74662 = FStar_Options.z3_refresh ()  in
                    if uu____74662
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____74667 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____74670 =
                      let uu____74673 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____74673  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____74667
                      uu____74670 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___1087_74696 = default_settings  in
                        {
                          query_env = (uu___1087_74696.query_env);
                          query_decl = (uu___1087_74696.query_decl);
                          query_name = (uu___1087_74696.query_name);
                          query_index = (uu___1087_74696.query_index);
                          query_range = (uu___1087_74696.query_range);
                          query_fuel = (uu___1087_74696.query_fuel);
                          query_ifuel = (uu___1087_74696.query_ifuel);
                          query_rlimit = (uu___1087_74696.query_rlimit);
                          query_hint = (uu___1087_74696.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___1087_74696.query_all_labels);
                          query_suffix = (uu___1087_74696.query_suffix);
                          query_hash = (uu___1087_74696.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____74697 =
                   let uu____74706 = FStar_Options.admit_smt_queries ()  in
                   let uu____74708 = FStar_Options.admit_except ()  in
                   (uu____74706, uu____74708)  in
                 (match uu____74697 with
                  | (true ,uu____74716) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____74746 =
                              let uu____74748 =
                                let uu____74750 =
                                  let uu____74752 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____74752 ")"  in
                                Prims.op_Hat ", " uu____74750  in
                              Prims.op_Hat default_settings.query_name
                                uu____74748
                               in
                            Prims.op_Hat "(" uu____74746  in
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
        (let uu____74792 =
           let uu____74794 =
             let uu____74796 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____74796  in
           FStar_Util.format1 "Starting query at %s" uu____74794  in
         FStar_SMTEncoding_Encode.push uu____74792);
        (let uu____74799 = FStar_Options.no_smt ()  in
         if uu____74799
         then
           let uu____74802 =
             let uu____74812 =
               let uu____74820 =
                 let uu____74822 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____74822
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____74820,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____74812]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____74802
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____74843 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____74843 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____74879 =
                  let uu____74880 =
                    let uu____74882 =
                      let uu____74884 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____74884
                       in
                    FStar_Util.format1 "Ending query at %s" uu____74882  in
                  FStar_SMTEncoding_Encode.pop uu____74880  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____74887);
                           FStar_SMTEncoding_Term.freevars = uu____74888;
                           FStar_SMTEncoding_Term.rng = uu____74889;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____74890;
                       FStar_SMTEncoding_Term.assumption_name = uu____74891;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____74892;_}
                     -> pop1 ()
                 | uu____74912 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____74913 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____74915 -> failwith "Impossible")))
  
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
           let uu____74923 =
             let uu____74930 = FStar_Options.peek ()  in (e, g, uu____74930)
              in
           [uu____74923]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____74946  -> ());
    FStar_TypeChecker_Env.push = (fun uu____74948  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____74951  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____74954  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____74973  -> fun uu____74974  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____74989  -> fun uu____74990  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____74996 =
             let uu____75003 = FStar_Options.peek ()  in (e, g, uu____75003)
              in
           [uu____74996]);
    FStar_TypeChecker_Env.solve =
      (fun uu____75019  -> fun uu____75020  -> fun uu____75021  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____75028  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____75030  -> ())
  } 
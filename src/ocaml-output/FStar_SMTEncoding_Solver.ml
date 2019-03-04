open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____70928 'Auu____70929 'Auu____70930 .
    ('Auu____70928,('Auu____70929 * 'Auu____70930)) FStar_Util.either ->
      ('Auu____70928,'Auu____70929) FStar_Util.either
  =
  fun uu___633_70947  ->
    match uu___633_70947 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____70962) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____71020 . Prims.string -> 'Auu____71020 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____71034 = FStar_Options.record_hints ()  in
       if uu____71034
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____71064 = FStar_Options.use_hints ()  in
       if uu____71064
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____71071 = FStar_Options.hint_file ()  in
           match uu____71071 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____71080 = FStar_Util.read_hints val_filename  in
         match uu____71080 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____71087 = FStar_Options.hint_info ()  in
               if uu____71087
               then
                 let uu____71090 =
                   let uu____71092 = FStar_Options.hint_file ()  in
                   match uu____71092 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____71102 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   uu____71090
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____71140 = FStar_Options.hint_info ()  in
             (if uu____71140
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____71157 = FStar_Options.record_hints ()  in
     if uu____71157
     then
       let hints =
         let uu____71161 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____71161  in
       let hints_db =
         let uu____71188 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____71188; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____71194 = FStar_Options.hint_file ()  in
         match uu____71194 with
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
        | uu____71319 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___634_71327  ->
                     match uu___634_71327 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____71330 -> false)))
              ||
              (let uu____71333 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____71333)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___635_71357 =
          match uu___635_71357 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____71372 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____71382 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____71405 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____71405
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____71423 ->
                   let uu____71424 = keep_decl d  in
                   if uu____71424 then d :: out else out) [] theory_rev
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
            let uu____71480 = filter_using_facts_from e theory  in
            (uu____71480, false, (Prims.parse_int "0"),
              (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____71501 =
              let uu____71512 =
                let uu____71523 =
                  let uu____71526 =
                    let uu____71527 =
                      let uu____71529 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____71529  in
                    FStar_SMTEncoding_Term.Caption uu____71527  in
                  [uu____71526]  in
                (uu____71523, (Prims.parse_int "0"), (Prims.parse_int "0"))
                 in
              FStar_List.fold_left
                (fun uu____71559  ->
                   fun d  ->
                     match uu____71559 with
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
                              let uu____71653 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____71653
                                (fun uu____71713  ->
                                   match uu____71713 with
                                   | (decls1,uu____71738,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____71758 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____71512 theory_rev
               in
            (match uu____71501 with
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
        let uu____71820 = filter_assertions_with_stats e core theory  in
        match uu____71820 with
        | (theory1,b,uu____71843,uu____71844) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____71880 = filter_using_facts_from e x  in (uu____71880, false)
  
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
    let uu____72110 = FStar_Util.string_of_int err.error_fuel  in
    let uu____72112 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____72110 uu____72112
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
      let uu____72651 =
        let uu____72654 =
          let uu____72655 =
            let uu____72657 = FStar_Util.string_of_int n1  in
            let uu____72659 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____72657
              uu____72659
             in
          FStar_SMTEncoding_Term.Caption uu____72655  in
        let uu____72662 =
          let uu____72665 =
            let uu____72666 =
              let uu____72674 =
                let uu____72675 =
                  let uu____72680 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____72685 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____72680, uu____72685)  in
                FStar_SMTEncoding_Util.mkEq uu____72675  in
              (uu____72674, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____72666  in
          let uu____72689 =
            let uu____72692 =
              let uu____72693 =
                let uu____72701 =
                  let uu____72702 =
                    let uu____72707 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____72712 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____72707, uu____72712)  in
                  FStar_SMTEncoding_Util.mkEq uu____72702  in
                (uu____72701, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____72693  in
            [uu____72692; settings.query_decl]  in
          uu____72665 :: uu____72689  in
        uu____72654 :: uu____72662  in
      let uu____72716 =
        let uu____72719 =
          let uu____72722 =
            let uu____72725 =
              let uu____72726 =
                let uu____72733 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____72733)  in
              FStar_SMTEncoding_Term.SetOption uu____72726  in
            [uu____72725;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____72738 =
            let uu____72741 =
              let uu____72744 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____72744
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____72741 settings.query_suffix  in
          FStar_List.append uu____72722 uu____72738  in
        FStar_List.append label_assumptions uu____72719  in
      FStar_List.append uu____72651 uu____72716
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____72778 = FStar_ST.op_Bang replaying_hints  in
      match uu____72778 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___636_72811  ->
               match uu___636_72811 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____72819 -> FStar_Pervasives_Native.None)
      | uu____72822 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____72840 ->
          FStar_Pervasives_Native.None
      | uu____72841 ->
          let uu____72842 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____72842 with
           | (msg,error_labels) ->
               let err =
                 let uu____72855 =
                   FStar_List.map
                     (fun uu____72883  ->
                        match uu____72883 with
                        | (uu____72898,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____72855
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____72915 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____72915
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____72918 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____72938 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____72938
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____72989 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____72989)
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
            match err.error_messages with | [] -> false | uu____73067 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____73089 = find_localized_errors errs  in
    FStar_Option.isSome uu____73089
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____73099 = find_localized_errors settings.query_errors  in
     match uu____73099 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____73109 =
                    let uu____73111 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____73111  in
                  FStar_Errors.diag settings.query_range uu____73109));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____73116 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____73129 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____73129))
              in
           FStar_All.pipe_right uu____73116 (FStar_String.concat "; ")  in
         let uu____73137 =
           let uu____73147 =
             let uu____73155 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____73155,
               (settings.query_range))
              in
           [uu____73147]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____73137);
    (let uu____73173 =
       (FStar_Options.detail_errors ()) &&
         (let uu____73176 = FStar_Options.n_cores ()  in
          uu____73176 = (Prims.parse_int "1"))
        in
     if uu____73173
     then
       let initial_fuel1 =
         let uu___868_73182 = settings  in
         let uu____73183 = FStar_Options.initial_fuel ()  in
         let uu____73185 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___868_73182.query_env);
           query_decl = (uu___868_73182.query_decl);
           query_name = (uu___868_73182.query_name);
           query_index = (uu___868_73182.query_index);
           query_range = (uu___868_73182.query_range);
           query_fuel = uu____73183;
           query_ifuel = uu____73185;
           query_rlimit = (uu___868_73182.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___868_73182.query_errors);
           query_all_labels = (uu___868_73182.query_all_labels);
           query_suffix = (uu___868_73182.query_suffix);
           query_hash = (uu___868_73182.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____73208 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____73208
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____73259 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____73259)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____73346 =
          let r = FStar_Util.mk_ref []  in
          let uu____73357 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____73501  ->
                 let uu____73502 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____73502
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____73357 with | (add1,get1) -> (add1, get1)  in
        let uu____73606 = accumulator ()  in
        match uu____73606 with
        | (add_module_name,get_module_names) ->
            let uu____73643 = accumulator ()  in
            (match uu____73643 with
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
                                  let uu____73766 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____73766
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
                         | uu____73811 ->
                             let uu____73815 = FStar_Util.prefix components
                                in
                             (match uu____73815 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____73842 = exclude_suffix last1
                                       in
                                    FStar_List.append module_name uu____73842
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____73849::[] -> ()
                                    | uu____73853 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____73870 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____73870])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____73897 =
                          let uu____73899 = get_module_names ()  in
                          FStar_All.pipe_right uu____73899
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____73897);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____73912 =
                          let uu____73914 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____73914
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____73912))))
         in
      let uu____73924 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____73924
      then
        let uu____73927 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____73927 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____73946 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____73960 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____73946 with
             | (tag,core) ->
                 let range =
                   let uu____73973 =
                     let uu____73975 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____73975 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____73973  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____73989 = FStar_Options.query_stats ()  in
                   if uu____73989
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
                     let uu____74023 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____74023 "}"
                   else ""  in
                 ((let uu____74032 =
                     let uu____74036 =
                       let uu____74040 =
                         let uu____74044 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____74046 =
                           let uu____74050 =
                             let uu____74054 =
                               let uu____74058 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____74060 =
                                 let uu____74064 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____74066 =
                                   let uu____74070 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____74072 =
                                     let uu____74076 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____74076; stats]  in
                                   uu____74070 :: uu____74072  in
                                 uu____74064 :: uu____74066  in
                               uu____74058 :: uu____74060  in
                             used_hint_tag :: uu____74054  in
                           tag :: uu____74050  in
                         uu____74044 :: uu____74046  in
                       (settings.query_name) :: uu____74040  in
                     range :: uu____74036  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____74032);
                  (let uu____74091 = FStar_Options.print_z3_statistics ()  in
                   if uu____74091 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____74117  ->
                          match uu____74117 with
                          | (uu____74125,msg,range1) ->
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
      let uu____74152 =
        let uu____74154 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____74154  in
      if uu____74152
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
                | uu____74181 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____74189 = FStar_ST.op_Bang recorded_hints  in
           match uu____74189 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____74245 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____74252 =
               let uu____74253 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____74253  in
             store_hint uu____74252
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____74260 -> ())
  
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
                     let uu____74371 = f q res  in
                     match uu____74371 with
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
            (let uu____74410 =
               let uu____74417 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____74430,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____74456,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____74479 = FStar_Ident.text_of_lid q  in
                     (uu____74479, n1)
                  in
               match uu____74417 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____74497 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____74499 =
                       let uu____74501 = FStar_Options.z3_rlimit ()  in
                       uu____74501 * (Prims.parse_int "544656")  in
                     uu____74497 * uu____74499  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____74508 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____74509 = FStar_Options.initial_fuel ()  in
                     let uu____74511 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____74508;
                       query_fuel = uu____74509;
                       query_ifuel = uu____74511;
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
                              { FStar_Util.hint_name = uu____74520;
                                FStar_Util.hint_index = uu____74521;
                                FStar_Util.fuel = uu____74522;
                                FStar_Util.ifuel = uu____74523;
                                FStar_Util.unsat_core = uu____74524;
                                FStar_Util.query_elapsed_time = uu____74525;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____74410 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____74553;
                         FStar_Util.hint_index = uu____74554;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____74558;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___1057_74575 = default_settings  in
                         {
                           query_env = (uu___1057_74575.query_env);
                           query_decl = (uu___1057_74575.query_decl);
                           query_name = (uu___1057_74575.query_name);
                           query_index = (uu___1057_74575.query_index);
                           query_range = (uu___1057_74575.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___1057_74575.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___1057_74575.query_errors);
                           query_all_labels =
                             (uu___1057_74575.query_all_labels);
                           query_suffix = (uu___1057_74575.query_suffix);
                           query_hash = (uu___1057_74575.query_hash)
                         })]
                   | uu____74579 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____74585 =
                     let uu____74587 = FStar_Options.max_ifuel ()  in
                     let uu____74589 = FStar_Options.initial_ifuel ()  in
                     uu____74587 > uu____74589  in
                   if uu____74585
                   then
                     let uu____74594 =
                       let uu___1062_74595 = default_settings  in
                       let uu____74596 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1062_74595.query_env);
                         query_decl = (uu___1062_74595.query_decl);
                         query_name = (uu___1062_74595.query_name);
                         query_index = (uu___1062_74595.query_index);
                         query_range = (uu___1062_74595.query_range);
                         query_fuel = (uu___1062_74595.query_fuel);
                         query_ifuel = uu____74596;
                         query_rlimit = (uu___1062_74595.query_rlimit);
                         query_hint = (uu___1062_74595.query_hint);
                         query_errors = (uu___1062_74595.query_errors);
                         query_all_labels =
                           (uu___1062_74595.query_all_labels);
                         query_suffix = (uu___1062_74595.query_suffix);
                         query_hash = (uu___1062_74595.query_hash)
                       }  in
                     [uu____74594]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____74603 =
                     let uu____74605 =
                       let uu____74607 = FStar_Options.max_fuel ()  in
                       uu____74607 / (Prims.parse_int "2")  in
                     let uu____74610 = FStar_Options.initial_fuel ()  in
                     uu____74605 > uu____74610  in
                   if uu____74603
                   then
                     let uu____74615 =
                       let uu___1066_74616 = default_settings  in
                       let uu____74617 =
                         let uu____74619 = FStar_Options.max_fuel ()  in
                         uu____74619 / (Prims.parse_int "2")  in
                       let uu____74622 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1066_74616.query_env);
                         query_decl = (uu___1066_74616.query_decl);
                         query_name = (uu___1066_74616.query_name);
                         query_index = (uu___1066_74616.query_index);
                         query_range = (uu___1066_74616.query_range);
                         query_fuel = uu____74617;
                         query_ifuel = uu____74622;
                         query_rlimit = (uu___1066_74616.query_rlimit);
                         query_hint = (uu___1066_74616.query_hint);
                         query_errors = (uu___1066_74616.query_errors);
                         query_all_labels =
                           (uu___1066_74616.query_all_labels);
                         query_suffix = (uu___1066_74616.query_suffix);
                         query_hash = (uu___1066_74616.query_hash)
                       }  in
                     [uu____74615]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____74629 =
                     (let uu____74635 = FStar_Options.max_fuel ()  in
                      let uu____74637 = FStar_Options.initial_fuel ()  in
                      uu____74635 > uu____74637) &&
                       (let uu____74641 = FStar_Options.max_ifuel ()  in
                        let uu____74643 = FStar_Options.initial_ifuel ()  in
                        uu____74641 >= uu____74643)
                      in
                   if uu____74629
                   then
                     let uu____74648 =
                       let uu___1070_74649 = default_settings  in
                       let uu____74650 = FStar_Options.max_fuel ()  in
                       let uu____74652 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1070_74649.query_env);
                         query_decl = (uu___1070_74649.query_decl);
                         query_name = (uu___1070_74649.query_name);
                         query_index = (uu___1070_74649.query_index);
                         query_range = (uu___1070_74649.query_range);
                         query_fuel = uu____74650;
                         query_ifuel = uu____74652;
                         query_rlimit = (uu___1070_74649.query_rlimit);
                         query_hint = (uu___1070_74649.query_hint);
                         query_errors = (uu___1070_74649.query_errors);
                         query_all_labels =
                           (uu___1070_74649.query_all_labels);
                         query_suffix = (uu___1070_74649.query_suffix);
                         query_hash = (uu___1070_74649.query_hash)
                       }  in
                     [uu____74648]
                   else []  in
                 let min_fuel1 =
                   let uu____74659 =
                     let uu____74661 = FStar_Options.min_fuel ()  in
                     let uu____74663 = FStar_Options.initial_fuel ()  in
                     uu____74661 < uu____74663  in
                   if uu____74659
                   then
                     let uu____74668 =
                       let uu___1074_74669 = default_settings  in
                       let uu____74670 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___1074_74669.query_env);
                         query_decl = (uu___1074_74669.query_decl);
                         query_name = (uu___1074_74669.query_name);
                         query_index = (uu___1074_74669.query_index);
                         query_range = (uu___1074_74669.query_range);
                         query_fuel = uu____74670;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___1074_74669.query_rlimit);
                         query_hint = (uu___1074_74669.query_hint);
                         query_errors = (uu___1074_74669.query_errors);
                         query_all_labels =
                           (uu___1074_74669.query_all_labels);
                         query_suffix = (uu___1074_74669.query_suffix);
                         query_hash = (uu___1074_74669.query_hash)
                       }  in
                     [uu____74668]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____74695 = FStar_Options.z3_refresh ()  in
                    if uu____74695
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____74700 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____74703 =
                      let uu____74706 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____74706  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____74700
                      uu____74703 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___1087_74729 = default_settings  in
                        {
                          query_env = (uu___1087_74729.query_env);
                          query_decl = (uu___1087_74729.query_decl);
                          query_name = (uu___1087_74729.query_name);
                          query_index = (uu___1087_74729.query_index);
                          query_range = (uu___1087_74729.query_range);
                          query_fuel = (uu___1087_74729.query_fuel);
                          query_ifuel = (uu___1087_74729.query_ifuel);
                          query_rlimit = (uu___1087_74729.query_rlimit);
                          query_hint = (uu___1087_74729.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___1087_74729.query_all_labels);
                          query_suffix = (uu___1087_74729.query_suffix);
                          query_hash = (uu___1087_74729.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____74730 =
                   let uu____74739 = FStar_Options.admit_smt_queries ()  in
                   let uu____74741 = FStar_Options.admit_except ()  in
                   (uu____74739, uu____74741)  in
                 (match uu____74730 with
                  | (true ,uu____74749) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____74779 =
                              let uu____74781 =
                                let uu____74783 =
                                  let uu____74785 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____74785 ")"  in
                                Prims.op_Hat ", " uu____74783  in
                              Prims.op_Hat default_settings.query_name
                                uu____74781
                               in
                            Prims.op_Hat "(" uu____74779  in
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
        (let uu____74825 =
           let uu____74827 =
             let uu____74829 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____74829  in
           FStar_Util.format1 "Starting query at %s" uu____74827  in
         FStar_SMTEncoding_Encode.push uu____74825);
        (let uu____74832 = FStar_Options.no_smt ()  in
         if uu____74832
         then
           let uu____74835 =
             let uu____74845 =
               let uu____74853 =
                 let uu____74855 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____74855
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____74853,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____74845]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____74835
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____74876 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____74876 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____74912 =
                  let uu____74913 =
                    let uu____74915 =
                      let uu____74917 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____74917
                       in
                    FStar_Util.format1 "Ending query at %s" uu____74915  in
                  FStar_SMTEncoding_Encode.pop uu____74913  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____74920);
                           FStar_SMTEncoding_Term.freevars = uu____74921;
                           FStar_SMTEncoding_Term.rng = uu____74922;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____74923;
                       FStar_SMTEncoding_Term.assumption_name = uu____74924;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____74925;_}
                     -> pop1 ()
                 | uu____74945 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____74946 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____74948 -> failwith "Impossible")))
  
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
           let uu____74956 =
             let uu____74963 = FStar_Options.peek ()  in (e, g, uu____74963)
              in
           [uu____74956]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____74979  -> ());
    FStar_TypeChecker_Env.push = (fun uu____74981  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____74984  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____74987  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____75006  -> fun uu____75007  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____75022  -> fun uu____75023  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____75029 =
             let uu____75036 = FStar_Options.peek ()  in (e, g, uu____75036)
              in
           [uu____75029]);
    FStar_TypeChecker_Env.solve =
      (fun uu____75052  -> fun uu____75053  -> fun uu____75054  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____75061  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____75063  -> ())
  } 
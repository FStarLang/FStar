open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14,'Auu____15) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___359_32  ->
    match uu___359_32 with
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
let initialize_hints_db : 'Auu____97 . Prims.string -> 'Auu____97 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____109 = FStar_Options.record_hints ()  in
       if uu____109
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____140 = FStar_Options.use_hints ()  in
       if uu____140
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____143 = FStar_Options.hint_file ()  in
           match uu____143 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____147 = FStar_Util.read_hints val_filename  in
         match uu____147 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____153 = FStar_Options.hint_info ()  in
               if uu____153
               then
                 let uu____154 =
                   let uu____155 = FStar_Options.hint_file ()  in
                   match uu____155 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____159 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____154
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____191 = FStar_Options.hint_info ()  in
             (if uu____191
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____200 = FStar_Options.record_hints ()  in
     if uu____200
     then
       let hints =
         let uu____202 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____202  in
       let hints_db =
         let uu____233 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____233; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____236 = FStar_Options.hint_file ()  in
         match uu____236 with
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
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____340 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____356 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____362 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____362)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____387 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____387 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____397 -> d :: out) [] theory_rev
         in
      pruned_theory
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____427 = filter_using_facts_from e theory  in
            (uu____427, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____437 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____461  ->
                     match uu____461 with
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
                          | uu____518 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____437 with
             | (theory',n_retained,n_pruned) ->
                 let uu____536 =
                   let uu____539 =
                     let uu____542 =
                       let uu____543 =
                         let uu____544 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____544  in
                       FStar_SMTEncoding_Term.Caption uu____543  in
                     [uu____542]  in
                   FStar_List.append theory' uu____539  in
                 (uu____536, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____565 = filter_using_facts_from e x  in (uu____565, false)
  
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
    }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
  
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
  
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
  
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
  
let (__proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
  
let (error_to_short_string : errors -> Prims.string) =
  fun err  ->
    let uu____746 = FStar_Util.string_of_int err.error_fuel  in
    let uu____747 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____746 uu____747
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
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_env
  
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_decl
  
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_name
  
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_index
  
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_range
  
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_fuel
  
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_ifuel
  
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_rlimit
  
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_hint
  
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_errors
  
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_all_labels
  
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_suffix
  
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { query_env = __fname__query_env; query_decl = __fname__query_decl;
        query_name = __fname__query_name; query_index = __fname__query_index;
        query_range = __fname__query_range; query_fuel = __fname__query_fuel;
        query_ifuel = __fname__query_ifuel;
        query_rlimit = __fname__query_rlimit;
        query_hint = __fname__query_hint;
        query_errors = __fname__query_errors;
        query_all_labels = __fname__query_all_labels;
        query_suffix = __fname__query_suffix;
        query_hash = __fname__query_hash;_} -> __fname__query_hash
  
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
      let uu____1165 =
        let uu____1168 =
          let uu____1169 =
            let uu____1170 = FStar_Util.string_of_int n1  in
            let uu____1171 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1170 uu____1171
             in
          FStar_SMTEncoding_Term.Caption uu____1169  in
        let uu____1172 =
          let uu____1175 =
            let uu____1176 =
              let uu____1183 =
                let uu____1184 =
                  let uu____1189 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1192 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1189, uu____1192)  in
                FStar_SMTEncoding_Util.mkEq uu____1184  in
              (uu____1183, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1176  in
          let uu____1193 =
            let uu____1196 =
              let uu____1197 =
                let uu____1204 =
                  let uu____1205 =
                    let uu____1210 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1213 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1210, uu____1213)  in
                  FStar_SMTEncoding_Util.mkEq uu____1205  in
                (uu____1204, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1197  in
            [uu____1196; settings.query_decl]  in
          uu____1175 :: uu____1193  in
        uu____1168 :: uu____1172  in
      let uu____1214 =
        let uu____1217 =
          let uu____1220 =
            let uu____1223 =
              let uu____1224 =
                let uu____1229 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1229)  in
              FStar_SMTEncoding_Term.SetOption uu____1224  in
            [uu____1223;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1230 =
            let uu____1233 =
              let uu____1236 = FStar_Options.record_hints ()  in
              if uu____1236
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1240 =
              let uu____1243 =
                let uu____1246 = FStar_Options.print_z3_statistics ()  in
                if uu____1246
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1243 settings.query_suffix  in
            FStar_List.append uu____1233 uu____1240  in
          FStar_List.append uu____1220 uu____1230  in
        FStar_List.append label_assumptions uu____1217  in
      FStar_List.append uu____1165 uu____1214
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1269 = FStar_ST.op_Bang replaying_hints  in
      match uu____1269 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___360_1306  ->
               match uu___360_1306 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1312 -> FStar_Pervasives_Native.None)
      | uu____1315 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1332 -> FStar_Pervasives_Native.None
      | uu____1333 ->
          let uu____1334 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1334 with
           | (msg,error_labels) ->
               let err =
                 let uu____1344 =
                   FStar_List.map
                     (fun uu____1369  ->
                        match uu____1369 with
                        | (uu____1382,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1344
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1395 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1395
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1396 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1416 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1416
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1470 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1470)
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
            match err.error_messages with | [] -> false | uu____1546 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1564 = find_localized_errors errs  in
    FStar_Option.isSome uu____1564
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____1573 = find_localized_errors settings.query_errors  in
     match uu____1573 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____1583 =
                    let uu____1584 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____1584  in
                  FStar_Errors.diag settings.query_range uu____1583));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____1586 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____1596 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____1596))
              in
           FStar_All.pipe_right uu____1586 (FStar_String.concat "; ")  in
         let uu____1599 =
           let uu____1608 =
             let uu____1615 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1615,
               (settings.query_range))
              in
           [uu____1608]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____1599);
    (let uu____1628 =
       (FStar_Options.detail_errors ()) &&
         (let uu____1630 = FStar_Options.n_cores ()  in
          uu____1630 = (Prims.parse_int "1"))
        in
     if uu____1628
     then
       let initial_fuel1 =
         let uu___361_1632 = settings  in
         let uu____1633 = FStar_Options.initial_fuel ()  in
         let uu____1634 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___361_1632.query_env);
           query_decl = (uu___361_1632.query_decl);
           query_name = (uu___361_1632.query_name);
           query_index = (uu___361_1632.query_index);
           query_range = (uu___361_1632.query_range);
           query_fuel = uu____1633;
           query_ifuel = uu____1634;
           query_rlimit = (uu___361_1632.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___361_1632.query_errors);
           query_all_labels = (uu___361_1632.query_all_labels);
           query_suffix = (uu___361_1632.query_suffix);
           query_hash = (uu___361_1632.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____1655 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____1655
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
         (let uu____1709 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____1709)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1772 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1772
      then
        let uu____1773 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1773 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1781 -> "succeeded"
              | uu____1782 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1784 =
                let uu____1785 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1786 =
                  let uu____1787 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1787 ")"  in
                Prims.strcat uu____1785 uu____1786  in
              Prims.strcat "(" uu____1784  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1791 = FStar_Options.print_z3_statistics ()  in
              if uu____1791
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
                let uu____1809 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1809 "}"
              else ""  in
            ((let uu____1812 =
                let uu____1815 =
                  let uu____1818 =
                    let uu____1821 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1822 =
                      let uu____1825 =
                        let uu____1828 =
                          let uu____1831 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1832 =
                            let uu____1835 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1836 =
                              let uu____1839 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1840 =
                                let uu____1843 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1843; stats]  in
                              uu____1839 :: uu____1840  in
                            uu____1835 :: uu____1836  in
                          uu____1831 :: uu____1832  in
                        used_hint_tag :: uu____1828  in
                      tag :: uu____1825  in
                    uu____1821 :: uu____1822  in
                  (settings.query_name) :: uu____1818  in
                range :: uu____1815  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1812);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1863  ->
                     match uu____1863 with
                     | (uu____1870,msg,range1) ->
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
      let uu____1886 =
        let uu____1887 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1887  in
      if uu____1886
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
                | uu____1907 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____1914 = FStar_ST.op_Bang recorded_hints  in
           match uu____1914 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____1978 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____1984 =
               let uu____1985 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____1985  in
             store_hint uu____1984
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____1990 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2006 =
         (used_hint settings) &&
           (let uu____2008 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2008)
          in
       if uu____2006 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2104 = f q res  in
                     match uu____2104 with
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
            (let uu____2142 =
               let uu____2149 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2158,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2177,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2194 = FStar_Ident.text_of_lid q  in
                     (uu____2194, n1)
                  in
               match uu____2149 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2204 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2205 =
                       let uu____2206 = FStar_Options.z3_rlimit ()  in
                       uu____2206 * (Prims.parse_int "544656")  in
                     uu____2204 * uu____2205  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2211 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2212 = FStar_Options.initial_fuel ()  in
                     let uu____2213 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2211;
                       query_fuel = uu____2212;
                       query_ifuel = uu____2213;
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
                              { FStar_Util.hint_name = uu____2218;
                                FStar_Util.hint_index = uu____2219;
                                FStar_Util.fuel = uu____2220;
                                FStar_Util.ifuel = uu____2221;
                                FStar_Util.unsat_core = uu____2222;
                                FStar_Util.query_elapsed_time = uu____2223;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2142 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2244;
                         FStar_Util.hint_index = uu____2245;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2249;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___362_2258 = default_settings  in
                         {
                           query_env = (uu___362_2258.query_env);
                           query_decl = (uu___362_2258.query_decl);
                           query_name = (uu___362_2258.query_name);
                           query_index = (uu___362_2258.query_index);
                           query_range = (uu___362_2258.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___362_2258.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___362_2258.query_errors);
                           query_all_labels =
                             (uu___362_2258.query_all_labels);
                           query_suffix = (uu___362_2258.query_suffix);
                           query_hash = (uu___362_2258.query_hash)
                         })]
                   | uu____2261 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2267 =
                     let uu____2268 = FStar_Options.max_ifuel ()  in
                     let uu____2269 = FStar_Options.initial_ifuel ()  in
                     uu____2268 > uu____2269  in
                   if uu____2267
                   then
                     let uu____2272 =
                       let uu___363_2273 = default_settings  in
                       let uu____2274 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___363_2273.query_env);
                         query_decl = (uu___363_2273.query_decl);
                         query_name = (uu___363_2273.query_name);
                         query_index = (uu___363_2273.query_index);
                         query_range = (uu___363_2273.query_range);
                         query_fuel = (uu___363_2273.query_fuel);
                         query_ifuel = uu____2274;
                         query_rlimit = (uu___363_2273.query_rlimit);
                         query_hint = (uu___363_2273.query_hint);
                         query_errors = (uu___363_2273.query_errors);
                         query_all_labels = (uu___363_2273.query_all_labels);
                         query_suffix = (uu___363_2273.query_suffix);
                         query_hash = (uu___363_2273.query_hash)
                       }  in
                     [uu____2272]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2279 =
                     let uu____2280 =
                       let uu____2281 = FStar_Options.max_fuel ()  in
                       uu____2281 / (Prims.parse_int "2")  in
                     let uu____2282 = FStar_Options.initial_fuel ()  in
                     uu____2280 > uu____2282  in
                   if uu____2279
                   then
                     let uu____2285 =
                       let uu___364_2286 = default_settings  in
                       let uu____2287 =
                         let uu____2288 = FStar_Options.max_fuel ()  in
                         uu____2288 / (Prims.parse_int "2")  in
                       let uu____2289 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___364_2286.query_env);
                         query_decl = (uu___364_2286.query_decl);
                         query_name = (uu___364_2286.query_name);
                         query_index = (uu___364_2286.query_index);
                         query_range = (uu___364_2286.query_range);
                         query_fuel = uu____2287;
                         query_ifuel = uu____2289;
                         query_rlimit = (uu___364_2286.query_rlimit);
                         query_hint = (uu___364_2286.query_hint);
                         query_errors = (uu___364_2286.query_errors);
                         query_all_labels = (uu___364_2286.query_all_labels);
                         query_suffix = (uu___364_2286.query_suffix);
                         query_hash = (uu___364_2286.query_hash)
                       }  in
                     [uu____2285]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2294 =
                     (let uu____2299 = FStar_Options.max_fuel ()  in
                      let uu____2300 = FStar_Options.initial_fuel ()  in
                      uu____2299 > uu____2300) &&
                       (let uu____2303 = FStar_Options.max_ifuel ()  in
                        let uu____2304 = FStar_Options.initial_ifuel ()  in
                        uu____2303 >= uu____2304)
                      in
                   if uu____2294
                   then
                     let uu____2307 =
                       let uu___365_2308 = default_settings  in
                       let uu____2309 = FStar_Options.max_fuel ()  in
                       let uu____2310 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___365_2308.query_env);
                         query_decl = (uu___365_2308.query_decl);
                         query_name = (uu___365_2308.query_name);
                         query_index = (uu___365_2308.query_index);
                         query_range = (uu___365_2308.query_range);
                         query_fuel = uu____2309;
                         query_ifuel = uu____2310;
                         query_rlimit = (uu___365_2308.query_rlimit);
                         query_hint = (uu___365_2308.query_hint);
                         query_errors = (uu___365_2308.query_errors);
                         query_all_labels = (uu___365_2308.query_all_labels);
                         query_suffix = (uu___365_2308.query_suffix);
                         query_hash = (uu___365_2308.query_hash)
                       }  in
                     [uu____2307]
                   else []  in
                 let min_fuel1 =
                   let uu____2315 =
                     let uu____2316 = FStar_Options.min_fuel ()  in
                     let uu____2317 = FStar_Options.initial_fuel ()  in
                     uu____2316 < uu____2317  in
                   if uu____2315
                   then
                     let uu____2320 =
                       let uu___366_2321 = default_settings  in
                       let uu____2322 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___366_2321.query_env);
                         query_decl = (uu___366_2321.query_decl);
                         query_name = (uu___366_2321.query_name);
                         query_index = (uu___366_2321.query_index);
                         query_range = (uu___366_2321.query_range);
                         query_fuel = uu____2322;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___366_2321.query_rlimit);
                         query_hint = (uu___366_2321.query_hint);
                         query_errors = (uu___366_2321.query_errors);
                         query_all_labels = (uu___366_2321.query_all_labels);
                         query_suffix = (uu___366_2321.query_suffix);
                         query_hash = (uu___366_2321.query_hash)
                       }  in
                     [uu____2320]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2344 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2344
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2346 = with_fuel_and_diagnostics config []  in
                    let uu____2349 =
                      let uu____2352 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2352  in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2346
                      uu____2349 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___367_2375 = default_settings  in
                        {
                          query_env = (uu___367_2375.query_env);
                          query_decl = (uu___367_2375.query_decl);
                          query_name = (uu___367_2375.query_name);
                          query_index = (uu___367_2375.query_index);
                          query_range = (uu___367_2375.query_range);
                          query_fuel = (uu___367_2375.query_fuel);
                          query_ifuel = (uu___367_2375.query_ifuel);
                          query_rlimit = (uu___367_2375.query_rlimit);
                          query_hint = (uu___367_2375.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___367_2375.query_all_labels);
                          query_suffix = (uu___367_2375.query_suffix);
                          query_hash = (uu___367_2375.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2376 =
                   let uu____2383 = FStar_Options.admit_smt_queries ()  in
                   let uu____2384 = FStar_Options.admit_except ()  in
                   (uu____2383, uu____2384)  in
                 (match uu____2376 with
                  | (true ,uu____2389) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2401 =
                              let uu____2402 =
                                let uu____2403 =
                                  let uu____2404 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2404 ")"  in
                                Prims.strcat ", " uu____2403  in
                              Prims.strcat default_settings.query_name
                                uu____2402
                               in
                            Prims.strcat "(" uu____2401  in
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
        (let uu____2432 =
           let uu____2433 =
             let uu____2434 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2434  in
           FStar_Util.format1 "Starting query at %s" uu____2433  in
         FStar_SMTEncoding_Encode.push uu____2432);
        (let uu____2435 = FStar_Options.no_smt ()  in
         if uu____2435
         then
           let uu____2436 =
             let uu____2445 =
               let uu____2452 =
                 let uu____2453 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____2453
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____2452,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____2445]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____2436
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____2468 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____2468 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____2504 =
                  let uu____2505 =
                    let uu____2506 =
                      let uu____2507 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____2507
                       in
                    FStar_Util.format1 "Ending query at %s" uu____2506  in
                  FStar_SMTEncoding_Encode.pop uu____2505  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____2508);
                           FStar_SMTEncoding_Term.freevars = uu____2509;
                           FStar_SMTEncoding_Term.rng = uu____2510;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____2511;
                       FStar_SMTEncoding_Term.assumption_name = uu____2512;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____2513;_}
                     -> pop1 ()
                 | uu____2528 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____2529 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____2531 -> failwith "Impossible")))
  
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
           let uu____2537 =
             let uu____2544 = FStar_Options.peek ()  in (e, g, uu____2544)
              in
           [uu____2537]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2559  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2561  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2563  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____2565  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____2574  -> fun uu____2575  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2586  -> fun uu____2587  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2590  -> fun uu____2591  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2597 =
             let uu____2604 = FStar_Options.peek ()  in (e, g, uu____2604)
              in
           [uu____2597]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2620  -> fun uu____2621  -> fun uu____2622  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2628  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2630  -> ())
  } 
open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result :
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____11,('Auu____10,'Auu____9) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____11,'Auu____10) FStar_Util.either
  =
  fun uu___57_27  ->
    match uu___57_27 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____42) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____139 . Prims.string -> 'Auu____139 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____149 = FStar_Options.record_hints ()  in
       if uu____149
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____180 = FStar_Options.use_hints ()  in
       if uu____180
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____183 = FStar_Options.hint_file ()  in
           match uu____183 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____187 = FStar_Util.read_hints val_filename  in
         match uu____187 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____193 = FStar_Options.hint_info ()  in
               if uu____193
               then
                 let uu____194 =
                   let uu____195 = FStar_Options.hint_file ()  in
                   match uu____195 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____199 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____194
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____227 = FStar_Options.hint_info ()  in
             (if uu____227
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> Prims.unit) =
  fun src_filename  ->
    (let uu____234 = FStar_Options.record_hints ()  in
     if uu____234
     then
       let hints =
         let uu____236 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____236  in
       let hints_db =
         let uu____263 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____263; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____266 = FStar_Options.hint_file ()  in
         match uu____266 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename
          in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
  
let with_hints_db : 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
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
        | uu____351 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____363 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____369 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____369)
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
                   let uu____394 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____394 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____404 -> d :: out) [] theory_rev
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
            let uu____428 = filter_using_facts_from e theory  in
            (uu____428, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____438 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____462  ->
                     match uu____462 with
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
                          | uu____519 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____438 with
             | (theory',n_retained,n_pruned) ->
                 let uu____537 =
                   let uu____540 =
                     let uu____543 =
                       let uu____544 =
                         let uu____545 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____545  in
                       FStar_SMTEncoding_Term.Caption uu____544  in
                     [uu____543]  in
                   FStar_List.append theory' uu____540  in
                 (uu____537, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____562 = filter_using_facts_from e x  in (uu____562, false)
  
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
    }[@@deriving show]
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
    let uu____726 = FStar_Util.string_of_int err.error_fuel  in
    let uu____727 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____726 uu____727
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
  query_hash: Prims.string FStar_Pervasives_Native.option }[@@deriving show]
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
      let uu____1102 =
        let uu____1105 =
          let uu____1106 =
            let uu____1107 = FStar_Util.string_of_int n1  in
            let uu____1108 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1107 uu____1108
             in
          FStar_SMTEncoding_Term.Caption uu____1106  in
        let uu____1109 =
          let uu____1112 =
            let uu____1113 =
              let uu____1120 =
                let uu____1121 =
                  let uu____1126 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1129 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1126, uu____1129)  in
                FStar_SMTEncoding_Util.mkEq uu____1121  in
              (uu____1120, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1113  in
          let uu____1132 =
            let uu____1135 =
              let uu____1136 =
                let uu____1143 =
                  let uu____1144 =
                    let uu____1149 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1152 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1149, uu____1152)  in
                  FStar_SMTEncoding_Util.mkEq uu____1144  in
                (uu____1143, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1136  in
            [uu____1135; settings.query_decl]  in
          uu____1112 :: uu____1132  in
        uu____1105 :: uu____1109  in
      let uu____1155 =
        let uu____1158 =
          let uu____1161 =
            let uu____1164 =
              let uu____1165 =
                let uu____1170 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1170)  in
              FStar_SMTEncoding_Term.SetOption uu____1165  in
            [uu____1164;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1171 =
            let uu____1174 =
              let uu____1177 = FStar_Options.record_hints ()  in
              if uu____1177
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1181 =
              let uu____1184 =
                let uu____1187 = FStar_Options.print_z3_statistics ()  in
                if uu____1187
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1184 settings.query_suffix  in
            FStar_List.append uu____1174 uu____1181  in
          FStar_List.append uu____1161 uu____1171  in
        FStar_List.append label_assumptions uu____1158  in
      FStar_List.append uu____1102 uu____1155
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1204 = FStar_ST.op_Bang replaying_hints  in
      match uu____1204 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___58_1237  ->
               match uu___58_1237 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1243 -> FStar_Pervasives_Native.None)
      | uu____1246 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1259 -> FStar_Pervasives_Native.None
      | uu____1260 ->
          let uu____1261 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1261 with
           | (msg,error_labels) ->
               let err =
                 let uu____1271 =
                   FStar_List.map
                     (fun uu____1296  ->
                        match uu____1296 with
                        | (uu____1309,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1271
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1318 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1318
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1319 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1337 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1337
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1439 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1439)
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
            match err.error_messages with | [] -> false | uu____1561 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1577 = find_localized_errors errs  in
    FStar_Option.isSome uu____1577
  
let (report_errors : query_settings -> Prims.unit) =
  fun settings  ->
    let uu____1583 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1585 = FStar_Options.n_cores ()  in
         uu____1585 = (Prims.parse_int "1"))
       in
    if uu____1583
    then
      let initial_fuel1 =
        let uu___59_1587 = settings  in
        let uu____1588 = FStar_Options.initial_fuel ()  in
        let uu____1589 = FStar_Options.initial_ifuel ()  in
        {
          query_env = (uu___59_1587.query_env);
          query_decl = (uu___59_1587.query_decl);
          query_name = (uu___59_1587.query_name);
          query_index = (uu___59_1587.query_index);
          query_range = (uu___59_1587.query_range);
          query_fuel = uu____1588;
          query_ifuel = uu____1589;
          query_rlimit = (uu___59_1587.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___59_1587.query_errors);
          query_all_labels = (uu___59_1587.query_all_labels);
          query_suffix = (uu___59_1587.query_suffix);
          query_hash = (uu___59_1587.query_hash)
        }  in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        (let uu____1608 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1608 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1710 = FStar_ST.op_Bang res  in
         FStar_Option.get uu____1710)
         in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1811 = find_localized_errors settings.query_errors  in
       match uu____1811 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1821 =
                      let uu____1822 = error_to_short_string e  in
                      Prims.strcat "SMT solver says: " uu____1822  in
                    FStar_Errors.diag settings.query_range uu____1821));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1824 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1834 = error_to_short_string e  in
                       Prims.strcat "SMT solver says: " uu____1834))
                in
             FStar_All.pipe_right uu____1824 (FStar_String.concat "; ")  in
           let uu____1837 =
             let uu____1846 =
               let uu____1853 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail
                  in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1853,
                 (settings.query_range))
                in
             [uu____1846]  in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1837)
  
let (query_info :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1872 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1872
      then
        let uu____1873 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1873 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1881 -> "succeeded"
              | uu____1882 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1884 =
                let uu____1885 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1886 =
                  let uu____1887 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1887 ")"  in
                Prims.strcat uu____1885 uu____1886  in
              Prims.strcat "(" uu____1884  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1891 = FStar_Options.print_z3_statistics ()  in
              if uu____1891
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
                let uu____1903 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1903 "}"
              else ""  in
            ((let uu____1906 =
                let uu____1909 =
                  let uu____1912 =
                    let uu____1915 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1916 =
                      let uu____1919 =
                        let uu____1922 =
                          let uu____1925 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1926 =
                            let uu____1929 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1930 =
                              let uu____1933 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1934 =
                                let uu____1937 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1937; stats]  in
                              uu____1933 :: uu____1934  in
                            uu____1929 :: uu____1930  in
                          uu____1925 :: uu____1926  in
                        used_hint_tag :: uu____1922  in
                      tag :: uu____1919  in
                    uu____1915 :: uu____1916  in
                  (settings.query_name) :: uu____1912  in
                range :: uu____1909  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1906);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1949  ->
                     match uu____1949 with
                     | (uu____1956,msg,range1) ->
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else ""  in
                         FStar_Errors.log_issue range1
                           (FStar_Errors.Warning_HitReplayFailed,
                             (Prims.strcat tag1 msg)))))
      else ()
  
let (record_hint :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1968 =
        let uu____1969 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1969  in
      if uu____1968
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
                | uu____1987 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____1992 = FStar_ST.op_Bang recorded_hints  in
           match uu____1992 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2052 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2060 =
               let uu____2061 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2061  in
             store_hint uu____2060
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2066 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2078 =
         (used_hint settings) &&
           (let uu____2080 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2080)
          in
       if uu____2078 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result  in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
  
let (fold_queries :
  query_settings Prims.list ->
    (query_settings ->
       (FStar_SMTEncoding_Z3.z3result -> Prims.unit) -> Prims.unit)
      ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> Prims.unit) -> Prims.unit)
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
                     let uu____2166 = f q res  in
                     match uu____2166 with
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
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit)
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____2194 =
               let uu____2201 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1)
                  in
               match uu____2201 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2233 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2234 =
                       let uu____2235 = FStar_Options.z3_rlimit ()  in
                       uu____2235 * (Prims.parse_int "544656")  in
                     uu____2233 * uu____2234  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2240 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2241 = FStar_Options.initial_fuel ()  in
                     let uu____2242 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2240;
                       query_fuel = uu____2241;
                       query_ifuel = uu____2242;
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
                              { FStar_Util.hint_name = uu____2247;
                                FStar_Util.hint_index = uu____2248;
                                FStar_Util.fuel = uu____2249;
                                FStar_Util.ifuel = uu____2250;
                                FStar_Util.unsat_core = uu____2251;
                                FStar_Util.query_elapsed_time = uu____2252;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2194 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2273;
                         FStar_Util.hint_index = uu____2274;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2278;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___60_2287 = default_settings  in
                         {
                           query_env = (uu___60_2287.query_env);
                           query_decl = (uu___60_2287.query_decl);
                           query_name = (uu___60_2287.query_name);
                           query_index = (uu___60_2287.query_index);
                           query_range = (uu___60_2287.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___60_2287.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___60_2287.query_errors);
                           query_all_labels = (uu___60_2287.query_all_labels);
                           query_suffix = (uu___60_2287.query_suffix);
                           query_hash = (uu___60_2287.query_hash)
                         })]
                   | uu____2290 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2296 =
                     let uu____2297 = FStar_Options.max_ifuel ()  in
                     let uu____2298 = FStar_Options.initial_ifuel ()  in
                     uu____2297 > uu____2298  in
                   if uu____2296
                   then
                     let uu____2301 =
                       let uu___61_2302 = default_settings  in
                       let uu____2303 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___61_2302.query_env);
                         query_decl = (uu___61_2302.query_decl);
                         query_name = (uu___61_2302.query_name);
                         query_index = (uu___61_2302.query_index);
                         query_range = (uu___61_2302.query_range);
                         query_fuel = (uu___61_2302.query_fuel);
                         query_ifuel = uu____2303;
                         query_rlimit = (uu___61_2302.query_rlimit);
                         query_hint = (uu___61_2302.query_hint);
                         query_errors = (uu___61_2302.query_errors);
                         query_all_labels = (uu___61_2302.query_all_labels);
                         query_suffix = (uu___61_2302.query_suffix);
                         query_hash = (uu___61_2302.query_hash)
                       }  in
                     [uu____2301]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2308 =
                     let uu____2309 =
                       let uu____2310 = FStar_Options.max_fuel ()  in
                       uu____2310 / (Prims.parse_int "2")  in
                     let uu____2317 = FStar_Options.initial_fuel ()  in
                     uu____2309 > uu____2317  in
                   if uu____2308
                   then
                     let uu____2320 =
                       let uu___62_2321 = default_settings  in
                       let uu____2322 =
                         let uu____2323 = FStar_Options.max_fuel ()  in
                         uu____2323 / (Prims.parse_int "2")  in
                       let uu____2330 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___62_2321.query_env);
                         query_decl = (uu___62_2321.query_decl);
                         query_name = (uu___62_2321.query_name);
                         query_index = (uu___62_2321.query_index);
                         query_range = (uu___62_2321.query_range);
                         query_fuel = uu____2322;
                         query_ifuel = uu____2330;
                         query_rlimit = (uu___62_2321.query_rlimit);
                         query_hint = (uu___62_2321.query_hint);
                         query_errors = (uu___62_2321.query_errors);
                         query_all_labels = (uu___62_2321.query_all_labels);
                         query_suffix = (uu___62_2321.query_suffix);
                         query_hash = (uu___62_2321.query_hash)
                       }  in
                     [uu____2320]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2335 =
                     (let uu____2340 = FStar_Options.max_fuel ()  in
                      let uu____2341 = FStar_Options.initial_fuel ()  in
                      uu____2340 > uu____2341) &&
                       (let uu____2344 = FStar_Options.max_ifuel ()  in
                        let uu____2345 = FStar_Options.initial_ifuel ()  in
                        uu____2344 >= uu____2345)
                      in
                   if uu____2335
                   then
                     let uu____2348 =
                       let uu___63_2349 = default_settings  in
                       let uu____2350 = FStar_Options.max_fuel ()  in
                       let uu____2351 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___63_2349.query_env);
                         query_decl = (uu___63_2349.query_decl);
                         query_name = (uu___63_2349.query_name);
                         query_index = (uu___63_2349.query_index);
                         query_range = (uu___63_2349.query_range);
                         query_fuel = uu____2350;
                         query_ifuel = uu____2351;
                         query_rlimit = (uu___63_2349.query_rlimit);
                         query_hint = (uu___63_2349.query_hint);
                         query_errors = (uu___63_2349.query_errors);
                         query_all_labels = (uu___63_2349.query_all_labels);
                         query_suffix = (uu___63_2349.query_suffix);
                         query_hash = (uu___63_2349.query_hash)
                       }  in
                     [uu____2348]
                   else []  in
                 let min_fuel1 =
                   let uu____2356 =
                     let uu____2357 = FStar_Options.min_fuel ()  in
                     let uu____2358 = FStar_Options.initial_fuel ()  in
                     uu____2357 < uu____2358  in
                   if uu____2356
                   then
                     let uu____2361 =
                       let uu___64_2362 = default_settings  in
                       let uu____2363 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___64_2362.query_env);
                         query_decl = (uu___64_2362.query_decl);
                         query_name = (uu___64_2362.query_name);
                         query_index = (uu___64_2362.query_index);
                         query_range = (uu___64_2362.query_range);
                         query_fuel = uu____2363;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___64_2362.query_rlimit);
                         query_hint = (uu___64_2362.query_hint);
                         query_errors = (uu___64_2362.query_errors);
                         query_all_labels = (uu___64_2362.query_all_labels);
                         query_suffix = (uu___64_2362.query_suffix);
                         query_hash = (uu___64_2362.query_hash)
                       }  in
                     [uu____2361]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2381 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2381
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2383 = with_fuel_and_diagnostics config []  in
                    let uu____2386 =
                      let uu____2389 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2389  in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2383
                      uu____2386 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___65_2408 = default_settings  in
                        {
                          query_env = (uu___65_2408.query_env);
                          query_decl = (uu___65_2408.query_decl);
                          query_name = (uu___65_2408.query_name);
                          query_index = (uu___65_2408.query_index);
                          query_range = (uu___65_2408.query_range);
                          query_fuel = (uu___65_2408.query_fuel);
                          query_ifuel = (uu___65_2408.query_ifuel);
                          query_rlimit = (uu___65_2408.query_rlimit);
                          query_hint = (uu___65_2408.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___65_2408.query_all_labels);
                          query_suffix = (uu___65_2408.query_suffix);
                          query_hash = (uu___65_2408.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2409 =
                   let uu____2416 = FStar_Options.admit_smt_queries ()  in
                   let uu____2417 = FStar_Options.admit_except ()  in
                   (uu____2416, uu____2417)  in
                 (match uu____2409 with
                  | (true ,uu____2422) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2434 =
                              let uu____2435 =
                                let uu____2436 =
                                  let uu____2437 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2437 ")"  in
                                Prims.strcat ", " uu____2436  in
                              Prims.strcat default_settings.query_name
                                uu____2435
                               in
                            Prims.strcat "(" uu____2434  in
                          full_query_id <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
  
let (solve :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2459 =
           let uu____2460 =
             let uu____2461 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2461  in
           FStar_Util.format1 "Starting query at %s" uu____2460  in
         FStar_SMTEncoding_Encode.push uu____2459);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____2463 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____2463 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2497 =
               let uu____2498 =
                 let uu____2499 =
                   let uu____2500 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2500
                    in
                 FStar_Util.format1 "Ending query at %s" uu____2499  in
               FStar_SMTEncoding_Encode.pop uu____2498  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2501);
                        FStar_SMTEncoding_Term.freevars = uu____2502;
                        FStar_SMTEncoding_Term.rng = uu____2503;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2504;
                    FStar_SMTEncoding_Term.assumption_name = uu____2505;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2506;_}
                  -> pop1 ()
              | uu____2521 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2522 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2524 -> failwith "Impossible"))
  
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.encode_modul =
      FStar_SMTEncoding_Encode.encode_modul;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2530 =
             let uu____2537 = FStar_Options.peek ()  in (e, g, uu____2537)
              in
           [uu____2530]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2552  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2554  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2556  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2559  -> fun uu____2560  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2563  -> fun uu____2564  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2570 =
             let uu____2577 = FStar_Options.peek ()  in (e, g, uu____2577)
              in
           [uu____2570]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2593  -> fun uu____2594  -> fun uu____2595  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2601  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2603  -> ())
  } 
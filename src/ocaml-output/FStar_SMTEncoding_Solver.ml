open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14,'Auu____15) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___86_32  ->
    match uu___86_32 with
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
      (let uu____144 = FStar_Options.use_hints ()  in
       if uu____144
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____147 = FStar_Options.hint_file ()  in
           match uu____147 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____151 = FStar_Util.read_hints val_filename  in
         match uu____151 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____157 = FStar_Options.hint_info ()  in
               if uu____157
               then
                 let uu____158 =
                   let uu____159 = FStar_Options.hint_file ()  in
                   match uu____159 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____163 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____158
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____195 = FStar_Options.hint_info ()  in
             (if uu____195
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____204 = FStar_Options.record_hints ()  in
     if uu____204
     then
       let hints =
         let uu____206 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____206  in
       let hints_db =
         let uu____237 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____237; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____240 = FStar_Options.hint_file ()  in
         match uu____240 with
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
        | uu____344 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____360 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____366 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____366)
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
                   let uu____391 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____391 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____401 -> d :: out) [] theory_rev
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
            let uu____431 = filter_using_facts_from e theory  in
            (uu____431, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____441 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____465  ->
                     match uu____465 with
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
                          | uu____522 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____441 with
             | (theory',n_retained,n_pruned) ->
                 let uu____540 =
                   let uu____543 =
                     let uu____546 =
                       let uu____547 =
                         let uu____548 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____548  in
                       FStar_SMTEncoding_Term.Caption uu____547  in
                     [uu____546]  in
                   FStar_List.append theory' uu____543  in
                 (uu____540, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____569 = filter_using_facts_from e x  in (uu____569, false)
  
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
    let uu____750 = FStar_Util.string_of_int err.error_fuel  in
    let uu____751 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____750 uu____751
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
      let uu____1169 =
        let uu____1172 =
          let uu____1173 =
            let uu____1174 = FStar_Util.string_of_int n1  in
            let uu____1175 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1174 uu____1175
             in
          FStar_SMTEncoding_Term.Caption uu____1173  in
        let uu____1176 =
          let uu____1179 =
            let uu____1180 =
              let uu____1187 =
                let uu____1188 =
                  let uu____1193 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1196 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1193, uu____1196)  in
                FStar_SMTEncoding_Util.mkEq uu____1188  in
              (uu____1187, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1180  in
          let uu____1199 =
            let uu____1202 =
              let uu____1203 =
                let uu____1210 =
                  let uu____1211 =
                    let uu____1216 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1219 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1216, uu____1219)  in
                  FStar_SMTEncoding_Util.mkEq uu____1211  in
                (uu____1210, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1203  in
            [uu____1202; settings.query_decl]  in
          uu____1179 :: uu____1199  in
        uu____1172 :: uu____1176  in
      let uu____1222 =
        let uu____1225 =
          let uu____1228 =
            let uu____1231 =
              let uu____1232 =
                let uu____1237 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1237)  in
              FStar_SMTEncoding_Term.SetOption uu____1232  in
            [uu____1231;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1238 =
            let uu____1241 =
              let uu____1244 = FStar_Options.record_hints ()  in
              if uu____1244
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1248 =
              let uu____1251 =
                let uu____1254 = FStar_Options.print_z3_statistics ()  in
                if uu____1254
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1251 settings.query_suffix  in
            FStar_List.append uu____1241 uu____1248  in
          FStar_List.append uu____1228 uu____1238  in
        FStar_List.append label_assumptions uu____1225  in
      FStar_List.append uu____1169 uu____1222
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1277 = FStar_ST.op_Bang replaying_hints  in
      match uu____1277 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___87_1314  ->
               match uu___87_1314 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1320 -> FStar_Pervasives_Native.None)
      | uu____1323 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1340 -> FStar_Pervasives_Native.None
      | uu____1341 ->
          let uu____1342 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1342 with
           | (msg,error_labels) ->
               let err =
                 let uu____1352 =
                   FStar_List.map
                     (fun uu____1377  ->
                        match uu____1377 with
                        | (uu____1390,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1352
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1403 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1403
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1404 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1424 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1424
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1478 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1478)
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
            match err.error_messages with | [] -> false | uu____1554 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1572 = find_localized_errors errs  in
    FStar_Option.isSome uu____1572
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____1581 = find_localized_errors settings.query_errors  in
     match uu____1581 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____1591 =
                    let uu____1592 = error_to_short_string e  in
                    Prims.strcat "SMT solver says: " uu____1592  in
                  FStar_Errors.diag settings.query_range uu____1591));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____1594 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____1604 = error_to_short_string e  in
                     Prims.strcat "SMT solver says: " uu____1604))
              in
           FStar_All.pipe_right uu____1594 (FStar_String.concat "; ")  in
         let uu____1607 =
           let uu____1616 =
             let uu____1623 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1623,
               (settings.query_range))
              in
           [uu____1616]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____1607);
    (let uu____1636 =
       (FStar_Options.detail_errors ()) &&
         (let uu____1638 = FStar_Options.n_cores ()  in
          uu____1638 = (Prims.parse_int "1"))
        in
     if uu____1636
     then
       let initial_fuel1 =
         let uu___88_1640 = settings  in
         let uu____1641 = FStar_Options.initial_fuel ()  in
         let uu____1642 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___88_1640.query_env);
           query_decl = (uu___88_1640.query_decl);
           query_name = (uu___88_1640.query_name);
           query_index = (uu___88_1640.query_index);
           query_range = (uu___88_1640.query_range);
           query_fuel = uu____1641;
           query_ifuel = uu____1642;
           query_rlimit = (uu___88_1640.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___88_1640.query_errors);
           query_all_labels = (uu___88_1640.query_all_labels);
           query_suffix = (uu___88_1640.query_suffix);
           query_hash = (uu___88_1640.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____1663 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____1663
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
         (let uu____1717 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____1717)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1780 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1780
      then
        let uu____1781 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1781 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1789 -> "succeeded"
              | uu____1790 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1792 =
                let uu____1793 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1794 =
                  let uu____1795 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1795 ")"  in
                Prims.strcat uu____1793 uu____1794  in
              Prims.strcat "(" uu____1792  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1799 = FStar_Options.print_z3_statistics ()  in
              if uu____1799
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
                let uu____1817 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1817 "}"
              else ""  in
            ((let uu____1820 =
                let uu____1823 =
                  let uu____1826 =
                    let uu____1829 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1830 =
                      let uu____1833 =
                        let uu____1836 =
                          let uu____1839 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1840 =
                            let uu____1843 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1844 =
                              let uu____1847 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1848 =
                                let uu____1851 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1851; stats]  in
                              uu____1847 :: uu____1848  in
                            uu____1843 :: uu____1844  in
                          uu____1839 :: uu____1840  in
                        used_hint_tag :: uu____1836  in
                      tag :: uu____1833  in
                    uu____1829 :: uu____1830  in
                  (settings.query_name) :: uu____1826  in
                range :: uu____1823  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1820);
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
           | uu____1982 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____1988 =
               let uu____1989 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____1989  in
             store_hint uu____1988
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____1994 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2010 =
         (used_hint settings) &&
           (let uu____2012 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2012)
          in
       if uu____2010 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2108 = f q res  in
                     match uu____2108 with
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
            (let uu____2146 =
               let uu____2153 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2162,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2181,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2198 = FStar_Ident.text_of_lid q  in
                     (uu____2198, n1)
                  in
               match uu____2153 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2208 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2209 =
                       let uu____2210 = FStar_Options.z3_rlimit ()  in
                       uu____2210 * (Prims.parse_int "544656")  in
                     uu____2208 * uu____2209  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2215 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2216 = FStar_Options.initial_fuel ()  in
                     let uu____2217 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2215;
                       query_fuel = uu____2216;
                       query_ifuel = uu____2217;
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
                              { FStar_Util.hint_name = uu____2222;
                                FStar_Util.hint_index = uu____2223;
                                FStar_Util.fuel = uu____2224;
                                FStar_Util.ifuel = uu____2225;
                                FStar_Util.unsat_core = uu____2226;
                                FStar_Util.query_elapsed_time = uu____2227;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2146 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2248;
                         FStar_Util.hint_index = uu____2249;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2253;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___89_2262 = default_settings  in
                         {
                           query_env = (uu___89_2262.query_env);
                           query_decl = (uu___89_2262.query_decl);
                           query_name = (uu___89_2262.query_name);
                           query_index = (uu___89_2262.query_index);
                           query_range = (uu___89_2262.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___89_2262.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___89_2262.query_errors);
                           query_all_labels = (uu___89_2262.query_all_labels);
                           query_suffix = (uu___89_2262.query_suffix);
                           query_hash = (uu___89_2262.query_hash)
                         })]
                   | uu____2265 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2271 =
                     let uu____2272 = FStar_Options.max_ifuel ()  in
                     let uu____2273 = FStar_Options.initial_ifuel ()  in
                     uu____2272 > uu____2273  in
                   if uu____2271
                   then
                     let uu____2276 =
                       let uu___90_2277 = default_settings  in
                       let uu____2278 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___90_2277.query_env);
                         query_decl = (uu___90_2277.query_decl);
                         query_name = (uu___90_2277.query_name);
                         query_index = (uu___90_2277.query_index);
                         query_range = (uu___90_2277.query_range);
                         query_fuel = (uu___90_2277.query_fuel);
                         query_ifuel = uu____2278;
                         query_rlimit = (uu___90_2277.query_rlimit);
                         query_hint = (uu___90_2277.query_hint);
                         query_errors = (uu___90_2277.query_errors);
                         query_all_labels = (uu___90_2277.query_all_labels);
                         query_suffix = (uu___90_2277.query_suffix);
                         query_hash = (uu___90_2277.query_hash)
                       }  in
                     [uu____2276]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2283 =
                     let uu____2284 =
                       let uu____2285 = FStar_Options.max_fuel ()  in
                       uu____2285 / (Prims.parse_int "2")  in
                     let uu____2286 = FStar_Options.initial_fuel ()  in
                     uu____2284 > uu____2286  in
                   if uu____2283
                   then
                     let uu____2289 =
                       let uu___91_2290 = default_settings  in
                       let uu____2291 =
                         let uu____2292 = FStar_Options.max_fuel ()  in
                         uu____2292 / (Prims.parse_int "2")  in
                       let uu____2293 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___91_2290.query_env);
                         query_decl = (uu___91_2290.query_decl);
                         query_name = (uu___91_2290.query_name);
                         query_index = (uu___91_2290.query_index);
                         query_range = (uu___91_2290.query_range);
                         query_fuel = uu____2291;
                         query_ifuel = uu____2293;
                         query_rlimit = (uu___91_2290.query_rlimit);
                         query_hint = (uu___91_2290.query_hint);
                         query_errors = (uu___91_2290.query_errors);
                         query_all_labels = (uu___91_2290.query_all_labels);
                         query_suffix = (uu___91_2290.query_suffix);
                         query_hash = (uu___91_2290.query_hash)
                       }  in
                     [uu____2289]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2298 =
                     (let uu____2303 = FStar_Options.max_fuel ()  in
                      let uu____2304 = FStar_Options.initial_fuel ()  in
                      uu____2303 > uu____2304) &&
                       (let uu____2307 = FStar_Options.max_ifuel ()  in
                        let uu____2308 = FStar_Options.initial_ifuel ()  in
                        uu____2307 >= uu____2308)
                      in
                   if uu____2298
                   then
                     let uu____2311 =
                       let uu___92_2312 = default_settings  in
                       let uu____2313 = FStar_Options.max_fuel ()  in
                       let uu____2314 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___92_2312.query_env);
                         query_decl = (uu___92_2312.query_decl);
                         query_name = (uu___92_2312.query_name);
                         query_index = (uu___92_2312.query_index);
                         query_range = (uu___92_2312.query_range);
                         query_fuel = uu____2313;
                         query_ifuel = uu____2314;
                         query_rlimit = (uu___92_2312.query_rlimit);
                         query_hint = (uu___92_2312.query_hint);
                         query_errors = (uu___92_2312.query_errors);
                         query_all_labels = (uu___92_2312.query_all_labels);
                         query_suffix = (uu___92_2312.query_suffix);
                         query_hash = (uu___92_2312.query_hash)
                       }  in
                     [uu____2311]
                   else []  in
                 let min_fuel1 =
                   let uu____2319 =
                     let uu____2320 = FStar_Options.min_fuel ()  in
                     let uu____2321 = FStar_Options.initial_fuel ()  in
                     uu____2320 < uu____2321  in
                   if uu____2319
                   then
                     let uu____2324 =
                       let uu___93_2325 = default_settings  in
                       let uu____2326 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___93_2325.query_env);
                         query_decl = (uu___93_2325.query_decl);
                         query_name = (uu___93_2325.query_name);
                         query_index = (uu___93_2325.query_index);
                         query_range = (uu___93_2325.query_range);
                         query_fuel = uu____2326;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___93_2325.query_rlimit);
                         query_hint = (uu___93_2325.query_hint);
                         query_errors = (uu___93_2325.query_errors);
                         query_all_labels = (uu___93_2325.query_all_labels);
                         query_suffix = (uu___93_2325.query_suffix);
                         query_hash = (uu___93_2325.query_hash)
                       }  in
                     [uu____2324]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2348 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2348
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2350 = with_fuel_and_diagnostics config []  in
                    let uu____2353 =
                      let uu____2356 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2356  in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2350
                      uu____2353 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___94_2379 = default_settings  in
                        {
                          query_env = (uu___94_2379.query_env);
                          query_decl = (uu___94_2379.query_decl);
                          query_name = (uu___94_2379.query_name);
                          query_index = (uu___94_2379.query_index);
                          query_range = (uu___94_2379.query_range);
                          query_fuel = (uu___94_2379.query_fuel);
                          query_ifuel = (uu___94_2379.query_ifuel);
                          query_rlimit = (uu___94_2379.query_rlimit);
                          query_hint = (uu___94_2379.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___94_2379.query_all_labels);
                          query_suffix = (uu___94_2379.query_suffix);
                          query_hash = (uu___94_2379.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2380 =
                   let uu____2387 = FStar_Options.admit_smt_queries ()  in
                   let uu____2388 = FStar_Options.admit_except ()  in
                   (uu____2387, uu____2388)  in
                 (match uu____2380 with
                  | (true ,uu____2393) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2405 =
                              let uu____2406 =
                                let uu____2407 =
                                  let uu____2408 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2408 ")"  in
                                Prims.strcat ", " uu____2407  in
                              Prims.strcat default_settings.query_name
                                uu____2406
                               in
                            Prims.strcat "(" uu____2405  in
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
        (let uu____2436 =
           let uu____2437 =
             let uu____2438 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2438  in
           FStar_Util.format1 "Starting query at %s" uu____2437  in
         FStar_SMTEncoding_Encode.push uu____2436);
        (let uu____2439 = FStar_Options.no_smt ()  in
         if uu____2439
         then
           let uu____2440 =
             let uu____2449 =
               let uu____2456 =
                 let uu____2457 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____2457
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____2456,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____2449]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____2440
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____2472 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____2472 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____2508 =
                  let uu____2509 =
                    let uu____2510 =
                      let uu____2511 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____2511
                       in
                    FStar_Util.format1 "Ending query at %s" uu____2510  in
                  FStar_SMTEncoding_Encode.pop uu____2509  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____2512);
                           FStar_SMTEncoding_Term.freevars = uu____2513;
                           FStar_SMTEncoding_Term.rng = uu____2514;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____2515;
                       FStar_SMTEncoding_Term.assumption_name = uu____2516;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____2517;_}
                     -> pop1 ()
                 | uu____2532 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____2533 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____2535 -> failwith "Impossible")))
  
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
           let uu____2541 =
             let uu____2548 = FStar_Options.peek ()  in (e, g, uu____2548)
              in
           [uu____2541]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2563  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2565  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2567  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____2569  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____2578  -> fun uu____2579  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2590  -> fun uu____2591  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2594  -> fun uu____2595  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2601 =
             let uu____2608 = FStar_Options.peek ()  in (e, g, uu____2608)
              in
           [uu____2601]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2624  -> fun uu____2625  -> fun uu____2626  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2632  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2634  -> ())
  } 
open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result :
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____13,('Auu____14,'Auu____15) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____13,'Auu____14) FStar_Util.either
  =
  fun uu___60_32  ->
    match uu___60_32 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____47) -> FStar_Util.Inr r
  
let recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let format_hints_file_name : Prims.string -> Prims.string =
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
  
let finalize_hints_db : Prims.string -> unit =
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
  
let filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
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
          FStar_Util.smap_create (Prims.lift_native_int (10000))  in
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
  
let filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
          FStar_Pervasives_Native.tuple2
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
                                  (n_retained + (Prims.lift_native_int (1))),
                                  n_pruned)
                              else
                                if
                                  FStar_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + (Prims.lift_native_int (1))))
                          | uu____522 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.lift_native_int (0)),
                  (Prims.lift_native_int (0)))
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
  
let filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
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
let __proj__Mkerrors__item__error_reason : errors -> Prims.string =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
  
let __proj__Mkerrors__item__error_fuel : errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
  
let __proj__Mkerrors__item__error_ifuel : errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
  
let __proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
  
let __proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
  
let error_to_short_string : errors -> Prims.string =
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
let __proj__Mkquery_settings__item__query_env :
  query_settings -> FStar_TypeChecker_Env.env =
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
  
let __proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl =
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
  
let __proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string =
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
  
let __proj__Mkquery_settings__item__query_index : query_settings -> Prims.int
  =
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
  
let __proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range =
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
  
let __proj__Mkquery_settings__item__query_fuel : query_settings -> Prims.int
  =
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
  
let __proj__Mkquery_settings__item__query_ifuel : query_settings -> Prims.int
  =
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
  
let __proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int =
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
  
let __proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core =
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
  
let __proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list =
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
  
let __proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels =
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
  
let __proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list =
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
  
let __proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option =
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
  
let with_fuel_and_diagnostics :
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list
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
  
let used_hint : query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint 
let get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____1277 = FStar_ST.op_Bang replaying_hints  in
      match uu____1277 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___61_1314  ->
               match uu___61_1314 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1320 -> FStar_Pervasives_Native.None)
      | uu____1323 -> FStar_Pervasives_Native.None
  
let query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
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
  
let detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit =
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
  
let find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err  ->
            match err.error_messages with | [] -> false | uu____1554 -> true))
  
let has_localized_errors : errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1572 = find_localized_errors errs  in
    FStar_Option.isSome uu____1572
  
let report_errors : query_settings -> unit =
  fun settings  ->
    let uu____1580 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1582 = FStar_Options.n_cores ()  in
         uu____1582 = (Prims.lift_native_int (1)))
       in
    if uu____1580
    then
      let initial_fuel1 =
        let uu___62_1584 = settings  in
        let uu____1585 = FStar_Options.initial_fuel ()  in
        let uu____1586 = FStar_Options.initial_ifuel ()  in
        {
          query_env = (uu___62_1584.query_env);
          query_decl = (uu___62_1584.query_decl);
          query_name = (uu___62_1584.query_name);
          query_index = (uu___62_1584.query_index);
          query_range = (uu___62_1584.query_range);
          query_fuel = uu____1585;
          query_ifuel = uu____1586;
          query_rlimit = (uu___62_1584.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___62_1584.query_errors);
          query_all_labels = (uu___62_1584.query_all_labels);
          query_suffix = (uu___62_1584.query_suffix);
          query_hash = (uu___62_1584.query_hash)
        }  in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        (let uu____1607 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1607 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1661 = FStar_ST.op_Bang res  in
         FStar_Option.get uu____1661)
         in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1714 = find_localized_errors settings.query_errors  in
       match uu____1714 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1724 =
                      let uu____1725 = error_to_short_string e  in
                      Prims.strcat "SMT solver says: " uu____1725  in
                    FStar_Errors.diag settings.query_range uu____1724));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1727 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1737 = error_to_short_string e  in
                       Prims.strcat "SMT solver says: " uu____1737))
                in
             FStar_All.pipe_right uu____1727 (FStar_String.concat "; ")  in
           let uu____1740 =
             let uu____1749 =
               let uu____1756 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail
                  in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1756,
                 (settings.query_range))
                in
             [uu____1749]  in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1740)
  
let query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit =
  fun settings  ->
    fun z3result  ->
      let uu____1779 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1779
      then
        let uu____1780 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1780 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1788 -> "succeeded"
              | uu____1789 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1791 =
                let uu____1792 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1793 =
                  let uu____1794 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1794 ")"  in
                Prims.strcat uu____1792 uu____1793  in
              Prims.strcat "(" uu____1791  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1798 = FStar_Options.print_z3_statistics ()  in
              if uu____1798
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
                let uu____1816 =
                  FStar_Util.substring str (Prims.lift_native_int (0))
                    ((FStar_String.length str) - (Prims.lift_native_int (1)))
                   in
                Prims.strcat uu____1816 "}"
              else ""  in
            ((let uu____1819 =
                let uu____1822 =
                  let uu____1825 =
                    let uu____1828 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1829 =
                      let uu____1832 =
                        let uu____1835 =
                          let uu____1838 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1839 =
                            let uu____1842 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1843 =
                              let uu____1846 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1847 =
                                let uu____1850 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1850; stats]  in
                              uu____1846 :: uu____1847  in
                            uu____1842 :: uu____1843  in
                          uu____1838 :: uu____1839  in
                        used_hint_tag :: uu____1835  in
                      tag :: uu____1832  in
                    uu____1828 :: uu____1829  in
                  (settings.query_name) :: uu____1825  in
                range :: uu____1822  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1819);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1862  ->
                     match uu____1862 with
                     | (uu____1869,msg,range1) ->
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else ""  in
                         FStar_Errors.log_issue range1
                           (FStar_Errors.Warning_HitReplayFailed,
                             (Prims.strcat tag1 msg)))))
      else ()
  
let record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit =
  fun settings  ->
    fun z3result  ->
      let uu____1885 =
        let uu____1886 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1886  in
      if uu____1885
      then ()
      else
        (let mk_hint core =
           {
             FStar_Util.hint_name = (settings.query_name);
             FStar_Util.hint_index = (settings.query_index);
             FStar_Util.fuel = (settings.query_fuel);
             FStar_Util.ifuel = (settings.query_ifuel);
             FStar_Util.unsat_core = core;
             FStar_Util.query_elapsed_time = (Prims.lift_native_int (0));
             FStar_Util.hash =
               (match z3result.FStar_SMTEncoding_Z3.z3result_status with
                | FStar_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStar_SMTEncoding_Z3.z3result_query_hash
                | uu____1906 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____1913 = FStar_ST.op_Bang recorded_hints  in
           match uu____1913 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____1981 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____1987 =
               let uu____1988 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____1988  in
             store_hint uu____1987
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____1993 -> ())
  
let process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2009 =
         (used_hint settings) &&
           (let uu____2011 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2011)
          in
       if uu____2009 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result  in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
  
let fold_queries :
  query_settings Prims.list ->
    (query_settings -> (FStar_SMTEncoding_Z3.z3result -> unit) -> unit) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> unit) -> unit
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
                     let uu____2107 = f q res  in
                     match uu____2107 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2)
             in
          aux [] qs
  
let ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____2145 =
               let uu____2152 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2161,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____2180,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____2197 = FStar_Ident.text_of_lid q  in
                     (uu____2197, n1)
                  in
               match uu____2152 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2207 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2208 =
                       let uu____2209 = FStar_Options.z3_rlimit ()  in
                       uu____2209 * (Prims.lift_native_int (544656))  in
                     uu____2207 * uu____2208  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2214 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2215 = FStar_Options.initial_fuel ()  in
                     let uu____2216 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2214;
                       query_fuel = uu____2215;
                       query_ifuel = uu____2216;
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
                              { FStar_Util.hint_name = uu____2221;
                                FStar_Util.hint_index = uu____2222;
                                FStar_Util.fuel = uu____2223;
                                FStar_Util.ifuel = uu____2224;
                                FStar_Util.unsat_core = uu____2225;
                                FStar_Util.query_elapsed_time = uu____2226;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2145 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2247;
                         FStar_Util.hint_index = uu____2248;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2252;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___63_2261 = default_settings  in
                         {
                           query_env = (uu___63_2261.query_env);
                           query_decl = (uu___63_2261.query_decl);
                           query_name = (uu___63_2261.query_name);
                           query_index = (uu___63_2261.query_index);
                           query_range = (uu___63_2261.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___63_2261.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___63_2261.query_errors);
                           query_all_labels = (uu___63_2261.query_all_labels);
                           query_suffix = (uu___63_2261.query_suffix);
                           query_hash = (uu___63_2261.query_hash)
                         })]
                   | uu____2264 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2270 =
                     let uu____2271 = FStar_Options.max_ifuel ()  in
                     let uu____2272 = FStar_Options.initial_ifuel ()  in
                     uu____2271 > uu____2272  in
                   if uu____2270
                   then
                     let uu____2275 =
                       let uu___64_2276 = default_settings  in
                       let uu____2277 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___64_2276.query_env);
                         query_decl = (uu___64_2276.query_decl);
                         query_name = (uu___64_2276.query_name);
                         query_index = (uu___64_2276.query_index);
                         query_range = (uu___64_2276.query_range);
                         query_fuel = (uu___64_2276.query_fuel);
                         query_ifuel = uu____2277;
                         query_rlimit = (uu___64_2276.query_rlimit);
                         query_hint = (uu___64_2276.query_hint);
                         query_errors = (uu___64_2276.query_errors);
                         query_all_labels = (uu___64_2276.query_all_labels);
                         query_suffix = (uu___64_2276.query_suffix);
                         query_hash = (uu___64_2276.query_hash)
                       }  in
                     [uu____2275]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2282 =
                     let uu____2283 =
                       let uu____2284 = FStar_Options.max_fuel ()  in
                       uu____2284 / (Prims.lift_native_int (2))  in
                     let uu____2285 = FStar_Options.initial_fuel ()  in
                     uu____2283 > uu____2285  in
                   if uu____2282
                   then
                     let uu____2288 =
                       let uu___65_2289 = default_settings  in
                       let uu____2290 =
                         let uu____2291 = FStar_Options.max_fuel ()  in
                         uu____2291 / (Prims.lift_native_int (2))  in
                       let uu____2292 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___65_2289.query_env);
                         query_decl = (uu___65_2289.query_decl);
                         query_name = (uu___65_2289.query_name);
                         query_index = (uu___65_2289.query_index);
                         query_range = (uu___65_2289.query_range);
                         query_fuel = uu____2290;
                         query_ifuel = uu____2292;
                         query_rlimit = (uu___65_2289.query_rlimit);
                         query_hint = (uu___65_2289.query_hint);
                         query_errors = (uu___65_2289.query_errors);
                         query_all_labels = (uu___65_2289.query_all_labels);
                         query_suffix = (uu___65_2289.query_suffix);
                         query_hash = (uu___65_2289.query_hash)
                       }  in
                     [uu____2288]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2297 =
                     (let uu____2302 = FStar_Options.max_fuel ()  in
                      let uu____2303 = FStar_Options.initial_fuel ()  in
                      uu____2302 > uu____2303) &&
                       (let uu____2306 = FStar_Options.max_ifuel ()  in
                        let uu____2307 = FStar_Options.initial_ifuel ()  in
                        uu____2306 >= uu____2307)
                      in
                   if uu____2297
                   then
                     let uu____2310 =
                       let uu___66_2311 = default_settings  in
                       let uu____2312 = FStar_Options.max_fuel ()  in
                       let uu____2313 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___66_2311.query_env);
                         query_decl = (uu___66_2311.query_decl);
                         query_name = (uu___66_2311.query_name);
                         query_index = (uu___66_2311.query_index);
                         query_range = (uu___66_2311.query_range);
                         query_fuel = uu____2312;
                         query_ifuel = uu____2313;
                         query_rlimit = (uu___66_2311.query_rlimit);
                         query_hint = (uu___66_2311.query_hint);
                         query_errors = (uu___66_2311.query_errors);
                         query_all_labels = (uu___66_2311.query_all_labels);
                         query_suffix = (uu___66_2311.query_suffix);
                         query_hash = (uu___66_2311.query_hash)
                       }  in
                     [uu____2310]
                   else []  in
                 let min_fuel1 =
                   let uu____2318 =
                     let uu____2319 = FStar_Options.min_fuel ()  in
                     let uu____2320 = FStar_Options.initial_fuel ()  in
                     uu____2319 < uu____2320  in
                   if uu____2318
                   then
                     let uu____2323 =
                       let uu___67_2324 = default_settings  in
                       let uu____2325 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___67_2324.query_env);
                         query_decl = (uu___67_2324.query_decl);
                         query_name = (uu___67_2324.query_name);
                         query_index = (uu___67_2324.query_index);
                         query_range = (uu___67_2324.query_range);
                         query_fuel = uu____2325;
                         query_ifuel = (Prims.lift_native_int (1));
                         query_rlimit = (uu___67_2324.query_rlimit);
                         query_hint = (uu___67_2324.query_hint);
                         query_errors = (uu___67_2324.query_errors);
                         query_all_labels = (uu___67_2324.query_all_labels);
                         query_suffix = (uu___67_2324.query_suffix);
                         query_hash = (uu___67_2324.query_hash)
                       }  in
                     [uu____2323]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2347 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2347
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2349 = with_fuel_and_diagnostics config []  in
                    let uu____2352 =
                      let uu____2355 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2355  in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2349
                      uu____2352 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___68_2378 = default_settings  in
                        {
                          query_env = (uu___68_2378.query_env);
                          query_decl = (uu___68_2378.query_decl);
                          query_name = (uu___68_2378.query_name);
                          query_index = (uu___68_2378.query_index);
                          query_range = (uu___68_2378.query_range);
                          query_fuel = (uu___68_2378.query_fuel);
                          query_ifuel = (uu___68_2378.query_ifuel);
                          query_rlimit = (uu___68_2378.query_rlimit);
                          query_hint = (uu___68_2378.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___68_2378.query_all_labels);
                          query_suffix = (uu___68_2378.query_suffix);
                          query_hash = (uu___68_2378.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2379 =
                   let uu____2386 = FStar_Options.admit_smt_queries ()  in
                   let uu____2387 = FStar_Options.admit_except ()  in
                   (uu____2386, uu____2387)  in
                 (match uu____2379 with
                  | (true ,uu____2392) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2404 =
                              let uu____2405 =
                                let uu____2406 =
                                  let uu____2407 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2407 ")"  in
                                Prims.strcat ", " uu____2406  in
                              Prims.strcat default_settings.query_name
                                uu____2405
                               in
                            Prims.strcat "(" uu____2404  in
                          full_query_id <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
  
let solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2435 =
           let uu____2436 =
             let uu____2437 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2437  in
           FStar_Util.format1 "Starting query at %s" uu____2436  in
         FStar_SMTEncoding_Encode.push uu____2435);
        (let uu____2438 = FStar_Options.no_smt ()  in
         if uu____2438
         then
           let uu____2439 =
             let uu____2448 =
               let uu____2455 =
                 let uu____2456 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____2456
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____2455,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____2448]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____2439
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____2471 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____2471 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____2507 =
                  let uu____2508 =
                    let uu____2509 =
                      let uu____2510 = FStar_TypeChecker_Env.get_range tcenv1
                         in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____2510
                       in
                    FStar_Util.format1 "Ending query at %s" uu____2509  in
                  FStar_SMTEncoding_Encode.pop uu____2508  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____2511);
                           FStar_SMTEncoding_Term.freevars = uu____2512;
                           FStar_SMTEncoding_Term.rng = uu____2513;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____2514;
                       FStar_SMTEncoding_Term.assumption_name = uu____2515;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____2516;_}
                     -> pop1 ()
                 | uu____2531 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____2532 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____2534 -> failwith "Impossible")))
  
let solver : FStar_TypeChecker_Env.solver_t =
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
           let uu____2540 =
             let uu____2547 = FStar_Options.peek ()  in (e, g, uu____2547)
              in
           [uu____2540]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let dummy : FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2562  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2564  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2566  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2569  -> fun uu____2570  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2573  -> fun uu____2574  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2580 =
             let uu____2587 = FStar_Options.peek ()  in (e, g, uu____2587)
              in
           [uu____2580]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2603  -> fun uu____2604  -> fun uu____2605  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2611  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2613  -> ())
  } 
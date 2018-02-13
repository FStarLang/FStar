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
let (format_hints_file_name : Prims.string -> Prims.bool -> Prims.string) =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      let uu____139 =
        if checking_or_using_extracted_interface
        then FStar_Parser_Dep.interface_filename src_filename
        else src_filename  in
      FStar_Util.format1 "%s.hints" uu____139
  
let initialize_hints_db :
  'Auu____145 . Prims.string -> Prims.bool -> 'Auu____145 -> Prims.unit =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      fun format_filename  ->
        (let uu____159 = FStar_Options.record_hints ()  in
         if uu____159
         then
           FStar_ST.op_Colon_Equals recorded_hints
             (FStar_Pervasives_Native.Some [])
         else ());
        (let uu____190 = FStar_Options.use_hints ()  in
         if uu____190
         then
           let norm_src_filename =
             FStar_Util.normalize_file_path src_filename  in
           let val_filename =
             let uu____193 = FStar_Options.hint_file ()  in
             match uu____193 with
             | FStar_Pervasives_Native.Some fn -> fn
             | FStar_Pervasives_Native.None  ->
                 format_hints_file_name norm_src_filename
                   checking_or_using_extracted_interface
              in
           let uu____197 = FStar_Util.read_hints val_filename  in
           match uu____197 with
           | FStar_Pervasives_Native.Some hints ->
               let expected_digest =
                 FStar_Util.digest_of_file norm_src_filename  in
               ((let uu____203 = FStar_Options.hint_info ()  in
                 if uu____203
                 then
                   let uu____204 =
                     let uu____205 = FStar_Options.hint_file ()  in
                     match uu____205 with
                     | FStar_Pervasives_Native.Some fn ->
                         Prims.strcat " from '"
                           (Prims.strcat val_filename "'")
                     | uu____209 -> ""  in
                   FStar_Util.print3 "(%s) digest is %s%s.\n"
                     norm_src_filename
                     (if hints.FStar_Util.module_digest = expected_digest
                      then "valid; using hints"
                      else "invalid; using potentially stale hints")
                     uu____204
                 else ());
                FStar_ST.op_Colon_Equals replaying_hints
                  (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
           | FStar_Pervasives_Native.None  ->
               let uu____237 = FStar_Options.hint_info ()  in
               (if uu____237
                then
                  FStar_Util.print1 "(%s) Unable to read hint file.\n"
                    norm_src_filename
                else ())
         else ())
  
let (finalize_hints_db : Prims.string -> Prims.bool -> Prims.unit) =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      (let uu____247 = FStar_Options.record_hints ()  in
       if uu____247
       then
         let hints =
           let uu____249 = FStar_ST.op_Bang recorded_hints  in
           FStar_Option.get uu____249  in
         let hints_db =
           let uu____276 = FStar_Util.digest_of_file src_filename  in
           { FStar_Util.module_digest = uu____276; FStar_Util.hints = hints }
            in
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____279 = FStar_Options.hint_file ()  in
           match uu____279 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
                 checking_or_using_extracted_interface
            in
         FStar_Util.write_hints val_filename hints_db
       else ());
      FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
      FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
  
let with_hints_db :
  'a . Prims.string -> Prims.bool -> (Prims.unit -> 'a) -> 'a =
  fun fname  ->
    fun checking_or_using_extracted_interface  ->
      fun f  ->
        initialize_hints_db fname checking_or_using_extracted_interface false;
        (let result = f ()  in
         finalize_hints_db fname checking_or_using_extracted_interface;
         result)
  
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
        | uu____369 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____381 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____387 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____387)
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
                   let uu____412 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____412 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____422 -> d :: out) [] theory_rev
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
            let uu____446 = filter_using_facts_from e theory  in
            (uu____446, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____456 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____480  ->
                     match uu____480 with
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
                          | uu____537 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____456 with
             | (theory',n_retained,n_pruned) ->
                 let uu____555 =
                   let uu____558 =
                     let uu____561 =
                       let uu____562 =
                         let uu____563 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____563  in
                       FStar_SMTEncoding_Term.Caption uu____562  in
                     [uu____561]  in
                   FStar_List.append theory' uu____558  in
                 (uu____555, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____580 = filter_using_facts_from e x  in (uu____580, false)
  
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
    let uu____744 = FStar_Util.string_of_int err.error_fuel  in
    let uu____745 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____744 uu____745
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
      let uu____1120 =
        let uu____1123 =
          let uu____1124 =
            let uu____1125 = FStar_Util.string_of_int n1  in
            let uu____1126 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1125 uu____1126
             in
          FStar_SMTEncoding_Term.Caption uu____1124  in
        let uu____1127 =
          let uu____1130 =
            let uu____1131 =
              let uu____1138 =
                let uu____1139 =
                  let uu____1144 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1147 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1144, uu____1147)  in
                FStar_SMTEncoding_Util.mkEq uu____1139  in
              (uu____1138, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1131  in
          let uu____1150 =
            let uu____1153 =
              let uu____1154 =
                let uu____1161 =
                  let uu____1162 =
                    let uu____1167 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1170 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1167, uu____1170)  in
                  FStar_SMTEncoding_Util.mkEq uu____1162  in
                (uu____1161, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1154  in
            [uu____1153; settings.query_decl]  in
          uu____1130 :: uu____1150  in
        uu____1123 :: uu____1127  in
      let uu____1173 =
        let uu____1176 =
          let uu____1179 =
            let uu____1182 =
              let uu____1183 =
                let uu____1188 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1188)  in
              FStar_SMTEncoding_Term.SetOption uu____1183  in
            [uu____1182;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1189 =
            let uu____1192 =
              let uu____1195 = FStar_Options.record_hints ()  in
              if uu____1195
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1199 =
              let uu____1202 =
                let uu____1205 = FStar_Options.print_z3_statistics ()  in
                if uu____1205
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1202 settings.query_suffix  in
            FStar_List.append uu____1192 uu____1199  in
          FStar_List.append uu____1179 uu____1189  in
        FStar_List.append label_assumptions uu____1176  in
      FStar_List.append uu____1120 uu____1173
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1222 = FStar_ST.op_Bang replaying_hints  in
      match uu____1222 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___58_1255  ->
               match uu___58_1255 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1261 -> FStar_Pervasives_Native.None)
      | uu____1264 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1277 -> FStar_Pervasives_Native.None
      | uu____1278 ->
          let uu____1279 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1279 with
           | (msg,error_labels) ->
               let err =
                 let uu____1289 =
                   FStar_List.map
                     (fun uu____1314  ->
                        match uu____1314 with
                        | (uu____1327,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1289
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1336 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1336
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1337 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1355 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1355
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1457 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1457)
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
            match err.error_messages with | [] -> false | uu____1579 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1595 = find_localized_errors errs  in
    FStar_Option.isSome uu____1595
  
let (report_errors : query_settings -> Prims.unit) =
  fun settings  ->
    let uu____1601 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1603 = FStar_Options.n_cores ()  in
         uu____1603 = (Prims.parse_int "1"))
       in
    if uu____1601
    then
      let initial_fuel1 =
        let uu___59_1605 = settings  in
        let uu____1606 = FStar_Options.initial_fuel ()  in
        let uu____1607 = FStar_Options.initial_ifuel ()  in
        {
          query_env = (uu___59_1605.query_env);
          query_decl = (uu___59_1605.query_decl);
          query_name = (uu___59_1605.query_name);
          query_index = (uu___59_1605.query_index);
          query_range = (uu___59_1605.query_range);
          query_fuel = uu____1606;
          query_ifuel = uu____1607;
          query_rlimit = (uu___59_1605.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___59_1605.query_errors);
          query_all_labels = (uu___59_1605.query_all_labels);
          query_suffix = (uu___59_1605.query_suffix);
          query_hash = (uu___59_1605.query_hash)
        }  in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        (let uu____1626 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1626 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1728 = FStar_ST.op_Bang res  in
         FStar_Option.get uu____1728)
         in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1829 = find_localized_errors settings.query_errors  in
       match uu____1829 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1839 =
                      let uu____1840 = error_to_short_string e  in
                      Prims.strcat "SMT solver says: " uu____1840  in
                    FStar_Errors.diag settings.query_range uu____1839));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1842 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1852 = error_to_short_string e  in
                       Prims.strcat "SMT solver says: " uu____1852))
                in
             FStar_All.pipe_right uu____1842 (FStar_String.concat "; ")  in
           let uu____1855 =
             let uu____1864 =
               let uu____1871 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail
                  in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1871,
                 (settings.query_range))
                in
             [uu____1864]  in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1855)
  
let (query_info :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1890 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1890
      then
        let uu____1891 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1891 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1899 -> "succeeded"
              | uu____1900 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1902 =
                let uu____1903 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1904 =
                  let uu____1905 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1905 ")"  in
                Prims.strcat uu____1903 uu____1904  in
              Prims.strcat "(" uu____1902  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1909 = FStar_Options.print_z3_statistics ()  in
              if uu____1909
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
                let uu____1921 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1921 "}"
              else ""  in
            ((let uu____1924 =
                let uu____1927 =
                  let uu____1930 =
                    let uu____1933 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1934 =
                      let uu____1937 =
                        let uu____1940 =
                          let uu____1943 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1944 =
                            let uu____1947 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1948 =
                              let uu____1951 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1952 =
                                let uu____1955 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1955; stats]  in
                              uu____1951 :: uu____1952  in
                            uu____1947 :: uu____1948  in
                          uu____1943 :: uu____1944  in
                        used_hint_tag :: uu____1940  in
                      tag :: uu____1937  in
                    uu____1933 :: uu____1934  in
                  (settings.query_name) :: uu____1930  in
                range :: uu____1927  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1924);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1967  ->
                     match uu____1967 with
                     | (uu____1974,msg,range1) ->
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
      let uu____1986 =
        let uu____1987 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1987  in
      if uu____1986
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
                | uu____2005 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____2010 = FStar_ST.op_Bang recorded_hints  in
           match uu____2010 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2070 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2078 =
               let uu____2079 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2079  in
             store_hint uu____2078
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2084 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2096 =
         (used_hint settings) &&
           (let uu____2098 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2098)
          in
       if uu____2096 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2184 = f q res  in
                     match uu____2184 with
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
            (let uu____2212 =
               let uu____2219 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1)
                  in
               match uu____2219 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2251 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2252 =
                       let uu____2253 = FStar_Options.z3_rlimit ()  in
                       uu____2253 * (Prims.parse_int "544656")  in
                     uu____2251 * uu____2252  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2258 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2259 = FStar_Options.initial_fuel ()  in
                     let uu____2260 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2258;
                       query_fuel = uu____2259;
                       query_ifuel = uu____2260;
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
                              { FStar_Util.hint_name = uu____2265;
                                FStar_Util.hint_index = uu____2266;
                                FStar_Util.fuel = uu____2267;
                                FStar_Util.ifuel = uu____2268;
                                FStar_Util.unsat_core = uu____2269;
                                FStar_Util.query_elapsed_time = uu____2270;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2212 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2291;
                         FStar_Util.hint_index = uu____2292;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2296;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___60_2305 = default_settings  in
                         {
                           query_env = (uu___60_2305.query_env);
                           query_decl = (uu___60_2305.query_decl);
                           query_name = (uu___60_2305.query_name);
                           query_index = (uu___60_2305.query_index);
                           query_range = (uu___60_2305.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___60_2305.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___60_2305.query_errors);
                           query_all_labels = (uu___60_2305.query_all_labels);
                           query_suffix = (uu___60_2305.query_suffix);
                           query_hash = (uu___60_2305.query_hash)
                         })]
                   | uu____2308 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2314 =
                     let uu____2315 = FStar_Options.max_ifuel ()  in
                     let uu____2316 = FStar_Options.initial_ifuel ()  in
                     uu____2315 > uu____2316  in
                   if uu____2314
                   then
                     let uu____2319 =
                       let uu___61_2320 = default_settings  in
                       let uu____2321 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___61_2320.query_env);
                         query_decl = (uu___61_2320.query_decl);
                         query_name = (uu___61_2320.query_name);
                         query_index = (uu___61_2320.query_index);
                         query_range = (uu___61_2320.query_range);
                         query_fuel = (uu___61_2320.query_fuel);
                         query_ifuel = uu____2321;
                         query_rlimit = (uu___61_2320.query_rlimit);
                         query_hint = (uu___61_2320.query_hint);
                         query_errors = (uu___61_2320.query_errors);
                         query_all_labels = (uu___61_2320.query_all_labels);
                         query_suffix = (uu___61_2320.query_suffix);
                         query_hash = (uu___61_2320.query_hash)
                       }  in
                     [uu____2319]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2326 =
                     let uu____2327 =
                       let uu____2328 = FStar_Options.max_fuel ()  in
                       uu____2328 / (Prims.parse_int "2")  in
                     let uu____2335 = FStar_Options.initial_fuel ()  in
                     uu____2327 > uu____2335  in
                   if uu____2326
                   then
                     let uu____2338 =
                       let uu___62_2339 = default_settings  in
                       let uu____2340 =
                         let uu____2341 = FStar_Options.max_fuel ()  in
                         uu____2341 / (Prims.parse_int "2")  in
                       let uu____2348 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___62_2339.query_env);
                         query_decl = (uu___62_2339.query_decl);
                         query_name = (uu___62_2339.query_name);
                         query_index = (uu___62_2339.query_index);
                         query_range = (uu___62_2339.query_range);
                         query_fuel = uu____2340;
                         query_ifuel = uu____2348;
                         query_rlimit = (uu___62_2339.query_rlimit);
                         query_hint = (uu___62_2339.query_hint);
                         query_errors = (uu___62_2339.query_errors);
                         query_all_labels = (uu___62_2339.query_all_labels);
                         query_suffix = (uu___62_2339.query_suffix);
                         query_hash = (uu___62_2339.query_hash)
                       }  in
                     [uu____2338]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2353 =
                     (let uu____2358 = FStar_Options.max_fuel ()  in
                      let uu____2359 = FStar_Options.initial_fuel ()  in
                      uu____2358 > uu____2359) &&
                       (let uu____2362 = FStar_Options.max_ifuel ()  in
                        let uu____2363 = FStar_Options.initial_ifuel ()  in
                        uu____2362 >= uu____2363)
                      in
                   if uu____2353
                   then
                     let uu____2366 =
                       let uu___63_2367 = default_settings  in
                       let uu____2368 = FStar_Options.max_fuel ()  in
                       let uu____2369 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___63_2367.query_env);
                         query_decl = (uu___63_2367.query_decl);
                         query_name = (uu___63_2367.query_name);
                         query_index = (uu___63_2367.query_index);
                         query_range = (uu___63_2367.query_range);
                         query_fuel = uu____2368;
                         query_ifuel = uu____2369;
                         query_rlimit = (uu___63_2367.query_rlimit);
                         query_hint = (uu___63_2367.query_hint);
                         query_errors = (uu___63_2367.query_errors);
                         query_all_labels = (uu___63_2367.query_all_labels);
                         query_suffix = (uu___63_2367.query_suffix);
                         query_hash = (uu___63_2367.query_hash)
                       }  in
                     [uu____2366]
                   else []  in
                 let min_fuel1 =
                   let uu____2374 =
                     let uu____2375 = FStar_Options.min_fuel ()  in
                     let uu____2376 = FStar_Options.initial_fuel ()  in
                     uu____2375 < uu____2376  in
                   if uu____2374
                   then
                     let uu____2379 =
                       let uu___64_2380 = default_settings  in
                       let uu____2381 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___64_2380.query_env);
                         query_decl = (uu___64_2380.query_decl);
                         query_name = (uu___64_2380.query_name);
                         query_index = (uu___64_2380.query_index);
                         query_range = (uu___64_2380.query_range);
                         query_fuel = uu____2381;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___64_2380.query_rlimit);
                         query_hint = (uu___64_2380.query_hint);
                         query_errors = (uu___64_2380.query_errors);
                         query_all_labels = (uu___64_2380.query_all_labels);
                         query_suffix = (uu___64_2380.query_suffix);
                         query_hash = (uu___64_2380.query_hash)
                       }  in
                     [uu____2379]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2399 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2399
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2401 = with_fuel_and_diagnostics config []  in
                    let uu____2404 =
                      let uu____2407 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2407  in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2401
                      uu____2404 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___65_2426 = default_settings  in
                        {
                          query_env = (uu___65_2426.query_env);
                          query_decl = (uu___65_2426.query_decl);
                          query_name = (uu___65_2426.query_name);
                          query_index = (uu___65_2426.query_index);
                          query_range = (uu___65_2426.query_range);
                          query_fuel = (uu___65_2426.query_fuel);
                          query_ifuel = (uu___65_2426.query_ifuel);
                          query_rlimit = (uu___65_2426.query_rlimit);
                          query_hint = (uu___65_2426.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___65_2426.query_all_labels);
                          query_suffix = (uu___65_2426.query_suffix);
                          query_hash = (uu___65_2426.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2427 =
                   let uu____2434 = FStar_Options.admit_smt_queries ()  in
                   let uu____2435 = FStar_Options.admit_except ()  in
                   (uu____2434, uu____2435)  in
                 (match uu____2427 with
                  | (true ,uu____2440) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2452 =
                              let uu____2453 =
                                let uu____2454 =
                                  let uu____2455 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2455 ")"  in
                                Prims.strcat ", " uu____2454  in
                              Prims.strcat default_settings.query_name
                                uu____2453
                               in
                            Prims.strcat "(" uu____2452  in
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
        (let uu____2477 =
           let uu____2478 =
             let uu____2479 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2479  in
           FStar_Util.format1 "Starting query at %s" uu____2478  in
         FStar_SMTEncoding_Encode.push uu____2477);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____2481 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____2481 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2515 =
               let uu____2516 =
                 let uu____2517 =
                   let uu____2518 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2518
                    in
                 FStar_Util.format1 "Ending query at %s" uu____2517  in
               FStar_SMTEncoding_Encode.pop uu____2516  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2519);
                        FStar_SMTEncoding_Term.freevars = uu____2520;
                        FStar_SMTEncoding_Term.rng = uu____2521;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2522;
                    FStar_SMTEncoding_Term.assumption_name = uu____2523;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2524;_}
                  -> pop1 ()
              | uu____2539 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2540 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2542 -> failwith "Impossible"))
  
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
           let uu____2548 =
             let uu____2555 = FStar_Options.peek ()  in (e, g, uu____2555)
              in
           [uu____2548]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2570  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2572  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2574  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2577  -> fun uu____2578  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2581  -> fun uu____2582  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2588 =
             let uu____2595 = FStar_Options.peek ()  in (e, g, uu____2595)
              in
           [uu____2588]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2611  -> fun uu____2612  -> fun uu____2613  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2619  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2621  -> ())
  } 
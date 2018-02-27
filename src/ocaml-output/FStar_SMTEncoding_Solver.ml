open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result :
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____11,('Auu____10,'Auu____9) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____11,'Auu____10) FStar_Util.either
  =
  fun uu___58_27  ->
    match uu___58_27 with
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
      let uu____87 =
        if checking_or_using_extracted_interface
        then FStar_Parser_Dep.interface_filename src_filename
        else src_filename  in
      FStar_Util.format1 "%s.hints" uu____87
  
let initialize_hints_db :
  'Auu____93 . Prims.string -> Prims.bool -> 'Auu____93 -> Prims.unit =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      fun format_filename  ->
        (let uu____107 = FStar_Options.record_hints ()  in
         if uu____107
         then
           FStar_ST.op_Colon_Equals recorded_hints
             (FStar_Pervasives_Native.Some [])
         else ());
        (let uu____138 = FStar_Options.use_hints ()  in
         if uu____138
         then
           let norm_src_filename =
             FStar_Util.normalize_file_path src_filename  in
           let src_filename_for_printing =
             if checking_or_using_extracted_interface
             then FStar_Parser_Dep.interface_filename norm_src_filename
             else norm_src_filename  in
           let val_filename =
             let uu____143 = FStar_Options.hint_file ()  in
             match uu____143 with
             | FStar_Pervasives_Native.Some fn -> fn
             | FStar_Pervasives_Native.None  ->
                 format_hints_file_name norm_src_filename
                   checking_or_using_extracted_interface
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
                         Prims.strcat " from '"
                           (Prims.strcat val_filename "'")
                     | uu____159 -> ""  in
                   FStar_Util.print3 "(%s) digest is %s%s.\n"
                     src_filename_for_printing
                     (if hints.FStar_Util.module_digest = expected_digest
                      then "valid; using hints"
                      else "invalid; using potentially stale hints")
                     uu____154
                 else ());
                FStar_ST.op_Colon_Equals replaying_hints
                  (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
           | FStar_Pervasives_Native.None  ->
               let uu____187 = FStar_Options.hint_info ()  in
               (if uu____187
                then
                  FStar_Util.print1 "(%s) Unable to read hint file.\n"
                    src_filename_for_printing
                else ())
         else ())
  
let (finalize_hints_db : Prims.string -> Prims.bool -> Prims.unit) =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      (let uu____197 = FStar_Options.record_hints ()  in
       if uu____197
       then
         let hints =
           let uu____199 = FStar_ST.op_Bang recorded_hints  in
           FStar_Option.get uu____199  in
         let hints_db =
           let uu____226 = FStar_Util.digest_of_file src_filename  in
           { FStar_Util.module_digest = uu____226; FStar_Util.hints = hints }
            in
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____229 = FStar_Options.hint_file ()  in
           match uu____229 with
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
        | uu____319 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____331 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____337 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____337)
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
                   let uu____362 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____362 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____372 -> d :: out) [] theory_rev
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
            let uu____396 = filter_using_facts_from e theory  in
            (uu____396, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____406 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____430  ->
                     match uu____430 with
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
                          | uu____487 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____406 with
             | (theory',n_retained,n_pruned) ->
                 let uu____505 =
                   let uu____508 =
                     let uu____511 =
                       let uu____512 =
                         let uu____513 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____513  in
                       FStar_SMTEncoding_Term.Caption uu____512  in
                     [uu____511]  in
                   FStar_List.append theory' uu____508  in
                 (uu____505, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____530 = filter_using_facts_from e x  in (uu____530, false)
  
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
    let uu____694 = FStar_Util.string_of_int err.error_fuel  in
    let uu____695 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____694 uu____695
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
      let uu____1070 =
        let uu____1073 =
          let uu____1074 =
            let uu____1075 = FStar_Util.string_of_int n1  in
            let uu____1076 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1075 uu____1076
             in
          FStar_SMTEncoding_Term.Caption uu____1074  in
        let uu____1077 =
          let uu____1080 =
            let uu____1081 =
              let uu____1088 =
                let uu____1089 =
                  let uu____1094 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1097 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1094, uu____1097)  in
                FStar_SMTEncoding_Util.mkEq uu____1089  in
              (uu____1088, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1081  in
          let uu____1100 =
            let uu____1103 =
              let uu____1104 =
                let uu____1111 =
                  let uu____1112 =
                    let uu____1117 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1120 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1117, uu____1120)  in
                  FStar_SMTEncoding_Util.mkEq uu____1112  in
                (uu____1111, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1104  in
            [uu____1103; settings.query_decl]  in
          uu____1080 :: uu____1100  in
        uu____1073 :: uu____1077  in
      let uu____1123 =
        let uu____1126 =
          let uu____1129 =
            let uu____1132 =
              let uu____1133 =
                let uu____1138 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1138)  in
              FStar_SMTEncoding_Term.SetOption uu____1133  in
            [uu____1132;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1139 =
            let uu____1142 =
              let uu____1145 = FStar_Options.record_hints ()  in
              if uu____1145
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1149 =
              let uu____1152 =
                let uu____1155 = FStar_Options.print_z3_statistics ()  in
                if uu____1155
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1152 settings.query_suffix  in
            FStar_List.append uu____1142 uu____1149  in
          FStar_List.append uu____1129 uu____1139  in
        FStar_List.append label_assumptions uu____1126  in
      FStar_List.append uu____1070 uu____1123
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1172 = FStar_ST.op_Bang replaying_hints  in
      match uu____1172 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___59_1205  ->
               match uu___59_1205 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1211 -> FStar_Pervasives_Native.None)
      | uu____1214 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1227 -> FStar_Pervasives_Native.None
      | uu____1228 ->
          let uu____1229 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1229 with
           | (msg,error_labels) ->
               let err =
                 let uu____1239 =
                   FStar_List.map
                     (fun uu____1264  ->
                        match uu____1264 with
                        | (uu____1277,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1239
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1286 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1286
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1287 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1305 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1305
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1355 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1355)
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
            match err.error_messages with | [] -> false | uu____1425 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1441 = find_localized_errors errs  in
    FStar_Option.isSome uu____1441
  
let (report_errors : query_settings -> Prims.unit) =
  fun settings  ->
    let uu____1447 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1449 = FStar_Options.n_cores ()  in
         uu____1449 = (Prims.parse_int "1"))
       in
    if uu____1447
    then
      let initial_fuel1 =
        let uu___60_1451 = settings  in
        let uu____1452 = FStar_Options.initial_fuel ()  in
        let uu____1453 = FStar_Options.initial_ifuel ()  in
        {
          query_env = (uu___60_1451.query_env);
          query_decl = (uu___60_1451.query_decl);
          query_name = (uu___60_1451.query_name);
          query_index = (uu___60_1451.query_index);
          query_range = (uu___60_1451.query_range);
          query_fuel = uu____1452;
          query_ifuel = uu____1453;
          query_rlimit = (uu___60_1451.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___60_1451.query_errors);
          query_all_labels = (uu___60_1451.query_all_labels);
          query_suffix = (uu___60_1451.query_suffix);
          query_hash = (uu___60_1451.query_hash)
        }  in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        (let uu____1472 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1472 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1522 = FStar_ST.op_Bang res  in
         FStar_Option.get uu____1522)
         in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1571 = find_localized_errors settings.query_errors  in
       match uu____1571 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1581 =
                      let uu____1582 = error_to_short_string e  in
                      Prims.strcat "SMT solver says: " uu____1582  in
                    FStar_Errors.diag settings.query_range uu____1581));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1584 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1594 = error_to_short_string e  in
                       Prims.strcat "SMT solver says: " uu____1594))
                in
             FStar_All.pipe_right uu____1584 (FStar_String.concat "; ")  in
           let uu____1597 =
             let uu____1606 =
               let uu____1613 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail
                  in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1613,
                 (settings.query_range))
                in
             [uu____1606]  in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1597)
  
let (query_info :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1632 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1632
      then
        let uu____1633 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1633 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1641 -> "succeeded"
              | uu____1642 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1644 =
                let uu____1645 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1646 =
                  let uu____1647 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1647 ")"  in
                Prims.strcat uu____1645 uu____1646  in
              Prims.strcat "(" uu____1644  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1651 = FStar_Options.print_z3_statistics ()  in
              if uu____1651
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
                let uu____1663 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1663 "}"
              else ""  in
            ((let uu____1666 =
                let uu____1669 =
                  let uu____1672 =
                    let uu____1675 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1676 =
                      let uu____1679 =
                        let uu____1682 =
                          let uu____1685 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1686 =
                            let uu____1689 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1690 =
                              let uu____1693 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1694 =
                                let uu____1697 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1697; stats]  in
                              uu____1693 :: uu____1694  in
                            uu____1689 :: uu____1690  in
                          uu____1685 :: uu____1686  in
                        used_hint_tag :: uu____1682  in
                      tag :: uu____1679  in
                    uu____1675 :: uu____1676  in
                  (settings.query_name) :: uu____1672  in
                range :: uu____1669  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1666);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1709  ->
                     match uu____1709 with
                     | (uu____1716,msg,range1) ->
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
      let uu____1728 =
        let uu____1729 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1729  in
      if uu____1728
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
                | uu____1747 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____1752 = FStar_ST.op_Bang recorded_hints  in
           match uu____1752 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____1812 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____1820 =
               let uu____1821 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____1821  in
             store_hint uu____1820
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____1826 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____1838 =
         (used_hint settings) &&
           (let uu____1840 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____1840)
          in
       if uu____1838 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____1926 = f q res  in
                     match uu____1926 with
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
            (let uu____1954 =
               let uu____1961 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1)
                  in
               match uu____1961 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____1993 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____1994 =
                       let uu____1995 = FStar_Options.z3_rlimit ()  in
                       uu____1995 * (Prims.parse_int "544656")  in
                     uu____1993 * uu____1994  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2000 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2001 = FStar_Options.initial_fuel ()  in
                     let uu____2002 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2000;
                       query_fuel = uu____2001;
                       query_ifuel = uu____2002;
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
                              { FStar_Util.hint_name = uu____2007;
                                FStar_Util.hint_index = uu____2008;
                                FStar_Util.fuel = uu____2009;
                                FStar_Util.ifuel = uu____2010;
                                FStar_Util.unsat_core = uu____2011;
                                FStar_Util.query_elapsed_time = uu____2012;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____1954 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2033;
                         FStar_Util.hint_index = uu____2034;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2038;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___61_2047 = default_settings  in
                         {
                           query_env = (uu___61_2047.query_env);
                           query_decl = (uu___61_2047.query_decl);
                           query_name = (uu___61_2047.query_name);
                           query_index = (uu___61_2047.query_index);
                           query_range = (uu___61_2047.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___61_2047.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___61_2047.query_errors);
                           query_all_labels = (uu___61_2047.query_all_labels);
                           query_suffix = (uu___61_2047.query_suffix);
                           query_hash = (uu___61_2047.query_hash)
                         })]
                   | uu____2050 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2056 =
                     let uu____2057 = FStar_Options.max_ifuel ()  in
                     let uu____2058 = FStar_Options.initial_ifuel ()  in
                     uu____2057 > uu____2058  in
                   if uu____2056
                   then
                     let uu____2061 =
                       let uu___62_2062 = default_settings  in
                       let uu____2063 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___62_2062.query_env);
                         query_decl = (uu___62_2062.query_decl);
                         query_name = (uu___62_2062.query_name);
                         query_index = (uu___62_2062.query_index);
                         query_range = (uu___62_2062.query_range);
                         query_fuel = (uu___62_2062.query_fuel);
                         query_ifuel = uu____2063;
                         query_rlimit = (uu___62_2062.query_rlimit);
                         query_hint = (uu___62_2062.query_hint);
                         query_errors = (uu___62_2062.query_errors);
                         query_all_labels = (uu___62_2062.query_all_labels);
                         query_suffix = (uu___62_2062.query_suffix);
                         query_hash = (uu___62_2062.query_hash)
                       }  in
                     [uu____2061]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2068 =
                     let uu____2069 =
                       let uu____2070 = FStar_Options.max_fuel ()  in
                       uu____2070 / (Prims.parse_int "2")  in
                     let uu____2071 = FStar_Options.initial_fuel ()  in
                     uu____2069 > uu____2071  in
                   if uu____2068
                   then
                     let uu____2074 =
                       let uu___63_2075 = default_settings  in
                       let uu____2076 =
                         let uu____2077 = FStar_Options.max_fuel ()  in
                         uu____2077 / (Prims.parse_int "2")  in
                       let uu____2078 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___63_2075.query_env);
                         query_decl = (uu___63_2075.query_decl);
                         query_name = (uu___63_2075.query_name);
                         query_index = (uu___63_2075.query_index);
                         query_range = (uu___63_2075.query_range);
                         query_fuel = uu____2076;
                         query_ifuel = uu____2078;
                         query_rlimit = (uu___63_2075.query_rlimit);
                         query_hint = (uu___63_2075.query_hint);
                         query_errors = (uu___63_2075.query_errors);
                         query_all_labels = (uu___63_2075.query_all_labels);
                         query_suffix = (uu___63_2075.query_suffix);
                         query_hash = (uu___63_2075.query_hash)
                       }  in
                     [uu____2074]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2083 =
                     (let uu____2088 = FStar_Options.max_fuel ()  in
                      let uu____2089 = FStar_Options.initial_fuel ()  in
                      uu____2088 > uu____2089) &&
                       (let uu____2092 = FStar_Options.max_ifuel ()  in
                        let uu____2093 = FStar_Options.initial_ifuel ()  in
                        uu____2092 >= uu____2093)
                      in
                   if uu____2083
                   then
                     let uu____2096 =
                       let uu___64_2097 = default_settings  in
                       let uu____2098 = FStar_Options.max_fuel ()  in
                       let uu____2099 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___64_2097.query_env);
                         query_decl = (uu___64_2097.query_decl);
                         query_name = (uu___64_2097.query_name);
                         query_index = (uu___64_2097.query_index);
                         query_range = (uu___64_2097.query_range);
                         query_fuel = uu____2098;
                         query_ifuel = uu____2099;
                         query_rlimit = (uu___64_2097.query_rlimit);
                         query_hint = (uu___64_2097.query_hint);
                         query_errors = (uu___64_2097.query_errors);
                         query_all_labels = (uu___64_2097.query_all_labels);
                         query_suffix = (uu___64_2097.query_suffix);
                         query_hash = (uu___64_2097.query_hash)
                       }  in
                     [uu____2096]
                   else []  in
                 let min_fuel1 =
                   let uu____2104 =
                     let uu____2105 = FStar_Options.min_fuel ()  in
                     let uu____2106 = FStar_Options.initial_fuel ()  in
                     uu____2105 < uu____2106  in
                   if uu____2104
                   then
                     let uu____2109 =
                       let uu___65_2110 = default_settings  in
                       let uu____2111 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___65_2110.query_env);
                         query_decl = (uu___65_2110.query_decl);
                         query_name = (uu___65_2110.query_name);
                         query_index = (uu___65_2110.query_index);
                         query_range = (uu___65_2110.query_range);
                         query_fuel = uu____2111;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___65_2110.query_rlimit);
                         query_hint = (uu___65_2110.query_hint);
                         query_errors = (uu___65_2110.query_errors);
                         query_all_labels = (uu___65_2110.query_all_labels);
                         query_suffix = (uu___65_2110.query_suffix);
                         query_hash = (uu___65_2110.query_hash)
                       }  in
                     [uu____2109]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2129 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2129
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2131 = with_fuel_and_diagnostics config []  in
                    let uu____2134 =
                      let uu____2137 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2137  in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2131
                      uu____2134 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___66_2156 = default_settings  in
                        {
                          query_env = (uu___66_2156.query_env);
                          query_decl = (uu___66_2156.query_decl);
                          query_name = (uu___66_2156.query_name);
                          query_index = (uu___66_2156.query_index);
                          query_range = (uu___66_2156.query_range);
                          query_fuel = (uu___66_2156.query_fuel);
                          query_ifuel = (uu___66_2156.query_ifuel);
                          query_rlimit = (uu___66_2156.query_rlimit);
                          query_hint = (uu___66_2156.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___66_2156.query_all_labels);
                          query_suffix = (uu___66_2156.query_suffix);
                          query_hash = (uu___66_2156.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2157 =
                   let uu____2164 = FStar_Options.admit_smt_queries ()  in
                   let uu____2165 = FStar_Options.admit_except ()  in
                   (uu____2164, uu____2165)  in
                 (match uu____2157 with
                  | (true ,uu____2170) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2182 =
                              let uu____2183 =
                                let uu____2184 =
                                  let uu____2185 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2185 ")"  in
                                Prims.strcat ", " uu____2184  in
                              Prims.strcat default_settings.query_name
                                uu____2183
                               in
                            Prims.strcat "(" uu____2182  in
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
        (let uu____2207 =
           let uu____2208 =
             let uu____2209 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2209  in
           FStar_Util.format1 "Starting query at %s" uu____2208  in
         FStar_SMTEncoding_Encode.push uu____2207);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____2211 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____2211 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2245 =
               let uu____2246 =
                 let uu____2247 =
                   let uu____2248 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2248
                    in
                 FStar_Util.format1 "Ending query at %s" uu____2247  in
               FStar_SMTEncoding_Encode.pop uu____2246  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2249);
                        FStar_SMTEncoding_Term.freevars = uu____2250;
                        FStar_SMTEncoding_Term.rng = uu____2251;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2252;
                    FStar_SMTEncoding_Term.assumption_name = uu____2253;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2254;_}
                  -> pop1 ()
              | uu____2269 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2270 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2272 -> failwith "Impossible"))
  
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
           let uu____2278 =
             let uu____2285 = FStar_Options.peek ()  in (e, g, uu____2285)
              in
           [uu____2278]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2300  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2302  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2304  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2307  -> fun uu____2308  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2311  -> fun uu____2312  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2318 =
             let uu____2325 = FStar_Options.peek ()  in (e, g, uu____2325)
              in
           [uu____2318]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2341  -> fun uu____2342  -> fun uu____2343  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2349  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2351  -> ())
  } 
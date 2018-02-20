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
           let src_filename_for_printing =
             if checking_or_using_extracted_interface
             then FStar_Parser_Dep.interface_filename norm_src_filename
             else norm_src_filename  in
           let val_filename =
             let uu____195 = FStar_Options.hint_file ()  in
             match uu____195 with
             | FStar_Pervasives_Native.Some fn -> fn
             | FStar_Pervasives_Native.None  ->
                 format_hints_file_name norm_src_filename
                   checking_or_using_extracted_interface
              in
           let uu____199 = FStar_Util.read_hints val_filename  in
           match uu____199 with
           | FStar_Pervasives_Native.Some hints ->
               let expected_digest =
                 FStar_Util.digest_of_file norm_src_filename  in
               ((let uu____205 = FStar_Options.hint_info ()  in
                 if uu____205
                 then
                   let uu____206 =
                     let uu____207 = FStar_Options.hint_file ()  in
                     match uu____207 with
                     | FStar_Pervasives_Native.Some fn ->
                         Prims.strcat " from '"
                           (Prims.strcat val_filename "'")
                     | uu____211 -> ""  in
                   FStar_Util.print3 "(%s) digest is %s%s.\n"
                     src_filename_for_printing
                     (if hints.FStar_Util.module_digest = expected_digest
                      then "valid; using hints"
                      else "invalid; using potentially stale hints")
                     uu____206
                 else ());
                FStar_ST.op_Colon_Equals replaying_hints
                  (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
           | FStar_Pervasives_Native.None  ->
               let uu____239 = FStar_Options.hint_info ()  in
               (if uu____239
                then
                  FStar_Util.print1 "(%s) Unable to read hint file.\n"
                    src_filename_for_printing
                else ())
         else ())
  
let (finalize_hints_db : Prims.string -> Prims.bool -> Prims.unit) =
  fun src_filename  ->
    fun checking_or_using_extracted_interface  ->
      (let uu____249 = FStar_Options.record_hints ()  in
       if uu____249
       then
         let hints =
           let uu____251 = FStar_ST.op_Bang recorded_hints  in
           FStar_Option.get uu____251  in
         let hints_db =
           let uu____278 = FStar_Util.digest_of_file src_filename  in
           { FStar_Util.module_digest = uu____278; FStar_Util.hints = hints }
            in
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____281 = FStar_Options.hint_file ()  in
           match uu____281 with
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
        | uu____371 -> false  in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____383 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____389 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____389)
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
                   let uu____414 =
                     matches_fact_ids include_assumption_names a  in
                   if uu____414 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____424 -> d :: out) [] theory_rev
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
            let uu____448 = filter_using_facts_from e theory  in
            (uu____448, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____458 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____482  ->
                     match uu____482 with
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
                          | uu____539 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0"))
               in
            (match uu____458 with
             | (theory',n_retained,n_pruned) ->
                 let uu____557 =
                   let uu____560 =
                     let uu____563 =
                       let uu____564 =
                         let uu____565 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ")
                            in
                         Prims.strcat "UNSAT CORE: " uu____565  in
                       FStar_SMTEncoding_Term.Caption uu____564  in
                     [uu____563]  in
                   FStar_List.append theory' uu____560  in
                 (uu____557, true))
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun x  ->
      let uu____582 = filter_using_facts_from e x  in (uu____582, false)
  
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
      let uu____1122 =
        let uu____1125 =
          let uu____1126 =
            let uu____1127 = FStar_Util.string_of_int n1  in
            let uu____1128 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1127 uu____1128
             in
          FStar_SMTEncoding_Term.Caption uu____1126  in
        let uu____1129 =
          let uu____1132 =
            let uu____1133 =
              let uu____1140 =
                let uu____1141 =
                  let uu____1146 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____1149 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____1146, uu____1149)  in
                FStar_SMTEncoding_Util.mkEq uu____1141  in
              (uu____1140, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____1133  in
          let uu____1152 =
            let uu____1155 =
              let uu____1156 =
                let uu____1163 =
                  let uu____1164 =
                    let uu____1169 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____1172 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____1169, uu____1172)  in
                  FStar_SMTEncoding_Util.mkEq uu____1164  in
                (uu____1163, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____1156  in
            [uu____1155; settings.query_decl]  in
          uu____1132 :: uu____1152  in
        uu____1125 :: uu____1129  in
      let uu____1175 =
        let uu____1178 =
          let uu____1181 =
            let uu____1184 =
              let uu____1185 =
                let uu____1190 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____1190)  in
              FStar_SMTEncoding_Term.SetOption uu____1185  in
            [uu____1184;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown]  in
          let uu____1191 =
            let uu____1194 =
              let uu____1197 = FStar_Options.record_hints ()  in
              if uu____1197
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else []  in
            let uu____1201 =
              let uu____1204 =
                let uu____1207 = FStar_Options.print_z3_statistics ()  in
                if uu____1207
                then [FStar_SMTEncoding_Term.GetStatistics]
                else []  in
              FStar_List.append uu____1204 settings.query_suffix  in
            FStar_List.append uu____1194 uu____1201  in
          FStar_List.append uu____1181 uu____1191  in
        FStar_List.append label_assumptions uu____1178  in
      FStar_List.append uu____1122 uu____1175
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____1224 = FStar_ST.op_Bang replaying_hints  in
      match uu____1224 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___58_1257  ->
               match uu___58_1257 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1263 -> FStar_Pervasives_Native.None)
      | uu____1266 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1279 -> FStar_Pervasives_Native.None
      | uu____1280 ->
          let uu____1281 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____1281 with
           | (msg,error_labels) ->
               let err =
                 let uu____1291 =
                   FStar_List.map
                     (fun uu____1316  ->
                        match uu____1316 with
                        | (uu____1329,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1291
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1338 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____1338
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1339 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____1357 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1357
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1459 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____1459)
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
            match err.error_messages with | [] -> false | uu____1581 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____1597 = find_localized_errors errs  in
    FStar_Option.isSome uu____1597
  
let (report_errors : query_settings -> Prims.unit) =
  fun settings  ->
    let uu____1603 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1605 = FStar_Options.n_cores ()  in
         uu____1605 = (Prims.parse_int "1"))
       in
    if uu____1603
    then
      let initial_fuel1 =
        let uu___59_1607 = settings  in
        let uu____1608 = FStar_Options.initial_fuel ()  in
        let uu____1609 = FStar_Options.initial_ifuel ()  in
        {
          query_env = (uu___59_1607.query_env);
          query_decl = (uu___59_1607.query_decl);
          query_name = (uu___59_1607.query_name);
          query_index = (uu___59_1607.query_index);
          query_range = (uu___59_1607.query_range);
          query_fuel = uu____1608;
          query_ifuel = uu____1609;
          query_rlimit = (uu___59_1607.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___59_1607.query_errors);
          query_all_labels = (uu___59_1607.query_all_labels);
          query_suffix = (uu___59_1607.query_suffix);
          query_hash = (uu___59_1607.query_hash)
        }  in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
        (let uu____1628 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1628 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1730 = FStar_ST.op_Bang res  in
         FStar_Option.get uu____1730)
         in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1831 = find_localized_errors settings.query_errors  in
       match uu____1831 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1841 =
                      let uu____1842 = error_to_short_string e  in
                      Prims.strcat "SMT solver says: " uu____1842  in
                    FStar_Errors.diag settings.query_range uu____1841));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1844 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1854 = error_to_short_string e  in
                       Prims.strcat "SMT solver says: " uu____1854))
                in
             FStar_All.pipe_right uu____1844 (FStar_String.concat "; ")  in
           let uu____1857 =
             let uu____1866 =
               let uu____1873 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail
                  in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1873,
                 (settings.query_range))
                in
             [uu____1866]  in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1857)
  
let (query_info :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings  ->
    fun z3result  ->
      let uu____1892 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ())
         in
      if uu____1892
      then
        let uu____1893 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____1893 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1901 -> "succeeded"
              | uu____1902 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}")
               in
            let range =
              let uu____1904 =
                let uu____1905 =
                  FStar_Range.string_of_range settings.query_range  in
                let uu____1906 =
                  let uu____1907 = FStar_SMTEncoding_Z3.at_log_file ()  in
                  Prims.strcat uu____1907 ")"  in
                Prims.strcat uu____1905 uu____1906  in
              Prims.strcat "(" uu____1904  in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else ""  in
            let stats =
              let uu____1911 = FStar_Options.print_z3_statistics ()  in
              if uu____1911
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
                let uu____1923 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1"))
                   in
                Prims.strcat uu____1923 "}"
              else ""  in
            ((let uu____1926 =
                let uu____1929 =
                  let uu____1932 =
                    let uu____1935 =
                      FStar_Util.string_of_int settings.query_index  in
                    let uu____1936 =
                      let uu____1939 =
                        let uu____1942 =
                          let uu____1945 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time
                             in
                          let uu____1946 =
                            let uu____1949 =
                              FStar_Util.string_of_int settings.query_fuel
                               in
                            let uu____1950 =
                              let uu____1953 =
                                FStar_Util.string_of_int settings.query_ifuel
                                 in
                              let uu____1954 =
                                let uu____1957 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit
                                   in
                                [uu____1957; stats]  in
                              uu____1953 :: uu____1954  in
                            uu____1949 :: uu____1950  in
                          uu____1945 :: uu____1946  in
                        used_hint_tag :: uu____1942  in
                      tag :: uu____1939  in
                    uu____1935 :: uu____1936  in
                  (settings.query_name) :: uu____1932  in
                range :: uu____1929  in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1926);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1969  ->
                     match uu____1969 with
                     | (uu____1976,msg,range1) ->
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
      let uu____1988 =
        let uu____1989 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____1989  in
      if uu____1988
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
                | uu____2007 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____2012 = FStar_ST.op_Bang recorded_hints  in
           match uu____2012 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2072 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2080 =
               let uu____2081 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____2081  in
             store_hint uu____2080
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2086 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      (let uu____2098 =
         (used_hint settings) &&
           (let uu____2100 = FStar_Options.z3_refresh ()  in
            Prims.op_Negation uu____2100)
          in
       if uu____2098 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2186 = f q res  in
                     match uu____2186 with
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
            (let uu____2214 =
               let uu____2221 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1)
                  in
               match uu____2221 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2253 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____2254 =
                       let uu____2255 = FStar_Options.z3_rlimit ()  in
                       uu____2255 * (Prims.parse_int "544656")  in
                     uu____2253 * uu____2254  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____2260 = FStar_TypeChecker_Env.get_range env  in
                     let uu____2261 = FStar_Options.initial_fuel ()  in
                     let uu____2262 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2260;
                       query_fuel = uu____2261;
                       query_ifuel = uu____2262;
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
                              { FStar_Util.hint_name = uu____2267;
                                FStar_Util.hint_index = uu____2268;
                                FStar_Util.fuel = uu____2269;
                                FStar_Util.ifuel = uu____2270;
                                FStar_Util.unsat_core = uu____2271;
                                FStar_Util.query_elapsed_time = uu____2272;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____2214 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2293;
                         FStar_Util.hint_index = uu____2294;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2298;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___60_2307 = default_settings  in
                         {
                           query_env = (uu___60_2307.query_env);
                           query_decl = (uu___60_2307.query_decl);
                           query_name = (uu___60_2307.query_name);
                           query_index = (uu___60_2307.query_index);
                           query_range = (uu___60_2307.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___60_2307.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___60_2307.query_errors);
                           query_all_labels = (uu___60_2307.query_all_labels);
                           query_suffix = (uu___60_2307.query_suffix);
                           query_hash = (uu___60_2307.query_hash)
                         })]
                   | uu____2310 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____2316 =
                     let uu____2317 = FStar_Options.max_ifuel ()  in
                     let uu____2318 = FStar_Options.initial_ifuel ()  in
                     uu____2317 > uu____2318  in
                   if uu____2316
                   then
                     let uu____2321 =
                       let uu___61_2322 = default_settings  in
                       let uu____2323 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___61_2322.query_env);
                         query_decl = (uu___61_2322.query_decl);
                         query_name = (uu___61_2322.query_name);
                         query_index = (uu___61_2322.query_index);
                         query_range = (uu___61_2322.query_range);
                         query_fuel = (uu___61_2322.query_fuel);
                         query_ifuel = uu____2323;
                         query_rlimit = (uu___61_2322.query_rlimit);
                         query_hint = (uu___61_2322.query_hint);
                         query_errors = (uu___61_2322.query_errors);
                         query_all_labels = (uu___61_2322.query_all_labels);
                         query_suffix = (uu___61_2322.query_suffix);
                         query_hash = (uu___61_2322.query_hash)
                       }  in
                     [uu____2321]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____2328 =
                     let uu____2329 =
                       let uu____2330 = FStar_Options.max_fuel ()  in
                       uu____2330 / (Prims.parse_int "2")  in
                     let uu____2337 = FStar_Options.initial_fuel ()  in
                     uu____2329 > uu____2337  in
                   if uu____2328
                   then
                     let uu____2340 =
                       let uu___62_2341 = default_settings  in
                       let uu____2342 =
                         let uu____2343 = FStar_Options.max_fuel ()  in
                         uu____2343 / (Prims.parse_int "2")  in
                       let uu____2350 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___62_2341.query_env);
                         query_decl = (uu___62_2341.query_decl);
                         query_name = (uu___62_2341.query_name);
                         query_index = (uu___62_2341.query_index);
                         query_range = (uu___62_2341.query_range);
                         query_fuel = uu____2342;
                         query_ifuel = uu____2350;
                         query_rlimit = (uu___62_2341.query_rlimit);
                         query_hint = (uu___62_2341.query_hint);
                         query_errors = (uu___62_2341.query_errors);
                         query_all_labels = (uu___62_2341.query_all_labels);
                         query_suffix = (uu___62_2341.query_suffix);
                         query_hash = (uu___62_2341.query_hash)
                       }  in
                     [uu____2340]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____2355 =
                     (let uu____2360 = FStar_Options.max_fuel ()  in
                      let uu____2361 = FStar_Options.initial_fuel ()  in
                      uu____2360 > uu____2361) &&
                       (let uu____2364 = FStar_Options.max_ifuel ()  in
                        let uu____2365 = FStar_Options.initial_ifuel ()  in
                        uu____2364 >= uu____2365)
                      in
                   if uu____2355
                   then
                     let uu____2368 =
                       let uu___63_2369 = default_settings  in
                       let uu____2370 = FStar_Options.max_fuel ()  in
                       let uu____2371 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___63_2369.query_env);
                         query_decl = (uu___63_2369.query_decl);
                         query_name = (uu___63_2369.query_name);
                         query_index = (uu___63_2369.query_index);
                         query_range = (uu___63_2369.query_range);
                         query_fuel = uu____2370;
                         query_ifuel = uu____2371;
                         query_rlimit = (uu___63_2369.query_rlimit);
                         query_hint = (uu___63_2369.query_hint);
                         query_errors = (uu___63_2369.query_errors);
                         query_all_labels = (uu___63_2369.query_all_labels);
                         query_suffix = (uu___63_2369.query_suffix);
                         query_hash = (uu___63_2369.query_hash)
                       }  in
                     [uu____2368]
                   else []  in
                 let min_fuel1 =
                   let uu____2376 =
                     let uu____2377 = FStar_Options.min_fuel ()  in
                     let uu____2378 = FStar_Options.initial_fuel ()  in
                     uu____2377 < uu____2378  in
                   if uu____2376
                   then
                     let uu____2381 =
                       let uu___64_2382 = default_settings  in
                       let uu____2383 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___64_2382.query_env);
                         query_decl = (uu___64_2382.query_decl);
                         query_name = (uu___64_2382.query_name);
                         query_index = (uu___64_2382.query_index);
                         query_range = (uu___64_2382.query_range);
                         query_fuel = uu____2383;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___64_2382.query_rlimit);
                         query_hint = (uu___64_2382.query_hint);
                         query_errors = (uu___64_2382.query_errors);
                         query_all_labels = (uu___64_2382.query_all_labels);
                         query_suffix = (uu___64_2382.query_suffix);
                         query_hash = (uu___64_2382.query_hash)
                       }  in
                     [uu____2381]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config k =
                   (let uu____2401 =
                      (used_hint config) || (FStar_Options.z3_refresh ())  in
                    if uu____2401
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2403 = with_fuel_and_diagnostics config []  in
                    let uu____2406 =
                      let uu____2409 = FStar_SMTEncoding_Z3.mk_fresh_scope ()
                         in
                      FStar_Pervasives_Native.Some uu____2409  in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2403
                      uu____2406 k)
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___65_2428 = default_settings  in
                        {
                          query_env = (uu___65_2428.query_env);
                          query_decl = (uu___65_2428.query_decl);
                          query_name = (uu___65_2428.query_name);
                          query_index = (uu___65_2428.query_index);
                          query_range = (uu___65_2428.query_range);
                          query_fuel = (uu___65_2428.query_fuel);
                          query_ifuel = (uu___65_2428.query_ifuel);
                          query_rlimit = (uu___65_2428.query_rlimit);
                          query_hint = (uu___65_2428.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___65_2428.query_all_labels);
                          query_suffix = (uu___65_2428.query_suffix);
                          query_hash = (uu___65_2428.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____2429 =
                   let uu____2436 = FStar_Options.admit_smt_queries ()  in
                   let uu____2437 = FStar_Options.admit_except ()  in
                   (uu____2436, uu____2437)  in
                 (match uu____2429 with
                  | (true ,uu____2442) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2454 =
                              let uu____2455 =
                                let uu____2456 =
                                  let uu____2457 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.strcat uu____2457 ")"  in
                                Prims.strcat ", " uu____2456  in
                              Prims.strcat default_settings.query_name
                                uu____2455
                               in
                            Prims.strcat "(" uu____2454  in
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
        (let uu____2479 =
           let uu____2480 =
             let uu____2481 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2481  in
           FStar_Util.format1 "Starting query at %s" uu____2480  in
         FStar_SMTEncoding_Encode.push uu____2479);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
         let uu____2483 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
         match uu____2483 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2517 =
               let uu____2518 =
                 let uu____2519 =
                   let uu____2520 = FStar_TypeChecker_Env.get_range tcenv1
                      in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2520
                    in
                 FStar_Util.format1 "Ending query at %s" uu____2519  in
               FStar_SMTEncoding_Encode.pop uu____2518  in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2521);
                        FStar_SMTEncoding_Term.freevars = uu____2522;
                        FStar_SMTEncoding_Term.rng = uu____2523;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2524;
                    FStar_SMTEncoding_Term.assumption_name = uu____2525;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2526;_}
                  -> pop1 ()
              | uu____2541 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2542 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2544 -> failwith "Impossible"))
  
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
           let uu____2550 =
             let uu____2557 = FStar_Options.peek ()  in (e, g, uu____2557)
              in
           [uu____2550]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2572  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2574  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2576  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2579  -> fun uu____2580  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2583  -> fun uu____2584  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2590 =
             let uu____2597 = FStar_Options.peek ()  in (e, g, uu____2597)
              in
           [uu____2590]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2613  -> fun uu____2614  -> fun uu____2615  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2621  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2623  -> ())
  } 
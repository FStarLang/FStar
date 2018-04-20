open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result :
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____9, ('Auu____10, 'Auu____11) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____9, 'Auu____10) FStar_Util.either
  =
  fun uu___61_27 ->
    match uu___61_27 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r, uu____42) -> FStar_Util.Inr r
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db :
  'Auu____135 . Prims.string -> 'Auu____135 -> Prims.unit =
  fun src_filename ->
    fun format_filename ->
      (let uu____145 = FStar_Options.record_hints () in
       if uu____145
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____182 = FStar_Options.use_hints () in
       if uu____182
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____185 = FStar_Options.hint_file () in
           match uu____185 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None ->
               format_hints_file_name norm_src_filename in
         let uu____189 = FStar_Util.read_hints val_filename in
         match uu____189 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____195 = FStar_Options.hint_info () in
               if uu____195
               then
                 let uu____196 =
                   let uu____197 = FStar_Options.hint_file () in
                   match uu____197 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____201 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____196
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None ->
             let uu____235 = FStar_Options.hint_info () in
             (if uu____235
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let (finalize_hints_db : Prims.string -> Prims.unit) =
  fun src_filename ->
    (let uu____242 = FStar_Options.record_hints () in
     if uu____242
     then
       let hints =
         let uu____244 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____244 in
       let hints_db =
         let uu____277 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____277; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____280 = FStar_Options.hint_file () in
         match uu____280 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db : 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
  fun fname ->
    fun f ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let (filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e ->
    fun theory ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____377 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____389 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____395 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____395) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        FStar_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____420 =
                     matches_fact_ids include_assumption_names a in
                   if uu____420 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____430 -> d :: out) [] theory_rev in
      pruned_theory
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decls_t ->
        (FStar_SMTEncoding_Term.decl Prims.list, Prims.bool)
          FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun core ->
      fun theory ->
        match core with
        | FStar_Pervasives_Native.None ->
            let uu____454 = filter_using_facts_from e theory in
            (uu____454, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____464 =
              FStar_List.fold_right
                (fun d ->
                   fun uu____488 ->
                     match uu____488 with
                     | (theory1, n_retained, n_pruned) ->
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
                          | uu____545 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____464 with
             | (theory', n_retained, n_pruned) ->
                 let uu____563 =
                   let uu____566 =
                     let uu____569 =
                       let uu____570 =
                         let uu____571 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____571 in
                       FStar_SMTEncoding_Term.Caption uu____570 in
                     [uu____569] in
                   FStar_List.append theory' uu____566 in
                 (uu____563, true))
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list, Prims.bool)
        FStar_Pervasives_Native.tuple2)
  =
  fun e ->
    fun x ->
      let uu____588 = filter_using_facts_from e x in (uu____588, false)
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error, Prims.string, FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list
    }[@@deriving show]
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
let (__proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error, Prims.string, FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list)
  =
  fun projectee ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
let (error_to_short_string : errors -> Prims.string) =
  fun err ->
    let uu____752 = FStar_Util.string_of_int err.error_fuel in
    let uu____753 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____752 uu____753
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun projectee ->
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
  fun settings ->
    fun label_assumptions ->
      let n1 = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1128 =
        let uu____1131 =
          let uu____1132 =
            let uu____1133 = FStar_Util.string_of_int n1 in
            let uu____1134 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1133 uu____1134 in
          FStar_SMTEncoding_Term.Caption uu____1132 in
        let uu____1135 =
          let uu____1138 =
            let uu____1139 =
              let uu____1146 =
                let uu____1147 =
                  let uu____1152 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1155 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1152, uu____1155) in
                FStar_SMTEncoding_Util.mkEq uu____1147 in
              (uu____1146, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1139 in
          let uu____1158 =
            let uu____1161 =
              let uu____1162 =
                let uu____1169 =
                  let uu____1170 =
                    let uu____1175 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1178 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1175, uu____1178) in
                  FStar_SMTEncoding_Util.mkEq uu____1170 in
                (uu____1169, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1162 in
            [uu____1161; settings.query_decl] in
          uu____1138 :: uu____1158 in
        uu____1131 :: uu____1135 in
      let uu____1181 =
        let uu____1184 =
          let uu____1187 =
            let uu____1190 =
              let uu____1191 =
                let uu____1196 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1196) in
              FStar_SMTEncoding_Term.SetOption uu____1191 in
            [uu____1190;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1197 =
            let uu____1200 =
              let uu____1203 = FStar_Options.record_hints () in
              if uu____1203
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1207 =
              let uu____1210 =
                let uu____1213 = FStar_Options.print_z3_statistics () in
                if uu____1213
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1210 settings.query_suffix in
            FStar_List.append uu____1200 uu____1207 in
          FStar_List.append uu____1187 uu____1197 in
        FStar_List.append label_assumptions uu____1184 in
      FStar_List.append uu____1128 uu____1181
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu____1230 = FStar_ST.op_Bang replaying_hints in
      match uu____1230 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___62_1269 ->
               match uu___62_1269 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1275 -> FStar_Pervasives_Native.None)
      | uu____1278 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1291 -> FStar_Pervasives_Native.None
      | uu____1292 ->
          let uu____1293 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1293 with
           | (msg, error_labels) ->
               let err =
                 let uu____1303 =
                   FStar_List.map
                     (fun uu____1328 ->
                        match uu____1328 with
                        | (uu____1341, x, y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1303
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings ->
    fun z3result ->
      let uu____1350 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1350
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1351 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____1369 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1369
                 FStar_Pervasives_Native.None
                 (fun r ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1473 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1473) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err ->
            match err.error_messages with | [] -> false | uu____1597 -> true))
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs ->
    let uu____1613 = find_localized_errors errs in
    FStar_Option.isSome uu____1613
let (report_errors : query_settings -> Prims.unit) =
  fun settings ->
    let uu____1619 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1621 = FStar_Options.n_cores () in
         uu____1621 = (Prims.parse_int "1")) in
    if uu____1619
    then
      let initial_fuel1 =
        let uu___63_1623 = settings in
        let uu____1624 = FStar_Options.initial_fuel () in
        let uu____1625 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___63_1623.query_env);
          query_decl = (uu___63_1623.query_decl);
          query_name = (uu___63_1623.query_name);
          query_index = (uu___63_1623.query_index);
          query_range = (uu___63_1623.query_range);
          query_fuel = uu____1624;
          query_ifuel = uu____1625;
          query_rlimit = (uu___63_1623.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___63_1623.query_errors);
          query_all_labels = (uu___63_1623.query_all_labels);
          query_suffix = (uu___63_1623.query_suffix);
          query_hash = (uu___63_1623.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1644 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1644 FStar_Pervasives_Native.None
           (fun r ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1748 = FStar_ST.op_Bang res in FStar_Option.get uu____1748) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1851 = find_localized_errors settings.query_errors in
       match uu____1851 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e ->
                    let uu____1861 =
                      let uu____1862 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1862 in
                    FStar_Errors.diag settings.query_range uu____1861));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None ->
           let err_detail =
             let uu____1864 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e ->
                       let uu____1874 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1874)) in
             FStar_All.pipe_right uu____1864 (FStar_String.concat "; ") in
           let uu____1877 =
             let uu____1886 =
               let uu____1893 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1893,
                 (settings.query_range)) in
             [uu____1886] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1877)
let (query_info :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings ->
    fun z3result ->
      let uu____1912 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1912
      then
        let uu____1913 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1913 with
        | (status_string, errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1921 -> "succeeded"
              | uu____1922 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1924 =
                let uu____1925 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1926 =
                  let uu____1927 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1927 ")" in
                Prims.strcat uu____1925 uu____1926 in
              Prims.strcat "(" uu____1924 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1931 = FStar_Options.print_z3_statistics () in
              if uu____1931
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1943 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1943 "}"
              else "" in
            ((let uu____1946 =
                let uu____1949 =
                  let uu____1952 =
                    let uu____1955 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1956 =
                      let uu____1959 =
                        let uu____1962 =
                          let uu____1965 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1966 =
                            let uu____1969 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1970 =
                              let uu____1973 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1974 =
                                let uu____1977 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1977; stats] in
                              uu____1973 :: uu____1974 in
                            uu____1969 :: uu____1970 in
                          uu____1965 :: uu____1966 in
                        used_hint_tag :: uu____1962 in
                      tag :: uu____1959 in
                    uu____1955 :: uu____1956 in
                  (settings.query_name) :: uu____1952 in
                range :: uu____1949 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1946);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1989 ->
                     match uu____1989 with
                     | (uu____1996, msg, range1) ->
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else "" in
                         FStar_Errors.log_issue range1
                           (FStar_Errors.Warning_HitReplayFailed,
                             (Prims.strcat tag1 msg)))))
      else ()
let (record_hint :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit) =
  fun settings ->
    fun z3result ->
      let uu____2008 =
        let uu____2009 = FStar_Options.record_hints () in
        Prims.op_Negation uu____2009 in
      if uu____2008
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
                | uu____2027 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____2032 = FStar_ST.op_Bang recorded_hints in
           match uu____2032 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2104 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu____2118 =
               let uu____2119 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____2119 in
             store_hint uu____2118
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2124 -> ())
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun result ->
      (let uu____2136 =
         (used_hint settings) &&
           (let uu____2138 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2138) in
       if uu____2136 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result in
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
  fun qs ->
    fun ask1 ->
      fun f ->
        fun report1 ->
          let rec aux acc qs1 =
            match qs1 with
            | [] -> report1 acc
            | q::qs2 ->
                ask1 q
                  (fun res ->
                     let uu____2224 = f q res in
                     match uu____2224 with
                     | FStar_Pervasives_Native.None -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2) in
          aux [] qs
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit)
  =
  fun env ->
    fun all_labels ->
      fun prefix1 ->
        fun query ->
          fun suffix ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____2252 =
               let uu____2259 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2268, FStar_Pervasives_Native.None) ->
                     failwith "No query name set!"
                 | (uu____2287, FStar_Pervasives_Native.Some (q, n1)) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2259 with
               | (qname, index1) ->
                   let rlimit =
                     let uu____2313 = FStar_Options.z3_rlimit_factor () in
                     let uu____2314 =
                       let uu____2315 = FStar_Options.z3_rlimit () in
                       uu____2315 * (Prims.parse_int "544656") in
                     uu____2313 * uu____2314 in
                   let next_hint = get_hint_for qname index1 in
                   let default_settings =
                     let uu____2320 = FStar_TypeChecker_Env.get_range env in
                     let uu____2321 = FStar_Options.initial_fuel () in
                     let uu____2322 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2320;
                       query_fuel = uu____2321;
                       query_ifuel = uu____2322;
                       query_rlimit = rlimit;
                       query_hint = FStar_Pervasives_Native.None;
                       query_errors = [];
                       query_all_labels = all_labels;
                       query_suffix = suffix;
                       query_hash =
                         (match next_hint with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              { FStar_Util.hint_name = uu____2327;
                                FStar_Util.hint_index = uu____2328;
                                FStar_Util.fuel = uu____2329;
                                FStar_Util.ifuel = uu____2330;
                                FStar_Util.unsat_core = uu____2331;
                                FStar_Util.query_elapsed_time = uu____2332;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____2252 with
             | (default_settings, next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2353;
                         FStar_Util.hint_index = uu____2354;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2358;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___64_2367 = default_settings in
                         {
                           query_env = (uu___64_2367.query_env);
                           query_decl = (uu___64_2367.query_decl);
                           query_name = (uu___64_2367.query_name);
                           query_index = (uu___64_2367.query_index);
                           query_range = (uu___64_2367.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___64_2367.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___64_2367.query_errors);
                           query_all_labels = (uu___64_2367.query_all_labels);
                           query_suffix = (uu___64_2367.query_suffix);
                           query_hash = (uu___64_2367.query_hash)
                         })]
                   | uu____2370 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2376 =
                     let uu____2377 = FStar_Options.max_ifuel () in
                     let uu____2378 = FStar_Options.initial_ifuel () in
                     uu____2377 > uu____2378 in
                   if uu____2376
                   then
                     let uu____2381 =
                       let uu___65_2382 = default_settings in
                       let uu____2383 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___65_2382.query_env);
                         query_decl = (uu___65_2382.query_decl);
                         query_name = (uu___65_2382.query_name);
                         query_index = (uu___65_2382.query_index);
                         query_range = (uu___65_2382.query_range);
                         query_fuel = (uu___65_2382.query_fuel);
                         query_ifuel = uu____2383;
                         query_rlimit = (uu___65_2382.query_rlimit);
                         query_hint = (uu___65_2382.query_hint);
                         query_errors = (uu___65_2382.query_errors);
                         query_all_labels = (uu___65_2382.query_all_labels);
                         query_suffix = (uu___65_2382.query_suffix);
                         query_hash = (uu___65_2382.query_hash)
                       } in
                     [uu____2381]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2388 =
                     let uu____2389 =
                       let uu____2390 = FStar_Options.max_fuel () in
                       uu____2390 / (Prims.parse_int "2") in
                     let uu____2391 = FStar_Options.initial_fuel () in
                     uu____2389 > uu____2391 in
                   if uu____2388
                   then
                     let uu____2394 =
                       let uu___66_2395 = default_settings in
                       let uu____2396 =
                         let uu____2397 = FStar_Options.max_fuel () in
                         uu____2397 / (Prims.parse_int "2") in
                       let uu____2398 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___66_2395.query_env);
                         query_decl = (uu___66_2395.query_decl);
                         query_name = (uu___66_2395.query_name);
                         query_index = (uu___66_2395.query_index);
                         query_range = (uu___66_2395.query_range);
                         query_fuel = uu____2396;
                         query_ifuel = uu____2398;
                         query_rlimit = (uu___66_2395.query_rlimit);
                         query_hint = (uu___66_2395.query_hint);
                         query_errors = (uu___66_2395.query_errors);
                         query_all_labels = (uu___66_2395.query_all_labels);
                         query_suffix = (uu___66_2395.query_suffix);
                         query_hash = (uu___66_2395.query_hash)
                       } in
                     [uu____2394]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2403 =
                     (let uu____2408 = FStar_Options.max_fuel () in
                      let uu____2409 = FStar_Options.initial_fuel () in
                      uu____2408 > uu____2409) &&
                       (let uu____2412 = FStar_Options.max_ifuel () in
                        let uu____2413 = FStar_Options.initial_ifuel () in
                        uu____2412 >= uu____2413) in
                   if uu____2403
                   then
                     let uu____2416 =
                       let uu___67_2417 = default_settings in
                       let uu____2418 = FStar_Options.max_fuel () in
                       let uu____2419 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___67_2417.query_env);
                         query_decl = (uu___67_2417.query_decl);
                         query_name = (uu___67_2417.query_name);
                         query_index = (uu___67_2417.query_index);
                         query_range = (uu___67_2417.query_range);
                         query_fuel = uu____2418;
                         query_ifuel = uu____2419;
                         query_rlimit = (uu___67_2417.query_rlimit);
                         query_hint = (uu___67_2417.query_hint);
                         query_errors = (uu___67_2417.query_errors);
                         query_all_labels = (uu___67_2417.query_all_labels);
                         query_suffix = (uu___67_2417.query_suffix);
                         query_hash = (uu___67_2417.query_hash)
                       } in
                     [uu____2416]
                   else [] in
                 let min_fuel1 =
                   let uu____2424 =
                     let uu____2425 = FStar_Options.min_fuel () in
                     let uu____2426 = FStar_Options.initial_fuel () in
                     uu____2425 < uu____2426 in
                   if uu____2424
                   then
                     let uu____2429 =
                       let uu___68_2430 = default_settings in
                       let uu____2431 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___68_2430.query_env);
                         query_decl = (uu___68_2430.query_decl);
                         query_name = (uu___68_2430.query_name);
                         query_index = (uu___68_2430.query_index);
                         query_range = (uu___68_2430.query_range);
                         query_fuel = uu____2431;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___68_2430.query_rlimit);
                         query_hint = (uu___68_2430.query_hint);
                         query_errors = (uu___68_2430.query_errors);
                         query_all_labels = (uu___68_2430.query_all_labels);
                         query_suffix = (uu___68_2430.query_suffix);
                         query_hash = (uu___68_2430.query_hash)
                       } in
                     [uu____2429]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2449 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2449
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2451 = with_fuel_and_diagnostics config [] in
                    let uu____2454 =
                      let uu____2457 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2457 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2451
                      uu____2454 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___69_2476 = default_settings in
                        {
                          query_env = (uu___69_2476.query_env);
                          query_decl = (uu___69_2476.query_decl);
                          query_name = (uu___69_2476.query_name);
                          query_index = (uu___69_2476.query_index);
                          query_range = (uu___69_2476.query_range);
                          query_fuel = (uu___69_2476.query_fuel);
                          query_ifuel = (uu___69_2476.query_ifuel);
                          query_rlimit = (uu___69_2476.query_rlimit);
                          query_hint = (uu___69_2476.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___69_2476.query_all_labels);
                          query_suffix = (uu___69_2476.query_suffix);
                          query_hash = (uu___69_2476.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2477 =
                   let uu____2484 = FStar_Options.admit_smt_queries () in
                   let uu____2485 = FStar_Options.admit_except () in
                   (uu____2484, uu____2485) in
                 (match uu____2477 with
                  | (true, uu____2490) -> ()
                  | (false, FStar_Pervasives_Native.None) ->
                      check_all_configs all_configs
                  | (false, FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2502 =
                              let uu____2503 =
                                let uu____2504 =
                                  let uu____2505 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2505 ")" in
                                Prims.strcat ", " uu____2504 in
                              Prims.strcat default_settings.query_name
                                uu____2503 in
                            Prims.strcat "(" uu____2502 in
                          full_query_id <> id1
                        else default_settings.query_name <> id1 in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
let (solve :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____2527 =
           let uu____2528 =
             let uu____2529 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2529 in
           FStar_Util.format1 "Starting query at %s" uu____2528 in
         FStar_SMTEncoding_Encode.push uu____2527);
        (let uu____2530 = FStar_Options.no_smt () in
         if uu____2530
         then
           let uu____2531 =
             let uu____2540 =
               let uu____2547 =
                 let uu____2548 = FStar_Syntax_Print.term_to_string q in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____2548 in
               (FStar_Errors.Error_NoSMTButNeeded, uu____2547,
                 (tcenv.FStar_TypeChecker_Env.range)) in
             [uu____2540] in
           FStar_TypeChecker_Err.add_errors tcenv uu____2531
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
            let uu____2563 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
            match uu____2563 with
            | (prefix1, labels, qry, suffix) ->
                let pop1 uu____2597 =
                  let uu____2598 =
                    let uu____2599 =
                      let uu____2600 = FStar_TypeChecker_Env.get_range tcenv1 in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____2600 in
                    FStar_Util.format1 "Ending query at %s" uu____2599 in
                  FStar_SMTEncoding_Encode.pop uu____2598 in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp, uu____2601);
                           FStar_SMTEncoding_Term.freevars = uu____2602;
                           FStar_SMTEncoding_Term.rng = uu____2603;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____2604;
                       FStar_SMTEncoding_Term.assumption_name = uu____2605;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____2606;_}
                     -> pop1 ()
                 | uu____2621 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____2622 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____2624 -> failwith "Impossible")))
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.encode_modul =
      FStar_SMTEncoding_Encode.encode_modul;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____2630 =
             let uu____2637 = FStar_Options.peek () in (e, g, uu____2637) in
           [uu____2630]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____2652 -> ());
    FStar_TypeChecker_Env.push = (fun uu____2654 -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2656 -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2659 -> fun uu____2660 -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2663 -> fun uu____2664 -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____2670 =
             let uu____2677 = FStar_Options.peek () in (e, g, uu____2677) in
           [uu____2670]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2693 -> fun uu____2694 -> fun uu____2695 -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2701 -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2703 -> ())
  }
open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result:
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____11,('Auu____10,'Auu____9) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____11,'Auu____10) FStar_Util.either
  =
  fun uu___57_27  ->
    match uu___57_27 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____42) -> FStar_Util.Inr r
let recorded_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let replaying_hints:
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let format_hints_file_name: Prims.string -> Prims.string =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db:
  'Auu____87 . Prims.string -> 'Auu____87 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____97 = FStar_Options.record_hints () in
       if uu____97
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____128 = FStar_Options.use_hints () in
       if uu____128
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____131 = FStar_Options.hint_file () in
           match uu____131 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____135 = FStar_Util.read_hints val_filename in
         match uu____135 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____141 = FStar_Options.hint_info () in
               if uu____141
               then
                 let uu____142 =
                   let uu____143 = FStar_Options.hint_file () in
                   match uu____143 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____147 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____142
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____175 = FStar_Options.hint_info () in
             (if uu____175
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____182 = FStar_Options.record_hints () in
     if uu____182
     then
       let hints =
         let uu____184 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____184 in
       let hints_db =
         let uu____211 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____211; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____214 = FStar_Options.hint_file () in
         match uu____214 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db: 'a . Prims.string -> (Prims.unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let filter_using_facts_from:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun e  ->
    fun theory  ->
      let should_enc_fid fid =
        match fid with
        | FStar_SMTEncoding_Term.Namespace lid ->
            FStar_TypeChecker_Env.should_enc_lid e lid
        | uu____299 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____311 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____317 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____317) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____342 =
                     matches_fact_ids include_assumption_names a in
                   if uu____342 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____352 -> d :: out) [] theory_rev in
      pruned_theory
let filter_assertions:
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
            let uu____376 = filter_using_facts_from e theory in
            (uu____376, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____386 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____410  ->
                     match uu____410 with
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
                          | uu____467 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____386 with
             | (theory',n_retained,n_pruned) ->
                 let uu____485 =
                   let uu____488 =
                     let uu____491 =
                       let uu____492 =
                         let uu____493 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____493 in
                       FStar_SMTEncoding_Term.Caption uu____492 in
                     [uu____491] in
                   FStar_List.append theory' uu____488 in
                 (uu____485, true))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____510 = filter_using_facts_from e x in (uu____510, false)
type errors =
  {
  error_reason: Prims.string;
  error_fuel: Prims.int;
  error_ifuel: Prims.int;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  error_messages:
    (FStar_Errors.raw_error,Prims.string,FStar_Range.range)
      FStar_Pervasives_Native.tuple3 Prims.list;}[@@deriving show]
let __proj__Mkerrors__item__error_reason: errors -> Prims.string =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_reason
let __proj__Mkerrors__item__error_fuel: errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_fuel
let __proj__Mkerrors__item__error_ifuel: errors -> Prims.int =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_ifuel
let __proj__Mkerrors__item__error_hint:
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} -> __fname__error_hint
let __proj__Mkerrors__item__error_messages:
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
let error_to_short_string: errors -> Prims.string =
  fun err  ->
    let uu____674 = FStar_Util.string_of_int err.error_fuel in
    let uu____675 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____674 uu____675
      (if FStar_Option.isSome err.error_hint then "with hint" else "")
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env;
  query_decl: FStar_SMTEncoding_Term.decl;
  query_name: Prims.string;
  query_index: Prims.int;
  query_range: FStar_Range.range;
  query_fuel: Prims.int;
  query_ifuel: Prims.int;
  query_rlimit: Prims.int;
  query_hint: FStar_SMTEncoding_Z3.unsat_core;
  query_errors: errors Prims.list;
  query_all_labels: FStar_SMTEncoding_Term.error_labels;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list;
  query_hash: Prims.string FStar_Pervasives_Native.option;}[@@deriving show]
let __proj__Mkquery_settings__item__query_env:
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
let __proj__Mkquery_settings__item__query_decl:
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
let __proj__Mkquery_settings__item__query_name:
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
let __proj__Mkquery_settings__item__query_index: query_settings -> Prims.int
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
let __proj__Mkquery_settings__item__query_range:
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
let __proj__Mkquery_settings__item__query_fuel: query_settings -> Prims.int =
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
let __proj__Mkquery_settings__item__query_ifuel: query_settings -> Prims.int
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
let __proj__Mkquery_settings__item__query_rlimit: query_settings -> Prims.int
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
        query_hash = __fname__query_hash;_} -> __fname__query_rlimit
let __proj__Mkquery_settings__item__query_hint:
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
let __proj__Mkquery_settings__item__query_errors:
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
let __proj__Mkquery_settings__item__query_all_labels:
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
let __proj__Mkquery_settings__item__query_suffix:
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
let __proj__Mkquery_settings__item__query_hash:
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
let with_fuel_and_diagnostics:
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list
  =
  fun settings  ->
    fun label_assumptions  ->
      let n1 = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1050 =
        let uu____1053 =
          let uu____1054 =
            let uu____1055 = FStar_Util.string_of_int n1 in
            let uu____1056 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1055 uu____1056 in
          FStar_SMTEncoding_Term.Caption uu____1054 in
        let uu____1057 =
          let uu____1060 =
            let uu____1061 =
              let uu____1068 =
                let uu____1069 =
                  let uu____1074 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1077 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1074, uu____1077) in
                FStar_SMTEncoding_Util.mkEq uu____1069 in
              (uu____1068, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1061 in
          let uu____1080 =
            let uu____1083 =
              let uu____1084 =
                let uu____1091 =
                  let uu____1092 =
                    let uu____1097 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1100 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1097, uu____1100) in
                  FStar_SMTEncoding_Util.mkEq uu____1092 in
                (uu____1091, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1084 in
            [uu____1083; settings.query_decl] in
          uu____1060 :: uu____1080 in
        uu____1053 :: uu____1057 in
      let uu____1103 =
        let uu____1106 =
          let uu____1109 =
            let uu____1112 =
              let uu____1113 =
                let uu____1118 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1118) in
              FStar_SMTEncoding_Term.SetOption uu____1113 in
            [uu____1112;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1119 =
            let uu____1122 =
              let uu____1125 = FStar_Options.record_hints () in
              if uu____1125
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1129 =
              let uu____1132 =
                let uu____1135 = FStar_Options.print_z3_statistics () in
                if uu____1135
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1132 settings.query_suffix in
            FStar_List.append uu____1122 uu____1129 in
          FStar_List.append uu____1109 uu____1119 in
        FStar_List.append label_assumptions uu____1106 in
      FStar_List.append uu____1050 uu____1103
let used_hint: query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint
let get_hint_for:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____1152 = FStar_ST.op_Bang replaying_hints in
      match uu____1152 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___58_1185  ->
               match uu___58_1185 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1191 -> FStar_Pervasives_Native.None)
      | uu____1194 -> FStar_Pervasives_Native.None
let query_errors:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1207 -> FStar_Pervasives_Native.None
      | uu____1208 ->
          let uu____1209 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1209 with
           | (msg,error_labels) ->
               let err =
                 let uu____1219 =
                   FStar_List.map
                     (fun uu____1244  ->
                        match uu____1244 with
                        | (uu____1257,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1219
                 } in
               FStar_Pervasives_Native.Some err)
let detail_hint_replay:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1266 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1266
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1267 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____1285 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1285
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1335 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1335) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err  ->
            match err.error_messages with | [] -> false | uu____1405 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1421 = find_localized_errors errs in
    FStar_Option.isSome uu____1421
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1427 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1429 = FStar_Options.n_cores () in
         uu____1429 = (Prims.parse_int "1")) in
    if uu____1427
    then
      let initial_fuel1 =
        let uu___59_1431 = settings in
        let uu____1432 = FStar_Options.initial_fuel () in
        let uu____1433 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___59_1431.query_env);
          query_decl = (uu___59_1431.query_decl);
          query_name = (uu___59_1431.query_name);
          query_index = (uu___59_1431.query_index);
          query_range = (uu___59_1431.query_range);
          query_fuel = uu____1432;
          query_ifuel = uu____1433;
          query_rlimit = (uu___59_1431.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___59_1431.query_errors);
          query_all_labels = (uu___59_1431.query_all_labels);
          query_suffix = (uu___59_1431.query_suffix);
          query_hash = (uu___59_1431.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1452 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1452 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1502 = FStar_ST.op_Bang res in FStar_Option.get uu____1502) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1551 = find_localized_errors settings.query_errors in
       match uu____1551 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1561 =
                      let uu____1562 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1562 in
                    FStar_Errors.diag settings.query_range uu____1561));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1564 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1574 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1574)) in
             FStar_All.pipe_right uu____1564 (FStar_String.concat "; ") in
           let uu____1577 =
             let uu____1586 =
               let uu____1593 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1593,
                 (settings.query_range)) in
             [uu____1586] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1577)
let query_info: query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1612 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1612
      then
        let uu____1613 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1613 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1621 -> "succeeded"
              | uu____1622 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1624 =
                let uu____1625 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1626 =
                  let uu____1627 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1627 ")" in
                Prims.strcat uu____1625 uu____1626 in
              Prims.strcat "(" uu____1624 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1631 = FStar_Options.print_z3_statistics () in
              if uu____1631
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1643 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1643 "}"
              else "" in
            ((let uu____1646 =
                let uu____1649 =
                  let uu____1652 =
                    let uu____1655 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1656 =
                      let uu____1659 =
                        let uu____1662 =
                          let uu____1665 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1666 =
                            let uu____1669 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1670 =
                              let uu____1673 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1674 =
                                let uu____1677 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1677; stats] in
                              uu____1673 :: uu____1674 in
                            uu____1669 :: uu____1670 in
                          uu____1665 :: uu____1666 in
                        used_hint_tag :: uu____1662 in
                      tag :: uu____1659 in
                    uu____1655 :: uu____1656 in
                  (settings.query_name) :: uu____1652 in
                range :: uu____1649 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1646);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1689  ->
                     match uu____1689 with
                     | (uu____1696,msg,range1) ->
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else "" in
                         FStar_Errors.log_issue range1
                           (FStar_Errors.Warning_HitReplayFailed,
                             (Prims.strcat tag1 msg)))))
      else ()
let record_hint:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1708 =
        let uu____1709 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1709 in
      if uu____1708
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
                | uu____1727 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____1732 = FStar_ST.op_Bang recorded_hints in
           match uu____1732 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____1792 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____1800 =
               let uu____1801 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____1801 in
             store_hint uu____1800
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____1806 -> ())
let process_result:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____1818 =
         (used_hint settings) &&
           (let uu____1820 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____1820) in
       if uu____1818 then FStar_SMTEncoding_Z3.refresh () else ());
      (let errs = query_errors settings result in
       query_info settings result;
       record_hint settings result;
       detail_hint_replay settings result;
       errs)
let fold_queries:
  query_settings Prims.list ->
    (query_settings ->
       (FStar_SMTEncoding_Z3.z3result -> Prims.unit) -> Prims.unit)
      ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> Prims.unit) -> Prims.unit
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
                     let uu____1906 = f q res in
                     match uu____1906 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2) in
          aux [] qs
let ask_and_report_errors:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> Prims.unit
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____1934 =
               let uu____1941 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____1941 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____1973 = FStar_Options.z3_rlimit_factor () in
                     let uu____1974 =
                       let uu____1975 = FStar_Options.z3_rlimit () in
                       uu____1975 * (Prims.parse_int "544656") in
                     uu____1973 * uu____1974 in
                   let next_hint = get_hint_for qname index1 in
                   let default_settings =
                     let uu____1980 = FStar_TypeChecker_Env.get_range env in
                     let uu____1981 = FStar_Options.initial_fuel () in
                     let uu____1982 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____1980;
                       query_fuel = uu____1981;
                       query_ifuel = uu____1982;
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
                              { FStar_Util.hint_name = uu____1987;
                                FStar_Util.hint_index = uu____1988;
                                FStar_Util.fuel = uu____1989;
                                FStar_Util.ifuel = uu____1990;
                                FStar_Util.unsat_core = uu____1991;
                                FStar_Util.query_elapsed_time = uu____1992;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____1934 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2013;
                         FStar_Util.hint_index = uu____2014;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2018;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___60_2027 = default_settings in
                         {
                           query_env = (uu___60_2027.query_env);
                           query_decl = (uu___60_2027.query_decl);
                           query_name = (uu___60_2027.query_name);
                           query_index = (uu___60_2027.query_index);
                           query_range = (uu___60_2027.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___60_2027.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___60_2027.query_errors);
                           query_all_labels = (uu___60_2027.query_all_labels);
                           query_suffix = (uu___60_2027.query_suffix);
                           query_hash = (uu___60_2027.query_hash)
                         })]
                   | uu____2030 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2036 =
                     let uu____2037 = FStar_Options.max_ifuel () in
                     let uu____2038 = FStar_Options.initial_ifuel () in
                     uu____2037 > uu____2038 in
                   if uu____2036
                   then
                     let uu____2041 =
                       let uu___61_2042 = default_settings in
                       let uu____2043 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___61_2042.query_env);
                         query_decl = (uu___61_2042.query_decl);
                         query_name = (uu___61_2042.query_name);
                         query_index = (uu___61_2042.query_index);
                         query_range = (uu___61_2042.query_range);
                         query_fuel = (uu___61_2042.query_fuel);
                         query_ifuel = uu____2043;
                         query_rlimit = (uu___61_2042.query_rlimit);
                         query_hint = (uu___61_2042.query_hint);
                         query_errors = (uu___61_2042.query_errors);
                         query_all_labels = (uu___61_2042.query_all_labels);
                         query_suffix = (uu___61_2042.query_suffix);
                         query_hash = (uu___61_2042.query_hash)
                       } in
                     [uu____2041]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2048 =
                     let uu____2049 =
                       let uu____2050 = FStar_Options.max_fuel () in
                       uu____2050 / (Prims.parse_int "2") in
                     let uu____2057 = FStar_Options.initial_fuel () in
                     uu____2049 > uu____2057 in
                   if uu____2048
                   then
                     let uu____2060 =
                       let uu___62_2061 = default_settings in
                       let uu____2062 =
                         let uu____2063 = FStar_Options.max_fuel () in
                         uu____2063 / (Prims.parse_int "2") in
                       let uu____2070 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___62_2061.query_env);
                         query_decl = (uu___62_2061.query_decl);
                         query_name = (uu___62_2061.query_name);
                         query_index = (uu___62_2061.query_index);
                         query_range = (uu___62_2061.query_range);
                         query_fuel = uu____2062;
                         query_ifuel = uu____2070;
                         query_rlimit = (uu___62_2061.query_rlimit);
                         query_hint = (uu___62_2061.query_hint);
                         query_errors = (uu___62_2061.query_errors);
                         query_all_labels = (uu___62_2061.query_all_labels);
                         query_suffix = (uu___62_2061.query_suffix);
                         query_hash = (uu___62_2061.query_hash)
                       } in
                     [uu____2060]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2075 =
                     (let uu____2080 = FStar_Options.max_fuel () in
                      let uu____2081 = FStar_Options.initial_fuel () in
                      uu____2080 > uu____2081) &&
                       (let uu____2084 = FStar_Options.max_ifuel () in
                        let uu____2085 = FStar_Options.initial_ifuel () in
                        uu____2084 >= uu____2085) in
                   if uu____2075
                   then
                     let uu____2088 =
                       let uu___63_2089 = default_settings in
                       let uu____2090 = FStar_Options.max_fuel () in
                       let uu____2091 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___63_2089.query_env);
                         query_decl = (uu___63_2089.query_decl);
                         query_name = (uu___63_2089.query_name);
                         query_index = (uu___63_2089.query_index);
                         query_range = (uu___63_2089.query_range);
                         query_fuel = uu____2090;
                         query_ifuel = uu____2091;
                         query_rlimit = (uu___63_2089.query_rlimit);
                         query_hint = (uu___63_2089.query_hint);
                         query_errors = (uu___63_2089.query_errors);
                         query_all_labels = (uu___63_2089.query_all_labels);
                         query_suffix = (uu___63_2089.query_suffix);
                         query_hash = (uu___63_2089.query_hash)
                       } in
                     [uu____2088]
                   else [] in
                 let min_fuel1 =
                   let uu____2096 =
                     let uu____2097 = FStar_Options.min_fuel () in
                     let uu____2098 = FStar_Options.initial_fuel () in
                     uu____2097 < uu____2098 in
                   if uu____2096
                   then
                     let uu____2101 =
                       let uu___64_2102 = default_settings in
                       let uu____2103 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___64_2102.query_env);
                         query_decl = (uu___64_2102.query_decl);
                         query_name = (uu___64_2102.query_name);
                         query_index = (uu___64_2102.query_index);
                         query_range = (uu___64_2102.query_range);
                         query_fuel = uu____2103;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___64_2102.query_rlimit);
                         query_hint = (uu___64_2102.query_hint);
                         query_errors = (uu___64_2102.query_errors);
                         query_all_labels = (uu___64_2102.query_all_labels);
                         query_suffix = (uu___64_2102.query_suffix);
                         query_hash = (uu___64_2102.query_hash)
                       } in
                     [uu____2101]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2121 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2121
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2123 = with_fuel_and_diagnostics config [] in
                    let uu____2126 =
                      let uu____2129 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2129 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2123
                      uu____2126 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___65_2148 = default_settings in
                        {
                          query_env = (uu___65_2148.query_env);
                          query_decl = (uu___65_2148.query_decl);
                          query_name = (uu___65_2148.query_name);
                          query_index = (uu___65_2148.query_index);
                          query_range = (uu___65_2148.query_range);
                          query_fuel = (uu___65_2148.query_fuel);
                          query_ifuel = (uu___65_2148.query_ifuel);
                          query_rlimit = (uu___65_2148.query_rlimit);
                          query_hint = (uu___65_2148.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___65_2148.query_all_labels);
                          query_suffix = (uu___65_2148.query_suffix);
                          query_hash = (uu___65_2148.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2149 =
                   let uu____2156 = FStar_Options.admit_smt_queries () in
                   let uu____2157 = FStar_Options.admit_except () in
                   (uu____2156, uu____2157) in
                 (match uu____2149 with
                  | (true ,uu____2162) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2174 =
                              let uu____2175 =
                                let uu____2176 =
                                  let uu____2177 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2177 ")" in
                                Prims.strcat ", " uu____2176 in
                              Prims.strcat default_settings.query_name
                                uu____2175 in
                            Prims.strcat "(" uu____2174 in
                          full_query_id <> id1
                        else default_settings.query_name <> id1 in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
let solve:
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.unit
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____2199 =
           let uu____2200 =
             let uu____2201 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2201 in
           FStar_Util.format1 "Starting query at %s" uu____2200 in
         FStar_SMTEncoding_Encode.push uu____2199);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2203 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2203 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2237 =
               let uu____2238 =
                 let uu____2239 =
                   let uu____2240 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2240 in
                 FStar_Util.format1 "Ending query at %s" uu____2239 in
               FStar_SMTEncoding_Encode.pop uu____2238 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2241);
                        FStar_SMTEncoding_Term.freevars = uu____2242;
                        FStar_SMTEncoding_Term.rng = uu____2243;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2244;
                    FStar_SMTEncoding_Term.assumption_name = uu____2245;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2246;_}
                  -> pop1 ()
              | uu____2261 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2262 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2264 -> failwith "Impossible"))
let solver: FStar_TypeChecker_Env.solver_t =
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
           let uu____2270 =
             let uu____2277 = FStar_Options.peek () in (e, g, uu____2277) in
           [uu____2270]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2292  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2294  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2296  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2299  -> fun uu____2300  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2303  -> fun uu____2304  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2310 =
             let uu____2317 = FStar_Options.peek () in (e, g, uu____2317) in
           [uu____2310]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2333  -> fun uu____2334  -> fun uu____2335  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2341  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2343  -> ())
  }
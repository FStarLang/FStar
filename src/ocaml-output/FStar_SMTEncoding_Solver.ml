open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result:
  'Auu____13 'Auu____14 'Auu____15 .
    ('Auu____15,('Auu____14,'Auu____13) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____15,'Auu____14) FStar_Util.either
  =
  fun uu___111_31  ->
    match uu___111_31 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____46) -> FStar_Util.Inr r
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
      (let uu____155 = FStar_Options.use_hints () in
       if uu____155
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____158 = FStar_Options.hint_file () in
           match uu____158 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____162 = FStar_Util.read_hints val_filename in
         match uu____162 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____168 = FStar_Options.hint_info () in
               if uu____168
               then
                 let uu____169 =
                   let uu____170 = FStar_Options.hint_file () in
                   match uu____170 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____174 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____169
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____229 = FStar_Options.hint_info () in
             (if uu____229
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____237 = FStar_Options.record_hints () in
     if uu____237
     then
       let hints =
         let uu____239 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____239 in
       let hints_db =
         let uu____293 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____293; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____296 = FStar_Options.hint_file () in
         match uu____296 with
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
        | uu____440 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____452 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____458 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____458) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____483 =
                     matches_fact_ids include_assumption_names a in
                   if uu____483 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____493 -> d :: out) [] theory_rev in
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
            let uu____520 = filter_using_facts_from e theory in
            (uu____520, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____530 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____554  ->
                     match uu____554 with
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
                          | uu____611 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____530 with
             | (theory',n_retained,n_pruned) ->
                 let uu____629 =
                   let uu____632 =
                     let uu____635 =
                       let uu____636 =
                         let uu____637 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____637 in
                       FStar_SMTEncoding_Term.Caption uu____636 in
                     [uu____635] in
                   FStar_List.append theory' uu____632 in
                 (uu____629, true))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____656 = filter_using_facts_from e x in (uu____656, false)
type errors =
  {
  error_reason: Prims.string;
  error_fuel: Prims.int;
  error_ifuel: Prims.int;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option;
  error_messages:
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list;}[@@deriving show]
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
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list
  =
  fun projectee  ->
    match projectee with
    | { error_reason = __fname__error_reason;
        error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel;
        error_hint = __fname__error_hint;
        error_messages = __fname__error_messages;_} ->
        __fname__error_messages
let error_to_short_string: errors -> Prims.string =
  fun err1  ->
    let uu____810 = FStar_Util.string_of_int err1.error_fuel in
    let uu____811 = FStar_Util.string_of_int err1.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason
      uu____810 uu____811
      (if FStar_Option.isSome err1.error_hint then "with hint" else "")
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
      let uu____1201 =
        let uu____1204 =
          let uu____1205 =
            let uu____1206 = FStar_Util.string_of_int n1 in
            let uu____1207 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1206 uu____1207 in
          FStar_SMTEncoding_Term.Caption uu____1205 in
        let uu____1208 =
          let uu____1211 =
            let uu____1212 =
              let uu____1219 =
                let uu____1220 =
                  let uu____1225 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1228 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1225, uu____1228) in
                FStar_SMTEncoding_Util.mkEq uu____1220 in
              (uu____1219, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1212 in
          let uu____1231 =
            let uu____1234 =
              let uu____1235 =
                let uu____1242 =
                  let uu____1243 =
                    let uu____1248 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1251 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1248, uu____1251) in
                  FStar_SMTEncoding_Util.mkEq uu____1243 in
                (uu____1242, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1235 in
            [uu____1234; settings.query_decl] in
          uu____1211 :: uu____1231 in
        uu____1204 :: uu____1208 in
      let uu____1254 =
        let uu____1257 =
          let uu____1260 =
            let uu____1263 =
              let uu____1264 =
                let uu____1269 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1269) in
              FStar_SMTEncoding_Term.SetOption uu____1264 in
            [uu____1263;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1270 =
            let uu____1273 =
              let uu____1276 = FStar_Options.record_hints () in
              if uu____1276
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1280 =
              let uu____1283 =
                let uu____1286 = FStar_Options.print_z3_statistics () in
                if uu____1286
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1283 settings.query_suffix in
            FStar_List.append uu____1273 uu____1280 in
          FStar_List.append uu____1260 uu____1270 in
        FStar_List.append label_assumptions uu____1257 in
      FStar_List.append uu____1201 uu____1254
let used_hint: query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint
let get_hint_for:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____1306 = FStar_ST.op_Bang replaying_hints in
      match uu____1306 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___112_1366  ->
               match uu___112_1366 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1372 -> FStar_Pervasives_Native.None)
      | uu____1375 -> FStar_Pervasives_Native.None
let query_errors:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1390 -> FStar_Pervasives_Native.None
      | uu____1391 ->
          let uu____1392 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1392 with
           | (msg,error_labels) ->
               let err1 =
                 let uu____1402 =
                   FStar_List.map
                     (fun uu____1423  ->
                        match uu____1423 with | (uu____1434,x,y) -> (x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1402
                 } in
               FStar_Pervasives_Native.Some err1)
let detail_hint_replay:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1445 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1445
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1446 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____1464 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1464
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1533 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1533) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err1  ->
            match err1.error_messages with | [] -> false | uu____1621 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1636 = find_localized_errors errs in
    FStar_Option.isSome uu____1636
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1643 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1645 = FStar_Options.n_cores () in
         uu____1645 = (Prims.parse_int "1")) in
    if uu____1643
    then
      let initial_fuel1 =
        let uu___113_1647 = settings in
        let uu____1648 = FStar_Options.initial_fuel () in
        let uu____1649 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___113_1647.query_env);
          query_decl = (uu___113_1647.query_decl);
          query_name = (uu___113_1647.query_name);
          query_index = (uu___113_1647.query_index);
          query_range = (uu___113_1647.query_range);
          query_fuel = uu____1648;
          query_ifuel = uu____1649;
          query_rlimit = (uu___113_1647.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___113_1647.query_errors);
          query_all_labels = (uu___113_1647.query_all_labels);
          query_suffix = (uu___113_1647.query_suffix);
          query_hash = (uu___113_1647.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1668 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1668 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1737 = FStar_ST.op_Bang res in FStar_Option.get uu____1737) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1805 = find_localized_errors settings.query_errors in
       match uu____1805 with
       | FStar_Pervasives_Native.Some err1 ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1815 =
                      let uu____1816 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1816 in
                    FStar_Errors.diag settings.query_range uu____1815));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err1.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1818 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1828 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1828)) in
             FStar_All.pipe_right uu____1818 (FStar_String.concat "; ") in
           let uu____1831 =
             let uu____1838 =
               let uu____1843 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (uu____1843, (settings.query_range)) in
             [uu____1838] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1831)
let query_info: query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1860 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1860
      then
        let uu____1861 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1861 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1869 -> "succeeded"
              | uu____1870 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1872 =
                let uu____1873 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1874 =
                  let uu____1875 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1875 ")" in
                Prims.strcat uu____1873 uu____1874 in
              Prims.strcat "(" uu____1872 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1879 = FStar_Options.print_z3_statistics () in
              if uu____1879
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1891 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1891 "}"
              else "" in
            ((let uu____1894 =
                let uu____1897 =
                  let uu____1900 =
                    let uu____1903 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1904 =
                      let uu____1907 =
                        let uu____1910 =
                          let uu____1913 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1914 =
                            let uu____1917 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1918 =
                              let uu____1921 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1922 =
                                let uu____1925 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1925; stats] in
                              uu____1921 :: uu____1922 in
                            uu____1917 :: uu____1918 in
                          uu____1913 :: uu____1914 in
                        used_hint_tag :: uu____1910 in
                      tag :: uu____1907 in
                    uu____1903 :: uu____1904 in
                  (settings.query_name) :: uu____1900 in
                range :: uu____1897 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1894);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1939  ->
                     match uu____1939 with
                     | (uu____1946,msg,range1) ->
                         let e =
                           FStar_Errors.mk_issue FStar_Errors.EInfo
                             (FStar_Pervasives_Native.Some range1) msg in
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else "" in
                         let uu____1952 = FStar_Errors.format_issue e in
                         FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1952)))
      else ()
let record_hint:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1962 =
        let uu____1963 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1963 in
      if uu____1962
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
                | uu____1981 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____1986 = FStar_ST.op_Bang recorded_hints in
           match uu____1986 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2100 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2108 =
               let uu____2109 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____2109 in
             store_hint uu____2108
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2114 -> ())
let process_result:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2128 =
         (used_hint settings) &&
           (let uu____2130 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2130) in
       if uu____2128 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2220 = f q res in
                     match uu____2220 with
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
            (let uu____2253 =
               let uu____2260 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2260 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2292 = FStar_Options.z3_rlimit_factor () in
                     let uu____2293 =
                       let uu____2294 = FStar_Options.z3_rlimit () in
                       uu____2294 * (Prims.parse_int "544656") in
                     uu____2292 * uu____2293 in
                   let next_hint = get_hint_for qname index1 in
                   let default_settings =
                     let uu____2299 = FStar_TypeChecker_Env.get_range env in
                     let uu____2300 = FStar_Options.initial_fuel () in
                     let uu____2301 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2299;
                       query_fuel = uu____2300;
                       query_ifuel = uu____2301;
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
                              { FStar_Util.hint_name = uu____2306;
                                FStar_Util.hint_index = uu____2307;
                                FStar_Util.fuel = uu____2308;
                                FStar_Util.ifuel = uu____2309;
                                FStar_Util.unsat_core = uu____2310;
                                FStar_Util.query_elapsed_time = uu____2311;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____2253 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2332;
                         FStar_Util.hint_index = uu____2333;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2337;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___114_2346 = default_settings in
                         {
                           query_env = (uu___114_2346.query_env);
                           query_decl = (uu___114_2346.query_decl);
                           query_name = (uu___114_2346.query_name);
                           query_index = (uu___114_2346.query_index);
                           query_range = (uu___114_2346.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___114_2346.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___114_2346.query_errors);
                           query_all_labels =
                             (uu___114_2346.query_all_labels);
                           query_suffix = (uu___114_2346.query_suffix);
                           query_hash = (uu___114_2346.query_hash)
                         })]
                   | uu____2349 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2355 =
                     let uu____2356 = FStar_Options.max_ifuel () in
                     let uu____2357 = FStar_Options.initial_ifuel () in
                     uu____2356 > uu____2357 in
                   if uu____2355
                   then
                     let uu____2360 =
                       let uu___115_2361 = default_settings in
                       let uu____2362 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___115_2361.query_env);
                         query_decl = (uu___115_2361.query_decl);
                         query_name = (uu___115_2361.query_name);
                         query_index = (uu___115_2361.query_index);
                         query_range = (uu___115_2361.query_range);
                         query_fuel = (uu___115_2361.query_fuel);
                         query_ifuel = uu____2362;
                         query_rlimit = (uu___115_2361.query_rlimit);
                         query_hint = (uu___115_2361.query_hint);
                         query_errors = (uu___115_2361.query_errors);
                         query_all_labels = (uu___115_2361.query_all_labels);
                         query_suffix = (uu___115_2361.query_suffix);
                         query_hash = (uu___115_2361.query_hash)
                       } in
                     [uu____2360]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2367 =
                     let uu____2368 =
                       let uu____2369 = FStar_Options.max_fuel () in
                       uu____2369 / (Prims.parse_int "2") in
                     let uu____2376 = FStar_Options.initial_fuel () in
                     uu____2368 > uu____2376 in
                   if uu____2367
                   then
                     let uu____2379 =
                       let uu___116_2380 = default_settings in
                       let uu____2381 =
                         let uu____2382 = FStar_Options.max_fuel () in
                         uu____2382 / (Prims.parse_int "2") in
                       let uu____2389 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___116_2380.query_env);
                         query_decl = (uu___116_2380.query_decl);
                         query_name = (uu___116_2380.query_name);
                         query_index = (uu___116_2380.query_index);
                         query_range = (uu___116_2380.query_range);
                         query_fuel = uu____2381;
                         query_ifuel = uu____2389;
                         query_rlimit = (uu___116_2380.query_rlimit);
                         query_hint = (uu___116_2380.query_hint);
                         query_errors = (uu___116_2380.query_errors);
                         query_all_labels = (uu___116_2380.query_all_labels);
                         query_suffix = (uu___116_2380.query_suffix);
                         query_hash = (uu___116_2380.query_hash)
                       } in
                     [uu____2379]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2394 =
                     (let uu____2399 = FStar_Options.max_fuel () in
                      let uu____2400 = FStar_Options.initial_fuel () in
                      uu____2399 > uu____2400) &&
                       (let uu____2403 = FStar_Options.max_ifuel () in
                        let uu____2404 = FStar_Options.initial_ifuel () in
                        uu____2403 >= uu____2404) in
                   if uu____2394
                   then
                     let uu____2407 =
                       let uu___117_2408 = default_settings in
                       let uu____2409 = FStar_Options.max_fuel () in
                       let uu____2410 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___117_2408.query_env);
                         query_decl = (uu___117_2408.query_decl);
                         query_name = (uu___117_2408.query_name);
                         query_index = (uu___117_2408.query_index);
                         query_range = (uu___117_2408.query_range);
                         query_fuel = uu____2409;
                         query_ifuel = uu____2410;
                         query_rlimit = (uu___117_2408.query_rlimit);
                         query_hint = (uu___117_2408.query_hint);
                         query_errors = (uu___117_2408.query_errors);
                         query_all_labels = (uu___117_2408.query_all_labels);
                         query_suffix = (uu___117_2408.query_suffix);
                         query_hash = (uu___117_2408.query_hash)
                       } in
                     [uu____2407]
                   else [] in
                 let min_fuel1 =
                   let uu____2415 =
                     let uu____2416 = FStar_Options.min_fuel () in
                     let uu____2417 = FStar_Options.initial_fuel () in
                     uu____2416 < uu____2417 in
                   if uu____2415
                   then
                     let uu____2420 =
                       let uu___118_2421 = default_settings in
                       let uu____2422 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___118_2421.query_env);
                         query_decl = (uu___118_2421.query_decl);
                         query_name = (uu___118_2421.query_name);
                         query_index = (uu___118_2421.query_index);
                         query_range = (uu___118_2421.query_range);
                         query_fuel = uu____2422;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___118_2421.query_rlimit);
                         query_hint = (uu___118_2421.query_hint);
                         query_errors = (uu___118_2421.query_errors);
                         query_all_labels = (uu___118_2421.query_all_labels);
                         query_suffix = (uu___118_2421.query_suffix);
                         query_hash = (uu___118_2421.query_hash)
                       } in
                     [uu____2420]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2440 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2440
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2442 = with_fuel_and_diagnostics config [] in
                    let uu____2445 =
                      let uu____2448 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2448 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2442
                      uu____2445 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___119_2467 = default_settings in
                        {
                          query_env = (uu___119_2467.query_env);
                          query_decl = (uu___119_2467.query_decl);
                          query_name = (uu___119_2467.query_name);
                          query_index = (uu___119_2467.query_index);
                          query_range = (uu___119_2467.query_range);
                          query_fuel = (uu___119_2467.query_fuel);
                          query_ifuel = (uu___119_2467.query_ifuel);
                          query_rlimit = (uu___119_2467.query_rlimit);
                          query_hint = (uu___119_2467.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___119_2467.query_all_labels);
                          query_suffix = (uu___119_2467.query_suffix);
                          query_hash = (uu___119_2467.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2468 =
                   let uu____2475 = FStar_Options.admit_smt_queries () in
                   let uu____2476 = FStar_Options.admit_except () in
                   (uu____2475, uu____2476) in
                 (match uu____2468 with
                  | (true ,uu____2481) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let skip =
                        if FStar_Util.starts_with id "("
                        then
                          let full_query_id =
                            let uu____2493 =
                              let uu____2494 =
                                let uu____2495 =
                                  let uu____2496 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2496 ")" in
                                Prims.strcat ", " uu____2495 in
                              Prims.strcat default_settings.query_name
                                uu____2494 in
                            Prims.strcat "(" uu____2493 in
                          full_query_id <> id
                        else default_settings.query_name <> id in
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
        (let uu____2521 =
           let uu____2522 =
             let uu____2523 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2523 in
           FStar_Util.format1 "Starting query at %s" uu____2522 in
         FStar_SMTEncoding_Encode.push uu____2521);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2525 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2525 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2559 =
               let uu____2560 =
                 let uu____2561 =
                   let uu____2562 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2562 in
                 FStar_Util.format1 "Ending query at %s" uu____2561 in
               FStar_SMTEncoding_Encode.pop uu____2560 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2563);
                        FStar_SMTEncoding_Term.freevars = uu____2564;
                        FStar_SMTEncoding_Term.rng = uu____2565;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2566;
                    FStar_SMTEncoding_Term.assumption_name = uu____2567;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2568;_}
                  -> pop1 ()
              | uu____2583 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2584 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2586 -> failwith "Impossible"))
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
           let uu____2592 =
             let uu____2599 = FStar_Options.peek () in (e, g, uu____2599) in
           [uu____2592]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2614  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2616  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2618  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2621  -> fun uu____2622  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2625  -> fun uu____2626  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2632 =
             let uu____2639 = FStar_Options.peek () in (e, g, uu____2639) in
           [uu____2632]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2655  -> fun uu____2656  -> fun uu____2657  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2663  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2665  -> ())
  }
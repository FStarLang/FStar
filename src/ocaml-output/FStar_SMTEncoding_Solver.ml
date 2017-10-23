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
let next_hint:
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
                 ((settings.query_hash), (settings.query_hint))
                 settings.query_all_labels uu____1464
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1535 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1535) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err1  ->
            match err1.error_messages with | [] -> false | uu____1623 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1638 = find_localized_errors errs in
    FStar_Option.isSome uu____1638
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1645 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1647 = FStar_Options.n_cores () in
         uu____1647 = (Prims.parse_int "1")) in
    if uu____1645
    then
      let initial_fuel1 =
        let uu___113_1649 = settings in
        let uu____1650 = FStar_Options.initial_fuel () in
        let uu____1651 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___113_1649.query_env);
          query_decl = (uu___113_1649.query_decl);
          query_name = (uu___113_1649.query_name);
          query_index = (uu___113_1649.query_index);
          query_range = (uu___113_1649.query_range);
          query_fuel = uu____1650;
          query_ifuel = uu____1651;
          query_rlimit = (uu___113_1649.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___113_1649.query_errors);
          query_all_labels = (uu___113_1649.query_all_labels);
          query_suffix = (uu___113_1649.query_suffix);
          query_hash = (uu___113_1649.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1670 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env)
           ((settings.query_hash), FStar_Pervasives_Native.None)
           settings.query_all_labels uu____1670 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1747 = FStar_ST.op_Bang res in FStar_Option.get uu____1747) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1815 = find_localized_errors settings.query_errors in
       match uu____1815 with
       | FStar_Pervasives_Native.Some err1 ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1825 =
                      let uu____1826 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1826 in
                    FStar_Errors.diag settings.query_range uu____1825));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err1.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1828 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1838 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1838)) in
             FStar_All.pipe_right uu____1828 (FStar_String.concat "; ") in
           let uu____1841 =
             let uu____1848 =
               let uu____1853 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (uu____1853, (settings.query_range)) in
             [uu____1848] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1841)
let query_info: query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1870 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1870
      then
        let uu____1871 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1871 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1879 -> "succeeded"
              | uu____1880 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1882 =
                let uu____1883 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1884 =
                  let uu____1885 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1885 ")" in
                Prims.strcat uu____1883 uu____1884 in
              Prims.strcat "(" uu____1882 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1889 = FStar_Options.print_z3_statistics () in
              if uu____1889
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1901 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1901 "}"
              else "" in
            ((let uu____1904 =
                let uu____1907 =
                  let uu____1910 =
                    let uu____1913 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1914 =
                      let uu____1917 =
                        let uu____1920 =
                          let uu____1923 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1924 =
                            let uu____1927 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1928 =
                              let uu____1931 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1932 =
                                let uu____1935 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1935; stats] in
                              uu____1931 :: uu____1932 in
                            uu____1927 :: uu____1928 in
                          uu____1923 :: uu____1924 in
                        used_hint_tag :: uu____1920 in
                      tag :: uu____1917 in
                    uu____1913 :: uu____1914 in
                  (settings.query_name) :: uu____1910 in
                range :: uu____1907 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1904);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1949  ->
                     match uu____1949 with
                     | (uu____1956,msg,range1) ->
                         let e =
                           FStar_Errors.mk_issue FStar_Errors.EInfo
                             (FStar_Pervasives_Native.Some range1) msg in
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else "" in
                         let uu____1962 = FStar_Errors.format_issue e in
                         FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1962)))
      else ()
let record_hint:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1972 =
        let uu____1973 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1973 in
      if uu____1972
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
                | uu____1991 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____1996 = FStar_ST.op_Bang recorded_hints in
           match uu____1996 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2110 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2118 -> ())
let process_result:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2132 =
         (used_hint settings) &&
           (let uu____2134 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2134) in
       if uu____2132 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2224 = f q res in
                     match uu____2224 with
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
            (let uu____2257 =
               let uu____2264 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2264 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2296 = FStar_Options.z3_rlimit_factor () in
                     let uu____2297 =
                       let uu____2298 = FStar_Options.z3_rlimit () in
                       uu____2298 * (Prims.parse_int "544656") in
                     uu____2296 * uu____2297 in
                   let next_hint1 = next_hint qname index1 in
                   let default_settings =
                     let uu____2303 = FStar_TypeChecker_Env.get_range env in
                     let uu____2304 = FStar_Options.initial_fuel () in
                     let uu____2305 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2303;
                       query_fuel = uu____2304;
                       query_ifuel = uu____2305;
                       query_rlimit = rlimit;
                       query_hint = FStar_Pervasives_Native.None;
                       query_errors = [];
                       query_all_labels = all_labels;
                       query_suffix = suffix;
                       query_hash =
                         (match next_hint1 with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some
                              { FStar_Util.hint_name = uu____2310;
                                FStar_Util.hint_index = uu____2311;
                                FStar_Util.fuel = uu____2312;
                                FStar_Util.ifuel = uu____2313;
                                FStar_Util.unsat_core = uu____2314;
                                FStar_Util.query_elapsed_time = uu____2315;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint1) in
             match uu____2257 with
             | (default_settings,next_hint1) ->
                 let use_hints_setting =
                   match next_hint1 with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2336;
                         FStar_Util.hint_index = uu____2337;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2341;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___114_2350 = default_settings in
                         {
                           query_env = (uu___114_2350.query_env);
                           query_decl = (uu___114_2350.query_decl);
                           query_name = (uu___114_2350.query_name);
                           query_index = (uu___114_2350.query_index);
                           query_range = (uu___114_2350.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___114_2350.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___114_2350.query_errors);
                           query_all_labels =
                             (uu___114_2350.query_all_labels);
                           query_suffix = (uu___114_2350.query_suffix);
                           query_hash = (uu___114_2350.query_hash)
                         })]
                   | uu____2353 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2359 =
                     let uu____2360 = FStar_Options.max_ifuel () in
                     let uu____2361 = FStar_Options.initial_ifuel () in
                     uu____2360 > uu____2361 in
                   if uu____2359
                   then
                     let uu____2364 =
                       let uu___115_2365 = default_settings in
                       let uu____2366 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___115_2365.query_env);
                         query_decl = (uu___115_2365.query_decl);
                         query_name = (uu___115_2365.query_name);
                         query_index = (uu___115_2365.query_index);
                         query_range = (uu___115_2365.query_range);
                         query_fuel = (uu___115_2365.query_fuel);
                         query_ifuel = uu____2366;
                         query_rlimit = (uu___115_2365.query_rlimit);
                         query_hint = (uu___115_2365.query_hint);
                         query_errors = (uu___115_2365.query_errors);
                         query_all_labels = (uu___115_2365.query_all_labels);
                         query_suffix = (uu___115_2365.query_suffix);
                         query_hash = (uu___115_2365.query_hash)
                       } in
                     [uu____2364]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2371 =
                     let uu____2372 =
                       let uu____2373 = FStar_Options.max_fuel () in
                       uu____2373 / (Prims.parse_int "2") in
                     let uu____2380 = FStar_Options.initial_fuel () in
                     uu____2372 > uu____2380 in
                   if uu____2371
                   then
                     let uu____2383 =
                       let uu___116_2384 = default_settings in
                       let uu____2385 =
                         let uu____2386 = FStar_Options.max_fuel () in
                         uu____2386 / (Prims.parse_int "2") in
                       let uu____2393 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___116_2384.query_env);
                         query_decl = (uu___116_2384.query_decl);
                         query_name = (uu___116_2384.query_name);
                         query_index = (uu___116_2384.query_index);
                         query_range = (uu___116_2384.query_range);
                         query_fuel = uu____2385;
                         query_ifuel = uu____2393;
                         query_rlimit = (uu___116_2384.query_rlimit);
                         query_hint = (uu___116_2384.query_hint);
                         query_errors = (uu___116_2384.query_errors);
                         query_all_labels = (uu___116_2384.query_all_labels);
                         query_suffix = (uu___116_2384.query_suffix);
                         query_hash = (uu___116_2384.query_hash)
                       } in
                     [uu____2383]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2398 =
                     (let uu____2403 = FStar_Options.max_fuel () in
                      let uu____2404 = FStar_Options.initial_fuel () in
                      uu____2403 > uu____2404) &&
                       (let uu____2407 = FStar_Options.max_ifuel () in
                        let uu____2408 = FStar_Options.initial_ifuel () in
                        uu____2407 >= uu____2408) in
                   if uu____2398
                   then
                     let uu____2411 =
                       let uu___117_2412 = default_settings in
                       let uu____2413 = FStar_Options.max_fuel () in
                       let uu____2414 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___117_2412.query_env);
                         query_decl = (uu___117_2412.query_decl);
                         query_name = (uu___117_2412.query_name);
                         query_index = (uu___117_2412.query_index);
                         query_range = (uu___117_2412.query_range);
                         query_fuel = uu____2413;
                         query_ifuel = uu____2414;
                         query_rlimit = (uu___117_2412.query_rlimit);
                         query_hint = (uu___117_2412.query_hint);
                         query_errors = (uu___117_2412.query_errors);
                         query_all_labels = (uu___117_2412.query_all_labels);
                         query_suffix = (uu___117_2412.query_suffix);
                         query_hash = (uu___117_2412.query_hash)
                       } in
                     [uu____2411]
                   else [] in
                 let min_fuel1 =
                   let uu____2419 =
                     let uu____2420 = FStar_Options.min_fuel () in
                     let uu____2421 = FStar_Options.initial_fuel () in
                     uu____2420 < uu____2421 in
                   if uu____2419
                   then
                     let uu____2424 =
                       let uu___118_2425 = default_settings in
                       let uu____2426 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___118_2425.query_env);
                         query_decl = (uu___118_2425.query_decl);
                         query_name = (uu___118_2425.query_name);
                         query_index = (uu___118_2425.query_index);
                         query_range = (uu___118_2425.query_range);
                         query_fuel = uu____2426;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___118_2425.query_rlimit);
                         query_hint = (uu___118_2425.query_hint);
                         query_errors = (uu___118_2425.query_errors);
                         query_all_labels = (uu___118_2425.query_all_labels);
                         query_suffix = (uu___118_2425.query_suffix);
                         query_hash = (uu___118_2425.query_hash)
                       } in
                     [uu____2424]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2444 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2444
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2446 = with_fuel_and_diagnostics config [] in
                    let uu____2449 =
                      let uu____2452 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2452 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      ((config.query_hash), (config.query_hint))
                      config.query_all_labels uu____2446 uu____2449 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___119_2473 = default_settings in
                        {
                          query_env = (uu___119_2473.query_env);
                          query_decl = (uu___119_2473.query_decl);
                          query_name = (uu___119_2473.query_name);
                          query_index = (uu___119_2473.query_index);
                          query_range = (uu___119_2473.query_range);
                          query_fuel = (uu___119_2473.query_fuel);
                          query_ifuel = (uu___119_2473.query_ifuel);
                          query_rlimit = (uu___119_2473.query_rlimit);
                          query_hint = (uu___119_2473.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___119_2473.query_all_labels);
                          query_suffix = (uu___119_2473.query_suffix);
                          query_hash = (uu___119_2473.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2474 =
                   let uu____2481 = FStar_Options.admit_smt_queries () in
                   let uu____2482 = FStar_Options.admit_except () in
                   (uu____2481, uu____2482) in
                 (match uu____2474 with
                  | (true ,uu____2487) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let skip =
                        if FStar_Util.starts_with id "("
                        then
                          let full_query_id =
                            let uu____2499 =
                              let uu____2500 =
                                let uu____2501 =
                                  let uu____2502 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2502 ")" in
                                Prims.strcat ", " uu____2501 in
                              Prims.strcat default_settings.query_name
                                uu____2500 in
                            Prims.strcat "(" uu____2499 in
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
        (let uu____2527 =
           let uu____2528 =
             let uu____2529 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2529 in
           FStar_Util.format1 "Starting query at %s" uu____2528 in
         FStar_SMTEncoding_Encode.push uu____2527);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2531 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2531 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2565 =
               let uu____2566 =
                 let uu____2567 =
                   let uu____2568 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2568 in
                 FStar_Util.format1 "Ending query at %s" uu____2567 in
               FStar_SMTEncoding_Encode.pop uu____2566 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2569);
                        FStar_SMTEncoding_Term.freevars = uu____2570;
                        FStar_SMTEncoding_Term.rng = uu____2571;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2572;
                    FStar_SMTEncoding_Term.assumption_name = uu____2573;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2574;_}
                  -> pop1 ()
              | uu____2589 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2590 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2592 -> failwith "Impossible"))
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
           let uu____2598 =
             let uu____2605 = FStar_Options.peek () in (e, g, uu____2605) in
           [uu____2598]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2620  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2622  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2624  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2627  -> fun uu____2628  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2631  -> fun uu____2632  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2638 =
             let uu____2645 = FStar_Options.peek () in (e, g, uu____2645) in
           [uu____2638]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2661  -> fun uu____2662  -> fun uu____2663  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2669  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2671  -> ())
  }
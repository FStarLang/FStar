open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result:
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____11,('Auu____10,'Auu____9) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____11,'Auu____10) FStar_Util.either
  =
  fun uu___56_27  ->
    match uu___56_27 with
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
      (let uu____157 = FStar_Options.use_hints () in
       if uu____157
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____160 = FStar_Options.hint_file () in
           match uu____160 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____164 = FStar_Util.read_hints val_filename in
         match uu____164 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____170 = FStar_Options.hint_info () in
               if uu____170
               then
                 let uu____171 =
                   let uu____172 = FStar_Options.hint_file () in
                   match uu____172 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____176 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____171
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____233 = FStar_Options.hint_info () in
             (if uu____233
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____240 = FStar_Options.record_hints () in
     if uu____240
     then
       let hints =
         let uu____242 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____242 in
       let hints_db =
         let uu____298 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____298; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____301 = FStar_Options.hint_file () in
         match uu____301 with
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
        | uu____444 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____456 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____462 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____462) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____487 =
                     matches_fact_ids include_assumption_names a in
                   if uu____487 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____497 -> d :: out) [] theory_rev in
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
            let uu____521 = filter_using_facts_from e theory in
            (uu____521, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____531 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____555  ->
                     match uu____555 with
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
                          | uu____612 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____531 with
             | (theory',n_retained,n_pruned) ->
                 let uu____630 =
                   let uu____633 =
                     let uu____636 =
                       let uu____637 =
                         let uu____638 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____638 in
                       FStar_SMTEncoding_Term.Caption uu____637 in
                     [uu____636] in
                   FStar_List.append theory' uu____633 in
                 (uu____630, true))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____655 = filter_using_facts_from e x in (uu____655, false)
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
    let uu____819 = FStar_Util.string_of_int err.error_fuel in
    let uu____820 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____819 uu____820
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
      let uu____1195 =
        let uu____1198 =
          let uu____1199 =
            let uu____1200 = FStar_Util.string_of_int n1 in
            let uu____1201 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1200 uu____1201 in
          FStar_SMTEncoding_Term.Caption uu____1199 in
        let uu____1202 =
          let uu____1205 =
            let uu____1206 =
              let uu____1213 =
                let uu____1214 =
                  let uu____1219 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1222 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1219, uu____1222) in
                FStar_SMTEncoding_Util.mkEq uu____1214 in
              (uu____1213, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1206 in
          let uu____1225 =
            let uu____1228 =
              let uu____1229 =
                let uu____1236 =
                  let uu____1237 =
                    let uu____1242 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1245 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1242, uu____1245) in
                  FStar_SMTEncoding_Util.mkEq uu____1237 in
                (uu____1236, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1229 in
            [uu____1228; settings.query_decl] in
          uu____1205 :: uu____1225 in
        uu____1198 :: uu____1202 in
      let uu____1248 =
        let uu____1251 =
          let uu____1254 =
            let uu____1257 =
              let uu____1258 =
                let uu____1263 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1263) in
              FStar_SMTEncoding_Term.SetOption uu____1258 in
            [uu____1257;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1264 =
            let uu____1267 =
              let uu____1270 = FStar_Options.record_hints () in
              if uu____1270
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1274 =
              let uu____1277 =
                let uu____1280 = FStar_Options.print_z3_statistics () in
                if uu____1280
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1277 settings.query_suffix in
            FStar_List.append uu____1267 uu____1274 in
          FStar_List.append uu____1254 uu____1264 in
        FStar_List.append label_assumptions uu____1251 in
      FStar_List.append uu____1195 uu____1248
let used_hint: query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint
let get_hint_for:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____1297 = FStar_ST.op_Bang replaying_hints in
      match uu____1297 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___57_1359  ->
               match uu___57_1359 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1365 -> FStar_Pervasives_Native.None)
      | uu____1368 -> FStar_Pervasives_Native.None
let query_errors:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1381 -> FStar_Pervasives_Native.None
      | uu____1382 ->
          let uu____1383 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1383 with
           | (msg,error_labels) ->
               let err =
                 let uu____1393 =
                   FStar_List.map
                     (fun uu____1418  ->
                        match uu____1418 with
                        | (uu____1431,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1393
                 } in
               FStar_Pervasives_Native.Some err)
let detail_hint_replay:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1440 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1440
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1441 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____1459 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____1459
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1538 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1538) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err  ->
            match err.error_messages with | [] -> false | uu____1637 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1653 = find_localized_errors errs in
    FStar_Option.isSome uu____1653
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1659 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1661 = FStar_Options.n_cores () in
         uu____1661 = (Prims.parse_int "1")) in
    if uu____1659
    then
      let initial_fuel1 =
        let uu___58_1663 = settings in
        let uu____1664 = FStar_Options.initial_fuel () in
        let uu____1665 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___58_1663.query_env);
          query_decl = (uu___58_1663.query_decl);
          query_name = (uu___58_1663.query_name);
          query_index = (uu___58_1663.query_index);
          query_range = (uu___58_1663.query_range);
          query_fuel = uu____1664;
          query_ifuel = uu____1665;
          query_rlimit = (uu___58_1663.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___58_1663.query_errors);
          query_all_labels = (uu___58_1663.query_all_labels);
          query_suffix = (uu___58_1663.query_suffix);
          query_hash = (uu___58_1663.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1684 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1684 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1763 = FStar_ST.op_Bang res in FStar_Option.get uu____1763) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1841 = find_localized_errors settings.query_errors in
       match uu____1841 with
       | FStar_Pervasives_Native.Some err ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1851 =
                      let uu____1852 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1852 in
                    FStar_Errors.diag settings.query_range uu____1851));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1854 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1864 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1864)) in
             FStar_All.pipe_right uu____1854 (FStar_String.concat "; ") in
           let uu____1867 =
             let uu____1876 =
               let uu____1883 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____1883,
                 (settings.query_range)) in
             [uu____1876] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1867)
let query_info: query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1902 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1902
      then
        let uu____1903 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1903 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1911 -> "succeeded"
              | uu____1912 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1914 =
                let uu____1915 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1916 =
                  let uu____1917 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1917 ")" in
                Prims.strcat uu____1915 uu____1916 in
              Prims.strcat "(" uu____1914 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1921 = FStar_Options.print_z3_statistics () in
              if uu____1921
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1933 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1933 "}"
              else "" in
            ((let uu____1936 =
                let uu____1939 =
                  let uu____1942 =
                    let uu____1945 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1946 =
                      let uu____1949 =
                        let uu____1952 =
                          let uu____1955 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1956 =
                            let uu____1959 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1960 =
                              let uu____1963 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1964 =
                                let uu____1967 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1967; stats] in
                              uu____1963 :: uu____1964 in
                            uu____1959 :: uu____1960 in
                          uu____1955 :: uu____1956 in
                        used_hint_tag :: uu____1952 in
                      tag :: uu____1949 in
                    uu____1945 :: uu____1946 in
                  (settings.query_name) :: uu____1942 in
                range :: uu____1939 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1936);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1979  ->
                     match uu____1979 with
                     | (uu____1986,msg,range1) ->
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
      let uu____1998 =
        let uu____1999 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1999 in
      if uu____1998
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
                | uu____2017 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____2022 = FStar_ST.op_Bang recorded_hints in
           match uu____2022 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2140 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____2148 =
               let uu____2149 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____2149 in
             store_hint uu____2148
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2154 -> ())
let process_result:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2166 =
         (used_hint settings) &&
           (let uu____2168 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2168) in
       if uu____2166 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2254 = f q res in
                     match uu____2254 with
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
            (let uu____2282 =
               let uu____2289 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2289 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2321 = FStar_Options.z3_rlimit_factor () in
                     let uu____2322 =
                       let uu____2323 = FStar_Options.z3_rlimit () in
                       uu____2323 * (Prims.parse_int "544656") in
                     uu____2321 * uu____2322 in
                   let next_hint = get_hint_for qname index1 in
                   let default_settings =
                     let uu____2328 = FStar_TypeChecker_Env.get_range env in
                     let uu____2329 = FStar_Options.initial_fuel () in
                     let uu____2330 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2328;
                       query_fuel = uu____2329;
                       query_ifuel = uu____2330;
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
                              { FStar_Util.hint_name = uu____2335;
                                FStar_Util.hint_index = uu____2336;
                                FStar_Util.fuel = uu____2337;
                                FStar_Util.ifuel = uu____2338;
                                FStar_Util.unsat_core = uu____2339;
                                FStar_Util.query_elapsed_time = uu____2340;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____2282 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2361;
                         FStar_Util.hint_index = uu____2362;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2366;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___59_2375 = default_settings in
                         {
                           query_env = (uu___59_2375.query_env);
                           query_decl = (uu___59_2375.query_decl);
                           query_name = (uu___59_2375.query_name);
                           query_index = (uu___59_2375.query_index);
                           query_range = (uu___59_2375.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___59_2375.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___59_2375.query_errors);
                           query_all_labels = (uu___59_2375.query_all_labels);
                           query_suffix = (uu___59_2375.query_suffix);
                           query_hash = (uu___59_2375.query_hash)
                         })]
                   | uu____2378 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2384 =
                     let uu____2385 = FStar_Options.max_ifuel () in
                     let uu____2386 = FStar_Options.initial_ifuel () in
                     uu____2385 > uu____2386 in
                   if uu____2384
                   then
                     let uu____2389 =
                       let uu___60_2390 = default_settings in
                       let uu____2391 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___60_2390.query_env);
                         query_decl = (uu___60_2390.query_decl);
                         query_name = (uu___60_2390.query_name);
                         query_index = (uu___60_2390.query_index);
                         query_range = (uu___60_2390.query_range);
                         query_fuel = (uu___60_2390.query_fuel);
                         query_ifuel = uu____2391;
                         query_rlimit = (uu___60_2390.query_rlimit);
                         query_hint = (uu___60_2390.query_hint);
                         query_errors = (uu___60_2390.query_errors);
                         query_all_labels = (uu___60_2390.query_all_labels);
                         query_suffix = (uu___60_2390.query_suffix);
                         query_hash = (uu___60_2390.query_hash)
                       } in
                     [uu____2389]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2396 =
                     let uu____2397 =
                       let uu____2398 = FStar_Options.max_fuel () in
                       uu____2398 / (Prims.parse_int "2") in
                     let uu____2405 = FStar_Options.initial_fuel () in
                     uu____2397 > uu____2405 in
                   if uu____2396
                   then
                     let uu____2408 =
                       let uu___61_2409 = default_settings in
                       let uu____2410 =
                         let uu____2411 = FStar_Options.max_fuel () in
                         uu____2411 / (Prims.parse_int "2") in
                       let uu____2418 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___61_2409.query_env);
                         query_decl = (uu___61_2409.query_decl);
                         query_name = (uu___61_2409.query_name);
                         query_index = (uu___61_2409.query_index);
                         query_range = (uu___61_2409.query_range);
                         query_fuel = uu____2410;
                         query_ifuel = uu____2418;
                         query_rlimit = (uu___61_2409.query_rlimit);
                         query_hint = (uu___61_2409.query_hint);
                         query_errors = (uu___61_2409.query_errors);
                         query_all_labels = (uu___61_2409.query_all_labels);
                         query_suffix = (uu___61_2409.query_suffix);
                         query_hash = (uu___61_2409.query_hash)
                       } in
                     [uu____2408]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2423 =
                     (let uu____2428 = FStar_Options.max_fuel () in
                      let uu____2429 = FStar_Options.initial_fuel () in
                      uu____2428 > uu____2429) &&
                       (let uu____2432 = FStar_Options.max_ifuel () in
                        let uu____2433 = FStar_Options.initial_ifuel () in
                        uu____2432 >= uu____2433) in
                   if uu____2423
                   then
                     let uu____2436 =
                       let uu___62_2437 = default_settings in
                       let uu____2438 = FStar_Options.max_fuel () in
                       let uu____2439 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___62_2437.query_env);
                         query_decl = (uu___62_2437.query_decl);
                         query_name = (uu___62_2437.query_name);
                         query_index = (uu___62_2437.query_index);
                         query_range = (uu___62_2437.query_range);
                         query_fuel = uu____2438;
                         query_ifuel = uu____2439;
                         query_rlimit = (uu___62_2437.query_rlimit);
                         query_hint = (uu___62_2437.query_hint);
                         query_errors = (uu___62_2437.query_errors);
                         query_all_labels = (uu___62_2437.query_all_labels);
                         query_suffix = (uu___62_2437.query_suffix);
                         query_hash = (uu___62_2437.query_hash)
                       } in
                     [uu____2436]
                   else [] in
                 let min_fuel1 =
                   let uu____2444 =
                     let uu____2445 = FStar_Options.min_fuel () in
                     let uu____2446 = FStar_Options.initial_fuel () in
                     uu____2445 < uu____2446 in
                   if uu____2444
                   then
                     let uu____2449 =
                       let uu___63_2450 = default_settings in
                       let uu____2451 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___63_2450.query_env);
                         query_decl = (uu___63_2450.query_decl);
                         query_name = (uu___63_2450.query_name);
                         query_index = (uu___63_2450.query_index);
                         query_range = (uu___63_2450.query_range);
                         query_fuel = uu____2451;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___63_2450.query_rlimit);
                         query_hint = (uu___63_2450.query_hint);
                         query_errors = (uu___63_2450.query_errors);
                         query_all_labels = (uu___63_2450.query_all_labels);
                         query_suffix = (uu___63_2450.query_suffix);
                         query_hash = (uu___63_2450.query_hash)
                       } in
                     [uu____2449]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2469 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2469
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2471 = with_fuel_and_diagnostics config [] in
                    let uu____2474 =
                      let uu____2477 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2477 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2471
                      uu____2474 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___64_2496 = default_settings in
                        {
                          query_env = (uu___64_2496.query_env);
                          query_decl = (uu___64_2496.query_decl);
                          query_name = (uu___64_2496.query_name);
                          query_index = (uu___64_2496.query_index);
                          query_range = (uu___64_2496.query_range);
                          query_fuel = (uu___64_2496.query_fuel);
                          query_ifuel = (uu___64_2496.query_ifuel);
                          query_rlimit = (uu___64_2496.query_rlimit);
                          query_hint = (uu___64_2496.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___64_2496.query_all_labels);
                          query_suffix = (uu___64_2496.query_suffix);
                          query_hash = (uu___64_2496.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2497 =
                   let uu____2504 = FStar_Options.admit_smt_queries () in
                   let uu____2505 = FStar_Options.admit_except () in
                   (uu____2504, uu____2505) in
                 (match uu____2497 with
                  | (true ,uu____2510) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____2522 =
                              let uu____2523 =
                                let uu____2524 =
                                  let uu____2525 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2525 ")" in
                                Prims.strcat ", " uu____2524 in
                              Prims.strcat default_settings.query_name
                                uu____2523 in
                            Prims.strcat "(" uu____2522 in
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
        (let uu____2547 =
           let uu____2548 =
             let uu____2549 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2549 in
           FStar_Util.format1 "Starting query at %s" uu____2548 in
         FStar_SMTEncoding_Encode.push uu____2547);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2551 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2551 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2585 =
               let uu____2586 =
                 let uu____2587 =
                   let uu____2588 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2588 in
                 FStar_Util.format1 "Ending query at %s" uu____2587 in
               FStar_SMTEncoding_Encode.pop uu____2586 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2589);
                        FStar_SMTEncoding_Term.freevars = uu____2590;
                        FStar_SMTEncoding_Term.rng = uu____2591;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2592;
                    FStar_SMTEncoding_Term.assumption_name = uu____2593;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2594;_}
                  -> pop1 ()
              | uu____2609 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2610 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2612 -> failwith "Impossible"))
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
           let uu____2618 =
             let uu____2625 = FStar_Options.peek () in (e, g, uu____2625) in
           [uu____2618]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2640  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2642  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2644  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2647  -> fun uu____2648  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2651  -> fun uu____2652  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2658 =
             let uu____2665 = FStar_Options.peek () in (e, g, uu____2665) in
           [uu____2658]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2681  -> fun uu____2682  -> fun uu____2683  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2689  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2691  -> ())
  }
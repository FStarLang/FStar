open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either[@@deriving show]
let z3_result_as_replay_result:
  'Auu____9 'Auu____10 'Auu____11 .
    ('Auu____11,('Auu____10,'Auu____9) FStar_Pervasives_Native.tuple2)
      FStar_Util.either -> ('Auu____11,'Auu____10) FStar_Util.either
  =
  fun uu___363_27  ->
    match uu___363_27 with
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
  'Auu____79 . Prims.string -> 'Auu____79 -> Prims.unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____89 = FStar_Options.record_hints () in
       if uu____89
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____147 = FStar_Options.use_hints () in
       if uu____147
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____150 = FStar_Options.hint_file () in
           match uu____150 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename in
         let uu____154 = FStar_Util.read_hints val_filename in
         match uu____154 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____160 = FStar_Options.hint_info () in
               if uu____160
               then
                 let uu____161 =
                   let uu____162 = FStar_Options.hint_file () in
                   match uu____162 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.strcat " from '" (Prims.strcat val_filename "'")
                   | uu____166 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____161
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____221 = FStar_Options.hint_info () in
             (if uu____221
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let finalize_hints_db: Prims.string -> Prims.unit =
  fun src_filename  ->
    (let uu____228 = FStar_Options.record_hints () in
     if uu____228
     then
       let hints =
         let uu____230 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____230 in
       let hints_db =
         let uu____284 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____284; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____287 = FStar_Options.hint_file () in
         match uu____287 with
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
        | uu____426 -> false in
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____438 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some should_enc_fid))
              ||
              (let uu____444 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____444) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Assume a ->
                   let uu____469 =
                     matches_fact_ids include_assumption_names a in
                   if uu____469 then d :: out else out
               | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
                   (FStar_List.iter
                      (fun x  ->
                         FStar_Util.smap_add include_assumption_names x true)
                      names1;
                    d
                    ::
                    out)
               | uu____479 -> d :: out) [] theory_rev in
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
            let uu____503 = filter_using_facts_from e theory in
            (uu____503, false)
        | FStar_Pervasives_Native.Some core1 ->
            let uu____513 =
              FStar_List.fold_right
                (fun d  ->
                   fun uu____537  ->
                     match uu____537 with
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
                          | uu____594 ->
                              ((d :: theory1), n_retained, n_pruned))) theory
                ([], (Prims.parse_int "0"), (Prims.parse_int "0")) in
            (match uu____513 with
             | (theory',n_retained,n_pruned) ->
                 let uu____612 =
                   let uu____615 =
                     let uu____618 =
                       let uu____619 =
                         let uu____620 =
                           FStar_All.pipe_right core1
                             (FStar_String.concat ", ") in
                         Prims.strcat "UNSAT CORE: " uu____620 in
                       FStar_SMTEncoding_Term.Caption uu____619 in
                     [uu____618] in
                   FStar_List.append theory' uu____615 in
                 (uu____612, true))
let filter_facts_without_core:
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decls_t ->
      (FStar_SMTEncoding_Term.decl Prims.list,Prims.bool)
        FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun x  ->
      let uu____637 = filter_using_facts_from e x in (uu____637, false)
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
    let uu____785 = FStar_Util.string_of_int err1.error_fuel in
    let uu____786 = FStar_Util.string_of_int err1.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason
      uu____785 uu____786
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
      let uu____1161 =
        let uu____1164 =
          let uu____1165 =
            let uu____1166 = FStar_Util.string_of_int n1 in
            let uu____1167 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1166 uu____1167 in
          FStar_SMTEncoding_Term.Caption uu____1165 in
        let uu____1168 =
          let uu____1171 =
            let uu____1172 =
              let uu____1179 =
                let uu____1180 =
                  let uu____1185 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1188 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1185, uu____1188) in
                FStar_SMTEncoding_Util.mkEq uu____1180 in
              (uu____1179, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1172 in
          let uu____1191 =
            let uu____1194 =
              let uu____1195 =
                let uu____1202 =
                  let uu____1203 =
                    let uu____1208 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1211 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1208, uu____1211) in
                  FStar_SMTEncoding_Util.mkEq uu____1203 in
                (uu____1202, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1195 in
            [uu____1194; settings.query_decl] in
          uu____1171 :: uu____1191 in
        uu____1164 :: uu____1168 in
      let uu____1214 =
        let uu____1217 =
          let uu____1220 =
            let uu____1223 =
              let uu____1224 =
                let uu____1229 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1229) in
              FStar_SMTEncoding_Term.SetOption uu____1224 in
            [uu____1223;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown] in
          let uu____1230 =
            let uu____1233 =
              let uu____1236 = FStar_Options.record_hints () in
              if uu____1236
              then [FStar_SMTEncoding_Term.GetUnsatCore]
              else [] in
            let uu____1240 =
              let uu____1243 =
                let uu____1246 = FStar_Options.print_z3_statistics () in
                if uu____1246
                then [FStar_SMTEncoding_Term.GetStatistics]
                else [] in
              FStar_List.append uu____1243 settings.query_suffix in
            FStar_List.append uu____1233 uu____1240 in
          FStar_List.append uu____1220 uu____1230 in
        FStar_List.append label_assumptions uu____1217 in
      FStar_List.append uu____1161 uu____1214
let used_hint: query_settings -> Prims.bool =
  fun s  -> FStar_Option.isSome s.query_hint
let next_hint:
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option
  =
  fun qname  ->
    fun qindex  ->
      let uu____1263 = FStar_ST.op_Bang replaying_hints in
      match uu____1263 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___364_1323  ->
               match uu___364_1323 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1329 -> FStar_Pervasives_Native.None)
      | uu____1332 -> FStar_Pervasives_Native.None
let query_errors:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1345 -> FStar_Pervasives_Native.None
      | uu____1346 ->
          let uu____1347 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1347 with
           | (msg,error_labels) ->
               let err1 =
                 let uu____1357 =
                   FStar_List.map
                     (fun uu____1378  ->
                        match uu____1378 with | (uu____1389,x,y) -> (x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1357
                 } in
               FStar_Pervasives_Native.Some err1)
let detail_hint_replay:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1398 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1398
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1399 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____1417 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask
                 (filter_assertions settings.query_env settings.query_hint)
                 ((settings.query_hash), (settings.query_hint))
                 settings.query_all_labels uu____1417
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)));
              (let uu____1488 = FStar_ST.op_Bang res in
               FStar_Option.get uu____1488) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let find_localized_errors:
  errors Prims.list -> errors FStar_Pervasives_Native.option =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err1  ->
            match err1.error_messages with | [] -> false | uu____1575 -> true))
let has_localized_errors: errors Prims.list -> Prims.bool =
  fun errs  ->
    let uu____1589 = find_localized_errors errs in
    FStar_Option.isSome uu____1589
let report_errors: query_settings -> Prims.unit =
  fun settings  ->
    let uu____1595 =
      (FStar_Options.detail_errors ()) &&
        (let uu____1597 = FStar_Options.n_cores () in
         uu____1597 = (Prims.parse_int "1")) in
    if uu____1595
    then
      let initial_fuel1 =
        let uu___365_1599 = settings in
        let uu____1600 = FStar_Options.initial_fuel () in
        let uu____1601 = FStar_Options.initial_ifuel () in
        {
          query_env = (uu___365_1599.query_env);
          query_decl = (uu___365_1599.query_decl);
          query_name = (uu___365_1599.query_name);
          query_index = (uu___365_1599.query_index);
          query_range = (uu___365_1599.query_range);
          query_fuel = uu____1600;
          query_ifuel = uu____1601;
          query_rlimit = (uu___365_1599.query_rlimit);
          query_hint = FStar_Pervasives_Native.None;
          query_errors = (uu___365_1599.query_errors);
          query_all_labels = (uu___365_1599.query_all_labels);
          query_suffix = (uu___365_1599.query_suffix);
          query_hash = (uu___365_1599.query_hash)
        } in
      let ask_z3 label_assumptions =
        let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
        (let uu____1620 =
           with_fuel_and_diagnostics initial_fuel1 label_assumptions in
         FStar_SMTEncoding_Z3.ask
           (filter_facts_without_core settings.query_env)
           ((settings.query_hash), FStar_Pervasives_Native.None)
           settings.query_all_labels uu____1620 FStar_Pervasives_Native.None
           (fun r  ->
              FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r)));
        (let uu____1697 = FStar_ST.op_Bang res in FStar_Option.get uu____1697) in
      FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env
        settings.query_all_labels ask_z3
    else
      (let uu____1765 = find_localized_errors settings.query_errors in
       match uu____1765 with
       | FStar_Pervasives_Native.Some err1 ->
           (FStar_All.pipe_right settings.query_errors
              (FStar_List.iter
                 (fun e  ->
                    let uu____1775 =
                      let uu____1776 = error_to_short_string e in
                      Prims.strcat "SMT solver says: " uu____1776 in
                    FStar_Errors.diag settings.query_range uu____1775));
            FStar_TypeChecker_Err.add_errors settings.query_env
              err1.error_messages)
       | FStar_Pervasives_Native.None  ->
           let err_detail =
             let uu____1778 =
               FStar_All.pipe_right settings.query_errors
                 (FStar_List.map
                    (fun e  ->
                       let uu____1788 = error_to_short_string e in
                       Prims.strcat "SMT solver says: " uu____1788)) in
             FStar_All.pipe_right uu____1778 (FStar_String.concat "; ") in
           let uu____1791 =
             let uu____1798 =
               let uu____1803 =
                 FStar_Util.format1 "Unknown assertion failed (%s)"
                   err_detail in
               (uu____1803, (settings.query_range)) in
             [uu____1798] in
           FStar_TypeChecker_Err.add_errors settings.query_env uu____1791)
let query_info: query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit
  =
  fun settings  ->
    fun z3result  ->
      let uu____1818 =
        (FStar_Options.hint_info ()) ||
          (FStar_Options.print_z3_statistics ()) in
      if uu____1818
      then
        let uu____1819 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____1819 with
        | (status_string,errs) ->
            let tag =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT uu____1827 -> "succeeded"
              | uu____1828 ->
                  Prims.strcat "failed {reason-unknown="
                    (Prims.strcat status_string "}") in
            let range =
              let uu____1830 =
                let uu____1831 =
                  FStar_Range.string_of_range settings.query_range in
                let uu____1832 =
                  let uu____1833 = FStar_SMTEncoding_Z3.at_log_file () in
                  Prims.strcat uu____1833 ")" in
                Prims.strcat uu____1831 uu____1832 in
              Prims.strcat "(" uu____1830 in
            let used_hint_tag =
              if used_hint settings then " (with hint)" else "" in
            let stats =
              let uu____1837 = FStar_Options.print_z3_statistics () in
              if uu____1837
              then
                let f k v1 a =
                  Prims.strcat a
                    (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " "))) in
                let str =
                  FStar_Util.smap_fold
                    z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                    "statistics={" in
                let uu____1849 =
                  FStar_Util.substring str (Prims.parse_int "0")
                    ((FStar_String.length str) - (Prims.parse_int "1")) in
                Prims.strcat uu____1849 "}"
              else "" in
            ((let uu____1852 =
                let uu____1855 =
                  let uu____1858 =
                    let uu____1861 =
                      FStar_Util.string_of_int settings.query_index in
                    let uu____1862 =
                      let uu____1865 =
                        let uu____1868 =
                          let uu____1871 =
                            FStar_Util.string_of_int
                              z3result.FStar_SMTEncoding_Z3.z3result_time in
                          let uu____1872 =
                            let uu____1875 =
                              FStar_Util.string_of_int settings.query_fuel in
                            let uu____1876 =
                              let uu____1879 =
                                FStar_Util.string_of_int settings.query_ifuel in
                              let uu____1880 =
                                let uu____1883 =
                                  FStar_Util.string_of_int
                                    settings.query_rlimit in
                                [uu____1883; stats] in
                              uu____1879 :: uu____1880 in
                            uu____1875 :: uu____1876 in
                          uu____1871 :: uu____1872 in
                        used_hint_tag :: uu____1868 in
                      tag :: uu____1865 in
                    uu____1861 :: uu____1862 in
                  (settings.query_name) :: uu____1858 in
                range :: uu____1855 in
              FStar_Util.print
                "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                uu____1852);
             FStar_All.pipe_right errs
               (FStar_List.iter
                  (fun uu____1897  ->
                     match uu____1897 with
                     | (uu____1904,msg,range1) ->
                         let e =
                           FStar_Errors.mk_issue FStar_Errors.EInfo
                             (FStar_Pervasives_Native.Some range1) msg in
                         let tag1 =
                           if used_hint settings
                           then "(Hint-replay failed): "
                           else "" in
                         let uu____1910 = FStar_Errors.format_issue e in
                         FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1910)))
      else ()
let record_hint:
  query_settings -> FStar_SMTEncoding_Z3.z3result -> Prims.unit =
  fun settings  ->
    fun z3result  ->
      let uu____1918 =
        let uu____1919 = FStar_Options.record_hints () in
        Prims.op_Negation uu____1919 in
      if uu____1918
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
                | uu____1937 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____1942 = FStar_ST.op_Bang recorded_hints in
           match uu____1942 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____2056 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2064 -> ())
let process_result:
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option
  =
  fun settings  ->
    fun result  ->
      (let uu____2076 =
         (used_hint settings) &&
           (let uu____2078 = FStar_Options.z3_refresh () in
            Prims.op_Negation uu____2078) in
       if uu____2076 then FStar_SMTEncoding_Z3.refresh () else ());
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
                     let uu____2164 = f q res in
                     match uu____2164 with
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
            (let uu____2192 =
               let uu____2199 =
                 match env.FStar_TypeChecker_Env.qname_and_index with
                 | FStar_Pervasives_Native.None  ->
                     failwith "No query name set!"
                 | FStar_Pervasives_Native.Some (q,n1) ->
                     ((FStar_Ident.text_of_lid q), n1) in
               match uu____2199 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____2231 = FStar_Options.z3_rlimit_factor () in
                     let uu____2232 =
                       let uu____2233 = FStar_Options.z3_rlimit () in
                       uu____2233 * (Prims.parse_int "544656") in
                     uu____2231 * uu____2232 in
                   let next_hint1 = next_hint qname index1 in
                   let default_settings =
                     let uu____2238 = FStar_TypeChecker_Env.get_range env in
                     let uu____2239 = FStar_Options.initial_fuel () in
                     let uu____2240 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____2238;
                       query_fuel = uu____2239;
                       query_ifuel = uu____2240;
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
                              { FStar_Util.hint_name = uu____2245;
                                FStar_Util.hint_index = uu____2246;
                                FStar_Util.fuel = uu____2247;
                                FStar_Util.ifuel = uu____2248;
                                FStar_Util.unsat_core = uu____2249;
                                FStar_Util.query_elapsed_time = uu____2250;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint1) in
             match uu____2192 with
             | (default_settings,next_hint1) ->
                 let use_hints_setting =
                   match next_hint1 with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____2271;
                         FStar_Util.hint_index = uu____2272;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2276;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___366_2285 = default_settings in
                         {
                           query_env = (uu___366_2285.query_env);
                           query_decl = (uu___366_2285.query_decl);
                           query_name = (uu___366_2285.query_name);
                           query_index = (uu___366_2285.query_index);
                           query_range = (uu___366_2285.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___366_2285.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___366_2285.query_errors);
                           query_all_labels =
                             (uu___366_2285.query_all_labels);
                           query_suffix = (uu___366_2285.query_suffix);
                           query_hash = (uu___366_2285.query_hash)
                         })]
                   | uu____2288 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____2294 =
                     let uu____2295 = FStar_Options.max_ifuel () in
                     let uu____2296 = FStar_Options.initial_ifuel () in
                     uu____2295 > uu____2296 in
                   if uu____2294
                   then
                     let uu____2299 =
                       let uu___367_2300 = default_settings in
                       let uu____2301 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___367_2300.query_env);
                         query_decl = (uu___367_2300.query_decl);
                         query_name = (uu___367_2300.query_name);
                         query_index = (uu___367_2300.query_index);
                         query_range = (uu___367_2300.query_range);
                         query_fuel = (uu___367_2300.query_fuel);
                         query_ifuel = uu____2301;
                         query_rlimit = (uu___367_2300.query_rlimit);
                         query_hint = (uu___367_2300.query_hint);
                         query_errors = (uu___367_2300.query_errors);
                         query_all_labels = (uu___367_2300.query_all_labels);
                         query_suffix = (uu___367_2300.query_suffix);
                         query_hash = (uu___367_2300.query_hash)
                       } in
                     [uu____2299]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2306 =
                     let uu____2307 =
                       let uu____2308 = FStar_Options.max_fuel () in
                       uu____2308 / (Prims.parse_int "2") in
                     let uu____2315 = FStar_Options.initial_fuel () in
                     uu____2307 > uu____2315 in
                   if uu____2306
                   then
                     let uu____2318 =
                       let uu___368_2319 = default_settings in
                       let uu____2320 =
                         let uu____2321 = FStar_Options.max_fuel () in
                         uu____2321 / (Prims.parse_int "2") in
                       let uu____2328 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___368_2319.query_env);
                         query_decl = (uu___368_2319.query_decl);
                         query_name = (uu___368_2319.query_name);
                         query_index = (uu___368_2319.query_index);
                         query_range = (uu___368_2319.query_range);
                         query_fuel = uu____2320;
                         query_ifuel = uu____2328;
                         query_rlimit = (uu___368_2319.query_rlimit);
                         query_hint = (uu___368_2319.query_hint);
                         query_errors = (uu___368_2319.query_errors);
                         query_all_labels = (uu___368_2319.query_all_labels);
                         query_suffix = (uu___368_2319.query_suffix);
                         query_hash = (uu___368_2319.query_hash)
                       } in
                     [uu____2318]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2333 =
                     (let uu____2338 = FStar_Options.max_fuel () in
                      let uu____2339 = FStar_Options.initial_fuel () in
                      uu____2338 > uu____2339) &&
                       (let uu____2342 = FStar_Options.max_ifuel () in
                        let uu____2343 = FStar_Options.initial_ifuel () in
                        uu____2342 >= uu____2343) in
                   if uu____2333
                   then
                     let uu____2346 =
                       let uu___369_2347 = default_settings in
                       let uu____2348 = FStar_Options.max_fuel () in
                       let uu____2349 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___369_2347.query_env);
                         query_decl = (uu___369_2347.query_decl);
                         query_name = (uu___369_2347.query_name);
                         query_index = (uu___369_2347.query_index);
                         query_range = (uu___369_2347.query_range);
                         query_fuel = uu____2348;
                         query_ifuel = uu____2349;
                         query_rlimit = (uu___369_2347.query_rlimit);
                         query_hint = (uu___369_2347.query_hint);
                         query_errors = (uu___369_2347.query_errors);
                         query_all_labels = (uu___369_2347.query_all_labels);
                         query_suffix = (uu___369_2347.query_suffix);
                         query_hash = (uu___369_2347.query_hash)
                       } in
                     [uu____2346]
                   else [] in
                 let min_fuel1 =
                   let uu____2354 =
                     let uu____2355 = FStar_Options.min_fuel () in
                     let uu____2356 = FStar_Options.initial_fuel () in
                     uu____2355 < uu____2356 in
                   if uu____2354
                   then
                     let uu____2359 =
                       let uu___370_2360 = default_settings in
                       let uu____2361 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___370_2360.query_env);
                         query_decl = (uu___370_2360.query_decl);
                         query_name = (uu___370_2360.query_name);
                         query_index = (uu___370_2360.query_index);
                         query_range = (uu___370_2360.query_range);
                         query_fuel = uu____2361;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___370_2360.query_rlimit);
                         query_hint = (uu___370_2360.query_hint);
                         query_errors = (uu___370_2360.query_errors);
                         query_all_labels = (uu___370_2360.query_all_labels);
                         query_suffix = (uu___370_2360.query_suffix);
                         query_hash = (uu___370_2360.query_hash)
                       } in
                     [uu____2359]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config k =
                   (let uu____2379 =
                      (used_hint config) || (FStar_Options.z3_refresh ()) in
                    if uu____2379
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2381 = with_fuel_and_diagnostics config [] in
                    let uu____2384 =
                      let uu____2387 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2387 in
                    FStar_SMTEncoding_Z3.ask
                      (filter_assertions config.query_env config.query_hint)
                      ((config.query_hash), (config.query_hint))
                      config.query_all_labels uu____2381 uu____2384 k) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___371_2408 = default_settings in
                        {
                          query_env = (uu___371_2408.query_env);
                          query_decl = (uu___371_2408.query_decl);
                          query_name = (uu___371_2408.query_name);
                          query_index = (uu___371_2408.query_index);
                          query_range = (uu___371_2408.query_range);
                          query_fuel = (uu___371_2408.query_fuel);
                          query_ifuel = (uu___371_2408.query_ifuel);
                          query_rlimit = (uu___371_2408.query_rlimit);
                          query_hint = (uu___371_2408.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___371_2408.query_all_labels);
                          query_suffix = (uu___371_2408.query_suffix);
                          query_hash = (uu___371_2408.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____2409 =
                   let uu____2416 = FStar_Options.admit_smt_queries () in
                   let uu____2417 = FStar_Options.admit_except () in
                   (uu____2416, uu____2417) in
                 (match uu____2409 with
                  | (true ,uu____2422) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id) ->
                      let skip =
                        if FStar_Util.starts_with id "("
                        then
                          let full_query_id =
                            let uu____2434 =
                              let uu____2435 =
                                let uu____2436 =
                                  let uu____2437 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.strcat uu____2437 ")" in
                                Prims.strcat ", " uu____2436 in
                              Prims.strcat default_settings.query_name
                                uu____2435 in
                            Prims.strcat "(" uu____2434 in
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
        (let uu____2459 =
           let uu____2460 =
             let uu____2461 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____2461 in
           FStar_Util.format1 "Starting query at %s" uu____2460 in
         FStar_SMTEncoding_Encode.push uu____2459);
        (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
         let uu____2463 =
           FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
         match uu____2463 with
         | (prefix1,labels,qry,suffix) ->
             let pop1 uu____2497 =
               let uu____2498 =
                 let uu____2499 =
                   let uu____2500 = FStar_TypeChecker_Env.get_range tcenv1 in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____2500 in
                 FStar_Util.format1 "Ending query at %s" uu____2499 in
               FStar_SMTEncoding_Encode.pop uu____2498 in
             (match qry with
              | FStar_SMTEncoding_Term.Assume
                  {
                    FStar_SMTEncoding_Term.assumption_term =
                      {
                        FStar_SMTEncoding_Term.tm =
                          FStar_SMTEncoding_Term.App
                          (FStar_SMTEncoding_Term.FalseOp ,uu____2501);
                        FStar_SMTEncoding_Term.freevars = uu____2502;
                        FStar_SMTEncoding_Term.rng = uu____2503;_};
                    FStar_SMTEncoding_Term.assumption_caption = uu____2504;
                    FStar_SMTEncoding_Term.assumption_name = uu____2505;
                    FStar_SMTEncoding_Term.assumption_fact_ids = uu____2506;_}
                  -> pop1 ()
              | uu____2521 when tcenv1.FStar_TypeChecker_Env.admit -> pop1 ()
              | FStar_SMTEncoding_Term.Assume uu____2522 ->
                  (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                   pop1 ())
              | uu____2524 -> failwith "Impossible"))
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
           let uu____2530 =
             let uu____2537 = FStar_Options.peek () in (e, g, uu____2537) in
           [uu____2530]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let dummy: FStar_TypeChecker_Env.solver_t =
  {
    FStar_TypeChecker_Env.init = (fun uu____2552  -> ());
    FStar_TypeChecker_Env.push = (fun uu____2554  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____2556  -> ());
    FStar_TypeChecker_Env.encode_modul =
      (fun uu____2559  -> fun uu____2560  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____2563  -> fun uu____2564  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____2570 =
             let uu____2577 = FStar_Options.peek () in (e, g, uu____2577) in
           [uu____2570]);
    FStar_TypeChecker_Env.solve =
      (fun uu____2593  -> fun uu____2594  -> fun uu____2595  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____2601  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____2603  -> ())
  }
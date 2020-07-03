open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'uuuuuu35 'uuuuuu36 'uuuuuu37 .
    ('uuuuuu35, ('uuuuuu36 * 'uuuuuu37)) FStar_Util.either ->
      ('uuuuuu35, 'uuuuuu36) FStar_Util.either
  =
  fun uu___0_54 ->
    match uu___0_54 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r, uu____69) -> FStar_Util.Inr r
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let initialize_hints_db : 'uuuuuu92 . Prims.string -> 'uuuuuu92 -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu____104 = FStar_Options.record_hints () in
       if uu____104
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       let uu____120 = FStar_Util.read_hints val_filename in
       match uu____120 with
       | FStar_Util.HintsOK hints ->
           let expected_digest = FStar_Util.digest_of_file norm_src_filename in
           ((let uu____124 = FStar_Options.hint_info () in
             if uu____124
             then
               FStar_Util.print3 "(%s) digest is %s from %s.\n"
                 norm_src_filename
                 (if hints.FStar_Util.module_digest = expected_digest
                  then "valid; using hints"
                  else "invalid; using potentially stale hints") val_filename
             else ());
            FStar_ST.op_Colon_Equals replaying_hints
              (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
       | FStar_Util.MalformedJson ->
           let uu____138 = FStar_Options.use_hints () in
           if uu____138
           then
             let uu____139 =
               let uu____144 =
                 FStar_Util.format1
                   "Malformed JSON hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu____144) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu____139
           else ()
       | FStar_Util.UnableToOpen ->
           let uu____147 = FStar_Options.use_hints () in
           if uu____147
           then
             let uu____148 =
               let uu____153 =
                 FStar_Util.format1
                   "Unable to open hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu____153) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu____148
           else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu____161 = FStar_Options.record_hints () in
     if uu____161
     then
       let hints =
         let uu____163 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____163 in
       let hints_db =
         let uu____177 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____177; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
let with_hints_db : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun fname ->
    fun f ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
let (filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e ->
    fun theory ->
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____258 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_265 ->
                     match uu___1_265 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____267 -> false)))
              ||
              (let uu____269 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____269) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.of_int (10000)) in
        let keep_decl uu___2_286 =
          match uu___2_286 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names ->
              (FStar_List.iter
                 (fun x ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names;
               true)
          | FStar_SMTEncoding_Term.Module uu____294 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____301 -> true in
        FStar_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Module (name, decls) ->
                   let uu____321 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl) in
                   FStar_All.pipe_right uu____321
                     (fun decls1 ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____338 ->
                   let uu____339 = keep_decl d in
                   if uu____339 then d :: out else out) [] theory_rev in
      pruned_theory
let rec (filter_assertions_with_stats :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int *
          Prims.int))
  =
  fun e ->
    fun core ->
      fun theory ->
        match core with
        | FStar_Pervasives_Native.None ->
            let uu____384 = filter_using_facts_from e theory in
            (uu____384, false, Prims.int_zero, Prims.int_zero)
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory in
            let uu____397 =
              let uu____406 =
                let uu____415 =
                  let uu____418 =
                    let uu____419 =
                      let uu____420 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ") in
                      Prims.op_Hat "UNSAT CORE: " uu____420 in
                    FStar_SMTEncoding_Term.Caption uu____419 in
                  [uu____418] in
                (uu____415, Prims.int_zero, Prims.int_zero) in
              FStar_List.fold_left
                (fun uu____439 ->
                   fun d ->
                     match uu____439 with
                     | (theory1, n_retained, n_pruned) ->
                         (match d with
                          | FStar_SMTEncoding_Term.Assume a ->
                              if
                                FStar_List.contains
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  core1
                              then
                                ((d :: theory1),
                                  (n_retained + Prims.int_one), n_pruned)
                              else
                                if
                                  FStar_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + Prims.int_one))
                          | FStar_SMTEncoding_Term.Module (name, decls) ->
                              let uu____503 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1)) in
                              FStar_All.pipe_right uu____503
                                (fun uu____551 ->
                                   match uu____551 with
                                   | (decls1, uu____571, r, p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____582 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____406 theory_rev in
            (match uu____397 with
             | (theory', n_retained, n_pruned) ->
                 (theory', true, n_retained, n_pruned))
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e ->
    fun core ->
      fun theory ->
        let uu____629 = filter_assertions_with_stats e core theory in
        match uu____629 with
        | (theory1, b, uu____648, uu____649) -> (theory1, b)
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e ->
    fun x ->
      let uu____676 = filter_using_facts_from e x in (uu____676, false)
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_reason
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_fuel
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_ifuel
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_hint
let (__proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
let (error_to_short_string : errors -> Prims.string) =
  fun err ->
    let uu____857 = FStar_Util.string_of_int err.error_fuel in
    let uu____858 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____857
      uu____858
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu____871 =
        let uu____872 = FStar_Util.string_of_int err.error_fuel in
        let uu____873 = FStar_Util.string_of_int err.error_ifuel in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu____872 uu____873
          (if FStar_Option.isSome err.error_hint then "with hint" else "") in
      [uu____871]
    else []
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
  query_hash: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkquery_settings__item__query_env :
  query_settings -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_env
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_decl
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_name
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_index
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_range
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_fuel
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_ifuel
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_rlimit
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hint
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_errors
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_all_labels
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_suffix
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hash
let (with_fuel_and_diagnostics :
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun settings ->
    fun label_assumptions ->
      let n = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1292 =
        let uu____1295 =
          let uu____1296 =
            let uu____1297 = FStar_Util.string_of_int n in
            let uu____1298 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1297 uu____1298 in
          FStar_SMTEncoding_Term.Caption uu____1296 in
        let uu____1299 =
          let uu____1302 =
            let uu____1303 =
              let uu____1310 =
                let uu____1311 =
                  let uu____1316 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1319 = FStar_SMTEncoding_Term.n_fuel n in
                  (uu____1316, uu____1319) in
                FStar_SMTEncoding_Util.mkEq uu____1311 in
              (uu____1310, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1303 in
          let uu____1320 =
            let uu____1323 =
              let uu____1324 =
                let uu____1331 =
                  let uu____1332 =
                    let uu____1337 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1340 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1337, uu____1340) in
                  FStar_SMTEncoding_Util.mkEq uu____1332 in
                (uu____1331, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1324 in
            [uu____1323; settings.query_decl] in
          uu____1302 :: uu____1320 in
        uu____1295 :: uu____1299 in
      let uu____1341 =
        let uu____1344 =
          let uu____1347 =
            let uu____1350 =
              let uu____1351 =
                let uu____1356 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1356) in
              FStar_SMTEncoding_Term.SetOption uu____1351 in
            [uu____1350;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore] in
          let uu____1357 =
            let uu____1360 =
              let uu____1363 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ()) in
              if uu____1363
              then [FStar_SMTEncoding_Term.GetStatistics]
              else [] in
            FStar_List.append uu____1360 settings.query_suffix in
          FStar_List.append uu____1347 uu____1357 in
        FStar_List.append label_assumptions uu____1344 in
      FStar_List.append uu____1292 uu____1341
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu____1386 = FStar_ST.op_Bang replaying_hints in
      match uu____1386 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1406 ->
               match uu___3_1406 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1412 -> FStar_Pervasives_Native.None)
      | uu____1415 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1432 -> FStar_Pervasives_Native.None
      | uu____1433 ->
          let uu____1434 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1434 with
           | (msg, error_labels) ->
               let err =
                 let uu____1444 =
                   FStar_List.map
                     (fun uu____1469 ->
                        match uu____1469 with
                        | (uu____1482, x, y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1444
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____1495 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1495
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____1496 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let uu____1508 =
                with_fuel_and_diagnostics settings label_assumptions in
              FStar_SMTEncoding_Z3.ask settings.query_range
                (filter_assertions settings.query_env settings.query_hint)
                settings.query_hash settings.query_all_labels uu____1508
                FStar_Pervasives_Native.None false in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err ->
            match err.error_messages with | [] -> false | uu____1535 -> true))
let (errors_to_report : query_settings -> FStar_Errors.error Prims.list) =
  fun settings ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg in
    let basic_errors =
      let smt_error =
        let uu____1567 = FStar_Options.query_stats () in
        if uu____1567
        then
          let uu____1572 =
            let uu____1573 =
              let uu____1574 =
                FStar_All.pipe_right settings.query_errors
                  (FStar_List.map error_to_short_string) in
              FStar_All.pipe_right uu____1574 (FStar_String.concat ";\n\t") in
            FStar_All.pipe_right uu____1573 format_smt_error in
          FStar_All.pipe_right uu____1572
            (fun uu____1587 -> FStar_Util.Inr uu____1587)
        else
          (let uu____1589 =
             FStar_List.fold_left
               (fun uu____1608 ->
                  fun err ->
                    match uu____1608 with
                    | (ic, cc, uc) ->
                        let err1 =
                          FStar_Util.substring_from err.error_reason
                            (FStar_String.length "unknown because ") in
                        if
                          ((FStar_Util.starts_with err1 "canceled") ||
                             (FStar_Util.starts_with err1 "(resource"))
                            || (FStar_Util.starts_with err1 "timeout")
                        then (ic, (cc + Prims.int_one), uc)
                        else
                          if FStar_Util.starts_with err1 "(incomplete"
                          then ((ic + Prims.int_one), cc, uc)
                          else (ic, cc, (uc + Prims.int_one)))
               (Prims.int_zero, Prims.int_zero, Prims.int_zero)
               settings.query_errors in
           match uu____1589 with
           | (incomplete_count, canceled_count, unknown_count) ->
               FStar_All.pipe_right
                 (match (incomplete_count, canceled_count, unknown_count)
                  with
                  | (uu____1652, uu____1653, uu____1654) when
                      ((uu____1653 = Prims.int_zero) &&
                         (uu____1654 = Prims.int_zero))
                        && (incomplete_count > Prims.int_zero)
                      ->
                      "The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
                  | (uu____1656, uu____1655, uu____1657) when
                      ((uu____1656 = Prims.int_zero) &&
                         (uu____1657 = Prims.int_zero))
                        && (canceled_count > Prims.int_zero)
                      ->
                      "The SMT query timed out, you might want to increase the rlimit"
                  | (uu____1658, uu____1659, uu____1660) ->
                      "Try with --query_stats to get more details")
                 (fun uu____1661 -> FStar_Util.Inl uu____1661)) in
      let uu____1662 = find_localized_errors settings.query_errors in
      match uu____1662 with
      | FStar_Pervasives_Native.Some err ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            err.error_messages smt_error
      | FStar_Pervasives_Native.None ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            [(FStar_Errors.Error_UnknownFatal_AssertionFailure,
               "Unknown assertion failed", (settings.query_range))] smt_error in
    (let uu____1681 = FStar_Options.detail_errors () in
     if uu____1681
     then
       let initial_fuel =
         let uu___252_1683 = settings in
         let uu____1684 = FStar_Options.initial_fuel () in
         let uu____1685 = FStar_Options.initial_ifuel () in
         {
           query_env = (uu___252_1683.query_env);
           query_decl = (uu___252_1683.query_decl);
           query_name = (uu___252_1683.query_name);
           query_index = (uu___252_1683.query_index);
           query_range = (uu___252_1683.query_range);
           query_fuel = uu____1684;
           query_ifuel = uu____1685;
           query_rlimit = (uu___252_1683.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___252_1683.query_errors);
           query_all_labels = (uu___252_1683.query_all_labels);
           query_suffix = (uu___252_1683.query_suffix);
           query_hash = (uu___252_1683.query_hash)
         } in
       let ask_z3 label_assumptions =
         let uu____1698 =
           with_fuel_and_diagnostics initial_fuel label_assumptions in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu____1698 FStar_Pervasives_Native.None
           false in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ());
    basic_errors
let (report_errors : query_settings -> unit) =
  fun qry_settings ->
    let uu____1707 = errors_to_report qry_settings in
    FStar_Errors.add_errors uu____1707
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let process_unsat_core core =
        let accumulator uu____1749 =
          let r = FStar_Util.mk_ref [] in
          let uu____1757 =
            let module_names = FStar_Util.mk_ref [] in
            ((fun m ->
                let ms = FStar_ST.op_Bang module_names in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____1814 ->
                 let uu____1815 = FStar_ST.op_Bang module_names in
                 FStar_All.pipe_right uu____1815
                   (FStar_Util.sort_with FStar_String.compare))) in
          match uu____1757 with | (add, get) -> (add, get) in
        let uu____1870 = accumulator () in
        match uu____1870 with
        | (add_module_name, get_module_names) ->
            let uu____1901 = accumulator () in
            (match uu____1901 with
             | (add_discarded_name, get_discarded_names) ->
                 let parse_axiom_name s =
                   let chars = FStar_String.list_of_string s in
                   let first_upper_index =
                     FStar_Util.try_find_index FStar_Util.is_upper chars in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStar_Util.substring_from s first_upper_index1 in
                       let components =
                         FStar_String.split [46] name_and_suffix in
                       let excluded_suffixes =
                         ["fuel_instrumented";
                         "_pretyping";
                         "_Tm_refine";
                         "_Tm_abs";
                         "@";
                         "_interpretation_Tm_arrow";
                         "MaxFuel_assumption";
                         "MaxIFuel_assumption"] in
                       let exclude_suffix s1 =
                         let s2 = FStar_Util.trim_string s1 in
                         let sopt =
                           FStar_Util.find_map excluded_suffixes
                             (fun sfx ->
                                if FStar_Util.contains s2 sfx
                                then
                                  let uu____1974 =
                                    FStar_List.hd (FStar_Util.split s2 sfx) in
                                  FStar_Pervasives_Native.Some uu____1974
                                else FStar_Pervasives_Native.None) in
                         match sopt with
                         | FStar_Pervasives_Native.None ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3] in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu____1990 ->
                             let uu____1993 = FStar_Util.prefix components in
                             (match uu____1993 with
                              | (module_name, last) ->
                                  let components1 =
                                    let uu____2011 = exclude_suffix last in
                                    FStar_List.append module_name uu____2011 in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2015::[] -> ()
                                    | uu____2016 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1)) in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2025 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".") in
                          [uu____2025]) in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1 in
                      ((let uu____2039 =
                          let uu____2040 = get_module_names () in
                          FStar_All.pipe_right uu____2040
                            (FStar_String.concat "\nZ3 Proof Stats:\t") in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2039);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2046 =
                          let uu____2047 = get_discarded_names () in
                          FStar_All.pipe_right uu____2047
                            (FStar_String.concat ", ") in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2046)))) in
      let uu____2052 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ()) in
      if uu____2052
      then
        let uu____2053 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____2053 with
        | (status_string, errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s in
            let uu____2062 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2072 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None) in
            (match uu____2062 with
             | (tag, core) ->
                 let range =
                   let uu____2078 =
                     let uu____2079 =
                       FStar_Range.string_of_range settings.query_range in
                     Prims.op_Hat uu____2079 (Prims.op_Hat at_log_file ")") in
                   Prims.op_Hat "(" uu____2078 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu____2083 = FStar_Options.query_stats () in
                   if uu____2083
                   then
                     let f k v a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v " "))) in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu____2101 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one) in
                     Prims.op_Hat uu____2101 "}"
                   else "" in
                 ((let uu____2104 =
                     let uu____2107 =
                       let uu____2110 =
                         let uu____2113 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu____2114 =
                           let uu____2117 =
                             let uu____2120 =
                               let uu____2123 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time in
                               let uu____2124 =
                                 let uu____2127 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu____2128 =
                                   let uu____2131 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu____2132 =
                                     let uu____2135 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu____2135; stats] in
                                   uu____2131 :: uu____2132 in
                                 uu____2127 :: uu____2128 in
                               uu____2123 :: uu____2124 in
                             used_hint_tag :: uu____2120 in
                           tag :: uu____2117 in
                         uu____2113 :: uu____2114 in
                       (settings.query_name) :: uu____2110 in
                     range :: uu____2107 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2104);
                  (let uu____2137 = FStar_Options.print_z3_statistics () in
                   if uu____2137 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____2158 ->
                          match uu____2158 with
                          | (uu____2165, msg, range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
let (store_hint : FStar_Util.hint -> unit) =
  fun hint ->
    let uu____2176 = FStar_ST.op_Bang recorded_hints in
    match uu____2176 with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
    | uu____2206 -> ()
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____2220 =
        let uu____2221 = FStar_Options.record_hints () in
        Prims.op_Negation uu____2221 in
      if uu____2220
      then ()
      else
        (let mk_hint core =
           {
             FStar_Util.hint_name = (settings.query_name);
             FStar_Util.hint_index = (settings.query_index);
             FStar_Util.fuel = (settings.query_fuel);
             FStar_Util.ifuel = (settings.query_ifuel);
             FStar_Util.unsat_core = core;
             FStar_Util.query_elapsed_time = Prims.int_zero;
             FStar_Util.hash =
               (match z3result.FStar_SMTEncoding_Z3.z3result_status with
                | FStar_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStar_SMTEncoding_Z3.z3result_query_hash
                | uu____2241 -> FStar_Pervasives_Native.None)
           } in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu____2244 =
               let uu____2245 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____2245 in
             store_hint uu____2244
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____2250 -> ())
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun result ->
      let errs = query_errors settings result in
      query_info settings result;
      record_hint settings result;
      detail_hint_replay settings result;
      errs
let (fold_queries :
  query_settings Prims.list ->
    (query_settings -> FStar_SMTEncoding_Z3.z3result) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list, query_settings) FStar_Util.either)
  =
  fun qs ->
    fun ask ->
      fun f ->
        let rec aux acc qs1 =
          match qs1 with
          | [] -> FStar_Util.Inl acc
          | q::qs2 ->
              let res = ask q in
              let uu____2359 = f q res in
              (match uu____2359 with
               | FStar_Pervasives_Native.None -> FStar_Util.Inr q
               | FStar_Pervasives_Native.Some errs -> aux (errs :: acc) qs2) in
        aux [] qs
let (full_query_id : query_settings -> Prims.string) =
  fun settings ->
    let uu____2376 =
      let uu____2377 =
        let uu____2378 =
          let uu____2379 = FStar_Util.string_of_int settings.query_index in
          Prims.op_Hat uu____2379 ")" in
        Prims.op_Hat ", " uu____2378 in
      Prims.op_Hat settings.query_name uu____2377 in
    Prims.op_Hat "(" uu____2376
let collect : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l ->
    let acc = [] in
    let rec add_one acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h, n)::t ->
          if h = x
          then (h, (n + Prims.int_one)) :: t
          else (let uu____2482 = add_one t x in (h, n) :: uu____2482) in
    FStar_List.fold_left add_one acc l
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit)
  =
  fun env ->
    fun all_labels ->
      fun prefix ->
        fun query ->
          fun suffix ->
            FStar_SMTEncoding_Z3.giveZ3 prefix;
            (let uu____2533 =
               let uu____2540 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____2549, FStar_Pervasives_Native.None) ->
                     failwith "No query name set!"
                 | (uu____2568, FStar_Pervasives_Native.Some (q, n)) ->
                     let uu____2585 = FStar_Ident.string_of_lid q in
                     (uu____2585, n) in
               match uu____2540 with
               | (qname, index) ->
                   let rlimit =
                     let uu____2595 = FStar_Options.z3_rlimit_factor () in
                     let uu____2596 =
                       let uu____2597 = FStar_Options.z3_rlimit () in
                       uu____2597 * (Prims.parse_int "544656") in
                     uu____2595 * uu____2596 in
                   let next_hint = get_hint_for qname index in
                   let default_settings =
                     let uu____2602 = FStar_TypeChecker_Env.get_range env in
                     let uu____2603 = FStar_Options.initial_fuel () in
                     let uu____2604 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index;
                       query_range = uu____2602;
                       query_fuel = uu____2603;
                       query_ifuel = uu____2604;
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
                              { FStar_Util.hint_name = uu____2609;
                                FStar_Util.hint_index = uu____2610;
                                FStar_Util.fuel = uu____2611;
                                FStar_Util.ifuel = uu____2612;
                                FStar_Util.unsat_core = uu____2613;
                                FStar_Util.query_elapsed_time = uu____2614;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____2533 with
             | (default_settings, next_hint) ->
                 let use_hints_setting =
                   let uu____2633 =
                     (FStar_Options.use_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   if uu____2633
                   then
                     let uu____2638 =
                       FStar_All.pipe_right next_hint FStar_Util.must in
                     match uu____2638 with
                     | { FStar_Util.hint_name = uu____2643;
                         FStar_Util.hint_index = uu____2644;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____2648;
                         FStar_Util.hash = h;_} ->
                         [(let uu___452_2657 = default_settings in
                           {
                             query_env = (uu___452_2657.query_env);
                             query_decl = (uu___452_2657.query_decl);
                             query_name = (uu___452_2657.query_name);
                             query_index = (uu___452_2657.query_index);
                             query_range = (uu___452_2657.query_range);
                             query_fuel = i;
                             query_ifuel = j;
                             query_rlimit = (uu___452_2657.query_rlimit);
                             query_hint = (FStar_Pervasives_Native.Some core);
                             query_errors = (uu___452_2657.query_errors);
                             query_all_labels =
                               (uu___452_2657.query_all_labels);
                             query_suffix = (uu___452_2657.query_suffix);
                             query_hash = (uu___452_2657.query_hash)
                           })]
                   else [] in
                 let initial_fuel_max_ifuel =
                   let uu____2664 =
                     let uu____2665 = FStar_Options.max_ifuel () in
                     let uu____2666 = FStar_Options.initial_ifuel () in
                     uu____2665 > uu____2666 in
                   if uu____2664
                   then
                     let uu____2669 =
                       let uu___456_2670 = default_settings in
                       let uu____2671 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___456_2670.query_env);
                         query_decl = (uu___456_2670.query_decl);
                         query_name = (uu___456_2670.query_name);
                         query_index = (uu___456_2670.query_index);
                         query_range = (uu___456_2670.query_range);
                         query_fuel = (uu___456_2670.query_fuel);
                         query_ifuel = uu____2671;
                         query_rlimit = (uu___456_2670.query_rlimit);
                         query_hint = (uu___456_2670.query_hint);
                         query_errors = (uu___456_2670.query_errors);
                         query_all_labels = (uu___456_2670.query_all_labels);
                         query_suffix = (uu___456_2670.query_suffix);
                         query_hash = (uu___456_2670.query_hash)
                       } in
                     [uu____2669]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____2676 =
                     let uu____2677 =
                       let uu____2678 = FStar_Options.max_fuel () in
                       uu____2678 / (Prims.of_int (2)) in
                     let uu____2679 = FStar_Options.initial_fuel () in
                     uu____2677 > uu____2679 in
                   if uu____2676
                   then
                     let uu____2682 =
                       let uu___460_2683 = default_settings in
                       let uu____2684 =
                         let uu____2685 = FStar_Options.max_fuel () in
                         uu____2685 / (Prims.of_int (2)) in
                       let uu____2686 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___460_2683.query_env);
                         query_decl = (uu___460_2683.query_decl);
                         query_name = (uu___460_2683.query_name);
                         query_index = (uu___460_2683.query_index);
                         query_range = (uu___460_2683.query_range);
                         query_fuel = uu____2684;
                         query_ifuel = uu____2686;
                         query_rlimit = (uu___460_2683.query_rlimit);
                         query_hint = (uu___460_2683.query_hint);
                         query_errors = (uu___460_2683.query_errors);
                         query_all_labels = (uu___460_2683.query_all_labels);
                         query_suffix = (uu___460_2683.query_suffix);
                         query_hash = (uu___460_2683.query_hash)
                       } in
                     [uu____2682]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____2691 =
                     (let uu____2696 = FStar_Options.max_fuel () in
                      let uu____2697 = FStar_Options.initial_fuel () in
                      uu____2696 > uu____2697) &&
                       (let uu____2700 = FStar_Options.max_ifuel () in
                        let uu____2701 = FStar_Options.initial_ifuel () in
                        uu____2700 >= uu____2701) in
                   if uu____2691
                   then
                     let uu____2704 =
                       let uu___464_2705 = default_settings in
                       let uu____2706 = FStar_Options.max_fuel () in
                       let uu____2707 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___464_2705.query_env);
                         query_decl = (uu___464_2705.query_decl);
                         query_name = (uu___464_2705.query_name);
                         query_index = (uu___464_2705.query_index);
                         query_range = (uu___464_2705.query_range);
                         query_fuel = uu____2706;
                         query_ifuel = uu____2707;
                         query_rlimit = (uu___464_2705.query_rlimit);
                         query_hint = (uu___464_2705.query_hint);
                         query_errors = (uu___464_2705.query_errors);
                         query_all_labels = (uu___464_2705.query_all_labels);
                         query_suffix = (uu___464_2705.query_suffix);
                         query_hash = (uu___464_2705.query_hash)
                       } in
                     [uu____2704]
                   else [] in
                 let min_fuel =
                   let uu____2712 =
                     let uu____2713 = FStar_Options.min_fuel () in
                     let uu____2714 = FStar_Options.initial_fuel () in
                     uu____2713 < uu____2714 in
                   if uu____2712
                   then
                     let uu____2717 =
                       let uu___468_2718 = default_settings in
                       let uu____2719 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___468_2718.query_env);
                         query_decl = (uu___468_2718.query_decl);
                         query_name = (uu___468_2718.query_name);
                         query_index = (uu___468_2718.query_index);
                         query_range = (uu___468_2718.query_range);
                         query_fuel = uu____2719;
                         query_ifuel = Prims.int_one;
                         query_rlimit = (uu___468_2718.query_rlimit);
                         query_hint = (uu___468_2718.query_hint);
                         query_errors = (uu___468_2718.query_errors);
                         query_all_labels = (uu___468_2718.query_all_labels);
                         query_suffix = (uu___468_2718.query_suffix);
                         query_hash = (uu___468_2718.query_hash)
                       } in
                     [uu____2717]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config =
                   (let uu____2731 = FStar_Options.z3_refresh () in
                    if uu____2731
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____2733 = with_fuel_and_diagnostics config [] in
                    let uu____2736 =
                      let uu____2739 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____2739 in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu____2733
                      uu____2736 (used_hint config)) in
                 let check_all_configs configs =
                   fold_queries configs check_one_config process_result in
                 let quake_and_check_all_configs configs =
                   let lo = FStar_Options.quake_lo () in
                   let hi = FStar_Options.quake_hi () in
                   let seed = FStar_Options.z3_seed () in
                   let name = full_query_id default_settings in
                   let quaking =
                     (hi > Prims.int_one) &&
                       (let uu____2778 = FStar_Options.retry () in
                        Prims.op_Negation uu____2778) in
                   let quaking_or_retrying = hi > Prims.int_one in
                   let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
                   let lo1 =
                     if lo < Prims.int_one
                     then Prims.int_one
                     else if lo > hi1 then hi1 else lo in
                   let run_one seed1 =
                     let uu____2797 = FStar_Options.z3_refresh () in
                     if uu____2797
                     then
                       FStar_Options.with_saved_options
                         (fun uu____2812 ->
                            FStar_Options.set_option "z3seed"
                              (FStar_Options.Int seed1);
                            check_all_configs configs)
                     else check_all_configs configs in
                   let rec fold_nat' f acc lo2 hi2 =
                     if lo2 > hi2
                     then acc
                     else
                       (let uu____2858 = f acc lo2 in
                        fold_nat' f uu____2858 (lo2 + Prims.int_one) hi2) in
                   let best_fuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let best_ifuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let maybe_improve r n =
                     let uu____2916 = FStar_ST.op_Bang r in
                     match uu____2916 with
                     | FStar_Pervasives_Native.None ->
                         FStar_ST.op_Colon_Equals r
                           (FStar_Pervasives_Native.Some n)
                     | FStar_Pervasives_Native.Some m ->
                         if n < m
                         then
                           FStar_ST.op_Colon_Equals r
                             (FStar_Pervasives_Native.Some n)
                         else () in
                   let uu____2951 =
                     fold_nat'
                       (fun uu____2986 ->
                          fun n ->
                            match uu____2986 with
                            | (nsucc, nfail, rs) ->
                                let uu____3035 =
                                  (let uu____3038 =
                                     FStar_Options.quake_keep () in
                                   Prims.op_Negation uu____3038) &&
                                    ((nsucc >= lo1) || (nfail > (hi1 - lo1))) in
                                if uu____3035
                                then (nsucc, nfail, rs)
                                else
                                  ((let uu____3063 =
                                      (quaking_or_retrying &&
                                         ((FStar_Options.interactive ()) ||
                                            (FStar_Options.debug_any ())))
                                        && (n > Prims.int_zero) in
                                    if uu____3063
                                    then
                                      let uu____3064 =
                                        if quaking
                                        then
                                          let uu____3065 =
                                            FStar_Util.string_of_int nsucc in
                                          FStar_Util.format1
                                            "succeeded %s times and "
                                            uu____3065
                                        else "" in
                                      let uu____3067 =
                                        if quaking
                                        then FStar_Util.string_of_int nfail
                                        else
                                          (let uu____3069 =
                                             FStar_Util.string_of_int nfail in
                                           Prims.op_Hat uu____3069 " times") in
                                      let uu____3070 =
                                        FStar_Util.string_of_int (hi1 - n) in
                                      FStar_Util.print5
                                        "%s: so far query %s %sfailed %s (%s runs remain)\n"
                                        (if quaking then "Quake" else "Retry")
                                        name uu____3064 uu____3067 uu____3070
                                    else ());
                                   (let r = run_one (seed + n) in
                                    let uu____3080 =
                                      match r with
                                      | FStar_Util.Inr cfg ->
                                          (maybe_improve best_fuel
                                             cfg.query_fuel;
                                           maybe_improve best_ifuel
                                             cfg.query_ifuel;
                                           ((nsucc + Prims.int_one), nfail))
                                      | uu____3094 ->
                                          (nsucc, (nfail + Prims.int_one)) in
                                    match uu____3080 with
                                    | (nsucc1, nfail1) ->
                                        (nsucc1, nfail1, (r :: rs)))))
                       (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
                       (hi1 - Prims.int_one) in
                   match uu____2951 with
                   | (nsuccess, nfailures, rs) ->
                       let total_ran = nsuccess + nfailures in
                       (if quaking
                        then
                          (let fuel_msg =
                             let uu____3167 =
                               let uu____3176 = FStar_ST.op_Bang best_fuel in
                               let uu____3189 = FStar_ST.op_Bang best_ifuel in
                               (uu____3176, uu____3189) in
                             match uu____3167 with
                             | (FStar_Pervasives_Native.Some f,
                                FStar_Pervasives_Native.Some i) ->
                                 let uu____3212 = FStar_Util.string_of_int f in
                                 let uu____3213 = FStar_Util.string_of_int i in
                                 FStar_Util.format2
                                   " (best fuel=%s, best ifuel=%s)"
                                   uu____3212 uu____3213
                             | (uu____3214, uu____3215) -> "" in
                           let uu____3224 = FStar_Util.string_of_int nsuccess in
                           let uu____3225 =
                             FStar_Util.string_of_int total_ran in
                           FStar_Util.print5
                             "Quake: query %s succeeded %s/%s times%s%s\n"
                             name uu____3224 uu____3225
                             (if total_ran < hi1
                              then " (early finish)"
                              else "") fuel_msg)
                        else ();
                        if nsuccess < lo1
                        then
                          (let all_errs =
                             FStar_List.concatMap
                               (fun uu___4_3243 ->
                                  match uu___4_3243 with
                                  | FStar_Util.Inr uu____3254 -> []
                                  | FStar_Util.Inl es -> [es]) rs in
                           let uu____3268 =
                             quaking_or_retrying &&
                               (let uu____3270 = FStar_Options.query_stats () in
                                Prims.op_Negation uu____3270) in
                           if uu____3268
                           then
                             let errors_to_report1 errs =
                               errors_to_report
                                 (let uu___559_3285 = default_settings in
                                  {
                                    query_env = (uu___559_3285.query_env);
                                    query_decl = (uu___559_3285.query_decl);
                                    query_name = (uu___559_3285.query_name);
                                    query_index = (uu___559_3285.query_index);
                                    query_range = (uu___559_3285.query_range);
                                    query_fuel = (uu___559_3285.query_fuel);
                                    query_ifuel = (uu___559_3285.query_ifuel);
                                    query_rlimit =
                                      (uu___559_3285.query_rlimit);
                                    query_hint = (uu___559_3285.query_hint);
                                    query_errors = errs;
                                    query_all_labels =
                                      (uu___559_3285.query_all_labels);
                                    query_suffix =
                                      (uu___559_3285.query_suffix);
                                    query_hash = (uu___559_3285.query_hash)
                                  }) in
                             let errs =
                               FStar_List.map errors_to_report1 all_errs in
                             let errs1 =
                               let uu____3308 =
                                 FStar_All.pipe_right errs FStar_List.flatten in
                               FStar_All.pipe_right uu____3308 collect in
                             let errs2 =
                               FStar_All.pipe_right errs1
                                 (FStar_List.map
                                    (fun uu____3382 ->
                                       match uu____3382 with
                                       | ((e, m, r), n) ->
                                           if n > Prims.int_one
                                           then
                                             let uu____3415 =
                                               let uu____3416 =
                                                 let uu____3417 =
                                                   FStar_Util.string_of_int n in
                                                 FStar_Util.format1
                                                   " (%s times)" uu____3417 in
                                               Prims.op_Hat m uu____3416 in
                                             (e, uu____3415, r)
                                           else (e, m, r))) in
                             (FStar_Errors.add_errors errs2;
                              (let rng =
                                 match FStar_Pervasives_Native.snd
                                         env.FStar_TypeChecker_Env.qtbl_name_and_index
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (l, uu____3430) ->
                                     FStar_Ident.range_of_lid l
                                 | uu____3435 -> FStar_Range.dummyRange in
                               if quaking
                               then
                                 let uu____3442 =
                                   let uu____3451 =
                                     let uu____3458 =
                                       let uu____3459 =
                                         FStar_Util.string_of_int nsuccess in
                                       let uu____3460 =
                                         FStar_Util.string_of_int total_ran in
                                       let uu____3461 =
                                         FStar_Util.string_of_int lo1 in
                                       let uu____3462 =
                                         FStar_Util.string_of_int hi1 in
                                       FStar_Util.format6
                                         "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                                         name uu____3459 uu____3460
                                         uu____3461 uu____3462
                                         (if total_ran < hi1
                                          then " (early abort)"
                                          else "") in
                                     (FStar_Errors.Error_QuakeFailed,
                                       uu____3458, rng) in
                                   [uu____3451] in
                                 FStar_TypeChecker_Err.add_errors env
                                   uu____3442
                               else ()))
                           else
                             (let report errs =
                                report_errors
                                  (let uu___582_3490 = default_settings in
                                   {
                                     query_env = (uu___582_3490.query_env);
                                     query_decl = (uu___582_3490.query_decl);
                                     query_name = (uu___582_3490.query_name);
                                     query_index =
                                       (uu___582_3490.query_index);
                                     query_range =
                                       (uu___582_3490.query_range);
                                     query_fuel = (uu___582_3490.query_fuel);
                                     query_ifuel =
                                       (uu___582_3490.query_ifuel);
                                     query_rlimit =
                                       (uu___582_3490.query_rlimit);
                                     query_hint = (uu___582_3490.query_hint);
                                     query_errors = errs;
                                     query_all_labels =
                                       (uu___582_3490.query_all_labels);
                                     query_suffix =
                                       (uu___582_3490.query_suffix);
                                     query_hash = (uu___582_3490.query_hash)
                                   }) in
                              FStar_List.iter report all_errs))
                        else ()) in
                 let skip =
                   (FStar_Options.admit_smt_queries ()) ||
                     (let uu____3498 = FStar_Options.admit_except () in
                      match uu____3498 with
                      | FStar_Pervasives_Native.Some id ->
                          if FStar_Util.starts_with id "("
                          then
                            let uu____3502 = full_query_id default_settings in
                            uu____3502 <> id
                          else default_settings.query_name <> id
                      | FStar_Pervasives_Native.None -> false) in
                 if skip
                 then
                   let uu____3504 =
                     (FStar_Options.record_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   (if uu____3504
                    then
                      let uu____3507 =
                        FStar_All.pipe_right next_hint FStar_Util.must in
                      FStar_All.pipe_right uu____3507 store_hint
                    else ())
                 else quake_and_check_all_configs all_configs)
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  valid_intro: Prims.bool ;
  valid_elim: Prims.bool }
let (__proj__Mksolver_cfg__item__seed : solver_cfg -> Prims.int) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> seed
let (__proj__Mksolver_cfg__item__cliopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> cliopt
let (__proj__Mksolver_cfg__item__facts :
  solver_cfg -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> facts
let (__proj__Mksolver_cfg__item__valid_intro : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_intro
let (__proj__Mksolver_cfg__item__valid_elim : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; facts; valid_intro; valid_elim;_} -> valid_elim
let (_last_cfg : solver_cfg FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (get_cfg : FStar_TypeChecker_Env.env -> solver_cfg) =
  fun env ->
    let uu____3678 = FStar_Options.z3_seed () in
    let uu____3679 = FStar_Options.z3_cliopt () in
    let uu____3682 = FStar_Options.smtencoding_valid_intro () in
    let uu____3683 = FStar_Options.smtencoding_valid_elim () in
    {
      seed = uu____3678;
      cliopt = uu____3679;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu____3682;
      valid_elim = uu____3683
    }
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu____3689 =
      let uu____3692 = get_cfg env in FStar_Pervasives_Native.Some uu____3692 in
    FStar_ST.op_Colon_Equals _last_cfg uu____3689
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    let uu____3708 = FStar_ST.op_Bang _last_cfg in
    match uu____3708 with
    | FStar_Pervasives_Native.None -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu____3723 = let uu____3724 = get_cfg env in cfg = uu____3724 in
        Prims.op_Negation uu____3723
let (do_solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____3750 = should_refresh tcenv in
         if uu____3750
         then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
         else ());
        (let uu____3754 =
           let uu____3755 =
             let uu____3756 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3756 in
           FStar_Util.format1 "Starting query at %s" uu____3755 in
         FStar_SMTEncoding_Encode.push uu____3754);
        (let pop uu____3762 =
           let uu____3763 =
             let uu____3764 =
               let uu____3765 = FStar_TypeChecker_Env.get_range tcenv in
               FStar_All.pipe_left FStar_Range.string_of_range uu____3765 in
             FStar_Util.format1 "Ending query at %s" uu____3764 in
           FStar_SMTEncoding_Encode.pop uu____3763 in
         try
           (fun uu___623_3779 ->
              match () with
              | () ->
                  let uu____3780 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
                  (match uu____3780 with
                   | (prefix, labels, qry, suffix) ->
                       let tcenv1 =
                         FStar_TypeChecker_Env.incr_query_index tcenv in
                       (match qry with
                        | FStar_SMTEncoding_Term.Assume
                            {
                              FStar_SMTEncoding_Term.assumption_term =
                                {
                                  FStar_SMTEncoding_Term.tm =
                                    FStar_SMTEncoding_Term.App
                                    (FStar_SMTEncoding_Term.FalseOp,
                                     uu____3812);
                                  FStar_SMTEncoding_Term.freevars =
                                    uu____3813;
                                  FStar_SMTEncoding_Term.rng = uu____3814;_};
                              FStar_SMTEncoding_Term.assumption_caption =
                                uu____3815;
                              FStar_SMTEncoding_Term.assumption_name =
                                uu____3816;
                              FStar_SMTEncoding_Term.assumption_fact_ids =
                                uu____3817;_}
                            -> pop ()
                        | uu____3834 when tcenv1.FStar_TypeChecker_Env.admit
                            -> pop ()
                        | FStar_SMTEncoding_Term.Assume uu____3835 ->
                            (ask_and_report_errors tcenv1 labels prefix qry
                               suffix;
                             pop ())
                        | uu____3837 -> failwith "Impossible"))) ()
         with
         | FStar_SMTEncoding_Env.Inner_let_rec names ->
             (pop ();
              (let uu____3851 =
                 let uu____3860 =
                   let uu____3867 =
                     let uu____3868 =
                       let uu____3869 =
                         FStar_List.map FStar_Pervasives_Native.fst names in
                       FStar_String.concat "," uu____3869 in
                     FStar_Util.format1
                       "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                       uu____3868 in
                   (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                     uu____3867, (tcenv.FStar_TypeChecker_Env.range)) in
                 [uu____3860] in
               FStar_TypeChecker_Err.add_errors tcenv uu____3851)))
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu____3912 = FStar_Options.no_smt () in
        if uu____3912
        then
          let uu____3913 =
            let uu____3922 =
              let uu____3929 =
                let uu____3930 = FStar_Syntax_Print.term_to_string q in
                FStar_Util.format1
                  "Q = %s\nA query could not be solved internally, and --no_smt was given"
                  uu____3930 in
              (FStar_Errors.Error_NoSMTButNeeded, uu____3929,
                (tcenv.FStar_TypeChecker_Env.range)) in
            [uu____3922] in
          FStar_TypeChecker_Err.add_errors tcenv uu____3913
        else
          (let uu____3944 =
             let uu____3947 =
               let uu____3948 = FStar_TypeChecker_Env.current_module tcenv in
               FStar_Ident.string_of_lid uu____3948 in
             FStar_Pervasives_Native.Some uu____3947 in
           FStar_Profiling.profile
             (fun uu____3950 -> do_solve use_env_msg tcenv q) uu____3944
             "FStar.TypeChecker.SMTEncoding.solve_top_level")
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init =
      (fun e -> save_cfg e; FStar_SMTEncoding_Encode.init e);
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____3962 =
             let uu____3969 = FStar_Options.peek () in (e, g, uu____3969) in
           [uu____3962]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3984 -> ());
    FStar_TypeChecker_Env.push = (fun uu____3986 -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3988 -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3990 ->
         ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback = (fun uu____3999 -> fun uu____4000 -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____4011 -> fun uu____4012 -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____4018 =
             let uu____4025 = FStar_Options.peek () in (e, g, uu____4025) in
           [uu____4018]);
    FStar_TypeChecker_Env.solve =
      (fun uu____4041 -> fun uu____4042 -> fun uu____4043 -> ());
    FStar_TypeChecker_Env.finish = (fun uu____4049 -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____4051 -> ())
  }
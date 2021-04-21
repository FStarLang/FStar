open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels)
    FStar_Pervasives.either
let z3_result_as_replay_result :
  'uuuuu 'uuuuu1 'uuuuu2 .
    ('uuuuu, ('uuuuu1 * 'uuuuu2)) FStar_Pervasives.either ->
      ('uuuuu, 'uuuuu1) FStar_Pervasives.either
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives.Inl l -> FStar_Pervasives.Inl l
    | FStar_Pervasives.Inr (r, uu___1) -> FStar_Pervasives.Inr r
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let initialize_hints_db : 'uuuuu . Prims.string -> 'uuuuu -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu___1 = FStar_Options.record_hints () in
       if uu___1
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       let uu___1 = FStar_Util.read_hints val_filename in
       match uu___1 with
       | FStar_Util.HintsOK hints ->
           let expected_digest = FStar_Util.digest_of_file norm_src_filename in
           ((let uu___3 = FStar_Options.hint_info () in
             if uu___3
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
           let uu___3 = FStar_Options.use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 FStar_Util.format1
                   "Malformed JSON hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu___5) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu___4
           else ()
       | FStar_Util.UnableToOpen ->
           let uu___3 = FStar_Options.use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 FStar_Util.format1
                   "Unable to open hints file: %s; ran without hints\n"
                   val_filename in
               (FStar_Errors.Warning_CouldNotReadHints, uu___5) in
             FStar_Errors.log_issue FStar_Range.dummyRange uu___4
           else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu___1 = FStar_Options.record_hints () in
     if uu___1
     then
       let hints =
         let uu___2 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu___2 in
       let hints_db =
         let uu___2 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu___2; FStar_Util.hints = hints } in
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
        | uu___ ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1 ->
                     match uu___1 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu___2 -> false)))
              ||
              (let uu___1 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu___1) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.of_int (10000)) in
        let keep_decl uu___ =
          match uu___ with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names ->
              (FStar_List.iter
                 (fun x ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names;
               true)
          | FStar_SMTEncoding_Term.Module uu___1 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu___1 -> true in
        FStar_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Module (name, decls) ->
                   let uu___ =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl) in
                   FStar_All.pipe_right uu___
                     (fun decls1 ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu___ ->
                   let uu___1 = keep_decl d in
                   if uu___1 then d :: out else out) [] theory_rev in
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
            let uu___ = filter_using_facts_from e theory in
            (uu___, false, Prims.int_zero, Prims.int_zero)
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ") in
                      Prims.op_Hat "UNSAT CORE: " uu___5 in
                    FStar_SMTEncoding_Term.Caption uu___4 in
                  [uu___3] in
                (uu___2, Prims.int_zero, Prims.int_zero) in
              FStar_List.fold_left
                (fun uu___2 ->
                   fun d ->
                     match uu___2 with
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
                              let uu___3 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1)) in
                              FStar_All.pipe_right uu___3
                                (fun uu___4 ->
                                   match uu___4 with
                                   | (decls1, uu___5, r, p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu___3 -> ((d :: theory1), n_retained, n_pruned)))
                uu___1 theory_rev in
            (match uu___ with
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
        let uu___ = filter_assertions_with_stats e core theory in
        match uu___ with | (theory1, b, uu___1, uu___2) -> (theory1, b)
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e -> fun x -> let uu___ = filter_using_facts_from e x in (uu___, false)
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages: FStar_Errors.error Prims.list }
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
  errors -> FStar_Errors.error Prims.list) =
  fun projectee ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
let (error_to_short_string : errors -> Prims.string) =
  fun err ->
    let uu___ = FStar_Util.string_of_int err.error_fuel in
    let uu___1 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu___
      uu___1
      (if FStar_Option.isSome err.error_hint then "; with hint" else "")
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err ->
    if FStar_Util.ends_with err.error_reason "canceled"
    then
      let uu___ =
        let uu___1 = FStar_Util.string_of_int err.error_fuel in
        let uu___2 = FStar_Util.string_of_int err.error_ifuel in
        FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason
          uu___1 uu___2
          (if FStar_Option.isSome err.error_hint then "with hint" else "") in
      [uu___]
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
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Util.string_of_int n in
            let uu___4 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu___3 uu___4 in
          FStar_SMTEncoding_Term.Caption uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu___8 = FStar_SMTEncoding_Term.n_fuel n in
                  (uu___7, uu___8) in
                FStar_SMTEncoding_Util.mkEq uu___6 in
              (uu___5, FStar_Pervasives_Native.None, "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu___10 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu___9, uu___10) in
                  FStar_SMTEncoding_Util.mkEq uu___8 in
                (uu___7, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu___6 in
            [uu___5; settings.query_decl] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu___6) in
              FStar_SMTEncoding_Term.SetOption uu___5 in
            [uu___4;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore] in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ()) in
              if uu___6 then [FStar_SMTEncoding_Term.GetStatistics] else [] in
            FStar_List.append uu___5 settings.query_suffix in
          FStar_List.append uu___3 uu___4 in
        FStar_List.append label_assumptions uu___2 in
      FStar_List.append uu___ uu___1
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu___ = FStar_ST.op_Bang replaying_hints in
      match uu___ with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu___2 -> FStar_Pervasives_Native.None)
      | uu___1 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu___ -> FStar_Pervasives_Native.None
      | uu___ ->
          let uu___1 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu___1 with
           | (msg, error_labels) ->
               let err =
                 let uu___2 =
                   FStar_List.map
                     (fun uu___3 ->
                        match uu___3 with
                        | (uu___4, x, y) ->
                            let uu___5 = FStar_Errors.get_ctx () in
                            (FStar_Errors.Error_Z3SolverError, x, y, uu___5))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu___2
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu___ =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu___
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu___1 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let uu___1 =
                with_fuel_and_diagnostics settings label_assumptions in
              FStar_SMTEncoding_Z3.ask settings.query_range
                (filter_assertions settings.query_env settings.query_hint)
                settings.query_hash settings.query_all_labels uu___1
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
            match err.error_messages with | [] -> false | uu___ -> true))
let (errors_to_report : query_settings -> FStar_Errors.error Prims.list) =
  fun settings ->
    let format_smt_error msg =
      FStar_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means Z3 could not prove the query, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg in
    let basic_errors =
      let smt_error =
        let uu___ = FStar_Options.query_stats () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_All.pipe_right settings.query_errors
                  (FStar_List.map error_to_short_string) in
              FStar_All.pipe_right uu___3 (FStar_String.concat ";\n\t") in
            FStar_All.pipe_right uu___2 format_smt_error in
          FStar_All.pipe_right uu___1
            (fun uu___2 -> FStar_Pervasives.Inr uu___2)
        else
          (let uu___2 =
             FStar_List.fold_left
               (fun uu___3 ->
                  fun err ->
                    match uu___3 with
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
           match uu___2 with
           | (incomplete_count, canceled_count, unknown_count) ->
               FStar_All.pipe_right
                 (match (incomplete_count, canceled_count, unknown_count)
                  with
                  | (uu___3, uu___4, uu___5) when
                      ((uu___4 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                        && (incomplete_count > Prims.int_zero)
                      ->
                      "The SMT solver could not prove the query, try to spell your proof in more detail or increase fuel/ifuel"
                  | (uu___3, uu___4, uu___5) when
                      ((uu___3 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                        && (canceled_count > Prims.int_zero)
                      ->
                      "The SMT query timed out, you might want to increase the rlimit"
                  | (uu___3, uu___4, uu___5) ->
                      "Try with --query_stats to get more details")
                 (fun uu___3 -> FStar_Pervasives.Inl uu___3)) in
      let uu___ = find_localized_errors settings.query_errors in
      match uu___ with
      | FStar_Pervasives_Native.Some err ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            err.error_messages smt_error
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Errors.get_ctx () in
              (FStar_Errors.Error_UnknownFatal_AssertionFailure,
                "Unknown assertion failed", (settings.query_range), uu___3) in
            [uu___2] in
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env uu___1
            smt_error in
    (let uu___ = FStar_Options.detail_errors () in
     if uu___
     then
       let initial_fuel =
         let uu___1 = settings in
         let uu___2 = FStar_Options.initial_fuel () in
         let uu___3 = FStar_Options.initial_ifuel () in
         {
           query_env = (uu___1.query_env);
           query_decl = (uu___1.query_decl);
           query_name = (uu___1.query_name);
           query_index = (uu___1.query_index);
           query_range = (uu___1.query_range);
           query_fuel = uu___2;
           query_ifuel = uu___3;
           query_rlimit = (uu___1.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___1.query_errors);
           query_all_labels = (uu___1.query_all_labels);
           query_suffix = (uu___1.query_suffix);
           query_hash = (uu___1.query_hash)
         } in
       let ask_z3 label_assumptions =
         let uu___1 =
           with_fuel_and_diagnostics initial_fuel label_assumptions in
         FStar_SMTEncoding_Z3.ask settings.query_range
           (filter_facts_without_core settings.query_env) settings.query_hash
           settings.query_all_labels uu___1 FStar_Pervasives_Native.None
           false in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ());
    basic_errors
let (report_errors : query_settings -> unit) =
  fun qry_settings ->
    let uu___ = errors_to_report qry_settings in
    FStar_Errors.add_errors uu___
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let process_unsat_core core =
        let accumulator uu___ =
          let r = FStar_Util.mk_ref [] in
          let uu___1 =
            let module_names = FStar_Util.mk_ref [] in
            ((fun m ->
                let ms = FStar_ST.op_Bang module_names in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu___2 ->
                 let uu___3 = FStar_ST.op_Bang module_names in
                 FStar_All.pipe_right uu___3
                   (FStar_Util.sort_with FStar_String.compare))) in
          match uu___1 with | (add, get) -> (add, get) in
        let uu___ = accumulator () in
        match uu___ with
        | (add_module_name, get_module_names) ->
            let uu___1 = accumulator () in
            (match uu___1 with
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
                                  let uu___2 =
                                    FStar_List.hd (FStar_Util.split s2 sfx) in
                                  FStar_Pervasives_Native.Some uu___2
                                else FStar_Pervasives_Native.None) in
                         match sopt with
                         | FStar_Pervasives_Native.None ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3] in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu___2 ->
                             let uu___3 = FStar_Util.prefix components in
                             (match uu___3 with
                              | (module_name, last) ->
                                  let components2 =
                                    let uu___4 = exclude_suffix last in
                                    FStar_List.append module_name uu___4 in
                                  ((match components2 with
                                    | [] -> ()
                                    | uu___5::[] -> ()
                                    | uu___5 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components2)) in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu___3 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".") in
                          [uu___3]) in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1 in
                      ((let uu___3 =
                          let uu___4 = get_module_names () in
                          FStar_All.pipe_right uu___4
                            (FStar_String.concat "\nZ3 Proof Stats:\t") in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu___3);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu___4 =
                          let uu___5 = get_discarded_names () in
                          FStar_All.pipe_right uu___5
                            (FStar_String.concat ", ") in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu___4)))) in
      let uu___ =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ()) in
      if uu___
      then
        let uu___1 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu___1 with
        | (status_string, errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s in
            let uu___2 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu___3 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None) in
            (match uu___2 with
             | (tag, core) ->
                 let range =
                   let uu___3 =
                     let uu___4 =
                       FStar_Range.string_of_range settings.query_range in
                     Prims.op_Hat uu___4 (Prims.op_Hat at_log_file ")") in
                   Prims.op_Hat "(" uu___3 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu___3 = FStar_Options.query_stats () in
                   if uu___3
                   then
                     let f k v a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v " "))) in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu___4 =
                       FStar_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one) in
                     Prims.op_Hat uu___4 "}"
                   else "" in
                 ((let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time in
                               let uu___12 =
                                 let uu___13 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu___14 =
                                   let uu___15 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu___16 =
                                     let uu___17 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu___17; stats] in
                                   uu___15 :: uu___16 in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             used_hint_tag :: uu___10 in
                           tag :: uu___9 in
                         uu___7 :: uu___8 in
                       (settings.query_name) :: uu___6 in
                     range :: uu___5 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu___4);
                  (let uu___5 = FStar_Options.print_z3_statistics () in
                   if uu___5 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu___5 ->
                          match uu___5 with
                          | (uu___6, msg, range1) ->
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
    let uu___ = FStar_ST.op_Bang recorded_hints in
    match uu___ with
    | FStar_Pervasives_Native.Some l ->
        FStar_ST.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
    | uu___1 -> ()
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu___ =
        let uu___1 = FStar_Options.record_hints () in
        Prims.op_Negation uu___1 in
      if uu___
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
                | uu___2 -> FStar_Pervasives_Native.None)
           } in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu___2 =
               let uu___3 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu___3 in
             store_hint uu___2
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu___2 -> ())
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
        -> (errors Prims.list, query_settings) FStar_Pervasives.either)
  =
  fun qs ->
    fun ask ->
      fun f ->
        let rec aux acc qs1 =
          match qs1 with
          | [] -> FStar_Pervasives.Inl acc
          | q::qs2 ->
              let res = ask q in
              let uu___ = f q res in
              (match uu___ with
               | FStar_Pervasives_Native.None -> FStar_Pervasives.Inr q
               | FStar_Pervasives_Native.Some errs -> aux (errs :: acc) qs2) in
        aux [] qs
let (full_query_id : query_settings -> Prims.string) =
  fun settings ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStar_Util.string_of_int settings.query_index in
          Prims.op_Hat uu___3 ")" in
        Prims.op_Hat ", " uu___2 in
      Prims.op_Hat settings.query_name uu___1 in
    Prims.op_Hat "(" uu___
let collect : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l ->
    let acc = [] in
    let rec add_one acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h, n)::t ->
          if h = x
          then (h, (n + Prims.int_one)) :: t
          else (let uu___1 = add_one t x in (h, n) :: uu___1) in
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
            (let uu___1 =
               let uu___2 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu___3, FStar_Pervasives_Native.None) ->
                     failwith "No query name set!"
                 | (uu___3, FStar_Pervasives_Native.Some (q, n)) ->
                     let uu___4 = FStar_Ident.string_of_lid q in (uu___4, n) in
               match uu___2 with
               | (qname, index) ->
                   let rlimit =
                     let uu___3 = FStar_Options.z3_rlimit_factor () in
                     let uu___4 =
                       let uu___5 = FStar_Options.z3_rlimit () in
                       uu___5 * (Prims.parse_int "544656") in
                     uu___3 * uu___4 in
                   let next_hint = get_hint_for qname index in
                   let default_settings =
                     let uu___3 = FStar_TypeChecker_Env.get_range env in
                     let uu___4 = FStar_Options.initial_fuel () in
                     let uu___5 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index;
                       query_range = uu___3;
                       query_fuel = uu___4;
                       query_ifuel = uu___5;
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
                              { FStar_Util.hint_name = uu___6;
                                FStar_Util.hint_index = uu___7;
                                FStar_Util.fuel = uu___8;
                                FStar_Util.ifuel = uu___9;
                                FStar_Util.unsat_core = uu___10;
                                FStar_Util.query_elapsed_time = uu___11;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu___1 with
             | (default_settings, next_hint) ->
                 let use_hints_setting =
                   let uu___2 =
                     (FStar_Options.use_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   if uu___2
                   then
                     let uu___3 =
                       FStar_All.pipe_right next_hint FStar_Util.must in
                     match uu___3 with
                     | { FStar_Util.hint_name = uu___4;
                         FStar_Util.hint_index = uu___5; FStar_Util.fuel = i;
                         FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu___6;
                         FStar_Util.hash = h;_} ->
                         [(let uu___7 = default_settings in
                           {
                             query_env = (uu___7.query_env);
                             query_decl = (uu___7.query_decl);
                             query_name = (uu___7.query_name);
                             query_index = (uu___7.query_index);
                             query_range = (uu___7.query_range);
                             query_fuel = i;
                             query_ifuel = j;
                             query_rlimit = (uu___7.query_rlimit);
                             query_hint = (FStar_Pervasives_Native.Some core);
                             query_errors = (uu___7.query_errors);
                             query_all_labels = (uu___7.query_all_labels);
                             query_suffix = (uu___7.query_suffix);
                             query_hash = (uu___7.query_hash)
                           })]
                   else [] in
                 let initial_fuel_max_ifuel =
                   let uu___2 =
                     let uu___3 = FStar_Options.max_ifuel () in
                     let uu___4 = FStar_Options.initial_ifuel () in
                     uu___3 > uu___4 in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 = default_settings in
                       let uu___5 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___4.query_env);
                         query_decl = (uu___4.query_decl);
                         query_name = (uu___4.query_name);
                         query_index = (uu___4.query_index);
                         query_range = (uu___4.query_range);
                         query_fuel = (uu___4.query_fuel);
                         query_ifuel = uu___5;
                         query_rlimit = (uu___4.query_rlimit);
                         query_hint = (uu___4.query_hint);
                         query_errors = (uu___4.query_errors);
                         query_all_labels = (uu___4.query_all_labels);
                         query_suffix = (uu___4.query_suffix);
                         query_hash = (uu___4.query_hash)
                       } in
                     [uu___3]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStar_Options.max_fuel () in
                       uu___4 / (Prims.of_int (2)) in
                     let uu___4 = FStar_Options.initial_fuel () in
                     uu___3 > uu___4 in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 = default_settings in
                       let uu___5 =
                         let uu___6 = FStar_Options.max_fuel () in
                         uu___6 / (Prims.of_int (2)) in
                       let uu___6 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___4.query_env);
                         query_decl = (uu___4.query_decl);
                         query_name = (uu___4.query_name);
                         query_index = (uu___4.query_index);
                         query_range = (uu___4.query_range);
                         query_fuel = uu___5;
                         query_ifuel = uu___6;
                         query_rlimit = (uu___4.query_rlimit);
                         query_hint = (uu___4.query_hint);
                         query_errors = (uu___4.query_errors);
                         query_all_labels = (uu___4.query_all_labels);
                         query_suffix = (uu___4.query_suffix);
                         query_hash = (uu___4.query_hash)
                       } in
                     [uu___3]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu___2 =
                     (let uu___3 = FStar_Options.max_fuel () in
                      let uu___4 = FStar_Options.initial_fuel () in
                      uu___3 > uu___4) &&
                       (let uu___3 = FStar_Options.max_ifuel () in
                        let uu___4 = FStar_Options.initial_ifuel () in
                        uu___3 >= uu___4) in
                   if uu___2
                   then
                     let uu___3 =
                       let uu___4 = default_settings in
                       let uu___5 = FStar_Options.max_fuel () in
                       let uu___6 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___4.query_env);
                         query_decl = (uu___4.query_decl);
                         query_name = (uu___4.query_name);
                         query_index = (uu___4.query_index);
                         query_range = (uu___4.query_range);
                         query_fuel = uu___5;
                         query_ifuel = uu___6;
                         query_rlimit = (uu___4.query_rlimit);
                         query_hint = (uu___4.query_hint);
                         query_errors = (uu___4.query_errors);
                         query_all_labels = (uu___4.query_all_labels);
                         query_suffix = (uu___4.query_suffix);
                         query_hash = (uu___4.query_hash)
                       } in
                     [uu___3]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config =
                   (let uu___3 = FStar_Options.z3_refresh () in
                    if uu___3 then FStar_SMTEncoding_Z3.refresh () else ());
                   (let uu___3 = with_fuel_and_diagnostics config [] in
                    let uu___4 =
                      let uu___5 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu___5 in
                    FStar_SMTEncoding_Z3.ask config.query_range
                      (filter_assertions config.query_env config.query_hint)
                      config.query_hash config.query_all_labels uu___3 uu___4
                      (used_hint config)) in
                 let check_all_configs configs =
                   fold_queries configs check_one_config process_result in
                 let quake_and_check_all_configs configs =
                   let lo = FStar_Options.quake_lo () in
                   let hi = FStar_Options.quake_hi () in
                   let seed = FStar_Options.z3_seed () in
                   let name = full_query_id default_settings in
                   let quaking =
                     (hi > Prims.int_one) &&
                       (let uu___2 = FStar_Options.retry () in
                        Prims.op_Negation uu___2) in
                   let quaking_or_retrying = hi > Prims.int_one in
                   let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
                   let lo1 =
                     if lo < Prims.int_one
                     then Prims.int_one
                     else if lo > hi1 then hi1 else lo in
                   let run_one seed1 =
                     let uu___2 = FStar_Options.z3_refresh () in
                     if uu___2
                     then
                       FStar_Options.with_saved_options
                         (fun uu___3 ->
                            FStar_Options.set_option "z3seed"
                              (FStar_Options.Int seed1);
                            check_all_configs configs)
                     else check_all_configs configs in
                   let rec fold_nat' f acc lo2 hi2 =
                     if lo2 > hi2
                     then acc
                     else
                       (let uu___3 = f acc lo2 in
                        fold_nat' f uu___3 (lo2 + Prims.int_one) hi2) in
                   let best_fuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let best_ifuel =
                     FStar_Util.mk_ref FStar_Pervasives_Native.None in
                   let maybe_improve r n =
                     let uu___2 = FStar_ST.op_Bang r in
                     match uu___2 with
                     | FStar_Pervasives_Native.None ->
                         FStar_ST.op_Colon_Equals r
                           (FStar_Pervasives_Native.Some n)
                     | FStar_Pervasives_Native.Some m ->
                         if n < m
                         then
                           FStar_ST.op_Colon_Equals r
                             (FStar_Pervasives_Native.Some n)
                         else () in
                   let uu___2 =
                     fold_nat'
                       (fun uu___3 ->
                          fun n ->
                            match uu___3 with
                            | (nsucc, nfail, rs) ->
                                let uu___4 =
                                  (let uu___5 = FStar_Options.quake_keep () in
                                   Prims.op_Negation uu___5) &&
                                    ((nsucc >= lo1) || (nfail > (hi1 - lo1))) in
                                if uu___4
                                then (nsucc, nfail, rs)
                                else
                                  ((let uu___7 =
                                      (quaking_or_retrying &&
                                         ((FStar_Options.interactive ()) ||
                                            (FStar_Options.debug_any ())))
                                        && (n > Prims.int_zero) in
                                    if uu___7
                                    then
                                      let uu___8 =
                                        if quaking
                                        then
                                          let uu___9 =
                                            FStar_Util.string_of_int nsucc in
                                          FStar_Util.format1
                                            "succeeded %s times and " uu___9
                                        else "" in
                                      let uu___9 =
                                        if quaking
                                        then FStar_Util.string_of_int nfail
                                        else
                                          (let uu___11 =
                                             FStar_Util.string_of_int nfail in
                                           Prims.op_Hat uu___11 " times") in
                                      let uu___10 =
                                        FStar_Util.string_of_int (hi1 - n) in
                                      FStar_Util.print5
                                        "%s: so far query %s %sfailed %s (%s runs remain)\n"
                                        (if quaking then "Quake" else "Retry")
                                        name uu___8 uu___9 uu___10
                                    else ());
                                   (let r = run_one (seed + n) in
                                    let uu___7 =
                                      match r with
                                      | FStar_Pervasives.Inr cfg ->
                                          (maybe_improve best_fuel
                                             cfg.query_fuel;
                                           maybe_improve best_ifuel
                                             cfg.query_ifuel;
                                           ((nsucc + Prims.int_one), nfail))
                                      | uu___8 ->
                                          (nsucc, (nfail + Prims.int_one)) in
                                    match uu___7 with
                                    | (nsucc1, nfail1) ->
                                        (nsucc1, nfail1, (r :: rs)))))
                       (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
                       (hi1 - Prims.int_one) in
                   match uu___2 with
                   | (nsuccess, nfailures, rs) ->
                       let total_ran = nsuccess + nfailures in
                       (if quaking
                        then
                          (let fuel_msg =
                             let uu___4 =
                               let uu___5 = FStar_ST.op_Bang best_fuel in
                               let uu___6 = FStar_ST.op_Bang best_ifuel in
                               (uu___5, uu___6) in
                             match uu___4 with
                             | (FStar_Pervasives_Native.Some f,
                                FStar_Pervasives_Native.Some i) ->
                                 let uu___5 = FStar_Util.string_of_int f in
                                 let uu___6 = FStar_Util.string_of_int i in
                                 FStar_Util.format2
                                   " (best fuel=%s, best ifuel=%s)" uu___5
                                   uu___6
                             | (uu___5, uu___6) -> "" in
                           let uu___4 = FStar_Util.string_of_int nsuccess in
                           let uu___5 = FStar_Util.string_of_int total_ran in
                           FStar_Util.print5
                             "Quake: query %s succeeded %s/%s times%s%s\n"
                             name uu___4 uu___5
                             (if total_ran < hi1
                              then " (early finish)"
                              else "") fuel_msg)
                        else ();
                        if nsuccess < lo1
                        then
                          (let all_errs =
                             FStar_List.concatMap
                               (fun uu___4 ->
                                  match uu___4 with
                                  | FStar_Pervasives.Inr uu___5 -> []
                                  | FStar_Pervasives.Inl es -> [es]) rs in
                           let uu___4 =
                             quaking_or_retrying &&
                               (let uu___5 = FStar_Options.query_stats () in
                                Prims.op_Negation uu___5) in
                           if uu___4
                           then
                             let errors_to_report1 errs =
                               errors_to_report
                                 (let uu___5 = default_settings in
                                  {
                                    query_env = (uu___5.query_env);
                                    query_decl = (uu___5.query_decl);
                                    query_name = (uu___5.query_name);
                                    query_index = (uu___5.query_index);
                                    query_range = (uu___5.query_range);
                                    query_fuel = (uu___5.query_fuel);
                                    query_ifuel = (uu___5.query_ifuel);
                                    query_rlimit = (uu___5.query_rlimit);
                                    query_hint = (uu___5.query_hint);
                                    query_errors = errs;
                                    query_all_labels =
                                      (uu___5.query_all_labels);
                                    query_suffix = (uu___5.query_suffix);
                                    query_hash = (uu___5.query_hash)
                                  }) in
                             let errs =
                               FStar_List.map errors_to_report1 all_errs in
                             let errs1 =
                               let uu___5 =
                                 FStar_All.pipe_right errs FStar_List.flatten in
                               FStar_All.pipe_right uu___5 collect in
                             let errs2 =
                               FStar_All.pipe_right errs1
                                 (FStar_List.map
                                    (fun uu___5 ->
                                       match uu___5 with
                                       | ((e, m, r, ctx), n) ->
                                           if n > Prims.int_one
                                           then
                                             let uu___6 =
                                               let uu___7 =
                                                 let uu___8 =
                                                   FStar_Util.string_of_int n in
                                                 FStar_Util.format1
                                                   " (%s times)" uu___8 in
                                               Prims.op_Hat m uu___7 in
                                             (e, uu___6, r, ctx)
                                           else (e, m, r, ctx))) in
                             (FStar_Errors.add_errors errs2;
                              (let rng =
                                 match FStar_Pervasives_Native.snd
                                         env.FStar_TypeChecker_Env.qtbl_name_and_index
                                 with
                                 | FStar_Pervasives_Native.Some (l, uu___6)
                                     -> FStar_Ident.range_of_lid l
                                 | uu___6 -> FStar_Range.dummyRange in
                               if quaking
                               then
                                 let uu___6 =
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_Util.string_of_int nsuccess in
                                     let uu___9 =
                                       FStar_Util.string_of_int total_ran in
                                     let uu___10 =
                                       FStar_Util.string_of_int lo1 in
                                     let uu___11 =
                                       FStar_Util.string_of_int hi1 in
                                     FStar_Util.format6
                                       "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                                       name uu___8 uu___9 uu___10 uu___11
                                       (if total_ran < hi1
                                        then " (early abort)"
                                        else "") in
                                   (FStar_Errors.Error_QuakeFailed, uu___7) in
                                 FStar_TypeChecker_Err.log_issue env rng
                                   uu___6
                               else ()))
                           else
                             (let report errs =
                                report_errors
                                  (let uu___6 = default_settings in
                                   {
                                     query_env = (uu___6.query_env);
                                     query_decl = (uu___6.query_decl);
                                     query_name = (uu___6.query_name);
                                     query_index = (uu___6.query_index);
                                     query_range = (uu___6.query_range);
                                     query_fuel = (uu___6.query_fuel);
                                     query_ifuel = (uu___6.query_ifuel);
                                     query_rlimit = (uu___6.query_rlimit);
                                     query_hint = (uu___6.query_hint);
                                     query_errors = errs;
                                     query_all_labels =
                                       (uu___6.query_all_labels);
                                     query_suffix = (uu___6.query_suffix);
                                     query_hash = (uu___6.query_hash)
                                   }) in
                              FStar_List.iter report all_errs))
                        else ()) in
                 let skip =
                   (FStar_Options.admit_smt_queries ()) ||
                     (let uu___2 = FStar_Options.admit_except () in
                      match uu___2 with
                      | FStar_Pervasives_Native.Some id ->
                          if FStar_Util.starts_with id "("
                          then
                            let uu___3 = full_query_id default_settings in
                            uu___3 <> id
                          else default_settings.query_name <> id
                      | FStar_Pervasives_Native.None -> false) in
                 if skip
                 then
                   let uu___2 =
                     (FStar_Options.record_hints ()) &&
                       (FStar_All.pipe_right next_hint FStar_Util.is_some) in
                   (if uu___2
                    then
                      let uu___3 =
                        FStar_All.pipe_right next_hint FStar_Util.must in
                      FStar_All.pipe_right uu___3 store_hint
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
    let uu___ = FStar_Options.z3_seed () in
    let uu___1 = FStar_Options.z3_cliopt () in
    let uu___2 = FStar_Options.smtencoding_valid_intro () in
    let uu___3 = FStar_Options.smtencoding_valid_elim () in
    {
      seed = uu___;
      cliopt = uu___1;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu___2;
      valid_elim = uu___3
    }
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu___ =
      let uu___1 = get_cfg env in FStar_Pervasives_Native.Some uu___1 in
    FStar_ST.op_Colon_Equals _last_cfg uu___
let (should_refresh : FStar_TypeChecker_Env.env -> Prims.bool) =
  fun env ->
    let uu___ = FStar_ST.op_Bang _last_cfg in
    match uu___ with
    | FStar_Pervasives_Native.None -> (save_cfg env; false)
    | FStar_Pervasives_Native.Some cfg ->
        let uu___1 = let uu___2 = get_cfg env in cfg = uu___2 in
        Prims.op_Negation uu___1
let (do_solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu___1 = should_refresh tcenv in
         if uu___1
         then (save_cfg tcenv; FStar_SMTEncoding_Z3.refresh ())
         else ());
        (let uu___2 =
           let uu___3 =
             let uu___4 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu___4 in
           FStar_Util.format1 "Starting query at %s" uu___3 in
         FStar_SMTEncoding_Encode.push uu___2);
        (let pop uu___2 =
           let uu___3 =
             let uu___4 =
               let uu___5 = FStar_TypeChecker_Env.get_range tcenv in
               FStar_All.pipe_left FStar_Range.string_of_range uu___5 in
             FStar_Util.format1 "Ending query at %s" uu___4 in
           FStar_SMTEncoding_Encode.pop uu___3 in
         try
           (fun uu___2 ->
              match () with
              | () ->
                  let uu___3 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
                  (match uu___3 with
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
                                    (FStar_SMTEncoding_Term.FalseOp, uu___4);
                                  FStar_SMTEncoding_Term.freevars = uu___5;
                                  FStar_SMTEncoding_Term.rng = uu___6;_};
                              FStar_SMTEncoding_Term.assumption_caption =
                                uu___7;
                              FStar_SMTEncoding_Term.assumption_name = uu___8;
                              FStar_SMTEncoding_Term.assumption_fact_ids =
                                uu___9;_}
                            -> pop ()
                        | uu___4 when tcenv1.FStar_TypeChecker_Env.admit ->
                            pop ()
                        | FStar_SMTEncoding_Term.Assume uu___4 ->
                            (ask_and_report_errors tcenv1 labels prefix qry
                               suffix;
                             pop ())
                        | uu___4 -> failwith "Impossible"))) ()
         with
         | FStar_SMTEncoding_Env.Inner_let_rec names ->
             (pop ();
              (let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       FStar_List.map FStar_Pervasives_Native.fst names in
                     FStar_String.concat "," uu___7 in
                   FStar_Util.format1
                     "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                     uu___6 in
                 (FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded,
                   uu___5) in
               FStar_TypeChecker_Err.log_issue tcenv
                 tcenv.FStar_TypeChecker_Env.range uu___4)))
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu___ = FStar_Options.no_smt () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Print.term_to_string q in
              FStar_Util.format1
                "Q = %s\nA query could not be solved internally, and --no_smt was given"
                uu___3 in
            (FStar_Errors.Error_NoSMTButNeeded, uu___2) in
          FStar_TypeChecker_Err.log_issue tcenv
            tcenv.FStar_TypeChecker_Env.range uu___1
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStar_TypeChecker_Env.current_module tcenv in
               FStar_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStar_Profiling.profile
             (fun uu___3 -> do_solve use_env_msg tcenv q) uu___2
             "FStar.SMTEncoding.solve_top_level")
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
           let uu___ = let uu___1 = FStar_Options.peek () in (e, g, uu___1) in
           [uu___]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu___ -> ());
    FStar_TypeChecker_Env.push = (fun uu___ -> ());
    FStar_TypeChecker_Env.pop = (fun uu___ -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu___ -> ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStar_TypeChecker_Env.rollback = (fun uu___ -> fun uu___1 -> ());
    FStar_TypeChecker_Env.encode_sig = (fun uu___ -> fun uu___1 -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu___ = let uu___1 = FStar_Options.peek () in (e, g, uu___1) in
           [uu___]);
    FStar_TypeChecker_Env.solve =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> ());
    FStar_TypeChecker_Env.finish = (fun uu___ -> ());
    FStar_TypeChecker_Env.refresh = (fun uu___ -> ())
  }
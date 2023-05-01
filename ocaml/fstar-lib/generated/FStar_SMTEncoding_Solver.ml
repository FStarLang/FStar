open Prims
exception SplitQueryAndRetry 
let (uu___is_SplitQueryAndRetry : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | SplitQueryAndRetry -> true | uu___ -> false
let (z3_replay_result : (unit * unit)) = ((), ())
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
  FStar_Compiler_Util.hints FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Compiler_Util.hints FStar_Pervasives_Native.option
    FStar_Compiler_Effect.ref)
  = FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let initialize_hints_db : 'uuuuu . Prims.string -> 'uuuuu -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu___1 = FStar_Options.record_hints () in
       if uu___1
       then
         FStar_Compiler_Effect.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename =
         FStar_Compiler_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       let uu___1 = FStar_Compiler_Util.read_hints val_filename in
       match uu___1 with
       | FStar_Compiler_Util.HintsOK hints ->
           let expected_digest =
             FStar_Compiler_Util.digest_of_file norm_src_filename in
           ((let uu___3 = FStar_Options.hint_info () in
             if uu___3
             then
               FStar_Compiler_Util.print3 "(%s) digest is %s from %s.\n"
                 norm_src_filename
                 (if
                    hints.FStar_Compiler_Util.module_digest = expected_digest
                  then "valid; using hints"
                  else "invalid; using potentially stale hints") val_filename
             else ());
            FStar_Compiler_Effect.op_Colon_Equals replaying_hints
              (FStar_Pervasives_Native.Some (hints.FStar_Compiler_Util.hints)))
       | FStar_Compiler_Util.MalformedJson ->
           let uu___3 = FStar_Options.use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 FStar_Compiler_Util.format1
                   "Malformed JSON hints file: %s; ran without hints"
                   val_filename in
               (FStar_Errors_Codes.Warning_CouldNotReadHints, uu___5) in
             FStar_Errors.log_issue FStar_Compiler_Range.dummyRange uu___4
           else ()
       | FStar_Compiler_Util.UnableToOpen ->
           let uu___3 = FStar_Options.use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 FStar_Compiler_Util.format1
                   "Unable to open hints file: %s; ran without hints"
                   val_filename in
               (FStar_Errors_Codes.Warning_CouldNotReadHints, uu___5) in
             FStar_Errors.log_issue FStar_Compiler_Range.dummyRange uu___4
           else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu___1 = FStar_Options.record_hints () in
     if uu___1
     then
       let hints =
         let uu___2 = FStar_Compiler_Effect.op_Bang recorded_hints in
         FStar_Compiler_Option.get uu___2 in
       let hints_db =
         let uu___2 = FStar_Compiler_Util.digest_of_file src_filename in
         {
           FStar_Compiler_Util.module_digest = uu___2;
           FStar_Compiler_Util.hints = hints
         } in
       let norm_src_filename =
         FStar_Compiler_Util.normalize_file_path src_filename in
       let val_filename = FStar_Options.hint_file_for_src norm_src_filename in
       FStar_Compiler_Util.write_hints val_filename hints_db
     else ());
    FStar_Compiler_Effect.op_Colon_Equals recorded_hints
      FStar_Pervasives_Native.None;
    FStar_Compiler_Effect.op_Colon_Equals replaying_hints
      FStar_Pervasives_Native.None
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
            (FStar_Compiler_Effect.op_Bar_Greater
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Compiler_Util.for_some
                  (fun uu___1 ->
                     match uu___1 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu___2 -> false)))
              ||
              (let uu___1 =
                 FStar_Compiler_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Compiler_Option.isSome uu___1) in
      let theory_rev = FStar_Compiler_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Compiler_Util.smap_create (Prims.of_int (10000)) in
        let keep_decl uu___ =
          match uu___ with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names ->
              (FStar_Compiler_List.iter
                 (fun x ->
                    FStar_Compiler_Util.smap_add include_assumption_names x
                      true) names;
               true)
          | FStar_SMTEncoding_Term.Module uu___1 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu___1 -> true in
        FStar_Compiler_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Module (name, decls) ->
                   let uu___ =
                     FStar_Compiler_Effect.op_Bar_Greater decls
                       (FStar_Compiler_List.filter keep_decl) in
                   FStar_Compiler_Effect.op_Bar_Greater uu___
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
            let theory_rev = FStar_Compiler_List.rev theory in
            let uu___ =
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Compiler_Effect.op_Bar_Greater core1
                          (FStar_String.concat ", ") in
                      Prims.op_Hat "UNSAT CORE: " uu___5 in
                    FStar_SMTEncoding_Term.Caption uu___4 in
                  [uu___3] in
                (uu___2, Prims.int_zero, Prims.int_zero) in
              FStar_Compiler_List.fold_left
                (fun uu___2 ->
                   fun d ->
                     match uu___2 with
                     | (theory1, n_retained, n_pruned) ->
                         (match d with
                          | FStar_SMTEncoding_Term.Assume a ->
                              if
                                FStar_Compiler_List.contains
                                  a.FStar_SMTEncoding_Term.assumption_name
                                  core1
                              then
                                ((d :: theory1),
                                  (n_retained + Prims.int_one), n_pruned)
                              else
                                if
                                  FStar_Compiler_Util.starts_with
                                    a.FStar_SMTEncoding_Term.assumption_name
                                    "@"
                                then ((d :: theory1), n_retained, n_pruned)
                                else
                                  (theory1, n_retained,
                                    (n_pruned + Prims.int_one))
                          | FStar_SMTEncoding_Term.Module (name, decls) ->
                              let uu___3 =
                                FStar_Compiler_Effect.op_Bar_Greater decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1)) in
                              FStar_Compiler_Effect.op_Bar_Greater uu___3
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
    let uu___ = FStar_Compiler_Util.string_of_int err.error_fuel in
    let uu___1 = FStar_Compiler_Util.string_of_int err.error_ifuel in
    FStar_Compiler_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason
      uu___ uu___1
      (if FStar_Compiler_Option.isSome err.error_hint
       then "; with hint"
       else "")
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err ->
    if FStar_Compiler_Util.ends_with err.error_reason "canceled"
    then
      let uu___ =
        let uu___1 = FStar_Compiler_Util.string_of_int err.error_fuel in
        let uu___2 = FStar_Compiler_Util.string_of_int err.error_ifuel in
        FStar_Compiler_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)"
          err.error_reason uu___1 uu___2
          (if FStar_Compiler_Option.isSome err.error_hint
           then "with hint"
           else "") in
      [uu___]
    else []
type query_settings =
  {
  query_env: FStar_TypeChecker_Env.env ;
  query_decl: FStar_SMTEncoding_Term.decl ;
  query_name: Prims.string ;
  query_index: Prims.int ;
  query_range: FStar_Compiler_Range.range ;
  query_fuel: Prims.int ;
  query_ifuel: Prims.int ;
  query_rlimit: Prims.int ;
  query_hint: FStar_SMTEncoding_Z3.unsat_core ;
  query_errors: errors Prims.list ;
  query_all_labels: FStar_SMTEncoding_Term.error_labels ;
  query_suffix: FStar_SMTEncoding_Term.decl Prims.list ;
  query_hash: Prims.string FStar_Pervasives_Native.option ;
  query_can_be_split_and_retried: Prims.bool ;
  query_term: FStar_Syntax_Syntax.term }
let (__proj__Mkquery_settings__item__query_env :
  query_settings -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_env
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_decl
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_name
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_index
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Compiler_Range.range) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_range
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_fuel
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_ifuel
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_rlimit
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_hint
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_errors
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_all_labels
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_suffix
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_hash
let (__proj__Mkquery_settings__item__query_can_be_split_and_retried :
  query_settings -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} ->
        query_can_be_split_and_retried
let (__proj__Mkquery_settings__item__query_term :
  query_settings -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_term
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
            let uu___3 = FStar_Compiler_Util.string_of_int n in
            let uu___4 = FStar_Compiler_Util.string_of_int i in
            FStar_Compiler_Util.format2 "<fuel='%s' ifuel='%s'>" uu___3
              uu___4 in
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
                let uu___6 = FStar_Compiler_Util.string_of_int rlimit in
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
            FStar_Compiler_List.op_At uu___5 settings.query_suffix in
          FStar_Compiler_List.op_At uu___3 uu___4 in
        FStar_Compiler_List.op_At label_assumptions uu___2 in
      FStar_Compiler_List.op_At uu___ uu___1
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Compiler_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string ->
    Prims.int -> FStar_Compiler_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu___ = FStar_Compiler_Effect.op_Bang replaying_hints in
      match uu___ with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Compiler_Util.find_map hints
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Compiler_Util.hint_name = qname) &&
                     (hint.FStar_Compiler_Util.hint_index = qindex)
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
                   FStar_Compiler_List.map
                     (fun uu___3 ->
                        match uu___3 with
                        | (uu___4, x, y) ->
                            let uu___5 = FStar_Errors.get_ctx () in
                            (FStar_Errors_Codes.Error_Z3SolverError, x, y,
                              uu___5)) error_labels in
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
    FStar_Compiler_Effect.op_Bar_Greater errs
      (FStar_Compiler_List.tryFind
         (fun err ->
            match err.error_messages with | [] -> false | uu___ -> true))
let (errors_to_report : query_settings -> FStar_Errors.error Prims.list) =
  fun settings ->
    let format_smt_error msg =
      FStar_Compiler_Util.format1
        "SMT solver says:\n\t%s;\n\tNote: 'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit;\n\t'incomplete quantifiers' means Z3 could not prove the query, so try to spell out your proof out in greater detail, increase fuel or ifuel\n\t'unknown' means Z3 provided no further reason for the proof failing"
        msg in
    let basic_errors =
      let smt_error =
        let uu___ = FStar_Options.query_stats () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Compiler_Effect.op_Bar_Greater settings.query_errors
                  (FStar_Compiler_List.map error_to_short_string) in
              FStar_Compiler_Effect.op_Bar_Greater uu___3
                (FStar_String.concat ";\n\t") in
            FStar_Compiler_Effect.op_Bar_Greater uu___2 format_smt_error in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            (fun uu___2 -> FStar_Pervasives.Inr uu___2)
        else
          (let uu___2 =
             FStar_Compiler_List.fold_left
               (fun uu___3 ->
                  fun err ->
                    match uu___3 with
                    | (ic, cc, uc) ->
                        let err1 =
                          FStar_Compiler_Util.substring_from err.error_reason
                            (FStar_String.length "unknown because ") in
                        if
                          ((FStar_Compiler_Util.starts_with err1 "canceled")
                             ||
                             (FStar_Compiler_Util.starts_with err1
                                "(resource"))
                            ||
                            (FStar_Compiler_Util.starts_with err1 "timeout")
                        then (ic, (cc + Prims.int_one), uc)
                        else
                          if
                            FStar_Compiler_Util.starts_with err1
                              "(incomplete"
                          then ((ic + Prims.int_one), cc, uc)
                          else (ic, cc, (uc + Prims.int_one)))
               (Prims.int_zero, Prims.int_zero, Prims.int_zero)
               settings.query_errors in
           match uu___2 with
           | (incomplete_count, canceled_count, unknown_count) ->
               FStar_Compiler_Effect.op_Bar_Greater
                 (match (incomplete_count, canceled_count, unknown_count)
                  with
                  | (uu___3, uu___4, uu___5) when
                      ((uu___4 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                        && (incomplete_count > Prims.int_zero)
                      ->
                      "The SMT solver could not prove the query. Use --query_stats for more details."
                  | (uu___3, uu___4, uu___5) when
                      ((uu___3 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                        && (canceled_count > Prims.int_zero)
                      ->
                      "The SMT query timed out, you might want to increase the rlimit"
                  | (uu___3, uu___4, uu___5) ->
                      "Try with --query_stats to get more details")
                 (fun uu___3 -> FStar_Pervasives.Inl uu___3)) in
      let uu___ =
        let uu___1 = find_localized_errors settings.query_errors in
        (uu___1, (settings.query_all_labels)) in
      match uu___ with
      | (FStar_Pervasives_Native.Some err, uu___1) ->
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env
            err.error_messages smt_error
      | (FStar_Pervasives_Native.None, (uu___1, msg, rng)::[]) ->
          let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Errors.get_ctx () in
              (FStar_Errors_Codes.Error_Z3SolverError, msg, rng, uu___4) in
            [uu___3] in
          FStar_TypeChecker_Err.errors_smt_detail settings.query_env uu___2
            (FStar_Pervasives.Inl "")
      | (FStar_Pervasives_Native.None, uu___1) ->
          if settings.query_can_be_split_and_retried
          then FStar_Compiler_Effect.raise SplitQueryAndRetry
          else
            (let l = FStar_Compiler_List.length settings.query_all_labels in
             let labels =
               if l = Prims.int_zero
               then
                 let dummy_fv =
                   FStar_SMTEncoding_Term.mk_fv
                     ("", FStar_SMTEncoding_Term.dummy_sort) in
                 let msg =
                   let uu___3 =
                     FStar_Syntax_Print.term_to_string settings.query_term in
                   FStar_Compiler_Util.format1
                     "Failed to prove the following goal, although it appears to be trivial: %s"
                     uu___3 in
                 let range =
                   FStar_TypeChecker_Env.get_range settings.query_env in
                 [(dummy_fv, msg, range)]
               else
                 if l > Prims.int_one
                 then
                   ((let uu___5 =
                       let uu___6 = FStar_Options.split_queries () in
                       uu___6 <> FStar_Options.No in
                     if uu___5
                     then
                       let uu___6 =
                         FStar_TypeChecker_Env.get_range settings.query_env in
                       FStar_TypeChecker_Err.log_issue settings.query_env
                         uu___6
                         (FStar_Errors_Codes.Warning_SplitAndRetryQueries,
                           "The verification condition was to be split into several atomic sub-goals, but this query has multiple sub-goals---the error report may be inaccurate")
                     else ());
                    settings.query_all_labels)
                 else settings.query_all_labels in
             FStar_Compiler_Effect.op_Bar_Greater labels
               (FStar_Compiler_List.collect
                  (fun uu___3 ->
                     match uu___3 with
                     | (uu___4, msg, rng) ->
                         let uu___5 =
                           let uu___6 =
                             let uu___7 = FStar_Errors.get_ctx () in
                             (FStar_Errors_Codes.Error_Z3SolverError, msg,
                               rng, uu___7) in
                           [uu___6] in
                         FStar_TypeChecker_Err.errors_smt_detail
                           settings.query_env uu___5
                           (FStar_Pervasives.Inl "")))) in
    (let uu___ = FStar_Options.detail_errors () in
     if uu___
     then
       let initial_fuel =
         let uu___1 = FStar_Options.initial_fuel () in
         let uu___2 = FStar_Options.initial_ifuel () in
         {
           query_env = (settings.query_env);
           query_decl = (settings.query_decl);
           query_name = (settings.query_name);
           query_index = (settings.query_index);
           query_range = (settings.query_range);
           query_fuel = uu___1;
           query_ifuel = uu___2;
           query_rlimit = (settings.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (settings.query_errors);
           query_all_labels = (settings.query_all_labels);
           query_suffix = (settings.query_suffix);
           query_hash = (settings.query_hash);
           query_can_be_split_and_retried =
             (settings.query_can_be_split_and_retried);
           query_term = (settings.query_term)
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
          let r = FStar_Compiler_Util.mk_ref [] in
          let uu___1 =
            let module_names = FStar_Compiler_Util.mk_ref [] in
            ((fun m ->
                let ms = FStar_Compiler_Effect.op_Bang module_names in
                if FStar_Compiler_List.contains m ms
                then ()
                else
                  FStar_Compiler_Effect.op_Colon_Equals module_names (m ::
                    ms)),
              (fun uu___2 ->
                 let uu___3 = FStar_Compiler_Effect.op_Bang module_names in
                 FStar_Compiler_Effect.op_Bar_Greater uu___3
                   (FStar_Compiler_Util.sort_with FStar_String.compare))) in
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
                     FStar_Compiler_Util.try_find_index
                       FStar_Compiler_Util.is_upper chars in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStar_Compiler_Util.substring_from s
                           first_upper_index1 in
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
                         let s2 = FStar_Compiler_Util.trim_string s1 in
                         let sopt =
                           FStar_Compiler_Util.find_map excluded_suffixes
                             (fun sfx ->
                                if FStar_Compiler_Util.contains s2 sfx
                                then
                                  let uu___2 =
                                    FStar_Compiler_List.hd
                                      (FStar_Compiler_Util.split s2 sfx) in
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
                             let uu___3 =
                               FStar_Compiler_Util.prefix components in
                             (match uu___3 with
                              | (module_name, last) ->
                                  let components2 =
                                    let uu___4 = exclude_suffix last in
                                    FStar_Compiler_List.op_At module_name
                                      uu___4 in
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
                            FStar_Compiler_Effect.op_Bar_Greater components1
                              (FStar_String.concat ".") in
                          [uu___3]) in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Compiler_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 =
                        FStar_Compiler_List.collect parse_axiom_name core1 in
                      ((let uu___3 =
                          let uu___4 = get_module_names () in
                          FStar_Compiler_Effect.op_Bar_Greater uu___4
                            (FStar_String.concat "\nZ3 Proof Stats:\t") in
                        FStar_Compiler_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu___3);
                       FStar_Compiler_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu___4 =
                          let uu___5 = get_discarded_names () in
                          FStar_Compiler_Effect.op_Bar_Greater uu___5
                            (FStar_String.concat ", ") in
                        FStar_Compiler_Util.print1
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
                       FStar_Compiler_Range.string_of_range
                         settings.query_range in
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
                       FStar_Compiler_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu___4 =
                       FStar_Compiler_Util.substring str Prims.int_zero
                         ((FStar_String.length str) - Prims.int_one) in
                     Prims.op_Hat uu___4 "}"
                   else "" in
                 ((let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStar_Compiler_Util.string_of_int
                             settings.query_index in
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStar_Compiler_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time in
                               let uu___12 =
                                 let uu___13 =
                                   FStar_Compiler_Util.string_of_int
                                     settings.query_fuel in
                                 let uu___14 =
                                   let uu___15 =
                                     FStar_Compiler_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu___16 =
                                     let uu___17 =
                                       FStar_Compiler_Util.string_of_int
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
                   FStar_Compiler_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu___4);
                  (let uu___5 = FStar_Options.print_z3_statistics () in
                   if uu___5 then process_unsat_core core else ());
                  FStar_Compiler_Effect.op_Bar_Greater errs
                    (FStar_Compiler_List.iter
                       (fun uu___5 ->
                          match uu___5 with
                          | (uu___6, msg, range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              FStar_Errors.log_issue range1
                                (FStar_Errors_Codes.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
let (store_hint : FStar_Compiler_Util.hint -> unit) =
  fun hint ->
    let uu___ = FStar_Compiler_Effect.op_Bang recorded_hints in
    match uu___ with
    | FStar_Pervasives_Native.Some l ->
        FStar_Compiler_Effect.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStar_Compiler_List.op_At l [FStar_Pervasives_Native.Some hint]))
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
             FStar_Compiler_Util.hint_name = (settings.query_name);
             FStar_Compiler_Util.hint_index = (settings.query_index);
             FStar_Compiler_Util.fuel = (settings.query_fuel);
             FStar_Compiler_Util.ifuel = (settings.query_ifuel);
             FStar_Compiler_Util.unsat_core = core;
             FStar_Compiler_Util.query_elapsed_time = Prims.int_zero;
             FStar_Compiler_Util.hash =
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
               FStar_Compiler_Option.get uu___3 in
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
          let uu___3 = FStar_Compiler_Util.string_of_int settings.query_index in
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
    FStar_Compiler_List.fold_left add_one acc l
type answer =
  {
  ok: Prims.bool ;
  nsuccess: Prims.int ;
  lo: Prims.int ;
  hi: Prims.int ;
  errs: errors Prims.list Prims.list ;
  quaking: Prims.bool ;
  quaking_or_retrying: Prims.bool ;
  total_ran: Prims.int }
let (__proj__Mkanswer__item__ok : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> ok
let (__proj__Mkanswer__item__nsuccess : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> nsuccess
let (__proj__Mkanswer__item__lo : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> lo
let (__proj__Mkanswer__item__hi : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> hi
let (__proj__Mkanswer__item__errs : answer -> errors Prims.list Prims.list) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> errs
let (__proj__Mkanswer__item__quaking : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> quaking
let (__proj__Mkanswer__item__quaking_or_retrying : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> quaking_or_retrying
let (__proj__Mkanswer__item__total_ran : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; nsuccess; lo; hi; errs; quaking; quaking_or_retrying;
        total_ran;_} -> total_ran
let (ans_ok : answer) =
  {
    ok = true;
    nsuccess = Prims.int_one;
    lo = Prims.int_one;
    hi = Prims.int_one;
    errs = [];
    quaking = false;
    quaking_or_retrying = false;
    total_ran = Prims.int_one
  }
let (ans_fail : answer) =
  {
    ok = false;
    nsuccess = Prims.int_zero;
    lo = (ans_ok.lo);
    hi = (ans_ok.hi);
    errs = (ans_ok.errs);
    quaking = (ans_ok.quaking);
    quaking_or_retrying = (ans_ok.quaking_or_retrying);
    total_ran = (ans_ok.total_ran)
  }
let (make_solver_configs :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            FStar_SMTEncoding_Term.decl ->
              FStar_Syntax_Syntax.term ->
                FStar_SMTEncoding_Term.decl Prims.list ->
                  (query_settings Prims.list * FStar_Compiler_Util.hint
                    FStar_Pervasives_Native.option))
  =
  fun can_split ->
    fun is_retry ->
      fun env ->
        fun all_labels ->
          fun prefix ->
            fun query ->
              fun query_term ->
                fun suffix ->
                  let uu___ =
                    let uu___1 =
                      match env.FStar_TypeChecker_Env.qtbl_name_and_index
                      with
                      | (uu___2, FStar_Pervasives_Native.None) ->
                          failwith "No query name set!"
                      | (uu___2, FStar_Pervasives_Native.Some (q, n)) ->
                          let uu___3 = FStar_Ident.string_of_lid q in
                          (uu___3, n) in
                    match uu___1 with
                    | (qname, index) ->
                        let rlimit =
                          let uu___2 = FStar_Options.z3_rlimit_factor () in
                          let uu___3 =
                            let uu___4 = FStar_Options.z3_rlimit () in
                            uu___4 * (Prims.parse_int "544656") in
                          uu___2 * uu___3 in
                        let next_hint = get_hint_for qname index in
                        let default_settings =
                          let uu___2 = FStar_TypeChecker_Env.get_range env in
                          let uu___3 = FStar_Options.initial_fuel () in
                          let uu___4 = FStar_Options.initial_ifuel () in
                          {
                            query_env = env;
                            query_decl = query;
                            query_name = qname;
                            query_index = index;
                            query_range = uu___2;
                            query_fuel = uu___3;
                            query_ifuel = uu___4;
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
                                   { FStar_Compiler_Util.hint_name = uu___5;
                                     FStar_Compiler_Util.hint_index = uu___6;
                                     FStar_Compiler_Util.fuel = uu___7;
                                     FStar_Compiler_Util.ifuel = uu___8;
                                     FStar_Compiler_Util.unsat_core = uu___9;
                                     FStar_Compiler_Util.query_elapsed_time =
                                       uu___10;
                                     FStar_Compiler_Util.hash = h;_}
                                   -> h);
                            query_can_be_split_and_retried = can_split;
                            query_term
                          } in
                        (default_settings, next_hint) in
                  match uu___ with
                  | (default_settings, next_hint) ->
                      let use_hints_setting =
                        let uu___1 =
                          (FStar_Options.use_hints ()) &&
                            (FStar_Compiler_Effect.op_Bar_Greater next_hint
                               FStar_Compiler_Util.is_some) in
                        if uu___1
                        then
                          let uu___2 =
                            FStar_Compiler_Effect.op_Bar_Greater next_hint
                              FStar_Compiler_Util.must in
                          match uu___2 with
                          | { FStar_Compiler_Util.hint_name = uu___3;
                              FStar_Compiler_Util.hint_index = uu___4;
                              FStar_Compiler_Util.fuel = i;
                              FStar_Compiler_Util.ifuel = j;
                              FStar_Compiler_Util.unsat_core =
                                FStar_Pervasives_Native.Some core;
                              FStar_Compiler_Util.query_elapsed_time = uu___5;
                              FStar_Compiler_Util.hash = h;_} ->
                              [{
                                 query_env = (default_settings.query_env);
                                 query_decl = (default_settings.query_decl);
                                 query_name = (default_settings.query_name);
                                 query_index = (default_settings.query_index);
                                 query_range = (default_settings.query_range);
                                 query_fuel = i;
                                 query_ifuel = j;
                                 query_rlimit =
                                   (default_settings.query_rlimit);
                                 query_hint =
                                   (FStar_Pervasives_Native.Some core);
                                 query_errors =
                                   (default_settings.query_errors);
                                 query_all_labels =
                                   (default_settings.query_all_labels);
                                 query_suffix =
                                   (default_settings.query_suffix);
                                 query_hash = (default_settings.query_hash);
                                 query_can_be_split_and_retried =
                                   (default_settings.query_can_be_split_and_retried);
                                 query_term = (default_settings.query_term)
                               }]
                        else [] in
                      let initial_fuel_max_ifuel =
                        let uu___1 =
                          let uu___2 = FStar_Options.max_ifuel () in
                          let uu___3 = FStar_Options.initial_ifuel () in
                          uu___2 > uu___3 in
                        if uu___1
                        then
                          let uu___2 =
                            let uu___3 = FStar_Options.max_ifuel () in
                            {
                              query_env = (default_settings.query_env);
                              query_decl = (default_settings.query_decl);
                              query_name = (default_settings.query_name);
                              query_index = (default_settings.query_index);
                              query_range = (default_settings.query_range);
                              query_fuel = (default_settings.query_fuel);
                              query_ifuel = uu___3;
                              query_rlimit = (default_settings.query_rlimit);
                              query_hint = (default_settings.query_hint);
                              query_errors = (default_settings.query_errors);
                              query_all_labels =
                                (default_settings.query_all_labels);
                              query_suffix = (default_settings.query_suffix);
                              query_hash = (default_settings.query_hash);
                              query_can_be_split_and_retried =
                                (default_settings.query_can_be_split_and_retried);
                              query_term = (default_settings.query_term)
                            } in
                          [uu___2]
                        else [] in
                      let half_max_fuel_max_ifuel =
                        let uu___1 =
                          let uu___2 =
                            let uu___3 = FStar_Options.max_fuel () in
                            uu___3 / (Prims.of_int (2)) in
                          let uu___3 = FStar_Options.initial_fuel () in
                          uu___2 > uu___3 in
                        if uu___1
                        then
                          let uu___2 =
                            let uu___3 =
                              let uu___4 = FStar_Options.max_fuel () in
                              uu___4 / (Prims.of_int (2)) in
                            let uu___4 = FStar_Options.max_ifuel () in
                            {
                              query_env = (default_settings.query_env);
                              query_decl = (default_settings.query_decl);
                              query_name = (default_settings.query_name);
                              query_index = (default_settings.query_index);
                              query_range = (default_settings.query_range);
                              query_fuel = uu___3;
                              query_ifuel = uu___4;
                              query_rlimit = (default_settings.query_rlimit);
                              query_hint = (default_settings.query_hint);
                              query_errors = (default_settings.query_errors);
                              query_all_labels =
                                (default_settings.query_all_labels);
                              query_suffix = (default_settings.query_suffix);
                              query_hash = (default_settings.query_hash);
                              query_can_be_split_and_retried =
                                (default_settings.query_can_be_split_and_retried);
                              query_term = (default_settings.query_term)
                            } in
                          [uu___2]
                        else [] in
                      let max_fuel_max_ifuel =
                        let uu___1 =
                          (let uu___2 = FStar_Options.max_fuel () in
                           let uu___3 = FStar_Options.initial_fuel () in
                           uu___2 > uu___3) &&
                            (let uu___2 = FStar_Options.max_ifuel () in
                             let uu___3 = FStar_Options.initial_ifuel () in
                             uu___2 >= uu___3) in
                        if uu___1
                        then
                          let uu___2 =
                            let uu___3 = FStar_Options.max_fuel () in
                            let uu___4 = FStar_Options.max_ifuel () in
                            {
                              query_env = (default_settings.query_env);
                              query_decl = (default_settings.query_decl);
                              query_name = (default_settings.query_name);
                              query_index = (default_settings.query_index);
                              query_range = (default_settings.query_range);
                              query_fuel = uu___3;
                              query_ifuel = uu___4;
                              query_rlimit = (default_settings.query_rlimit);
                              query_hint = (default_settings.query_hint);
                              query_errors = (default_settings.query_errors);
                              query_all_labels =
                                (default_settings.query_all_labels);
                              query_suffix = (default_settings.query_suffix);
                              query_hash = (default_settings.query_hash);
                              query_can_be_split_and_retried =
                                (default_settings.query_can_be_split_and_retried);
                              query_term = (default_settings.query_term)
                            } in
                          [uu___2]
                        else [] in
                      let cfgs =
                        if is_retry
                        then [default_settings]
                        else
                          FStar_Compiler_List.op_At use_hints_setting
                            (FStar_Compiler_List.op_At [default_settings]
                               (FStar_Compiler_List.op_At
                                  initial_fuel_max_ifuel
                                  (FStar_Compiler_List.op_At
                                     half_max_fuel_max_ifuel
                                     max_fuel_max_ifuel))) in
                      (cfgs, next_hint)
let (__ask_solver :
  query_settings Prims.list ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (errors Prims.list, query_settings) FStar_Pervasives.either)
  =
  fun configs ->
    fun prefix ->
      let check_one_config config =
        (let uu___1 = FStar_Options.z3_refresh () in
         if uu___1 then FStar_SMTEncoding_Z3.refresh () else ());
        (let uu___1 = with_fuel_and_diagnostics config [] in
         let uu___2 =
           let uu___3 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
           FStar_Pervasives_Native.Some uu___3 in
         FStar_SMTEncoding_Z3.ask config.query_range
           (filter_assertions config.query_env config.query_hint)
           config.query_hash config.query_all_labels uu___1 uu___2
           (used_hint config)) in
      fold_queries configs check_one_config process_result
let (ask_solver_quake :
  query_settings Prims.list ->
    FStar_SMTEncoding_Term.decl Prims.list -> answer)
  =
  fun configs ->
    fun prefix ->
      FStar_SMTEncoding_Z3.giveZ3 prefix;
      (let lo = FStar_Options.quake_lo () in
       let hi = FStar_Options.quake_hi () in
       let seed = FStar_Options.z3_seed () in
       let default_settings = FStar_Compiler_List.hd configs in
       let name = full_query_id default_settings in
       let quaking =
         (hi > Prims.int_one) &&
           (let uu___1 = FStar_Options.retry () in Prims.op_Negation uu___1) in
       let quaking_or_retrying = hi > Prims.int_one in
       let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
       let lo1 =
         if lo < Prims.int_one
         then Prims.int_one
         else if lo > hi1 then hi1 else lo in
       let run_one seed1 =
         let uu___1 = FStar_Options.z3_refresh () in
         if uu___1
         then
           FStar_Options.with_saved_options
             (fun uu___2 ->
                FStar_Options.set_option "z3seed" (FStar_Options.Int seed1);
                __ask_solver configs prefix)
         else __ask_solver configs prefix in
       let rec fold_nat' f acc lo2 hi2 =
         if lo2 > hi2
         then acc
         else
           (let uu___2 = f acc lo2 in
            fold_nat' f uu___2 (lo2 + Prims.int_one) hi2) in
       let best_fuel =
         FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
       let best_ifuel =
         FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
       let maybe_improve r n =
         let uu___1 = FStar_Compiler_Effect.op_Bang r in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Compiler_Effect.op_Colon_Equals r
               (FStar_Pervasives_Native.Some n)
         | FStar_Pervasives_Native.Some m ->
             if n < m
             then
               FStar_Compiler_Effect.op_Colon_Equals r
                 (FStar_Pervasives_Native.Some n)
             else () in
       let uu___1 =
         fold_nat'
           (fun uu___2 ->
              fun n ->
                match uu___2 with
                | (nsucc, nfail, rs) ->
                    let uu___3 =
                      (let uu___4 = FStar_Options.quake_keep () in
                       Prims.op_Negation uu___4) &&
                        ((nsucc >= lo1) || (nfail > (hi1 - lo1))) in
                    if uu___3
                    then (nsucc, nfail, rs)
                    else
                      ((let uu___6 =
                          (quaking_or_retrying &&
                             ((FStar_Options.interactive ()) ||
                                (FStar_Options.debug_any ())))
                            && (n > Prims.int_zero) in
                        if uu___6
                        then
                          let uu___7 =
                            if quaking
                            then
                              let uu___8 =
                                FStar_Compiler_Util.string_of_int nsucc in
                              FStar_Compiler_Util.format1
                                "succeeded %s times and " uu___8
                            else "" in
                          let uu___8 =
                            if quaking
                            then FStar_Compiler_Util.string_of_int nfail
                            else
                              (let uu___10 =
                                 FStar_Compiler_Util.string_of_int nfail in
                               Prims.op_Hat uu___10 " times") in
                          let uu___9 =
                            FStar_Compiler_Util.string_of_int (hi1 - n) in
                          FStar_Compiler_Util.print5
                            "%s: so far query %s %sfailed %s (%s runs remain)\n"
                            (if quaking then "Quake" else "Retry") name
                            uu___7 uu___8 uu___9
                        else ());
                       (let r = run_one (seed + n) in
                        let uu___6 =
                          match r with
                          | FStar_Pervasives.Inr cfg ->
                              (maybe_improve best_fuel cfg.query_fuel;
                               maybe_improve best_ifuel cfg.query_ifuel;
                               ((nsucc + Prims.int_one), nfail))
                          | uu___7 -> (nsucc, (nfail + Prims.int_one)) in
                        match uu___6 with
                        | (nsucc1, nfail1) -> (nsucc1, nfail1, (r :: rs)))))
           (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
           (hi1 - Prims.int_one) in
       match uu___1 with
       | (nsuccess, nfailures, rs) ->
           let total_ran = nsuccess + nfailures in
           (if quaking
            then
              (let fuel_msg =
                 let uu___3 =
                   let uu___4 = FStar_Compiler_Effect.op_Bang best_fuel in
                   let uu___5 = FStar_Compiler_Effect.op_Bang best_ifuel in
                   (uu___4, uu___5) in
                 match uu___3 with
                 | (FStar_Pervasives_Native.Some f,
                    FStar_Pervasives_Native.Some i) ->
                     let uu___4 = FStar_Compiler_Util.string_of_int f in
                     let uu___5 = FStar_Compiler_Util.string_of_int i in
                     FStar_Compiler_Util.format2
                       " (best fuel=%s, best ifuel=%s)" uu___4 uu___5
                 | (uu___4, uu___5) -> "" in
               let uu___3 = FStar_Compiler_Util.string_of_int nsuccess in
               let uu___4 = FStar_Compiler_Util.string_of_int total_ran in
               FStar_Compiler_Util.print5
                 "Quake: query %s succeeded %s/%s times%s%s\n" name uu___3
                 uu___4 (if total_ran < hi1 then " (early finish)" else "")
                 fuel_msg)
            else ();
            (let all_errs =
               FStar_Compiler_List.concatMap
                 (fun uu___3 ->
                    match uu___3 with
                    | FStar_Pervasives.Inr uu___4 -> []
                    | FStar_Pervasives.Inl es -> [es]) rs in
             {
               ok = (nsuccess >= lo1);
               nsuccess;
               lo = lo1;
               hi = hi1;
               errs = all_errs;
               quaking;
               quaking_or_retrying;
               total_ran
             })))
let (ask_solver :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_SMTEncoding_Term.error_labels ->
          FStar_SMTEncoding_Term.decl Prims.list ->
            FStar_SMTEncoding_Term.decl ->
              FStar_Syntax_Syntax.term ->
                FStar_SMTEncoding_Term.decl Prims.list ->
                  (query_settings Prims.list * answer))
  =
  fun can_split ->
    fun is_retry ->
      fun env ->
        fun all_labels ->
          fun prefix ->
            fun query ->
              fun query_term ->
                fun suffix ->
                  let uu___ =
                    make_solver_configs can_split is_retry env all_labels
                      prefix query query_term suffix in
                  match uu___ with
                  | (configs, next_hint) ->
                      let default_settings = FStar_Compiler_List.hd configs in
                      let skip =
                        ((FStar_Options.admit_smt_queries ()) ||
                           (FStar_TypeChecker_Env.too_early_in_prims env))
                          ||
                          (let uu___1 = FStar_Options.admit_except () in
                           match uu___1 with
                           | FStar_Pervasives_Native.Some id ->
                               if FStar_Compiler_Util.starts_with id "("
                               then
                                 let uu___2 = full_query_id default_settings in
                                 uu___2 <> id
                               else default_settings.query_name <> id
                           | FStar_Pervasives_Native.None -> false) in
                      let ans =
                        if skip
                        then
                          ((let uu___2 =
                              (FStar_Options.record_hints ()) &&
                                (FStar_Compiler_Effect.op_Bar_Greater
                                   next_hint FStar_Compiler_Util.is_some) in
                            if uu___2
                            then
                              let uu___3 =
                                FStar_Compiler_Effect.op_Bar_Greater
                                  next_hint FStar_Compiler_Util.must in
                              FStar_Compiler_Effect.op_Bar_Greater uu___3
                                store_hint
                            else ());
                           ans_ok)
                        else ask_solver_quake configs prefix in
                      (configs, ans)
let (report : FStar_TypeChecker_Env.env -> query_settings -> answer -> unit)
  =
  fun env ->
    fun default_settings ->
      fun a ->
        let nsuccess = a.nsuccess in
        let name = full_query_id default_settings in
        let lo = a.lo in
        let hi = a.hi in
        let total_ran = a.total_ran in
        let all_errs = a.errs in
        let quaking_or_retrying = a.quaking_or_retrying in
        let quaking = a.quaking in
        if nsuccess < lo
        then
          let uu___ =
            quaking_or_retrying &&
              (let uu___1 = FStar_Options.query_stats () in
               Prims.op_Negation uu___1) in
          (if uu___
           then
             let errors_to_report1 errs =
               errors_to_report
                 {
                   query_env = (default_settings.query_env);
                   query_decl = (default_settings.query_decl);
                   query_name = (default_settings.query_name);
                   query_index = (default_settings.query_index);
                   query_range = (default_settings.query_range);
                   query_fuel = (default_settings.query_fuel);
                   query_ifuel = (default_settings.query_ifuel);
                   query_rlimit = (default_settings.query_rlimit);
                   query_hint = (default_settings.query_hint);
                   query_errors = errs;
                   query_all_labels = (default_settings.query_all_labels);
                   query_suffix = (default_settings.query_suffix);
                   query_hash = (default_settings.query_hash);
                   query_can_be_split_and_retried =
                     (default_settings.query_can_be_split_and_retried);
                   query_term = (default_settings.query_term)
                 } in
             let errs = FStar_Compiler_List.map errors_to_report1 all_errs in
             let errs1 =
               let uu___1 =
                 FStar_Compiler_Effect.op_Bar_Greater errs
                   FStar_Compiler_List.flatten in
               FStar_Compiler_Effect.op_Bar_Greater uu___1 collect in
             let errs2 =
               FStar_Compiler_Effect.op_Bar_Greater errs1
                 (FStar_Compiler_List.map
                    (fun uu___1 ->
                       match uu___1 with
                       | ((e, m, r, ctx), n) ->
                           let m1 =
                             if n > Prims.int_one
                             then
                               let uu___2 =
                                 let uu___3 =
                                   FStar_Compiler_Util.string_of_int n in
                                 FStar_Compiler_Util.format1 " (%s times)"
                                   uu___3 in
                               Prims.op_Hat m uu___2
                             else m in
                           (e, m1, r, ctx))) in
             (FStar_Errors.add_errors errs2;
              if quaking
              then
                (let rng =
                   match FStar_Pervasives_Native.snd
                           env.FStar_TypeChecker_Env.qtbl_name_and_index
                   with
                   | FStar_Pervasives_Native.Some (l, uu___2) ->
                       FStar_Ident.range_of_lid l
                   | uu___2 -> FStar_Compiler_Range.dummyRange in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 = FStar_Compiler_Util.string_of_int nsuccess in
                     let uu___5 = FStar_Compiler_Util.string_of_int total_ran in
                     let uu___6 = FStar_Compiler_Util.string_of_int lo in
                     let uu___7 = FStar_Compiler_Util.string_of_int hi in
                     FStar_Compiler_Util.format6
                       "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                       name uu___4 uu___5 uu___6 uu___7
                       (if total_ran < hi then " (early abort)" else "") in
                   (FStar_Errors_Codes.Error_QuakeFailed, uu___3) in
                 FStar_TypeChecker_Err.log_issue env rng uu___2)
              else ())
           else
             (let report1 errs =
                report_errors
                  {
                    query_env = (default_settings.query_env);
                    query_decl = (default_settings.query_decl);
                    query_name = (default_settings.query_name);
                    query_index = (default_settings.query_index);
                    query_range = (default_settings.query_range);
                    query_fuel = (default_settings.query_fuel);
                    query_ifuel = (default_settings.query_ifuel);
                    query_rlimit = (default_settings.query_rlimit);
                    query_hint = (default_settings.query_hint);
                    query_errors = errs;
                    query_all_labels = (default_settings.query_all_labels);
                    query_suffix = (default_settings.query_suffix);
                    query_hash = (default_settings.query_hash);
                    query_can_be_split_and_retried =
                      (default_settings.query_can_be_split_and_retried);
                    query_term = (default_settings.query_term)
                  } in
              FStar_Compiler_List.iter report1 all_errs))
        else ()
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  smtopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  valid_intro: Prims.bool ;
  valid_elim: Prims.bool }
let (__proj__Mksolver_cfg__item__seed : solver_cfg -> Prims.int) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} -> seed
let (__proj__Mksolver_cfg__item__cliopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} -> cliopt
let (__proj__Mksolver_cfg__item__smtopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} -> smtopt
let (__proj__Mksolver_cfg__item__facts :
  solver_cfg -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} -> facts
let (__proj__Mksolver_cfg__item__valid_intro : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} ->
        valid_intro
let (__proj__Mksolver_cfg__item__valid_elim : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim;_} -> valid_elim
let (_last_cfg :
  solver_cfg FStar_Pervasives_Native.option FStar_Compiler_Effect.ref) =
  FStar_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (get_cfg : FStar_TypeChecker_Env.env -> solver_cfg) =
  fun env ->
    let uu___ = FStar_Options.z3_seed () in
    let uu___1 = FStar_Options.z3_cliopt () in
    let uu___2 = FStar_Options.z3_smtopt () in
    let uu___3 = FStar_Options.smtencoding_valid_intro () in
    let uu___4 = FStar_Options.smtencoding_valid_elim () in
    {
      seed = uu___;
      cliopt = uu___1;
      smtopt = uu___2;
      facts = (env.FStar_TypeChecker_Env.proof_ns);
      valid_intro = uu___3;
      valid_elim = uu___4
    }
let (save_cfg : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu___ =
      let uu___1 = get_cfg env in FStar_Pervasives_Native.Some uu___1 in
    FStar_Compiler_Effect.op_Colon_Equals _last_cfg uu___
let (maybe_refresh_solver : FStar_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu___ = FStar_Compiler_Effect.op_Bang _last_cfg in
    match uu___ with
    | FStar_Pervasives_Native.None -> save_cfg env
    | FStar_Pervasives_Native.Some cfg ->
        let uu___1 = let uu___2 = get_cfg env in cfg <> uu___2 in
        if uu___1
        then (save_cfg env; FStar_SMTEncoding_Z3.refresh ())
        else ()
let finally : 'a . (unit -> unit) -> (unit -> 'a) -> 'a =
  fun h ->
    fun f ->
      let r =
        try (fun uu___ -> match () with | () -> f ()) ()
        with | uu___ -> (h (); FStar_Compiler_Effect.raise uu___) in
      h (); r
let (encode_and_ask :
  Prims.bool ->
    Prims.bool ->
      (unit -> Prims.string) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env ->
          FStar_Syntax_Syntax.term -> (query_settings Prims.list * answer))
  =
  fun can_split ->
    fun is_retry ->
      fun use_env_msg ->
        fun tcenv ->
          fun q ->
            maybe_refresh_solver tcenv;
            (let uu___2 =
               let uu___3 =
                 let uu___4 = FStar_TypeChecker_Env.get_range tcenv in
                 FStar_Compiler_Effect.op_Less_Bar
                   FStar_Compiler_Range.string_of_range uu___4 in
               FStar_Compiler_Util.format1 "Starting query at %s" uu___3 in
             FStar_SMTEncoding_Encode.push uu___2);
            (let pop uu___2 =
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStar_TypeChecker_Env.get_range tcenv in
                   FStar_Compiler_Effect.op_Less_Bar
                     FStar_Compiler_Range.string_of_range uu___5 in
                 FStar_Compiler_Util.format1 "Ending query at %s" uu___4 in
               FStar_SMTEncoding_Encode.pop uu___3 in
             finally pop
               (fun uu___2 ->
                  let uu___3 =
                    FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
                  match uu___3 with
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
                           -> ([], ans_ok)
                       | uu___4 when tcenv1.FStar_TypeChecker_Env.admit ->
                           ([], ans_ok)
                       | FStar_SMTEncoding_Term.Assume uu___4 ->
                           ((let uu___6 =
                               (is_retry ||
                                  (let uu___7 =
                                     FStar_Options.split_queries () in
                                   uu___7 = FStar_Options.Always))
                                 && (FStar_Options.debug_any ()) in
                             if uu___6
                             then
                               let n = FStar_Compiler_List.length labels in
                               (if n <> Prims.int_one
                                then
                                  let uu___7 =
                                    FStar_TypeChecker_Env.get_range tcenv1 in
                                  let uu___8 =
                                    let uu___9 =
                                      FStar_Syntax_Print.term_to_string q in
                                    let uu___10 =
                                      FStar_SMTEncoding_Term.declToSmt "" qry in
                                    let uu___11 =
                                      FStar_Compiler_Util.string_of_int n in
                                    FStar_Compiler_Util.format3
                                      "Encoded split query %s\nto %s\nwith %s labels"
                                      uu___9 uu___10 uu___11 in
                                  FStar_Errors.diag uu___7 uu___8
                                else ())
                             else ());
                            ask_solver can_split is_retry tcenv1 labels
                              prefix qry q suffix)
                       | uu___4 -> failwith "Impossible")))
let (do_solve :
  Prims.bool ->
    Prims.bool ->
      (unit -> Prims.string) FStar_Pervasives_Native.option ->
        FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun can_split ->
    fun is_retry ->
      fun use_env_msg ->
        fun tcenv ->
          fun q ->
            let ans_opt =
              try
                (fun uu___ ->
                   match () with
                   | () ->
                       let uu___1 =
                         encode_and_ask can_split is_retry use_env_msg tcenv
                           q in
                       FStar_Pervasives_Native.Some uu___1) ()
              with
              | FStar_SMTEncoding_Env.Inner_let_rec names ->
                  ((let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            FStar_Compiler_List.map
                              FStar_Pervasives_Native.fst names in
                          FStar_String.concat "," uu___5 in
                        FStar_Compiler_Util.format1
                          "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                          uu___4 in
                      (FStar_Errors_Codes.Error_NonTopRecFunctionNotFullyEncoded,
                        uu___3) in
                    FStar_TypeChecker_Err.log_issue tcenv
                      tcenv.FStar_TypeChecker_Env.range uu___2);
                   FStar_Pervasives_Native.None) in
            match ans_opt with
            | FStar_Pervasives_Native.Some (default_settings::uu___, ans)
                when Prims.op_Negation ans.ok ->
                report tcenv default_settings ans
            | FStar_Pervasives_Native.Some (uu___, ans) when ans.ok -> ()
            | FStar_Pervasives_Native.Some ([], ans) when
                Prims.op_Negation ans.ok ->
                failwith "impossible: bad answer from encode_and_ask"
            | FStar_Pervasives_Native.None -> ()
let (split_and_solve :
  Prims.bool ->
    (unit -> Prims.string) FStar_Pervasives_Native.option ->
      FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun retrying ->
    fun use_env_msg ->
      fun tcenv ->
        fun q ->
          let goals =
            let uu___ = FStar_TypeChecker_Env.split_smt_query tcenv q in
            match uu___ with
            | FStar_Pervasives_Native.None ->
                failwith "Impossible: split_query callback is not set"
            | FStar_Pervasives_Native.Some goals1 -> goals1 in
          FStar_Compiler_Effect.op_Bar_Greater goals
            (FStar_Compiler_List.iter
               (fun uu___1 ->
                  match uu___1 with
                  | (env, goal) ->
                      do_solve false retrying use_env_msg env goal));
          (let uu___1 =
             (let uu___2 = FStar_Errors.get_err_count () in
              uu___2 = Prims.int_zero) && retrying in
           if uu___1
           then
             FStar_TypeChecker_Err.log_issue tcenv
               tcenv.FStar_TypeChecker_Env.range
               (FStar_Errors_Codes.Warning_SplitAndRetryQueries,
                 "The verification condition succeeded after splitting it to localize potential errors, although the original non-split verification condition failed. If you want to rely on splitting queries for verifying your program please use the '--split_queries always' option rather than relying on it implicitly.")
           else ())
let disable_quake_for : 'a . (unit -> 'a) -> 'a =
  fun f ->
    FStar_Options.with_saved_options
      (fun uu___ ->
         FStar_Options.set_option "quake_hi"
           (FStar_Options.Int Prims.int_one);
         f ())
let (do_solve_maybe_split :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu___ = FStar_Options.split_queries () in
        match uu___ with
        | FStar_Options.No -> do_solve false false use_env_msg tcenv q
        | FStar_Options.OnFailure ->
            let can_split =
              let uu___1 =
                let uu___2 = FStar_Options.quake_hi () in
                uu___2 > Prims.int_one in
              Prims.op_Negation uu___1 in
            (try
               (fun uu___1 ->
                  match () with
                  | () -> do_solve can_split false use_env_msg tcenv q) ()
             with
             | SplitQueryAndRetry -> split_and_solve true use_env_msg tcenv q)
        | FStar_Options.Always -> split_and_solve false use_env_msg tcenv q
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
              FStar_Compiler_Util.format1
                "Q = %s\nA query could not be solved internally, and --no_smt was given"
                uu___3 in
            (FStar_Errors_Codes.Error_NoSMTButNeeded, uu___2) in
          FStar_TypeChecker_Err.log_issue tcenv
            tcenv.FStar_TypeChecker_Env.range uu___1
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStar_TypeChecker_Env.current_module tcenv in
               FStar_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStar_Profiling.profile
             (fun uu___3 -> do_solve_maybe_split use_env_msg tcenv q) uu___2
             "FStar.SMTEncoding.solve_top_level")
let (solve_sync :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> answer)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu___ = FStar_Options.no_smt () in
        if uu___
        then ans_fail
        else
          (let go uu___2 =
             let uu___3 =
               disable_quake_for
                 (fun uu___4 ->
                    encode_and_ask false false use_env_msg tcenv q) in
             match uu___3 with | (_cfgs, ans) -> ans in
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_TypeChecker_Env.current_module tcenv in
               FStar_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStar_Profiling.profile go uu___2
             "FStar.SMTEncoding.solve_sync_top_level")
let (solve_sync_bool :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun use_env_msg ->
    fun tcenv -> fun q -> let ans = solve_sync use_env_msg tcenv q in ans.ok
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
    FStar_TypeChecker_Env.spinoff_strictly_positive_goals =
      FStar_Pervasives_Native.None;
    FStar_TypeChecker_Env.handle_smt_goal = (fun e -> fun g -> [(e, g)]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.solve_sync = solve_sync_bool;
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
    FStar_TypeChecker_Env.spinoff_strictly_positive_goals =
      FStar_Pervasives_Native.None;
    FStar_TypeChecker_Env.handle_smt_goal = (fun e -> fun g -> [(e, g)]);
    FStar_TypeChecker_Env.solve =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> ());
    FStar_TypeChecker_Env.solve_sync =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> false);
    FStar_TypeChecker_Env.finish = (fun uu___ -> ());
    FStar_TypeChecker_Env.refresh = (fun uu___ -> ())
  }
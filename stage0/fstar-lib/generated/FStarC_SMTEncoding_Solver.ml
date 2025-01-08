open Prims
exception SplitQueryAndRetry 
let (uu___is_SplitQueryAndRetry : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | SplitQueryAndRetry -> true | uu___ -> false
let (dbg_SMTQuery : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SMTQuery"
let (dbg_SMTFail : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Debug.get_toggle "SMTFail"
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
  FStarC_Compiler_Hints.hints FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStarC_Compiler_Hints.hints FStar_Pervasives_Native.option
    FStarC_Compiler_Effect.ref)
  = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (use_hints : unit -> Prims.bool) =
  fun uu___ ->
    (FStarC_Options.use_hints ()) &&
      (let uu___1 = FStarC_Options_Ext.get "context_pruning" in uu___1 = "")
let initialize_hints_db : 'uuuuu . Prims.string -> 'uuuuu -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu___1 = FStarC_Options.record_hints () in
       if uu___1
       then
         FStarC_Compiler_Effect.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let norm_src_filename =
         FStarC_Compiler_Util.normalize_file_path src_filename in
       let val_filename = FStarC_Options.hint_file_for_src norm_src_filename in
       let uu___1 = FStarC_Compiler_Hints.read_hints val_filename in
       match uu___1 with
       | FStarC_Compiler_Hints.HintsOK hints ->
           let expected_digest =
             FStarC_Compiler_Util.digest_of_file norm_src_filename in
           ((let uu___3 = FStarC_Options.hint_info () in
             if uu___3
             then
               FStarC_Compiler_Util.print3 "(%s) digest is %s from %s.\n"
                 norm_src_filename
                 (if
                    hints.FStarC_Compiler_Hints.module_digest =
                      expected_digest
                  then "valid; using hints"
                  else "invalid; using potentially stale hints") val_filename
             else ());
            FStarC_Compiler_Effect.op_Colon_Equals replaying_hints
              (FStar_Pervasives_Native.Some
                 (hints.FStarC_Compiler_Hints.hints)))
       | FStarC_Compiler_Hints.MalformedJson ->
           let uu___3 = use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Compiler_Util.format1
                     "Malformed JSON hints file: %s; ran without hints"
                     val_filename in
                 FStarC_Errors_Msg.text uu___6 in
               [uu___5] in
             FStarC_Errors.log_issue0
               FStarC_Errors_Codes.Warning_CouldNotReadHints ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___4)
           else ()
       | FStarC_Compiler_Hints.UnableToOpen ->
           let uu___3 = use_hints () in
           if uu___3
           then
             let uu___4 =
               let uu___5 =
                 let uu___6 =
                   FStarC_Compiler_Util.format1
                     "Unable to open hints file: %s; ran without hints"
                     val_filename in
                 FStarC_Errors_Msg.text uu___6 in
               [uu___5] in
             FStarC_Errors.log_issue0
               FStarC_Errors_Codes.Warning_CouldNotReadHints ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
               (Obj.magic uu___4)
           else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu___1 = FStarC_Options.record_hints () in
     if uu___1
     then
       let hints =
         let uu___2 = FStarC_Compiler_Effect.op_Bang recorded_hints in
         FStarC_Compiler_Option.get uu___2 in
       let hints_db =
         let uu___2 = FStarC_Compiler_Util.digest_of_file src_filename in
         {
           FStarC_Compiler_Hints.module_digest = uu___2;
           FStarC_Compiler_Hints.hints = hints
         } in
       let norm_src_filename =
         FStarC_Compiler_Util.normalize_file_path src_filename in
       let val_filename = FStarC_Options.hint_file_for_src norm_src_filename in
       FStarC_Compiler_Hints.write_hints val_filename hints_db
     else ());
    FStarC_Compiler_Effect.op_Colon_Equals recorded_hints
      FStar_Pervasives_Native.None;
    FStarC_Compiler_Effect.op_Colon_Equals replaying_hints
      FStar_Pervasives_Native.None
let with_hints_db : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun fname ->
    fun f ->
      initialize_hints_db fname false;
      (let result = f () in finalize_hints_db fname; result)
type errors =
  {
  error_reason: Prims.string ;
  error_rlimit: Prims.int ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages: FStarC_Errors.error Prims.list }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_reason
let (__proj__Mkerrors__item__error_rlimit : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_rlimit
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_fuel
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_ifuel
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_hint
let (__proj__Mkerrors__item__error_messages :
  errors -> FStarC_Errors.error Prims.list) =
  fun projectee ->
    match projectee with
    | { error_reason; error_rlimit; error_fuel; error_ifuel; error_hint;
        error_messages;_} -> error_messages
let (error_to_short_string : errors -> Prims.string) =
  fun err ->
    let uu___ =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_rlimit in
    let uu___1 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_fuel in
    let uu___2 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_ifuel in
    FStarC_Compiler_Util.format5 "%s (rlimit=%s; fuel=%s; ifuel=%s%s)"
      err.error_reason uu___ uu___1 uu___2
      (if FStarC_Compiler_Option.isSome err.error_hint
       then "; with hint"
       else "")
let (error_to_is_timeout : errors -> Prims.string Prims.list) =
  fun err ->
    if FStarC_Compiler_Util.ends_with err.error_reason "canceled"
    then
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            err.error_rlimit in
        let uu___2 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            err.error_fuel in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            err.error_ifuel in
        FStarC_Compiler_Util.format5
          "timeout (rlimit=%s; fuel=%s; ifuel=%s; %s)" err.error_reason
          uu___1 uu___2 uu___3
          (if FStarC_Compiler_Option.isSome err.error_hint
           then "with hint"
           else "") in
      [uu___]
    else []
type query_settings =
  {
  query_env: FStarC_SMTEncoding_Env.env_t ;
  query_decl: FStarC_SMTEncoding_Term.decl ;
  query_name: Prims.string ;
  query_index: Prims.int ;
  query_range: FStarC_Compiler_Range_Type.range ;
  query_fuel: Prims.int ;
  query_ifuel: Prims.int ;
  query_rlimit: Prims.int ;
  query_hint:
    FStarC_SMTEncoding_UnsatCore.unsat_core FStar_Pervasives_Native.option ;
  query_errors: errors Prims.list ;
  query_all_labels: FStarC_SMTEncoding_Term.error_labels ;
  query_suffix: FStarC_SMTEncoding_Term.decl Prims.list ;
  query_hash: Prims.string FStar_Pervasives_Native.option ;
  query_can_be_split_and_retried: Prims.bool ;
  query_term: FStarC_Syntax_Syntax.term }
let (__proj__Mkquery_settings__item__query_env :
  query_settings -> FStarC_SMTEncoding_Env.env_t) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_env
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStarC_SMTEncoding_Term.decl) =
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
  query_settings -> FStarC_Compiler_Range_Type.range) =
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
  query_settings ->
    FStarC_SMTEncoding_UnsatCore.unsat_core FStar_Pervasives_Native.option)
  =
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
  query_settings -> FStarC_SMTEncoding_Term.error_labels) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_all_labels
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStarC_SMTEncoding_Term.decl Prims.list) =
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
  query_settings -> FStarC_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;
        query_can_be_split_and_retried; query_term;_} -> query_term
let (convert_rlimit : Prims.int -> Prims.int) =
  fun r ->
    let uu___ =
      let uu___1 = FStarC_Options.z3_version () in
      FStarC_Compiler_Misc.version_ge uu___1 "4.12.3" in
    if uu___
    then (Prims.parse_int "500000") * r
    else (Prims.parse_int "544656") * r
let (with_fuel_and_diagnostics :
  query_settings ->
    FStarC_SMTEncoding_Term.decl Prims.list ->
      FStarC_SMTEncoding_Term.decl Prims.list)
  =
  fun settings ->
    fun label_assumptions ->
      let n = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = convert_rlimit settings.query_rlimit in
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Compiler_Util.string_of_int n in
            let uu___4 = FStarC_Compiler_Util.string_of_int i in
            FStarC_Compiler_Util.format2 "<fuel='%s' ifuel='%s'>" uu___3
              uu___4 in
          FStarC_SMTEncoding_Term.Caption uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 =
                  let uu___7 = FStarC_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu___8 = FStarC_SMTEncoding_Term.n_fuel n in
                  (uu___7, uu___8) in
                FStarC_SMTEncoding_Util.mkEq uu___6 in
              (uu___5, FStar_Pervasives_Native.None, "@MaxFuel_assumption") in
            FStarC_SMTEncoding_Util.mkAssume uu___4 in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    let uu___9 =
                      FStarC_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu___10 = FStarC_SMTEncoding_Term.n_fuel i in
                    (uu___9, uu___10) in
                  FStarC_SMTEncoding_Util.mkEq uu___8 in
                (uu___7, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStarC_SMTEncoding_Util.mkAssume uu___6 in
            [uu___5; settings.query_decl] in
          uu___3 :: uu___4 in
        uu___1 :: uu___2 in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_Compiler_Util.string_of_int rlimit in
                ("rlimit", uu___6) in
              FStarC_SMTEncoding_Term.SetOption uu___5 in
            [uu___4;
            FStarC_SMTEncoding_Term.CheckSat;
            FStarC_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStarC_SMTEncoding_Term.GetReasonUnknown;
            FStarC_SMTEncoding_Term.GetUnsatCore] in
          let uu___4 =
            let uu___5 =
              let uu___6 =
                (FStarC_Options.print_z3_statistics ()) ||
                  (FStarC_Options.query_stats ()) in
              if uu___6 then [FStarC_SMTEncoding_Term.GetStatistics] else [] in
            FStarC_Compiler_List.op_At uu___5 settings.query_suffix in
          FStarC_Compiler_List.op_At uu___3 uu___4 in
        FStarC_Compiler_List.op_At label_assumptions uu___2 in
      FStarC_Compiler_List.op_At uu___ uu___1
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStarC_Compiler_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string ->
    Prims.int -> FStarC_Compiler_Hints.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu___ = FStarC_Compiler_Effect.op_Bang replaying_hints in
      match uu___ with
      | FStar_Pervasives_Native.Some hints ->
          FStarC_Compiler_Util.find_map hints
            (fun uu___1 ->
               match uu___1 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStarC_Compiler_Hints.hint_name = qname) &&
                     (hint.FStarC_Compiler_Hints.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu___2 -> FStar_Pervasives_Native.None)
      | uu___1 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStarC_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStarC_SMTEncoding_Z3.z3result_status with
      | FStarC_SMTEncoding_Z3.UNSAT uu___ -> FStar_Pervasives_Native.None
      | uu___ ->
          let uu___1 =
            FStarC_SMTEncoding_Z3.status_string_and_errors
              z3result.FStarC_SMTEncoding_Z3.z3result_status in
          (match uu___1 with
           | (msg, error_labels) ->
               let err =
                 let uu___2 =
                   FStarC_Compiler_List.map
                     (fun uu___3 ->
                        match uu___3 with
                        | (uu___4, x, y) ->
                            let uu___5 = FStarC_Errors.get_ctx () in
                            (FStarC_Errors_Codes.Error_Z3SolverError, x, y,
                              uu___5)) error_labels in
                 {
                   error_reason = msg;
                   error_rlimit = (settings.query_rlimit);
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu___2
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStarC_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu___ =
        (used_hint settings) && (FStarC_Options.detail_hint_replay ()) in
      if uu___
      then
        match z3result.FStarC_SMTEncoding_Z3.z3result_status with
        | FStarC_SMTEncoding_Z3.UNSAT uu___1 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let uu___1 =
                with_fuel_and_diagnostics settings label_assumptions in
              let uu___2 =
                let uu___3 =
                  FStarC_Compiler_Util.string_of_int settings.query_index in
                FStarC_Compiler_Util.format2 "(%s, %s)" settings.query_name
                  uu___3 in
              FStarC_SMTEncoding_Z3.ask settings.query_range
                settings.query_hash settings.query_all_labels uu___1 uu___2
                false FStar_Pervasives_Native.None in
            FStarC_SMTEncoding_ErrorReporting.detail_errors true
              (settings.query_env).FStarC_SMTEncoding_Env.tcenv
              settings.query_all_labels ask_z3
      else ()
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs ->
    FStarC_Compiler_List.tryFind
      (fun err -> match err.error_messages with | [] -> false | uu___ -> true)
      errs
let (errors_to_report :
  Prims.bool -> query_settings -> FStarC_Errors.error Prims.list) =
  fun tried_recovery ->
    fun settings ->
      let format_smt_error msg =
        let d =
          let uu___ = FStarC_Pprint.doc_of_string "SMT solver says:" in
          let uu___1 =
            let uu___2 = FStarC_Errors_Msg.sublist FStarC_Pprint.empty msg in
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Pprint.doc_of_string "Note:" in
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Errors_Msg.text
                        "'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit" in
                    let uu___9 =
                      let uu___10 =
                        FStarC_Errors_Msg.text
                          "'incomplete quantifiers' means Z3 could not prove the query, so try to spell out your proof out in greater detail, increase fuel or ifuel" in
                      let uu___11 =
                        let uu___12 =
                          FStarC_Errors_Msg.text
                            "'unknown' means Z3 provided no further reason for the proof failing" in
                        [uu___12] in
                      uu___10 :: uu___11 in
                    uu___8 :: uu___9 in
                  FStarC_Errors_Msg.bulleted uu___7 in
                FStarC_Pprint.op_Hat_Hat uu___5 uu___6 in
              FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___4 in
            FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
          FStarC_Pprint.op_Hat_Hat uu___ uu___1 in
        [d] in
      let recovery_failed_msg =
        if tried_recovery
        then
          let uu___ =
            FStarC_Errors_Msg.text
              "This query was retried due to the --proof_recovery option, yet it\n               still failed on all attempts." in
          [uu___]
        else [] in
      let basic_errors =
        let smt_error =
          let uu___ = FStarC_Options.query_stats () in
          if uu___
          then
            let uu___1 =
              let uu___2 =
                FStarC_Compiler_List.map error_to_short_string
                  settings.query_errors in
              FStarC_Compiler_List.map FStarC_Pprint.doc_of_string uu___2 in
            format_smt_error uu___1
          else
            (let uu___2 =
               FStarC_Compiler_List.fold_left
                 (fun uu___3 ->
                    fun err ->
                      match uu___3 with
                      | (ic, cc, uc, bc) ->
                          let err1 =
                            FStarC_Compiler_Util.substring_from
                              err.error_reason
                              (FStarC_Compiler_String.length
                                 "unknown because ") in
                          if
                            FStarC_Compiler_Util.starts_with err1
                              "(incomplete"
                          then ((ic + Prims.int_one), cc, uc, bc)
                          else
                            if
                              ((FStarC_Compiler_Util.starts_with err1
                                  "canceled")
                                 ||
                                 (FStarC_Compiler_Util.starts_with err1
                                    "(resource"))
                                ||
                                (FStarC_Compiler_Util.starts_with err1
                                   "timeout")
                            then (ic, (cc + Prims.int_one), uc, bc)
                            else
                              if
                                FStarC_Compiler_Util.starts_with err1
                                  "Overflow encountered when expanding old_vector"
                              then (ic, cc, uc, (bc + Prims.int_one))
                              else (ic, cc, (uc + Prims.int_one), bc))
                 (Prims.int_zero, Prims.int_zero, Prims.int_zero,
                   Prims.int_zero) settings.query_errors in
             match uu___2 with
             | (incomplete_count, canceled_count, unknown_count,
                z3_overflow_bug_count) ->
                 (if z3_overflow_bug_count > Prims.int_zero
                  then
                    (let uu___4 =
                       let uu___5 =
                         FStarC_Errors_Msg.text
                           "Z3 ran into an internal overflow while trying to prove this query." in
                       let uu___6 =
                         let uu___7 =
                           FStarC_Errors_Msg.text
                             "Try breaking it down, or using --split_queries." in
                         [uu___7] in
                       uu___5 :: uu___6 in
                     FStarC_Errors.log_issue
                       FStarC_Class_HasRange.hasRange_range
                       settings.query_range
                       FStarC_Errors_Codes.Warning_UnexpectedZ3Stderr ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___4))
                  else ();
                  (let base =
                     match (incomplete_count, canceled_count, unknown_count)
                     with
                     | (uu___4, uu___5, uu___6) when
                         ((uu___5 = Prims.int_zero) &&
                            (uu___6 = Prims.int_zero))
                           && (incomplete_count > Prims.int_zero)
                         ->
                         let uu___7 =
                           FStarC_Errors_Msg.text
                             "The SMT solver could not prove the query. Use --query_stats for more details." in
                         [uu___7]
                     | (uu___4, uu___5, uu___6) when
                         ((uu___4 = Prims.int_zero) &&
                            (uu___6 = Prims.int_zero))
                           && (canceled_count > Prims.int_zero)
                         ->
                         let uu___7 =
                           FStarC_Errors_Msg.text
                             "The SMT query timed out, you might want to increase the rlimit" in
                         [uu___7]
                     | (uu___4, uu___5, uu___6) ->
                         let uu___7 =
                           FStarC_Errors_Msg.text
                             "Try with --query_stats to get more details" in
                         [uu___7] in
                   FStarC_Compiler_List.op_At base recovery_failed_msg))) in
        let uu___ =
          let uu___1 = find_localized_errors settings.query_errors in
          (uu___1, (settings.query_all_labels)) in
        match uu___ with
        | (FStar_Pervasives_Native.Some err, uu___1) ->
            FStarC_TypeChecker_Err.errors_smt_detail
              (settings.query_env).FStarC_SMTEncoding_Env.tcenv
              err.error_messages smt_error
        | (FStar_Pervasives_Native.None, (uu___1, msg, rng)::[]) ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Errors.get_ctx () in
                (FStarC_Errors_Codes.Error_Z3SolverError, msg, rng, uu___4) in
              [uu___3] in
            FStarC_TypeChecker_Err.errors_smt_detail
              (settings.query_env).FStarC_SMTEncoding_Env.tcenv uu___2
              recovery_failed_msg
        | (FStar_Pervasives_Native.None, uu___1) ->
            if settings.query_can_be_split_and_retried
            then FStarC_Compiler_Effect.raise SplitQueryAndRetry
            else
              (let l = FStarC_Compiler_List.length settings.query_all_labels in
               let labels =
                 if l = Prims.int_zero
                 then
                   let dummy_fv =
                     FStarC_SMTEncoding_Term.mk_fv
                       ("", FStarC_SMTEncoding_Term.dummy_sort) in
                   let msg =
                     let uu___3 =
                       let uu___4 =
                         FStarC_Errors_Msg.text
                           "Failed to prove the following goal, although it appears to be trivial:" in
                       let uu___5 =
                         FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                           settings.query_term in
                       FStarC_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
                     [uu___3] in
                   let range =
                     FStarC_TypeChecker_Env.get_range
                       (settings.query_env).FStarC_SMTEncoding_Env.tcenv in
                   [(dummy_fv, msg, range)]
                 else
                   if l > Prims.int_one
                   then
                     ((let uu___5 =
                         let uu___6 = FStarC_Options.split_queries () in
                         uu___6 <> FStarC_Options.No in
                       if uu___5
                       then
                         let uu___6 =
                           FStarC_TypeChecker_Env.get_range
                             (settings.query_env).FStarC_SMTEncoding_Env.tcenv in
                         FStarC_TypeChecker_Err.log_issue_text
                           (settings.query_env).FStarC_SMTEncoding_Env.tcenv
                           uu___6
                           (FStarC_Errors_Codes.Warning_SplitAndRetryQueries,
                             "The verification condition was to be split into several atomic sub-goals, but this query has multiple sub-goals---the error report may be inaccurate")
                       else ());
                      settings.query_all_labels)
                   else settings.query_all_labels in
               FStarC_Compiler_List.collect
                 (fun uu___3 ->
                    match uu___3 with
                    | (uu___4, msg, rng) ->
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStarC_Errors.get_ctx () in
                            (FStarC_Errors_Codes.Error_Z3SolverError, msg,
                              rng, uu___7) in
                          [uu___6] in
                        FStarC_TypeChecker_Err.errors_smt_detail
                          (settings.query_env).FStarC_SMTEncoding_Env.tcenv
                          uu___5 recovery_failed_msg) labels) in
      (let uu___ = FStarC_Options.detail_errors () in
       if uu___
       then
         let initial_fuel =
           let uu___1 = FStarC_Options.initial_fuel () in
           let uu___2 = FStarC_Options.initial_ifuel () in
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
           let uu___2 =
             let uu___3 =
               FStarC_Compiler_Util.string_of_int settings.query_index in
             FStarC_Compiler_Util.format2 "(%s, %s)" settings.query_name
               uu___3 in
           FStarC_SMTEncoding_Z3.ask settings.query_range settings.query_hash
             settings.query_all_labels uu___1 uu___2 false
             FStar_Pervasives_Native.None in
         FStarC_SMTEncoding_ErrorReporting.detail_errors false
           (settings.query_env).FStarC_SMTEncoding_Env.tcenv
           settings.query_all_labels ask_z3
       else ());
      basic_errors
let (report_errors : Prims.bool -> query_settings -> unit) =
  fun tried_recovery ->
    fun qry_settings ->
      let uu___ = errors_to_report tried_recovery qry_settings in
      FStarC_Errors.add_errors uu___
type unique_string_accumulator =
  {
  add: Prims.string -> unit ;
  get: unit -> Prims.string Prims.list ;
  clear: unit -> unit }
let (__proj__Mkunique_string_accumulator__item__add :
  unique_string_accumulator -> Prims.string -> unit) =
  fun projectee -> match projectee with | { add; get; clear;_} -> add
let (__proj__Mkunique_string_accumulator__item__get :
  unique_string_accumulator -> unit -> Prims.string Prims.list) =
  fun projectee -> match projectee with | { add; get; clear;_} -> get
let (__proj__Mkunique_string_accumulator__item__clear :
  unique_string_accumulator -> unit -> unit) =
  fun projectee -> match projectee with | { add; get; clear;_} -> clear
let (mk_unique_string_accumulator : unit -> unique_string_accumulator) =
  fun uu___ ->
    let strings = FStarC_Compiler_Util.mk_ref [] in
    let add m =
      let ms = FStarC_Compiler_Effect.op_Bang strings in
      if FStarC_Compiler_List.contains m ms
      then ()
      else FStarC_Compiler_Effect.op_Colon_Equals strings (m :: ms) in
    let get uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang strings in
      FStarC_Compiler_Util.sort_with FStarC_Compiler_String.compare uu___2 in
    let clear uu___1 = FStarC_Compiler_Effect.op_Colon_Equals strings [] in
    { add; get; clear }
let (query_info : query_settings -> FStarC_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let process_unsat_core core =
        let uu___ = mk_unique_string_accumulator () in
        match uu___ with
        | { add = add_module_name; get = get_module_names; clear = uu___1;_}
            ->
            let add_module_name1 s = add_module_name s in
            let uu___2 = mk_unique_string_accumulator () in
            (match uu___2 with
             | { add = add_discarded_name; get = get_discarded_names;
                 clear = uu___3;_} ->
                 let parse_axiom_name s =
                   let chars = FStarC_Compiler_String.list_of_string s in
                   let first_upper_index =
                     FStarC_Compiler_Util.try_find_index
                       FStarC_Compiler_Util.is_upper chars in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStarC_Compiler_Util.substring_from s
                           first_upper_index1 in
                       let components =
                         FStarC_Compiler_String.split [46] name_and_suffix in
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
                         let s2 = FStarC_Compiler_Util.trim_string s1 in
                         let sopt =
                           FStarC_Compiler_Util.find_map excluded_suffixes
                             (fun sfx ->
                                if FStarC_Compiler_Util.contains s2 sfx
                                then
                                  let uu___4 =
                                    FStarC_Compiler_List.hd
                                      (FStarC_Compiler_Util.split s2 sfx) in
                                  FStar_Pervasives_Native.Some uu___4
                                else FStar_Pervasives_Native.None) in
                         match sopt with
                         | FStar_Pervasives_Native.None ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3] in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu___4 ->
                             let uu___5 =
                               FStarC_Compiler_Util.prefix components in
                             (match uu___5 with
                              | (lident, last) ->
                                  let components2 =
                                    let uu___6 = exclude_suffix last in
                                    FStarC_Compiler_List.op_At lident uu___6 in
                                  let module_name =
                                    FStarC_Compiler_Util.prefix_until
                                      (fun s1 ->
                                         let uu___6 =
                                           let uu___7 =
                                             FStarC_Compiler_Util.char_at s1
                                               Prims.int_zero in
                                           FStarC_Compiler_Util.is_upper
                                             uu___7 in
                                         Prims.op_Negation uu___6)
                                      components2 in
                                  ((match module_name with
                                    | FStar_Pervasives_Native.None -> ()
                                    | FStar_Pervasives_Native.Some
                                        (m, uu___7, uu___8) ->
                                        add_module_name1
                                          (FStarC_Compiler_String.concat "."
                                             m));
                                   components2)) in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else [FStarC_Compiler_String.concat "." components1] in
                 let should_log =
                   (FStarC_Options.hint_info ()) ||
                     (FStarC_Options.query_stats ()) in
                 let maybe_log f = if should_log then f () else () in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      maybe_log
                        (fun uu___4 ->
                           FStarC_Compiler_Util.print_string
                             "no unsat core\n")
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 =
                        FStarC_Compiler_List.collect parse_axiom_name core1 in
                      maybe_log
                        (fun uu___4 ->
                           (let uu___6 =
                              let uu___7 = get_module_names () in
                              FStarC_Compiler_String.concat
                                "\nZ3 Proof Stats:\t" uu___7 in
                            FStarC_Compiler_Util.print1
                              "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                              uu___6);
                           FStarC_Compiler_Util.print1
                             "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                             (FStarC_Compiler_String.concat
                                "\nZ3 Proof Stats (Detail 1):\t" core2);
                           (let uu___7 =
                              let uu___8 = get_discarded_names () in
                              FStarC_Compiler_String.concat ", " uu___8 in
                            FStarC_Compiler_Util.print1
                              "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                              uu___7)))) in
      let uu___ =
        (FStarC_Options.hint_info ()) || (FStarC_Options.query_stats ()) in
      if uu___
      then
        let uu___1 =
          FStarC_SMTEncoding_Z3.status_string_and_errors
            z3result.FStarC_SMTEncoding_Z3.z3result_status in
        match uu___1 with
        | (status_string, errs) ->
            let at_log_file =
              match z3result.FStarC_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some s -> Prims.strcat "@" s in
            let uu___2 =
              match z3result.FStarC_SMTEncoding_Z3.z3result_status with
              | FStarC_SMTEncoding_Z3.UNSAT core ->
                  let uu___3 =
                    FStarC_Compiler_Util.colorize_green "succeeded" in
                  (uu___3, core)
              | uu___3 ->
                  let uu___4 =
                    FStarC_Compiler_Util.colorize_red
                      (Prims.strcat "failed {reason-unknown="
                         (Prims.strcat status_string "}")) in
                  (uu___4, FStar_Pervasives_Native.None) in
            (match uu___2 with
             | (tag, core) ->
                 let range =
                   let uu___3 =
                     let uu___4 =
                       FStarC_Class_Show.show
                         FStarC_Compiler_Range_Ops.showable_range
                         settings.query_range in
                     Prims.strcat uu___4 (Prims.strcat at_log_file ")") in
                   Prims.strcat "(" uu___3 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu___3 = FStarC_Options.query_stats () in
                   if uu___3
                   then
                     let f k v a =
                       Prims.strcat a
                         (Prims.strcat k
                            (Prims.strcat "=" (Prims.strcat v " "))) in
                     let str =
                       FStarC_Compiler_Util.smap_fold
                         z3result.FStarC_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu___4 =
                       FStarC_Compiler_Util.substring str Prims.int_zero
                         ((FStarC_Compiler_String.length str) - Prims.int_one) in
                     Prims.strcat uu___4 "}"
                   else "" in
                 ((let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           FStarC_Class_Show.show
                             FStarC_Class_Show.showable_int
                             settings.query_index in
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStarC_Class_Show.show
                                   FStarC_Class_Show.showable_int
                                   z3result.FStarC_SMTEncoding_Z3.z3result_time in
                               let uu___12 =
                                 let uu___13 =
                                   FStarC_Class_Show.show
                                     FStarC_Class_Show.showable_int
                                     settings.query_fuel in
                                 let uu___14 =
                                   let uu___15 =
                                     FStarC_Class_Show.show
                                       FStarC_Class_Show.showable_int
                                       settings.query_ifuel in
                                   let uu___16 =
                                     let uu___17 =
                                       FStarC_Class_Show.show
                                         FStarC_Class_Show.showable_int
                                         settings.query_rlimit in
                                     [uu___17] in
                                   uu___15 :: uu___16 in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             used_hint_tag :: uu___10 in
                           tag :: uu___9 in
                         uu___7 :: uu___8 in
                       (settings.query_name) :: uu___6 in
                     range :: uu___5 in
                   FStarC_Compiler_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s\n"
                     uu___4);
                  (let uu___5 = FStarC_Options.print_z3_statistics () in
                   if uu___5 then process_unsat_core core else ());
                  FStarC_Compiler_List.iter
                    (fun uu___5 ->
                       match uu___5 with
                       | (uu___6, msg, range1) ->
                           let msg1 =
                             if used_hint settings
                             then
                               let uu___7 =
                                 FStarC_Pprint.doc_of_string
                                   "Hint-replay failed" in
                               uu___7 :: msg
                             else msg in
                           FStarC_Errors.log_issue
                             FStarC_Class_HasRange.hasRange_range range1
                             FStarC_Errors_Codes.Warning_HitReplayFailed ()
                             (Obj.magic
                                FStarC_Errors_Msg.is_error_message_list_doc)
                             (Obj.magic msg1)) errs))
      else
        (let uu___2 =
           let uu___3 = FStarC_Options_Ext.get "profile_context" in
           uu___3 <> "" in
         if uu___2
         then
           match z3result.FStarC_SMTEncoding_Z3.z3result_status with
           | FStarC_SMTEncoding_Z3.UNSAT core -> process_unsat_core core
           | uu___3 -> ()
         else ())
let (store_hint : FStarC_Compiler_Hints.hint -> unit) =
  fun hint ->
    let uu___ = FStarC_Compiler_Effect.op_Bang recorded_hints in
    match uu___ with
    | FStar_Pervasives_Native.Some l ->
        FStarC_Compiler_Effect.op_Colon_Equals recorded_hints
          (FStar_Pervasives_Native.Some
             (FStarC_Compiler_List.op_At l
                [FStar_Pervasives_Native.Some hint]))
    | uu___1 -> ()
let (record_hint : query_settings -> FStarC_SMTEncoding_Z3.z3result -> unit)
  =
  fun settings ->
    fun z3result ->
      let uu___ =
        let uu___1 = FStarC_Options.record_hints () in
        Prims.op_Negation uu___1 in
      if uu___
      then ()
      else
        (let mk_hint core =
           {
             FStarC_Compiler_Hints.hint_name = (settings.query_name);
             FStarC_Compiler_Hints.hint_index = (settings.query_index);
             FStarC_Compiler_Hints.fuel = (settings.query_fuel);
             FStarC_Compiler_Hints.ifuel = (settings.query_ifuel);
             FStarC_Compiler_Hints.unsat_core = core;
             FStarC_Compiler_Hints.query_elapsed_time = Prims.int_zero;
             FStarC_Compiler_Hints.hash =
               (match z3result.FStarC_SMTEncoding_Z3.z3result_status with
                | FStarC_SMTEncoding_Z3.UNSAT core1 ->
                    z3result.FStarC_SMTEncoding_Z3.z3result_query_hash
                | uu___2 -> FStar_Pervasives_Native.None)
           } in
         match z3result.FStarC_SMTEncoding_Z3.z3result_status with
         | FStarC_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu___2 =
               let uu___3 =
                 get_hint_for settings.query_name settings.query_index in
               FStarC_Compiler_Option.get uu___3 in
             store_hint uu___2
         | FStarC_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu___2 -> ())
let (process_result :
  query_settings ->
    FStarC_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
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
    (query_settings -> FStarC_SMTEncoding_Z3.z3result) ->
      (query_settings ->
         FStarC_SMTEncoding_Z3.z3result ->
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
          let uu___3 =
            FStarC_Compiler_Util.string_of_int settings.query_index in
          Prims.strcat uu___3 ")" in
        Prims.strcat ", " uu___2 in
      Prims.strcat settings.query_name uu___1 in
    Prims.strcat "(" uu___
let collect_dups : 'a . 'a Prims.list -> ('a * Prims.int) Prims.list =
  fun l ->
    let acc = [] in
    let rec add_one acc1 x =
      match acc1 with
      | [] -> [(x, Prims.int_one)]
      | (h, n)::t ->
          if h = x
          then (h, (n + Prims.int_one)) :: t
          else (let uu___1 = add_one t x in (h, n) :: uu___1) in
    FStarC_Compiler_List.fold_left add_one acc l
type answer =
  {
  ok: Prims.bool ;
  cache_hit: Prims.bool ;
  quaking: Prims.bool ;
  quaking_or_retrying: Prims.bool ;
  lo: Prims.int ;
  hi: Prims.int ;
  nsuccess: Prims.int ;
  total_ran: Prims.int ;
  tried_recovery: Prims.bool ;
  errs: errors Prims.list Prims.list }
let (__proj__Mkanswer__item__ok : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> ok
let (__proj__Mkanswer__item__cache_hit : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> cache_hit
let (__proj__Mkanswer__item__quaking : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> quaking
let (__proj__Mkanswer__item__quaking_or_retrying : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> quaking_or_retrying
let (__proj__Mkanswer__item__lo : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> lo
let (__proj__Mkanswer__item__hi : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> hi
let (__proj__Mkanswer__item__nsuccess : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> nsuccess
let (__proj__Mkanswer__item__total_ran : answer -> Prims.int) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> total_ran
let (__proj__Mkanswer__item__tried_recovery : answer -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> tried_recovery
let (__proj__Mkanswer__item__errs : answer -> errors Prims.list Prims.list) =
  fun projectee ->
    match projectee with
    | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; nsuccess;
        total_ran; tried_recovery; errs;_} -> errs
let (ans_ok : answer) =
  {
    ok = true;
    cache_hit = false;
    quaking = false;
    quaking_or_retrying = false;
    lo = Prims.int_one;
    hi = Prims.int_one;
    nsuccess = Prims.int_one;
    total_ran = Prims.int_one;
    tried_recovery = false;
    errs = []
  }
let (ans_fail : answer) =
  {
    ok = false;
    cache_hit = (ans_ok.cache_hit);
    quaking = (ans_ok.quaking);
    quaking_or_retrying = (ans_ok.quaking_or_retrying);
    lo = (ans_ok.lo);
    hi = (ans_ok.hi);
    nsuccess = Prims.int_zero;
    total_ran = (ans_ok.total_ran);
    tried_recovery = (ans_ok.tried_recovery);
    errs = (ans_ok.errs)
  }
let (uu___0 : answer FStarC_Class_Show.showable) =
  {
    FStarC_Class_Show.show =
      (fun ans ->
         let uu___ =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool ans.ok in
         let uu___1 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int ans.nsuccess in
         let uu___2 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int ans.lo in
         let uu___3 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int ans.hi in
         let uu___4 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             ans.tried_recovery in
         FStarC_Compiler_Util.format5
           "ok=%s nsuccess=%s lo=%s hi=%s tried_recovery=%s" uu___ uu___1
           uu___2 uu___3 uu___4)
  }
let (make_solver_configs :
  Prims.bool ->
    Prims.bool ->
      FStarC_SMTEncoding_Env.env_t ->
        FStarC_SMTEncoding_Term.error_labels ->
          FStarC_SMTEncoding_Term.decl ->
            FStarC_Syntax_Syntax.term ->
              FStarC_SMTEncoding_Term.decl Prims.list ->
                (query_settings Prims.list * FStarC_Compiler_Hints.hint
                  FStar_Pervasives_Native.option))
  =
  fun can_split ->
    fun is_retry ->
      fun env ->
        fun all_labels ->
          fun query ->
            fun query_term ->
              fun suffix ->
                let uu___ =
                  let uu___1 =
                    match (env.FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.qtbl_name_and_index
                    with
                    | (FStar_Pervasives_Native.None, uu___2) ->
                        failwith "No query name set!"
                    | (FStar_Pervasives_Native.Some (q, _typ, n), uu___2) ->
                        let uu___3 = FStarC_Ident.string_of_lid q in
                        (uu___3, n) in
                  match uu___1 with
                  | (qname, index) ->
                      let rlimit =
                        let uu___2 = FStarC_Options.z3_rlimit_factor () in
                        let uu___3 = FStarC_Options.z3_rlimit () in
                        uu___2 * uu___3 in
                      let next_hint = get_hint_for qname index in
                      let default_settings =
                        let uu___2 =
                          FStarC_TypeChecker_Env.get_range
                            env.FStarC_SMTEncoding_Env.tcenv in
                        let uu___3 = FStarC_Options.initial_fuel () in
                        let uu___4 = FStarC_Options.initial_ifuel () in
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
                                 { FStarC_Compiler_Hints.hint_name = uu___5;
                                   FStarC_Compiler_Hints.hint_index = uu___6;
                                   FStarC_Compiler_Hints.fuel = uu___7;
                                   FStarC_Compiler_Hints.ifuel = uu___8;
                                   FStarC_Compiler_Hints.unsat_core = uu___9;
                                   FStarC_Compiler_Hints.query_elapsed_time =
                                     uu___10;
                                   FStarC_Compiler_Hints.hash = h;_}
                                 -> h);
                          query_can_be_split_and_retried = can_split;
                          query_term
                        } in
                      (default_settings, next_hint) in
                match uu___ with
                | (default_settings, next_hint) ->
                    let use_hints_setting =
                      let uu___1 =
                        (use_hints ()) &&
                          (FStarC_Compiler_Util.is_some next_hint) in
                      if uu___1
                      then
                        let uu___2 = FStarC_Compiler_Util.must next_hint in
                        match uu___2 with
                        | { FStarC_Compiler_Hints.hint_name = uu___3;
                            FStarC_Compiler_Hints.hint_index = uu___4;
                            FStarC_Compiler_Hints.fuel = i;
                            FStarC_Compiler_Hints.ifuel = j;
                            FStarC_Compiler_Hints.unsat_core =
                              FStar_Pervasives_Native.Some core;
                            FStarC_Compiler_Hints.query_elapsed_time = uu___5;
                            FStarC_Compiler_Hints.hash = h;_} ->
                            [{
                               query_env = (default_settings.query_env);
                               query_decl = (default_settings.query_decl);
                               query_name = (default_settings.query_name);
                               query_index = (default_settings.query_index);
                               query_range = (default_settings.query_range);
                               query_fuel = i;
                               query_ifuel = j;
                               query_rlimit = (default_settings.query_rlimit);
                               query_hint =
                                 (FStar_Pervasives_Native.Some core);
                               query_errors = (default_settings.query_errors);
                               query_all_labels =
                                 (default_settings.query_all_labels);
                               query_suffix = (default_settings.query_suffix);
                               query_hash = (default_settings.query_hash);
                               query_can_be_split_and_retried =
                                 (default_settings.query_can_be_split_and_retried);
                               query_term = (default_settings.query_term)
                             }]
                      else [] in
                    let initial_fuel_max_ifuel =
                      let uu___1 =
                        let uu___2 = FStarC_Options.max_ifuel () in
                        let uu___3 = FStarC_Options.initial_ifuel () in
                        uu___2 > uu___3 in
                      if uu___1
                      then
                        let uu___2 =
                          let uu___3 = FStarC_Options.max_ifuel () in
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
                          let uu___3 = FStarC_Options.max_fuel () in
                          uu___3 / (Prims.of_int (2)) in
                        let uu___3 = FStarC_Options.initial_fuel () in
                        uu___2 > uu___3 in
                      if uu___1
                      then
                        let uu___2 =
                          let uu___3 =
                            let uu___4 = FStarC_Options.max_fuel () in
                            uu___4 / (Prims.of_int (2)) in
                          let uu___4 = FStarC_Options.max_ifuel () in
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
                        (let uu___2 = FStarC_Options.max_fuel () in
                         let uu___3 = FStarC_Options.initial_fuel () in
                         uu___2 > uu___3) &&
                          (let uu___2 = FStarC_Options.max_ifuel () in
                           let uu___3 = FStarC_Options.initial_ifuel () in
                           uu___2 >= uu___3) in
                      if uu___1
                      then
                        let uu___2 =
                          let uu___3 = FStarC_Options.max_fuel () in
                          let uu___4 = FStarC_Options.max_ifuel () in
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
                        FStarC_Compiler_List.op_At use_hints_setting
                          (FStarC_Compiler_List.op_At [default_settings]
                             (FStarC_Compiler_List.op_At
                                initial_fuel_max_ifuel
                                (FStarC_Compiler_List.op_At
                                   half_max_fuel_max_ifuel max_fuel_max_ifuel))) in
                    (cfgs, next_hint)
let (__ask_solver :
  query_settings Prims.list ->
    (errors Prims.list, query_settings) FStar_Pervasives.either)
  =
  fun configs ->
    let check_one_config config =
      (let uu___1 = FStarC_Options.z3_refresh () in
       if uu___1
       then
         FStarC_SMTEncoding_Z3.refresh
           (FStar_Pervasives_Native.Some
              (((config.query_env).FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.proof_ns))
       else ());
      (let uu___1 = with_fuel_and_diagnostics config [] in
       let uu___2 =
         let uu___3 = FStarC_Compiler_Util.string_of_int config.query_index in
         FStarC_Compiler_Util.format2 "(%s, %s)" config.query_name uu___3 in
       FStarC_SMTEncoding_Z3.ask config.query_range config.query_hash
         config.query_all_labels uu___1 uu___2 (used_hint config)
         config.query_hint) in
    fold_queries configs check_one_config process_result
let (ask_solver_quake : query_settings Prims.list -> answer) =
  fun configs ->
    let lo = FStarC_Options.quake_lo () in
    let hi = FStarC_Options.quake_hi () in
    let seed = FStarC_Options.z3_seed () in
    let default_settings = FStarC_Compiler_List.hd configs in
    let name = full_query_id default_settings in
    let quaking =
      (hi > Prims.int_one) &&
        (let uu___ = FStarC_Options.retry () in Prims.op_Negation uu___) in
    let quaking_or_retrying = hi > Prims.int_one in
    let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
    let lo1 =
      if lo < Prims.int_one
      then Prims.int_one
      else if lo > hi1 then hi1 else lo in
    let run_one seed1 =
      let uu___ = FStarC_Options.z3_refresh () in
      if uu___
      then
        FStarC_Options.with_saved_options
          (fun uu___1 ->
             FStarC_Options.set_option "z3seed" (FStarC_Options.Int seed1);
             __ask_solver configs)
      else __ask_solver configs in
    let rec fold_nat' f acc lo2 hi2 =
      if lo2 > hi2
      then acc
      else
        (let uu___1 = f acc lo2 in
         fold_nat' f uu___1 (lo2 + Prims.int_one) hi2) in
    let best_fuel = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
    let best_ifuel = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
    let maybe_improve r n =
      let uu___ = FStarC_Compiler_Effect.op_Bang r in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStarC_Compiler_Effect.op_Colon_Equals r
            (FStar_Pervasives_Native.Some n)
      | FStar_Pervasives_Native.Some m ->
          if n < m
          then
            FStarC_Compiler_Effect.op_Colon_Equals r
              (FStar_Pervasives_Native.Some n)
          else () in
    let uu___ =
      fold_nat'
        (fun uu___1 ->
           fun n ->
             match uu___1 with
             | (nsucc, nfail, rs) ->
                 let uu___2 =
                   (let uu___3 = FStarC_Options.quake_keep () in
                    Prims.op_Negation uu___3) &&
                     ((nsucc >= lo1) || (nfail > (hi1 - lo1))) in
                 if uu___2
                 then (nsucc, nfail, rs)
                 else
                   ((let uu___5 =
                       (quaking_or_retrying &&
                          ((FStarC_Options.interactive ()) ||
                             (FStarC_Compiler_Debug.any ())))
                         && (n > Prims.int_zero) in
                     if uu___5
                     then
                       let uu___6 =
                         if quaking
                         then
                           let uu___7 =
                             FStarC_Compiler_Util.string_of_int nsucc in
                           FStarC_Compiler_Util.format1
                             "succeeded %s times and " uu___7
                         else "" in
                       let uu___7 =
                         if quaking
                         then FStarC_Compiler_Util.string_of_int nfail
                         else
                           (let uu___9 =
                              FStarC_Compiler_Util.string_of_int nfail in
                            Prims.strcat uu___9 " times") in
                       let uu___8 =
                         FStarC_Compiler_Util.string_of_int (hi1 - n) in
                       FStarC_Compiler_Util.print5
                         "%s: so far query %s %sfailed %s (%s runs remain)\n"
                         (if quaking then "Quake" else "Retry") name uu___6
                         uu___7 uu___8
                     else ());
                    (let r = run_one (seed + n) in
                     let uu___5 =
                       match r with
                       | FStar_Pervasives.Inr cfg ->
                           (maybe_improve best_fuel cfg.query_fuel;
                            maybe_improve best_ifuel cfg.query_ifuel;
                            ((nsucc + Prims.int_one), nfail))
                       | uu___6 -> (nsucc, (nfail + Prims.int_one)) in
                     match uu___5 with
                     | (nsucc1, nfail1) -> (nsucc1, nfail1, (r :: rs)))))
        (Prims.int_zero, Prims.int_zero, []) Prims.int_zero
        (hi1 - Prims.int_one) in
    match uu___ with
    | (nsuccess, nfailures, rs) ->
        let total_ran = nsuccess + nfailures in
        (if quaking
         then
           (let fuel_msg =
              let uu___2 =
                let uu___3 = FStarC_Compiler_Effect.op_Bang best_fuel in
                let uu___4 = FStarC_Compiler_Effect.op_Bang best_ifuel in
                (uu___3, uu___4) in
              match uu___2 with
              | (FStar_Pervasives_Native.Some f, FStar_Pervasives_Native.Some
                 i) ->
                  let uu___3 = FStarC_Compiler_Util.string_of_int f in
                  let uu___4 = FStarC_Compiler_Util.string_of_int i in
                  FStarC_Compiler_Util.format2
                    " (best fuel=%s, best ifuel=%s)" uu___3 uu___4
              | (uu___3, uu___4) -> "" in
            let uu___2 = FStarC_Compiler_Util.string_of_int nsuccess in
            let uu___3 = FStarC_Compiler_Util.string_of_int total_ran in
            FStarC_Compiler_Util.print5
              "Quake: query %s succeeded %s/%s times%s%s\n" name uu___2
              uu___3 (if total_ran < hi1 then " (early finish)" else "")
              fuel_msg)
         else ();
         (let all_errs =
            FStarC_Compiler_List.concatMap
              (fun uu___2 ->
                 match uu___2 with
                 | FStar_Pervasives.Inr uu___3 -> []
                 | FStar_Pervasives.Inl es -> [es]) rs in
          {
            ok = (nsuccess >= lo1);
            cache_hit = false;
            quaking;
            quaking_or_retrying;
            lo = lo1;
            hi = hi1;
            nsuccess;
            total_ran;
            tried_recovery = false;
            errs = all_errs
          }))
type recovery_hammer =
  | IncreaseRLimit of Prims.int 
  | RestartAnd of recovery_hammer 
let (uu___is_IncreaseRLimit : recovery_hammer -> Prims.bool) =
  fun projectee ->
    match projectee with | IncreaseRLimit _0 -> true | uu___ -> false
let (__proj__IncreaseRLimit__item___0 : recovery_hammer -> Prims.int) =
  fun projectee -> match projectee with | IncreaseRLimit _0 -> _0
let (uu___is_RestartAnd : recovery_hammer -> Prims.bool) =
  fun projectee ->
    match projectee with | RestartAnd _0 -> true | uu___ -> false
let (__proj__RestartAnd__item___0 : recovery_hammer -> recovery_hammer) =
  fun projectee -> match projectee with | RestartAnd _0 -> _0
let rec (pp_hammer : recovery_hammer -> FStarC_Pprint.document) =
  fun h ->
    match h with
    | IncreaseRLimit factor ->
        let uu___ = FStarC_Errors_Msg.text "increasing its rlimit by" in
        let uu___1 =
          let uu___2 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int factor in
          let uu___3 = FStarC_Pprint.doc_of_string "x" in
          FStarC_Pprint.op_Hat_Hat uu___2 uu___3 in
        FStarC_Pprint.op_Hat_Slash_Hat uu___ uu___1
    | RestartAnd h1 ->
        let uu___ = FStarC_Errors_Msg.text "restarting the solver and" in
        let uu___1 = pp_hammer h1 in
        FStarC_Pprint.op_Hat_Slash_Hat uu___ uu___1
let (ask_solver_recover : query_settings Prims.list -> answer) =
  fun configs ->
    let uu___ = FStarC_Options.proof_recovery () in
    if uu___
    then
      let r = ask_solver_quake configs in
      (if r.ok
       then r
       else
         (let restarted = FStarC_Compiler_Util.mk_ref false in
          let cfg = FStarC_Compiler_List.last configs in
          (let uu___3 =
             let uu___4 =
               FStarC_Errors_Msg.text
                 "This query failed to be solved. Will now retry with higher rlimits due to --proof_recovery." in
             [uu___4] in
           FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
             cfg.query_range ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___3));
          (let try_factor n =
             (let uu___4 =
                let uu___5 =
                  let uu___6 =
                    FStarC_Errors_Msg.text
                      "Retrying query with rlimit factor" in
                  let uu___7 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int n in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                [uu___5] in
              FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                cfg.query_range ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic uu___4));
             (let cfg1 =
                {
                  query_env = (cfg.query_env);
                  query_decl = (cfg.query_decl);
                  query_name = (cfg.query_name);
                  query_index = (cfg.query_index);
                  query_range = (cfg.query_range);
                  query_fuel = (cfg.query_fuel);
                  query_ifuel = (cfg.query_ifuel);
                  query_rlimit = (n * cfg.query_rlimit);
                  query_hint = (cfg.query_hint);
                  query_errors = (cfg.query_errors);
                  query_all_labels = (cfg.query_all_labels);
                  query_suffix = (cfg.query_suffix);
                  query_hash = (cfg.query_hash);
                  query_can_be_split_and_retried =
                    (cfg.query_can_be_split_and_retried);
                  query_term = (cfg.query_term)
                } in
              ask_solver_quake [cfg1]) in
           let rec try_hammer h =
             match h with
             | IncreaseRLimit factor -> try_factor factor
             | RestartAnd h1 ->
                 ((let uu___4 =
                     let uu___5 =
                       FStarC_Errors_Msg.text "Trying a solver restart" in
                     [uu___5] in
                   FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                     cfg.query_range ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___4));
                  (((cfg.query_env).FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.solver).FStarC_TypeChecker_Env.refresh
                    (FStar_Pervasives_Native.Some
                       (((cfg.query_env).FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.proof_ns));
                  try_hammer h1) in
           let rec aux hammers =
             match hammers with
             | [] ->
                 {
                   ok = (r.ok);
                   cache_hit = (r.cache_hit);
                   quaking = (r.quaking);
                   quaking_or_retrying = (r.quaking_or_retrying);
                   lo = (r.lo);
                   hi = (r.hi);
                   nsuccess = (r.nsuccess);
                   total_ran = (r.total_ran);
                   tried_recovery = true;
                   errs = (r.errs)
                 }
             | h::hs ->
                 let r1 = try_hammer h in
                 if r1.ok
                 then
                   ((let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStarC_Errors_Msg.text
                             "This query succeeded after " in
                         let uu___7 = pp_hammer h in
                         FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                       let uu___6 =
                         let uu___7 =
                           FStarC_Errors_Msg.text
                             "Increase the rlimit in the file or simplify the proof. This is only succeeding due to --proof_recovery being given." in
                         [uu___7] in
                       uu___5 :: uu___6 in
                     FStarC_Errors.log_issue
                       FStarC_Class_HasRange.hasRange_range cfg.query_range
                       FStarC_Errors_Codes.Warning_ProofRecovery ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___4));
                    r1)
                 else aux hs in
           aux
             [IncreaseRLimit (Prims.of_int (2));
             IncreaseRLimit (Prims.of_int (4));
             IncreaseRLimit (Prims.of_int (8));
             RestartAnd (IncreaseRLimit (Prims.of_int (8)))])))
    else ask_solver_quake configs
let (failing_query_ctr : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (maybe_save_failing_query :
  FStarC_SMTEncoding_Env.env_t -> query_settings -> unit) =
  fun env ->
    fun qs ->
      (let uu___1 = FStarC_Options.log_failing_queries () in
       if uu___1
       then
         let mod1 =
           let uu___2 =
             FStarC_TypeChecker_Env.current_module
               env.FStarC_SMTEncoding_Env.tcenv in
           FStarC_Class_Show.show FStarC_Ident.showable_lident uu___2 in
         let n =
           (let uu___3 =
              let uu___4 = FStarC_Compiler_Effect.op_Bang failing_query_ctr in
              uu___4 + Prims.int_one in
            FStarC_Compiler_Effect.op_Colon_Equals failing_query_ctr uu___3);
           FStarC_Compiler_Effect.op_Bang failing_query_ctr in
         let file_name =
           let uu___2 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
           FStarC_Compiler_Util.format2 "failedQueries-%s-%s.smt2" mod1
             uu___2 in
         let query_str =
           let uu___2 = with_fuel_and_diagnostics qs [] in
           let uu___3 =
             let uu___4 = FStarC_Compiler_Util.string_of_int qs.query_index in
             FStarC_Compiler_Util.format2 "(%s, %s)" qs.query_name uu___4 in
           FStarC_SMTEncoding_Z3.ask_text qs.query_range qs.query_hash
             qs.query_all_labels uu___2 uu___3 qs.query_hint in
         FStarC_Compiler_Util.write_file file_name query_str
       else ());
      (let uu___2 = FStarC_Compiler_Effect.op_Bang dbg_SMTFail in
       if uu___2
       then
         let uu___3 =
           let uu___4 = FStarC_Errors_Msg.text "This query failed:" in
           let uu___5 =
             let uu___6 =
               FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                 qs.query_term in
             [uu___6] in
           uu___4 :: uu___5 in
         FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
           qs.query_range ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
           (Obj.magic uu___3)
       else ())
let (ask_solver :
  FStarC_SMTEncoding_Env.env_t ->
    query_settings Prims.list ->
      FStarC_Compiler_Hints.hint FStar_Pervasives_Native.option ->
        (query_settings Prims.list * answer))
  =
  fun env ->
    fun configs ->
      fun next_hint ->
        let default_settings = FStarC_Compiler_List.hd configs in
        let skip =
          ((env.FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.admit ||
             (FStarC_TypeChecker_Env.too_early_in_prims
                env.FStarC_SMTEncoding_Env.tcenv))
            ||
            (let uu___ = FStarC_Options.admit_except () in
             match uu___ with
             | FStar_Pervasives_Native.Some id ->
                 if FStarC_Compiler_Util.starts_with id "("
                 then
                   let uu___1 = full_query_id default_settings in
                   uu___1 <> id
                 else default_settings.query_name <> id
             | FStar_Pervasives_Native.None -> false) in
        let ans =
          if skip
          then
            ((let uu___1 =
                (FStarC_Options.record_hints ()) &&
                  (FStarC_Compiler_Util.is_some next_hint) in
              if uu___1
              then
                let uu___2 = FStarC_Compiler_Util.must next_hint in
                store_hint uu___2
              else ());
             ans_ok)
          else
            (let ans1 = ask_solver_recover configs in
             let cfg = FStarC_Compiler_List.last configs in
             if Prims.op_Negation ans1.ok
             then maybe_save_failing_query env cfg
             else ();
             ans1) in
        (configs, ans)
let (report : FStarC_TypeChecker_Env.env -> query_settings -> answer -> unit)
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
              (let uu___1 = FStarC_Options.query_stats () in
               Prims.op_Negation uu___1) in
          (if uu___
           then
             let errors_to_report1 errs =
               errors_to_report a.tried_recovery
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
             let errs = FStarC_Compiler_List.map errors_to_report1 all_errs in
             let errs1 = collect_dups (FStarC_Compiler_List.flatten errs) in
             let errs2 =
               FStarC_Compiler_List.map
                 (fun uu___1 ->
                    match uu___1 with
                    | ((e, m, r, ctx), n) ->
                        let m1 =
                          if n > Prims.int_one
                          then
                            let uu___2 =
                              let uu___3 =
                                let uu___4 =
                                  let uu___5 =
                                    FStarC_Compiler_Util.string_of_int n in
                                  FStarC_Compiler_Util.format1
                                    "Repeated %s times" uu___5 in
                                FStarC_Pprint.doc_of_string uu___4 in
                              [uu___3] in
                            FStarC_Compiler_List.op_At m uu___2
                          else m in
                        (e, m1, r, ctx)) errs1 in
             (FStarC_Errors.add_errors errs2;
              if quaking
              then
                (let rng =
                   match FStar_Pervasives_Native.fst
                           env.FStarC_TypeChecker_Env.qtbl_name_and_index
                   with
                   | FStar_Pervasives_Native.Some (l, uu___2, uu___3) ->
                       FStarC_Ident.range_of_lid l
                   | uu___2 -> FStarC_Compiler_Range_Type.dummyRange in
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       let uu___5 =
                         let uu___6 =
                           FStarC_Compiler_Util.string_of_int nsuccess in
                         let uu___7 =
                           FStarC_Compiler_Util.string_of_int total_ran in
                         let uu___8 = FStarC_Compiler_Util.string_of_int lo in
                         let uu___9 = FStarC_Compiler_Util.string_of_int hi in
                         FStarC_Compiler_Util.format6
                           "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s out of %s%s"
                           name uu___6 uu___7 uu___8 uu___9
                           (if total_ran < hi then " (early abort)" else "") in
                       FStarC_Errors_Msg.text uu___5 in
                     [uu___4] in
                   (FStarC_Errors_Codes.Error_QuakeFailed, uu___3) in
                 FStarC_TypeChecker_Err.log_issue env rng uu___2)
              else ())
           else
             (let report1 errs =
                report_errors a.tried_recovery
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
              FStarC_Compiler_List.iter report1 all_errs))
        else ()
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  smtopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  valid_intro: Prims.bool ;
  valid_elim: Prims.bool ;
  z3version: Prims.string ;
  context_pruning: Prims.bool }
let (__proj__Mksolver_cfg__item__seed : solver_cfg -> Prims.int) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> seed
let (__proj__Mksolver_cfg__item__cliopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> cliopt
let (__proj__Mksolver_cfg__item__smtopt :
  solver_cfg -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> smtopt
let (__proj__Mksolver_cfg__item__facts :
  solver_cfg -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> facts
let (__proj__Mksolver_cfg__item__valid_intro : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> valid_intro
let (__proj__Mksolver_cfg__item__valid_elim : solver_cfg -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> valid_elim
let (__proj__Mksolver_cfg__item__z3version : solver_cfg -> Prims.string) =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> z3version
let (__proj__Mksolver_cfg__item__context_pruning : solver_cfg -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { seed; cliopt; smtopt; facts; valid_intro; valid_elim; z3version;
        context_pruning;_} -> context_pruning
let (_last_cfg :
  solver_cfg FStar_Pervasives_Native.option FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None
let (get_cfg : FStarC_TypeChecker_Env.env -> solver_cfg) =
  fun env ->
    let uu___ = FStarC_Options.z3_seed () in
    let uu___1 = FStarC_Options.z3_cliopt () in
    let uu___2 = FStarC_Options.z3_smtopt () in
    let uu___3 = FStarC_Options.smtencoding_valid_intro () in
    let uu___4 = FStarC_Options.smtencoding_valid_elim () in
    let uu___5 = FStarC_Options.z3_version () in
    let uu___6 =
      let uu___7 = FStarC_Options_Ext.get "context_pruning" in uu___7 <> "" in
    {
      seed = uu___;
      cliopt = uu___1;
      smtopt = uu___2;
      facts = (env.FStarC_TypeChecker_Env.proof_ns);
      valid_intro = uu___3;
      valid_elim = uu___4;
      z3version = uu___5;
      context_pruning = uu___6
    }
let (save_cfg : FStarC_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu___ =
      let uu___1 = get_cfg env in FStar_Pervasives_Native.Some uu___1 in
    FStarC_Compiler_Effect.op_Colon_Equals _last_cfg uu___
let (maybe_refresh_solver : FStarC_TypeChecker_Env.env -> unit) =
  fun env ->
    let uu___ = FStarC_Compiler_Effect.op_Bang _last_cfg in
    match uu___ with
    | FStar_Pervasives_Native.None -> save_cfg env
    | FStar_Pervasives_Native.Some cfg ->
        let uu___1 = let uu___2 = get_cfg env in cfg <> uu___2 in
        if uu___1
        then
          (save_cfg env;
           FStarC_SMTEncoding_Z3.refresh
             (FStar_Pervasives_Native.Some
                (env.FStarC_TypeChecker_Env.proof_ns)))
        else ()
let finally : 'a . (unit -> unit) -> (unit -> 'a) -> 'a =
  fun h ->
    fun f ->
      let r =
        try (fun uu___ -> match () with | () -> f ()) ()
        with | uu___ -> (h (); FStarC_Compiler_Effect.raise uu___) in
      h (); r
let (encode_and_ask :
  Prims.bool ->
    Prims.bool ->
      (unit -> Prims.string) FStar_Pervasives_Native.option ->
        FStarC_TypeChecker_Env.env ->
          FStarC_Syntax_Syntax.term -> (query_settings Prims.list * answer))
  =
  fun can_split ->
    fun is_retry ->
      fun use_env_msg ->
        fun tcenv ->
          fun q ->
            let do1 uu___ =
              maybe_refresh_solver tcenv;
              (let msg =
                 let uu___2 =
                   let uu___3 = FStarC_TypeChecker_Env.get_range tcenv in
                   FStarC_Compiler_Range_Ops.string_of_range uu___3 in
                 FStarC_Compiler_Util.format1 "Starting query at %s" uu___2 in
               FStarC_SMTEncoding_Encode.push_encoding_state msg;
               (let uu___3 =
                  FStarC_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
                match uu___3 with
                | (prefix, labels, qry, suffix) ->
                    (FStarC_SMTEncoding_Z3.start_query msg prefix qry;
                     (let finish_query uu___5 =
                        let msg1 =
                          let uu___6 =
                            let uu___7 =
                              FStarC_TypeChecker_Env.get_range tcenv in
                            FStarC_Compiler_Range_Ops.string_of_range uu___7 in
                          FStarC_Compiler_Util.format1 "Ending query at %s"
                            uu___6 in
                        FStarC_SMTEncoding_Encode.pop_encoding_state msg1;
                        FStarC_SMTEncoding_Z3.finish_query msg1 in
                      finally finish_query
                        (fun uu___5 ->
                           let tcenv1 =
                             FStarC_TypeChecker_Env.incr_query_index tcenv in
                           match qry with
                           | FStarC_SMTEncoding_Term.Assume
                               {
                                 FStarC_SMTEncoding_Term.assumption_term =
                                   {
                                     FStarC_SMTEncoding_Term.tm =
                                       FStarC_SMTEncoding_Term.App
                                       (FStarC_SMTEncoding_Term.FalseOp,
                                        uu___6);
                                     FStarC_SMTEncoding_Term.freevars =
                                       uu___7;
                                     FStarC_SMTEncoding_Term.rng = uu___8;_};
                                 FStarC_SMTEncoding_Term.assumption_caption =
                                   uu___9;
                                 FStarC_SMTEncoding_Term.assumption_name =
                                   uu___10;
                                 FStarC_SMTEncoding_Term.assumption_fact_ids
                                   = uu___11;
                                 FStarC_SMTEncoding_Term.assumption_free_names
                                   = uu___12;_}
                               -> ([], ans_ok)
                           | uu___6 when tcenv1.FStarC_TypeChecker_Env.admit
                               -> ([], ans_ok)
                           | FStarC_SMTEncoding_Term.Assume uu___6 ->
                               ((let uu___8 =
                                   (is_retry ||
                                      (let uu___9 =
                                         FStarC_Options.split_queries () in
                                       uu___9 = FStarC_Options.Always))
                                     && (FStarC_Compiler_Debug.any ()) in
                                 if uu___8
                                 then
                                   let n = FStarC_Compiler_List.length labels in
                                   (if n <> Prims.int_one
                                    then
                                      let uu___9 =
                                        FStarC_TypeChecker_Env.get_range
                                          tcenv1 in
                                      let uu___10 =
                                        let uu___11 =
                                          FStarC_Class_Show.show
                                            FStarC_Syntax_Print.showable_term
                                            q in
                                        let uu___12 =
                                          FStarC_SMTEncoding_Term.declToSmt
                                            "" qry in
                                        let uu___13 =
                                          FStarC_Compiler_Util.string_of_int
                                            n in
                                        FStarC_Compiler_Util.format3
                                          "Encoded split query %s\nto %s\nwith %s labels"
                                          uu___11 uu___12 uu___13 in
                                      FStarC_Errors.diag
                                        FStarC_Class_HasRange.hasRange_range
                                        uu___9 ()
                                        (Obj.magic
                                           FStarC_Errors_Msg.is_error_message_string)
                                        (Obj.magic uu___10)
                                    else ())
                                 else ());
                                (let env =
                                   FStarC_SMTEncoding_Encode.get_current_env
                                     tcenv1 in
                                 let uu___8 =
                                   make_solver_configs can_split is_retry env
                                     labels qry q suffix in
                                 match uu___8 with
                                 | (configs, next_hint) ->
                                     ask_solver env configs next_hint))
                           | uu___6 -> failwith "Impossible"))))) in
            let uu___ =
              FStarC_SMTEncoding_Solver_Cache.try_find_query_cache tcenv q in
            if uu___
            then
              ([],
                {
                  ok = (ans_ok.ok);
                  cache_hit = true;
                  quaking = (ans_ok.quaking);
                  quaking_or_retrying = (ans_ok.quaking_or_retrying);
                  lo = (ans_ok.lo);
                  hi = (ans_ok.hi);
                  nsuccess = (ans_ok.nsuccess);
                  total_ran = (ans_ok.total_ran);
                  tried_recovery = (ans_ok.tried_recovery);
                  errs = (ans_ok.errs)
                })
            else
              (let uu___2 = do1 () in
               match uu___2 with
               | (cfgs, ans) ->
                   (if ans.ok
                    then
                      FStarC_SMTEncoding_Solver_Cache.query_cache_add tcenv q
                    else ();
                    (cfgs, ans)))
let (do_solve :
  Prims.bool ->
    Prims.bool ->
      (unit -> Prims.string) FStar_Pervasives_Native.option ->
        FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> unit)
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
              | FStarC_SMTEncoding_Env.Inner_let_rec names ->
                  ((let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                FStarC_Compiler_List.map
                                  FStar_Pervasives_Native.fst names in
                              FStarC_Compiler_String.concat "," uu___7 in
                            FStarC_Compiler_Util.format1
                              "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)"
                              uu___6 in
                          FStarC_Errors_Msg.text uu___5 in
                        [uu___4] in
                      (FStarC_Errors_Codes.Error_NonTopRecFunctionNotFullyEncoded,
                        uu___3) in
                    FStarC_TypeChecker_Err.log_issue tcenv
                      tcenv.FStarC_TypeChecker_Env.range uu___2);
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
      FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> unit)
  =
  fun retrying ->
    fun use_env_msg ->
      fun tcenv ->
        fun q ->
          (let uu___1 =
             (FStarC_Compiler_Debug.any ()) ||
               (FStarC_Options.query_stats ()) in
           if uu___1
           then
             let range =
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_TypeChecker_Env.get_range tcenv in
                   FStarC_Compiler_Range_Ops.string_of_range uu___4 in
                 Prims.strcat uu___3 ")" in
               Prims.strcat "(" uu___2 in
             FStarC_Compiler_Util.print2
               "%s\tQuery-stats splitting query because %s\n" range
               (if retrying
                then "retrying failed query"
                else "--split_queries is always")
           else ());
          (let goals =
             let uu___1 = FStarC_TypeChecker_Env.split_smt_query tcenv q in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 failwith "Impossible: split_query callback is not set"
             | FStar_Pervasives_Native.Some goals1 -> goals1 in
           FStarC_Compiler_List.iter
             (fun uu___2 ->
                match uu___2 with
                | (env, goal) -> do_solve false retrying use_env_msg env goal)
             goals;
           (let uu___2 =
              (let uu___3 = FStarC_Errors.get_err_count () in
               uu___3 = Prims.int_zero) && retrying in
            if uu___2
            then
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStarC_Errors_Msg.text
                      "The verification condition succeeded after splitting it to localize potential errors, although the original non-split verification condition failed. If you want to rely on splitting queries for verifying your program please use the '--split_queries always' option rather than relying on it implicitly." in
                  [uu___5] in
                (FStarC_Errors_Codes.Warning_SplitAndRetryQueries, uu___4) in
              FStarC_TypeChecker_Err.log_issue tcenv
                tcenv.FStarC_TypeChecker_Env.range uu___3
            else ()))
let disable_quake_for : 'a . (unit -> 'a) -> 'a =
  fun f ->
    FStarC_Options.with_saved_options
      (fun uu___ ->
         FStarC_Options.set_option "quake_hi"
           (FStarC_Options.Int Prims.int_one);
         f ())
let (do_solve_maybe_split :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        if tcenv.FStarC_TypeChecker_Env.admit
        then ()
        else
          (let uu___1 = FStarC_Options.split_queries () in
           match uu___1 with
           | FStarC_Options.No -> do_solve false false use_env_msg tcenv q
           | FStarC_Options.OnFailure ->
               let can_split =
                 let uu___2 =
                   let uu___3 = FStarC_Options.quake_hi () in
                   uu___3 > Prims.int_one in
                 Prims.op_Negation uu___2 in
               (try
                  (fun uu___2 ->
                     match () with
                     | () -> do_solve can_split false use_env_msg tcenv q) ()
                with
                | SplitQueryAndRetry ->
                    split_and_solve true use_env_msg tcenv q)
           | FStarC_Options.Always ->
               split_and_solve false use_env_msg tcenv q)
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu___ = FStarC_Options.no_smt () in
        if uu___
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStarC_Errors_Msg.text
                  "A query could not be solved internally, and --no_smt was given." in
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_Errors_Msg.text "Query = " in
                  let uu___7 =
                    FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term q in
                  FStarC_Pprint.op_Hat_Slash_Hat uu___6 uu___7 in
                [uu___5] in
              uu___3 :: uu___4 in
            (FStarC_Errors_Codes.Error_NoSMTButNeeded, uu___2) in
          FStarC_TypeChecker_Err.log_issue tcenv
            tcenv.FStarC_TypeChecker_Env.range uu___1
        else
          (let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_TypeChecker_Env.current_module tcenv in
               FStarC_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStarC_Profiling.profile
             (fun uu___3 -> do_solve_maybe_split use_env_msg tcenv q) uu___2
             "FStarC.SMTEncoding.solve_top_level")
let (solve_sync :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> answer)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        let uu___ = FStarC_Options.no_smt () in
        if uu___
        then ans_fail
        else
          (let go uu___2 =
             (let uu___4 = FStarC_Compiler_Effect.op_Bang dbg_SMTQuery in
              if uu___4
              then
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      FStarC_Errors_Msg.text
                        "Running synchronous SMT query. Q =" in
                    let uu___8 =
                      FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term q in
                    FStarC_Pprint.prefix (Prims.of_int (2)) Prims.int_one
                      uu___7 uu___8 in
                  [uu___6] in
                FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                  q.FStarC_Syntax_Syntax.pos ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic uu___5)
              else ());
             (let uu___4 =
                disable_quake_for
                  (fun uu___5 ->
                     encode_and_ask false false use_env_msg tcenv q) in
              match uu___4 with | (_cfgs, ans) -> ans) in
           let uu___2 =
             let uu___3 =
               let uu___4 = FStarC_TypeChecker_Env.current_module tcenv in
               FStarC_Ident.string_of_lid uu___4 in
             FStar_Pervasives_Native.Some uu___3 in
           FStarC_Profiling.profile go uu___2
             "FStarC.SMTEncoding.solve_sync_top_level")
let (solve_sync_bool :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.bool)
  =
  fun use_env_msg ->
    fun tcenv -> fun q -> let ans = solve_sync use_env_msg tcenv q in ans.ok
let (snapshot : Prims.string -> ((Prims.int * Prims.int * Prims.int) * unit))
  =
  fun msg ->
    let uu___ = FStarC_SMTEncoding_Encode.snapshot_encoding msg in
    match uu___ with
    | (v0, v1) ->
        let v2 = FStarC_SMTEncoding_Z3.snapshot msg in ((v0, v1, v2), ())
let (rollback :
  Prims.string ->
    (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option ->
      unit)
  =
  fun msg ->
    fun tok ->
      let uu___ =
        match tok with
        | FStar_Pervasives_Native.None ->
            (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | FStar_Pervasives_Native.Some (v0, v1, v2) ->
            ((FStar_Pervasives_Native.Some (v0, v1)),
              (FStar_Pervasives_Native.Some v2)) in
      match uu___ with
      | (tok01, tok2) ->
          (FStarC_SMTEncoding_Encode.rollback_encoding msg tok01;
           FStarC_SMTEncoding_Z3.rollback msg tok2)
let (solver : FStarC_TypeChecker_Env.solver_t) =
  {
    FStarC_TypeChecker_Env.init =
      (fun e -> save_cfg e; FStarC_SMTEncoding_Encode.init e);
    FStarC_TypeChecker_Env.snapshot = snapshot;
    FStarC_TypeChecker_Env.rollback = rollback;
    FStarC_TypeChecker_Env.encode_sig = FStarC_SMTEncoding_Encode.encode_sig;
    FStarC_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu___ =
             let uu___1 =
               let uu___2 = FStarC_Options.peek () in (e, g, uu___2) in
             [uu___1] in
           (false, uu___));
    FStarC_TypeChecker_Env.spinoff_strictly_positive_goals =
      FStar_Pervasives_Native.None;
    FStarC_TypeChecker_Env.handle_smt_goal = (fun e -> fun g -> [(e, g)]);
    FStarC_TypeChecker_Env.solve = solve;
    FStarC_TypeChecker_Env.solve_sync = solve_sync_bool;
    FStarC_TypeChecker_Env.finish = (fun uu___ -> ());
    FStarC_TypeChecker_Env.refresh = FStarC_SMTEncoding_Z3.refresh
  }
let (dummy : FStarC_TypeChecker_Env.solver_t) =
  {
    FStarC_TypeChecker_Env.init = (fun uu___ -> ());
    FStarC_TypeChecker_Env.snapshot =
      (fun uu___ -> ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStarC_TypeChecker_Env.rollback = (fun uu___ -> fun uu___1 -> ());
    FStarC_TypeChecker_Env.encode_sig = (fun uu___ -> fun uu___1 -> ());
    FStarC_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu___ =
             let uu___1 =
               let uu___2 = FStarC_Options.peek () in (e, g, uu___2) in
             [uu___1] in
           (false, uu___));
    FStarC_TypeChecker_Env.spinoff_strictly_positive_goals =
      FStar_Pervasives_Native.None;
    FStarC_TypeChecker_Env.handle_smt_goal = (fun e -> fun g -> [(e, g)]);
    FStarC_TypeChecker_Env.solve =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> ());
    FStarC_TypeChecker_Env.solve_sync =
      (fun uu___ -> fun uu___1 -> fun uu___2 -> false);
    FStarC_TypeChecker_Env.finish = (fun uu___ -> ());
    FStarC_TypeChecker_Env.refresh = (fun uu___ -> ())
  }
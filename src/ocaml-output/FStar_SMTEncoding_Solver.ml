open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____30 'Auu____31 'Auu____32 .
    ('Auu____30, ('Auu____31 * 'Auu____32)) FStar_Util.either ->
      ('Auu____30, 'Auu____31) FStar_Util.either
  =
  fun uu___0_49 ->
    match uu___0_49 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r, uu____64) -> FStar_Util.Inr r
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename -> FStar_Util.format1 "%s.hints" src_filename
let initialize_hints_db : 'Auu____100 . Prims.string -> 'Auu____100 -> unit =
  fun src_filename ->
    fun format_filename ->
      (let uu____114 = FStar_Options.record_hints () in
       if uu____114
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____144 = FStar_Options.use_hints () in
       if uu____144
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename in
         let val_filename =
           let uu____151 = FStar_Options.hint_file () in
           match uu____151 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None ->
               format_hints_file_name norm_src_filename in
         let uu____160 = FStar_Util.read_hints val_filename in
         match uu____160 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename in
             ((let uu____167 = FStar_Options.hint_info () in
               if uu____167
               then
                 let uu____170 =
                   let uu____172 = FStar_Options.hint_file () in
                   match uu____172 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____182 -> "" in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints") uu____170
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None ->
             let uu____220 = FStar_Options.hint_info () in
             (if uu____220
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename ->
    (let uu____237 = FStar_Options.record_hints () in
     if uu____237
     then
       let hints =
         let uu____241 = FStar_ST.op_Bang recorded_hints in
         FStar_Option.get uu____241 in
       let hints_db =
         let uu____268 = FStar_Util.digest_of_file src_filename in
         { FStar_Util.module_digest = uu____268; FStar_Util.hints = hints } in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename in
       let val_filename =
         let uu____274 = FStar_Options.hint_file () in
         match uu____274 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None ->
             format_hints_file_name norm_src_filename in
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
        | uu____399 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___1_407 ->
                     match uu___1_407 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____410 -> false)))
              ||
              (let uu____413 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name in
               FStar_Option.isSome uu____413) in
      let theory_rev = FStar_List.rev theory in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000") in
        let keep_decl uu___2_437 =
          match uu___2_437 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____452 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____462 -> true in
        FStar_List.fold_left
          (fun out ->
             fun d ->
               match d with
               | FStar_SMTEncoding_Term.Module (name, decls) ->
                   let uu____485 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl) in
                   FStar_All.pipe_right uu____485
                     (fun decls1 ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____503 ->
                   let uu____504 = keep_decl d in
                   if uu____504 then d :: out else out) [] theory_rev in
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
            let uu____560 = filter_using_facts_from e theory in
            (uu____560, false, (Prims.parse_int "0"), (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory in
            let uu____581 =
              let uu____592 =
                let uu____603 =
                  let uu____606 =
                    let uu____607 =
                      let uu____609 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ") in
                      Prims.op_Hat "UNSAT CORE: " uu____609 in
                    FStar_SMTEncoding_Term.Caption uu____607 in
                  [uu____606] in
                (uu____603, (Prims.parse_int "0"), (Prims.parse_int "0")) in
              FStar_List.fold_left
                (fun uu____639 ->
                   fun d ->
                     match uu____639 with
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
                          | FStar_SMTEncoding_Term.Module (name, decls) ->
                              let uu____733 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1)) in
                              FStar_All.pipe_right uu____733
                                (fun uu____793 ->
                                   match uu____793 with
                                   | (decls1, uu____818, r, p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____838 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____592 theory_rev in
            (match uu____581 with
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
        let uu____900 = filter_assertions_with_stats e core theory in
        match uu____900 with
        | (theory1, b, uu____923, uu____924) -> (theory1, b)
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e ->
    fun x ->
      let uu____960 = filter_using_facts_from e x in (uu____960, false)
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
    let uu____1190 = FStar_Util.string_of_int err.error_fuel in
    let uu____1192 = FStar_Util.string_of_int err.error_ifuel in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____1190 uu____1192
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
      let n1 = settings.query_fuel in
      let i = settings.query_ifuel in
      let rlimit = settings.query_rlimit in
      let uu____1731 =
        let uu____1734 =
          let uu____1735 =
            let uu____1737 = FStar_Util.string_of_int n1 in
            let uu____1739 = FStar_Util.string_of_int i in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____1737 uu____1739 in
          FStar_SMTEncoding_Term.Caption uu____1735 in
        let uu____1742 =
          let uu____1745 =
            let uu____1746 =
              let uu____1754 =
                let uu____1755 =
                  let uu____1760 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                  let uu____1765 = FStar_SMTEncoding_Term.n_fuel n1 in
                  (uu____1760, uu____1765) in
                FStar_SMTEncoding_Util.mkEq uu____1755 in
              (uu____1754, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption") in
            FStar_SMTEncoding_Util.mkAssume uu____1746 in
          let uu____1769 =
            let uu____1772 =
              let uu____1773 =
                let uu____1781 =
                  let uu____1782 =
                    let uu____1787 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                    let uu____1792 = FStar_SMTEncoding_Term.n_fuel i in
                    (uu____1787, uu____1792) in
                  FStar_SMTEncoding_Util.mkEq uu____1782 in
                (uu____1781, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption") in
              FStar_SMTEncoding_Util.mkAssume uu____1773 in
            [uu____1772; settings.query_decl] in
          uu____1745 :: uu____1769 in
        uu____1734 :: uu____1742 in
      let uu____1796 =
        let uu____1799 =
          let uu____1802 =
            let uu____1805 =
              let uu____1806 =
                let uu____1813 = FStar_Util.string_of_int rlimit in
                ("rlimit", uu____1813) in
              FStar_SMTEncoding_Term.SetOption uu____1806 in
            [uu____1805;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.SetOption ("rlimit", "0");
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore] in
          let uu____1822 =
            let uu____1825 =
              let uu____1828 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ()) in
              if uu____1828
              then [FStar_SMTEncoding_Term.GetStatistics]
              else [] in
            FStar_List.append uu____1825 settings.query_suffix in
          FStar_List.append uu____1802 uu____1822 in
        FStar_List.append label_assumptions uu____1799 in
      FStar_List.append uu____1731 uu____1796
let (used_hint : query_settings -> Prims.bool) =
  fun s -> FStar_Option.isSome s.query_hint
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname ->
    fun qindex ->
      let uu____1862 = FStar_ST.op_Bang replaying_hints in
      match uu____1862 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___3_1895 ->
               match uu___3_1895 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____1903 -> FStar_Pervasives_Native.None)
      | uu____1906 -> FStar_Pervasives_Native.None
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings ->
    fun z3result ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____1924 -> FStar_Pervasives_Native.None
      | uu____1925 ->
          let uu____1926 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status in
          (match uu____1926 with
           | (msg, error_labels) ->
               let err =
                 let uu____1939 =
                   FStar_List.map
                     (fun uu____1967 ->
                        match uu____1967 with
                        | (uu____1982, x, y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____1939
                 } in
               FStar_Pervasives_Native.Some err)
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____1999 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ()) in
      if uu____1999
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____2002 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
              (let uu____2022 =
                 with_fuel_and_diagnostics settings label_assumptions in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____2022
                 FStar_Pervasives_Native.None
                 (fun r ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____2051 = FStar_ST.op_Bang res in
               FStar_Option.get uu____2051) in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err ->
            match err.error_messages with | [] -> false | uu____2107 -> true))
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs ->
    let uu____2129 = find_localized_errors errs in
    FStar_Option.isSome uu____2129
let (report_errors : query_settings -> unit) =
  fun settings ->
    (let uu____2139 = find_localized_errors settings.query_errors in
     match uu____2139 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e ->
                  let uu____2149 =
                    let uu____2151 = error_to_short_string e in
                    Prims.op_Hat "SMT solver says: " uu____2151 in
                  FStar_Errors.diag settings.query_range uu____2149));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None ->
         let err_detail =
           let uu____2156 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e ->
                     let uu____2169 = error_to_short_string e in
                     Prims.op_Hat "SMT solver says: " uu____2169)) in
           FStar_All.pipe_right uu____2156 (FStar_String.concat "; ") in
         let uu____2177 =
           let uu____2187 =
             let uu____2195 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____2195,
               (settings.query_range)) in
           [uu____2187] in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____2177);
    (let uu____2213 =
       (FStar_Options.detail_errors ()) &&
         (let uu____2216 = FStar_Options.n_cores () in
          uu____2216 = (Prims.parse_int "1")) in
     if uu____2213
     then
       let initial_fuel1 =
         let uu___235_2222 = settings in
         let uu____2223 = FStar_Options.initial_fuel () in
         let uu____2225 = FStar_Options.initial_ifuel () in
         {
           query_env = (uu___235_2222.query_env);
           query_decl = (uu___235_2222.query_decl);
           query_name = (uu___235_2222.query_name);
           query_index = (uu___235_2222.query_index);
           query_range = (uu___235_2222.query_range);
           query_fuel = uu____2223;
           query_ifuel = uu____2225;
           query_rlimit = (uu___235_2222.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___235_2222.query_errors);
           query_all_labels = (uu___235_2222.query_all_labels);
           query_suffix = (uu___235_2222.query_suffix);
           query_hash = (uu___235_2222.query_hash)
         } in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None in
         (let uu____2248 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____2248
            FStar_Pervasives_Native.None
            (fun r ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____2277 = FStar_ST.op_Bang res in
          FStar_Option.get uu____2277) in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let process_unsat_core core =
        let accumulator uu____2342 =
          let r = FStar_Util.mk_ref [] in
          let uu____2353 =
            let module_names = FStar_Util.mk_ref [] in
            ((fun m ->
                let ms = FStar_ST.op_Bang module_names in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____2453 ->
                 let uu____2454 = FStar_ST.op_Bang module_names in
                 FStar_All.pipe_right uu____2454
                   (FStar_Util.sort_with FStar_String.compare))) in
          match uu____2353 with | (add1, get1) -> (add1, get1) in
        let uu____2536 = accumulator () in
        match uu____2536 with
        | (add_module_name, get_module_names) ->
            let uu____2573 = accumulator () in
            (match uu____2573 with
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
                                  let uu____2696 =
                                    FStar_List.hd (FStar_Util.split s2 sfx) in
                                  FStar_Pervasives_Native.Some uu____2696
                                else FStar_Pervasives_Native.None) in
                         match sopt with
                         | FStar_Pervasives_Native.None ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3] in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu____2741 ->
                             let uu____2745 = FStar_Util.prefix components in
                             (match uu____2745 with
                              | (module_name, last1) ->
                                  let components1 =
                                    let uu____2772 = exclude_suffix last1 in
                                    FStar_List.append module_name uu____2772 in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____2779::[] -> ()
                                    | uu____2783 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1)) in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____2800 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".") in
                          [uu____2800]) in
                 (match core with
                  | FStar_Pervasives_Native.None ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1 in
                      ((let uu____2827 =
                          let uu____2829 = get_module_names () in
                          FStar_All.pipe_right uu____2829
                            (FStar_String.concat "\nZ3 Proof Stats:\t") in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____2827);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____2842 =
                          let uu____2844 = get_discarded_names () in
                          FStar_All.pipe_right uu____2844
                            (FStar_String.concat ", ") in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____2842)))) in
      let uu____2854 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ()) in
      if uu____2854
      then
        let uu____2857 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status in
        match uu____2857 with
        | (status_string, errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s in
            let uu____2876 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____2890 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None) in
            (match uu____2876 with
             | (tag, core) ->
                 let range =
                   let uu____2903 =
                     let uu____2905 =
                       FStar_Range.string_of_range settings.query_range in
                     Prims.op_Hat uu____2905 (Prims.op_Hat at_log_file ")") in
                   Prims.op_Hat "(" uu____2903 in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else "" in
                 let stats =
                   let uu____2919 = FStar_Options.query_stats () in
                   if uu____2919
                   then
                     let f k v1 a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v1 " "))) in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={" in
                     let uu____2953 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1")) in
                     Prims.op_Hat uu____2953 "}"
                   else "" in
                 ((let uu____2962 =
                     let uu____2966 =
                       let uu____2970 =
                         let uu____2974 =
                           FStar_Util.string_of_int settings.query_index in
                         let uu____2976 =
                           let uu____2980 =
                             let uu____2984 =
                               let uu____2988 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time in
                               let uu____2990 =
                                 let uu____2994 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel in
                                 let uu____2996 =
                                   let uu____3000 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel in
                                   let uu____3002 =
                                     let uu____3006 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit in
                                     [uu____3006; stats] in
                                   uu____3000 :: uu____3002 in
                                 uu____2994 :: uu____2996 in
                               uu____2988 :: uu____2990 in
                             used_hint_tag :: uu____2984 in
                           tag :: uu____2980 in
                         uu____2974 :: uu____2976 in
                       (settings.query_name) :: uu____2970 in
                     range :: uu____2966 in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____2962);
                  (let uu____3021 = FStar_Options.print_z3_statistics () in
                   if uu____3021 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____3047 ->
                          match uu____3047 with
                          | (uu____3055, msg, range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else "" in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings ->
    fun z3result ->
      let uu____3082 =
        let uu____3084 = FStar_Options.record_hints () in
        Prims.op_Negation uu____3084 in
      if uu____3082
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
                | uu____3111 -> FStar_Pervasives_Native.None)
           } in
         let store_hint hint =
           let uu____3119 = FStar_ST.op_Bang recorded_hints in
           match uu____3119 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____3175 -> () in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) ->
             let uu____3182 =
               let uu____3183 =
                 get_hint_for settings.query_name settings.query_index in
               FStar_Option.get uu____3183 in
             store_hint uu____3182
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____3190 -> ())
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
    (query_settings -> (FStar_SMTEncoding_Z3.z3result -> unit) -> unit) ->
      (query_settings ->
         FStar_SMTEncoding_Z3.z3result ->
           errors FStar_Pervasives_Native.option)
        -> (errors Prims.list -> unit) -> unit)
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
                     let uu____3301 = f q res in
                     match uu____3301 with
                     | FStar_Pervasives_Native.None -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2) in
          aux [] qs
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit)
  =
  fun env ->
    fun all_labels ->
      fun prefix1 ->
        fun query ->
          fun suffix ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____3340 =
               let uu____3347 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____3360, FStar_Pervasives_Native.None) ->
                     failwith "No query name set!"
                 | (uu____3386, FStar_Pervasives_Native.Some (q, n1)) ->
                     let uu____3409 = FStar_Ident.text_of_lid q in
                     (uu____3409, n1) in
               match uu____3347 with
               | (qname, index1) ->
                   let rlimit =
                     let uu____3427 = FStar_Options.z3_rlimit_factor () in
                     let uu____3429 =
                       let uu____3431 = FStar_Options.z3_rlimit () in
                       uu____3431 * (Prims.parse_int "544656") in
                     uu____3427 * uu____3429 in
                   let next_hint = get_hint_for qname index1 in
                   let default_settings =
                     let uu____3438 = FStar_TypeChecker_Env.get_range env in
                     let uu____3439 = FStar_Options.initial_fuel () in
                     let uu____3441 = FStar_Options.initial_ifuel () in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____3438;
                       query_fuel = uu____3439;
                       query_ifuel = uu____3441;
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
                              { FStar_Util.hint_name = uu____3450;
                                FStar_Util.hint_index = uu____3451;
                                FStar_Util.fuel = uu____3452;
                                FStar_Util.ifuel = uu____3453;
                                FStar_Util.unsat_core = uu____3454;
                                FStar_Util.query_elapsed_time = uu____3455;
                                FStar_Util.hash = h;_}
                              -> h)
                     } in
                   (default_settings, next_hint) in
             match uu____3340 with
             | (default_settings, next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____3483;
                         FStar_Util.hint_index = uu____3484;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____3488;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___424_3505 = default_settings in
                         {
                           query_env = (uu___424_3505.query_env);
                           query_decl = (uu___424_3505.query_decl);
                           query_name = (uu___424_3505.query_name);
                           query_index = (uu___424_3505.query_index);
                           query_range = (uu___424_3505.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___424_3505.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___424_3505.query_errors);
                           query_all_labels =
                             (uu___424_3505.query_all_labels);
                           query_suffix = (uu___424_3505.query_suffix);
                           query_hash = (uu___424_3505.query_hash)
                         })]
                   | uu____3509 -> [] in
                 let initial_fuel_max_ifuel =
                   let uu____3515 =
                     let uu____3517 = FStar_Options.max_ifuel () in
                     let uu____3519 = FStar_Options.initial_ifuel () in
                     uu____3517 > uu____3519 in
                   if uu____3515
                   then
                     let uu____3524 =
                       let uu___429_3525 = default_settings in
                       let uu____3526 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___429_3525.query_env);
                         query_decl = (uu___429_3525.query_decl);
                         query_name = (uu___429_3525.query_name);
                         query_index = (uu___429_3525.query_index);
                         query_range = (uu___429_3525.query_range);
                         query_fuel = (uu___429_3525.query_fuel);
                         query_ifuel = uu____3526;
                         query_rlimit = (uu___429_3525.query_rlimit);
                         query_hint = (uu___429_3525.query_hint);
                         query_errors = (uu___429_3525.query_errors);
                         query_all_labels = (uu___429_3525.query_all_labels);
                         query_suffix = (uu___429_3525.query_suffix);
                         query_hash = (uu___429_3525.query_hash)
                       } in
                     [uu____3524]
                   else [] in
                 let half_max_fuel_max_ifuel =
                   let uu____3533 =
                     let uu____3535 =
                       let uu____3537 = FStar_Options.max_fuel () in
                       uu____3537 / (Prims.parse_int "2") in
                     let uu____3540 = FStar_Options.initial_fuel () in
                     uu____3535 > uu____3540 in
                   if uu____3533
                   then
                     let uu____3545 =
                       let uu___433_3546 = default_settings in
                       let uu____3547 =
                         let uu____3549 = FStar_Options.max_fuel () in
                         uu____3549 / (Prims.parse_int "2") in
                       let uu____3552 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___433_3546.query_env);
                         query_decl = (uu___433_3546.query_decl);
                         query_name = (uu___433_3546.query_name);
                         query_index = (uu___433_3546.query_index);
                         query_range = (uu___433_3546.query_range);
                         query_fuel = uu____3547;
                         query_ifuel = uu____3552;
                         query_rlimit = (uu___433_3546.query_rlimit);
                         query_hint = (uu___433_3546.query_hint);
                         query_errors = (uu___433_3546.query_errors);
                         query_all_labels = (uu___433_3546.query_all_labels);
                         query_suffix = (uu___433_3546.query_suffix);
                         query_hash = (uu___433_3546.query_hash)
                       } in
                     [uu____3545]
                   else [] in
                 let max_fuel_max_ifuel =
                   let uu____3559 =
                     (let uu____3565 = FStar_Options.max_fuel () in
                      let uu____3567 = FStar_Options.initial_fuel () in
                      uu____3565 > uu____3567) &&
                       (let uu____3571 = FStar_Options.max_ifuel () in
                        let uu____3573 = FStar_Options.initial_ifuel () in
                        uu____3571 >= uu____3573) in
                   if uu____3559
                   then
                     let uu____3578 =
                       let uu___437_3579 = default_settings in
                       let uu____3580 = FStar_Options.max_fuel () in
                       let uu____3582 = FStar_Options.max_ifuel () in
                       {
                         query_env = (uu___437_3579.query_env);
                         query_decl = (uu___437_3579.query_decl);
                         query_name = (uu___437_3579.query_name);
                         query_index = (uu___437_3579.query_index);
                         query_range = (uu___437_3579.query_range);
                         query_fuel = uu____3580;
                         query_ifuel = uu____3582;
                         query_rlimit = (uu___437_3579.query_rlimit);
                         query_hint = (uu___437_3579.query_hint);
                         query_errors = (uu___437_3579.query_errors);
                         query_all_labels = (uu___437_3579.query_all_labels);
                         query_suffix = (uu___437_3579.query_suffix);
                         query_hash = (uu___437_3579.query_hash)
                       } in
                     [uu____3578]
                   else [] in
                 let min_fuel1 =
                   let uu____3589 =
                     let uu____3591 = FStar_Options.min_fuel () in
                     let uu____3593 = FStar_Options.initial_fuel () in
                     uu____3591 < uu____3593 in
                   if uu____3589
                   then
                     let uu____3598 =
                       let uu___441_3599 = default_settings in
                       let uu____3600 = FStar_Options.min_fuel () in
                       {
                         query_env = (uu___441_3599.query_env);
                         query_decl = (uu___441_3599.query_decl);
                         query_name = (uu___441_3599.query_name);
                         query_index = (uu___441_3599.query_index);
                         query_range = (uu___441_3599.query_range);
                         query_fuel = uu____3600;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___441_3599.query_rlimit);
                         query_hint = (uu___441_3599.query_hint);
                         query_errors = (uu___441_3599.query_errors);
                         query_all_labels = (uu___441_3599.query_all_labels);
                         query_suffix = (uu___441_3599.query_suffix);
                         query_hash = (uu___441_3599.query_hash)
                       } in
                     [uu____3598]
                   else [] in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel))) in
                 let check_one_config config1 k =
                   (let uu____3625 = FStar_Options.z3_refresh () in
                    if uu____3625
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____3630 = with_fuel_and_diagnostics config1 [] in
                    let uu____3633 =
                      let uu____3636 = FStar_SMTEncoding_Z3.mk_fresh_scope () in
                      FStar_Pervasives_Native.Some uu____3636 in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____3630
                      uu____3633 k (used_hint config1)) in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___454_3659 = default_settings in
                        {
                          query_env = (uu___454_3659.query_env);
                          query_decl = (uu___454_3659.query_decl);
                          query_name = (uu___454_3659.query_name);
                          query_index = (uu___454_3659.query_index);
                          query_range = (uu___454_3659.query_range);
                          query_fuel = (uu___454_3659.query_fuel);
                          query_ifuel = (uu___454_3659.query_ifuel);
                          query_rlimit = (uu___454_3659.query_rlimit);
                          query_hint = (uu___454_3659.query_hint);
                          query_errors = errs;
                          query_all_labels = (uu___454_3659.query_all_labels);
                          query_suffix = (uu___454_3659.query_suffix);
                          query_hash = (uu___454_3659.query_hash)
                        }) in
                   fold_queries configs check_one_config process_result
                     report1 in
                 let uu____3660 =
                   let uu____3669 = FStar_Options.admit_smt_queries () in
                   let uu____3671 = FStar_Options.admit_except () in
                   (uu____3669, uu____3671) in
                 (match uu____3660 with
                  | (true, uu____3679) -> ()
                  | (false, FStar_Pervasives_Native.None) ->
                      check_all_configs all_configs
                  | (false, FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____3709 =
                              let uu____3711 =
                                let uu____3713 =
                                  let uu____3715 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index in
                                  Prims.op_Hat uu____3715 ")" in
                                Prims.op_Hat ", " uu____3713 in
                              Prims.op_Hat default_settings.query_name
                                uu____3711 in
                            Prims.op_Hat "(" uu____3709 in
                          full_query_id <> id1
                        else default_settings.query_name <> id1 in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg ->
    fun tcenv ->
      fun q ->
        (let uu____3755 =
           let uu____3757 =
             let uu____3759 = FStar_TypeChecker_Env.get_range tcenv in
             FStar_All.pipe_left FStar_Range.string_of_range uu____3759 in
           FStar_Util.format1 "Starting query at %s" uu____3757 in
         FStar_SMTEncoding_Encode.push uu____3755);
        (let uu____3762 = FStar_Options.no_smt () in
         if uu____3762
         then
           let uu____3765 =
             let uu____3775 =
               let uu____3783 =
                 let uu____3785 = FStar_Syntax_Print.term_to_string q in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____3785 in
               (FStar_Errors.Error_NoSMTButNeeded, uu____3783,
                 (tcenv.FStar_TypeChecker_Env.range)) in
             [uu____3775] in
           FStar_TypeChecker_Err.add_errors tcenv uu____3765
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv in
            let uu____3806 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q in
            match uu____3806 with
            | (prefix1, labels, qry, suffix) ->
                let pop1 uu____3842 =
                  let uu____3843 =
                    let uu____3845 =
                      let uu____3847 = FStar_TypeChecker_Env.get_range tcenv1 in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____3847 in
                    FStar_Util.format1 "Ending query at %s" uu____3845 in
                  FStar_SMTEncoding_Encode.pop uu____3843 in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp, uu____3850);
                           FStar_SMTEncoding_Term.freevars = uu____3851;
                           FStar_SMTEncoding_Term.rng = uu____3852;_};
                       FStar_SMTEncoding_Term.assumption_caption = uu____3853;
                       FStar_SMTEncoding_Term.assumption_name = uu____3854;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____3855;_}
                     -> pop1 ()
                 | uu____3875 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____3876 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____3878 -> failwith "Impossible")))
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____3886 =
             let uu____3893 = FStar_Options.peek () in (e, g, uu____3893) in
           [uu____3886]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  }
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____3909 -> ());
    FStar_TypeChecker_Env.push = (fun uu____3911 -> ());
    FStar_TypeChecker_Env.pop = (fun uu____3914 -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____3917 ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback = (fun uu____3936 -> fun uu____3937 -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____3952 -> fun uu____3953 -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e ->
         fun g ->
           let uu____3959 =
             let uu____3966 = FStar_Options.peek () in (e, g, uu____3966) in
           [uu____3959]);
    FStar_TypeChecker_Env.solve =
      (fun uu____3982 -> fun uu____3983 -> fun uu____3984 -> ());
    FStar_TypeChecker_Env.finish = (fun uu____3991 -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____3993 -> ())
  }
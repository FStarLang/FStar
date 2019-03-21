open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____66006 'Auu____66007 'Auu____66008 .
    ('Auu____66006,('Auu____66007 * 'Auu____66008)) FStar_Util.either ->
      ('Auu____66006,'Auu____66007) FStar_Util.either
  =
  fun uu___633_66025  ->
    match uu___633_66025 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____66040) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____66076 . Prims.string -> 'Auu____66076 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____66090 = FStar_Options.record_hints ()  in
       if uu____66090
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____66120 = FStar_Options.use_hints ()  in
       if uu____66120
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____66127 = FStar_Options.hint_file ()  in
           match uu____66127 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____66136 = FStar_Util.read_hints val_filename  in
         match uu____66136 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____66143 = FStar_Options.hint_info ()  in
               if uu____66143
               then
                 let uu____66146 =
                   let uu____66148 = FStar_Options.hint_file ()  in
                   match uu____66148 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____66158 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   uu____66146
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____66196 = FStar_Options.hint_info ()  in
             (if uu____66196
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____66213 = FStar_Options.record_hints ()  in
     if uu____66213
     then
       let hints =
         let uu____66217 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____66217  in
       let hints_db =
         let uu____66244 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____66244; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____66250 = FStar_Options.hint_file ()  in
         match uu____66250 with
         | FStar_Pervasives_Native.Some fn -> fn
         | FStar_Pervasives_Native.None  ->
             format_hints_file_name norm_src_filename
          in
       FStar_Util.write_hints val_filename hints_db
     else ());
    FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None;
    FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None
  
let with_hints_db : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun fname  ->
    fun f  ->
      initialize_hints_db fname false;
      (let result = f ()  in finalize_hints_db fname; result)
  
let (filter_using_facts_from :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun e  ->
    fun theory  ->
      let matches_fact_ids include_assumption_names a =
        match a.FStar_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu____66375 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___634_66383  ->
                     match uu___634_66383 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____66386 -> false)))
              ||
              (let uu____66389 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____66389)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___635_66413 =
          match uu___635_66413 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____66428 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____66438 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____66461 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____66461
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____66479 ->
                   let uu____66480 = keep_decl d  in
                   if uu____66480 then d :: out else out) [] theory_rev
         in
      pruned_theory
  
let rec (filter_assertions_with_stats :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int *
          Prims.int))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        match core with
        | FStar_Pervasives_Native.None  ->
            let uu____66536 = filter_using_facts_from e theory  in
            (uu____66536, false, (Prims.parse_int "0"),
              (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____66557 =
              let uu____66568 =
                let uu____66579 =
                  let uu____66582 =
                    let uu____66583 =
                      let uu____66585 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____66585  in
                    FStar_SMTEncoding_Term.Caption uu____66583  in
                  [uu____66582]  in
                (uu____66579, (Prims.parse_int "0"), (Prims.parse_int "0"))
                 in
              FStar_List.fold_left
                (fun uu____66615  ->
                   fun d  ->
                     match uu____66615 with
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
                          | FStar_SMTEncoding_Term.Module (name,decls) ->
                              let uu____66709 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____66709
                                (fun uu____66769  ->
                                   match uu____66769 with
                                   | (decls1,uu____66794,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____66814 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____66568 theory_rev
               in
            (match uu____66557 with
             | (theory',n_retained,n_pruned) ->
                 (theory', true, n_retained, n_pruned))
  
let (filter_assertions :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Z3.unsat_core ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun core  ->
      fun theory  ->
        let uu____66876 = filter_assertions_with_stats e core theory  in
        match uu____66876 with
        | (theory1,b,uu____66899,uu____66900) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____66936 = filter_using_facts_from e x  in (uu____66936, false)
  
type errors =
  {
  error_reason: Prims.string ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int ;
  error_hint: Prims.string Prims.list FStar_Pervasives_Native.option ;
  error_messages:
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list }
let (__proj__Mkerrors__item__error_reason : errors -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_reason
  
let (__proj__Mkerrors__item__error_fuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_fuel
  
let (__proj__Mkerrors__item__error_ifuel : errors -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_ifuel
  
let (__proj__Mkerrors__item__error_hint :
  errors -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_hint
  
let (__proj__Mkerrors__item__error_messages :
  errors ->
    (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { error_reason; error_fuel; error_ifuel; error_hint; error_messages;_}
        -> error_messages
  
let (error_to_short_string : errors -> Prims.string) =
  fun err  ->
    let uu____67166 = FStar_Util.string_of_int err.error_fuel  in
    let uu____67168 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____67166 uu____67168
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
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_env
  
let (__proj__Mkquery_settings__item__query_decl :
  query_settings -> FStar_SMTEncoding_Term.decl) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_decl
  
let (__proj__Mkquery_settings__item__query_name :
  query_settings -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_name
  
let (__proj__Mkquery_settings__item__query_index :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_index
  
let (__proj__Mkquery_settings__item__query_range :
  query_settings -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_range
  
let (__proj__Mkquery_settings__item__query_fuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_fuel
  
let (__proj__Mkquery_settings__item__query_ifuel :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_ifuel
  
let (__proj__Mkquery_settings__item__query_rlimit :
  query_settings -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_rlimit
  
let (__proj__Mkquery_settings__item__query_hint :
  query_settings -> FStar_SMTEncoding_Z3.unsat_core) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hint
  
let (__proj__Mkquery_settings__item__query_errors :
  query_settings -> errors Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_errors
  
let (__proj__Mkquery_settings__item__query_all_labels :
  query_settings -> FStar_SMTEncoding_Term.error_labels) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_all_labels
  
let (__proj__Mkquery_settings__item__query_suffix :
  query_settings -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_suffix
  
let (__proj__Mkquery_settings__item__query_hash :
  query_settings -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { query_env; query_decl; query_name; query_index; query_range;
        query_fuel; query_ifuel; query_rlimit; query_hint; query_errors;
        query_all_labels; query_suffix; query_hash;_} -> query_hash
  
let (with_fuel_and_diagnostics :
  query_settings ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun settings  ->
    fun label_assumptions  ->
      let n1 = settings.query_fuel  in
      let i = settings.query_ifuel  in
      let rlimit = settings.query_rlimit  in
      let uu____67707 =
        let uu____67710 =
          let uu____67711 =
            let uu____67713 = FStar_Util.string_of_int n1  in
            let uu____67715 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____67713
              uu____67715
             in
          FStar_SMTEncoding_Term.Caption uu____67711  in
        let uu____67718 =
          let uu____67721 =
            let uu____67722 =
              let uu____67730 =
                let uu____67731 =
                  let uu____67736 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____67741 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____67736, uu____67741)  in
                FStar_SMTEncoding_Util.mkEq uu____67731  in
              (uu____67730, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____67722  in
          let uu____67745 =
            let uu____67748 =
              let uu____67749 =
                let uu____67757 =
                  let uu____67758 =
                    let uu____67763 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____67768 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____67763, uu____67768)  in
                  FStar_SMTEncoding_Util.mkEq uu____67758  in
                (uu____67757, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____67749  in
            [uu____67748; settings.query_decl]  in
          uu____67721 :: uu____67745  in
        uu____67710 :: uu____67718  in
      let uu____67772 =
        let uu____67775 =
          let uu____67778 =
            let uu____67781 =
              let uu____67782 =
                let uu____67789 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____67789)  in
              FStar_SMTEncoding_Term.SetOption uu____67782  in
            [uu____67781;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____67794 =
            let uu____67797 =
              let uu____67800 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____67800
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____67797 settings.query_suffix  in
          FStar_List.append uu____67778 uu____67794  in
        FStar_List.append label_assumptions uu____67775  in
      FStar_List.append uu____67707 uu____67772
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____67834 = FStar_ST.op_Bang replaying_hints  in
      match uu____67834 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___636_67867  ->
               match uu___636_67867 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____67875 -> FStar_Pervasives_Native.None)
      | uu____67878 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____67896 ->
          FStar_Pervasives_Native.None
      | uu____67897 ->
          let uu____67898 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____67898 with
           | (msg,error_labels) ->
               let err =
                 let uu____67911 =
                   FStar_List.map
                     (fun uu____67939  ->
                        match uu____67939 with
                        | (uu____67954,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____67911
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____67971 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____67971
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____67974 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____67994 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____67994
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____68023 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____68023)
               in
            FStar_SMTEncoding_ErrorReporting.detail_errors true
              settings.query_env settings.query_all_labels ask_z3
      else ()
  
let (find_localized_errors :
  errors Prims.list -> errors FStar_Pervasives_Native.option) =
  fun errs  ->
    FStar_All.pipe_right errs
      (FStar_List.tryFind
         (fun err  ->
            match err.error_messages with | [] -> false | uu____68079 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____68101 = find_localized_errors errs  in
    FStar_Option.isSome uu____68101
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____68111 = find_localized_errors settings.query_errors  in
     match uu____68111 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____68121 =
                    let uu____68123 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____68123  in
                  FStar_Errors.diag settings.query_range uu____68121));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____68128 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____68141 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____68141))
              in
           FStar_All.pipe_right uu____68128 (FStar_String.concat "; ")  in
         let uu____68149 =
           let uu____68159 =
             let uu____68167 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____68167,
               (settings.query_range))
              in
           [uu____68159]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____68149);
    (let uu____68185 =
       (FStar_Options.detail_errors ()) &&
         (let uu____68188 = FStar_Options.n_cores ()  in
          uu____68188 = (Prims.parse_int "1"))
        in
     if uu____68185
     then
       let initial_fuel1 =
         let uu___868_68194 = settings  in
         let uu____68195 = FStar_Options.initial_fuel ()  in
         let uu____68197 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___868_68194.query_env);
           query_decl = (uu___868_68194.query_decl);
           query_name = (uu___868_68194.query_name);
           query_index = (uu___868_68194.query_index);
           query_range = (uu___868_68194.query_range);
           query_fuel = uu____68195;
           query_ifuel = uu____68197;
           query_rlimit = (uu___868_68194.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___868_68194.query_errors);
           query_all_labels = (uu___868_68194.query_all_labels);
           query_suffix = (uu___868_68194.query_suffix);
           query_hash = (uu___868_68194.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____68220 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____68220
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____68249 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____68249)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____68314 =
          let r = FStar_Util.mk_ref []  in
          let uu____68325 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____68425  ->
                 let uu____68426 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____68426
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____68325 with | (add1,get1) -> (add1, get1)  in
        let uu____68508 = accumulator ()  in
        match uu____68508 with
        | (add_module_name,get_module_names) ->
            let uu____68545 = accumulator ()  in
            (match uu____68545 with
             | (add_discarded_name,get_discarded_names) ->
                 let parse_axiom_name s =
                   let chars = FStar_String.list_of_string s  in
                   let first_upper_index =
                     FStar_Util.try_find_index FStar_Util.is_upper chars  in
                   match first_upper_index with
                   | FStar_Pervasives_Native.None  ->
                       (add_discarded_name s; [])
                   | FStar_Pervasives_Native.Some first_upper_index1 ->
                       let name_and_suffix =
                         FStar_Util.substring_from s first_upper_index1  in
                       let components =
                         FStar_String.split [46] name_and_suffix  in
                       let excluded_suffixes =
                         ["fuel_instrumented";
                         "_pretyping";
                         "_Tm_refine";
                         "_Tm_abs";
                         "@";
                         "_interpretation_Tm_arrow";
                         "MaxFuel_assumption";
                         "MaxIFuel_assumption"]  in
                       let exclude_suffix s1 =
                         let s2 = FStar_Util.trim_string s1  in
                         let sopt =
                           FStar_Util.find_map excluded_suffixes
                             (fun sfx  ->
                                if FStar_Util.contains s2 sfx
                                then
                                  let uu____68668 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____68668
                                else FStar_Pervasives_Native.None)
                            in
                         match sopt with
                         | FStar_Pervasives_Native.None  ->
                             if s2 = "" then [] else [s2]
                         | FStar_Pervasives_Native.Some s3 ->
                             if s3 = "" then [] else [s3]
                          in
                       let components1 =
                         match components with
                         | [] -> []
                         | uu____68713 ->
                             let uu____68717 = FStar_Util.prefix components
                                in
                             (match uu____68717 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____68744 = exclude_suffix last1
                                       in
                                    FStar_List.append module_name uu____68744
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____68751::[] -> ()
                                    | uu____68755 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____68772 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____68772])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____68799 =
                          let uu____68801 = get_module_names ()  in
                          FStar_All.pipe_right uu____68801
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____68799);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____68814 =
                          let uu____68816 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____68816
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____68814))))
         in
      let uu____68826 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____68826
      then
        let uu____68829 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____68829 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____68848 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____68862 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____68848 with
             | (tag,core) ->
                 let range =
                   let uu____68875 =
                     let uu____68877 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____68877 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____68875  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____68891 = FStar_Options.query_stats ()  in
                   if uu____68891
                   then
                     let f k v1 a =
                       Prims.op_Hat a
                         (Prims.op_Hat k
                            (Prims.op_Hat "=" (Prims.op_Hat v1 " ")))
                        in
                     let str =
                       FStar_Util.smap_fold
                         z3result.FStar_SMTEncoding_Z3.z3result_statistics f
                         "statistics={"
                        in
                     let uu____68925 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____68925 "}"
                   else ""  in
                 ((let uu____68934 =
                     let uu____68938 =
                       let uu____68942 =
                         let uu____68946 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____68948 =
                           let uu____68952 =
                             let uu____68956 =
                               let uu____68960 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____68962 =
                                 let uu____68966 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____68968 =
                                   let uu____68972 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____68974 =
                                     let uu____68978 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____68978; stats]  in
                                   uu____68972 :: uu____68974  in
                                 uu____68966 :: uu____68968  in
                               uu____68960 :: uu____68962  in
                             used_hint_tag :: uu____68956  in
                           tag :: uu____68952  in
                         uu____68946 :: uu____68948  in
                       (settings.query_name) :: uu____68942  in
                     range :: uu____68938  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____68934);
                  (let uu____68993 = FStar_Options.print_z3_statistics ()  in
                   if uu____68993 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____69019  ->
                          match uu____69019 with
                          | (uu____69027,msg,range1) ->
                              let tag1 =
                                if used_hint settings
                                then "(Hint-replay failed): "
                                else ""  in
                              FStar_Errors.log_issue range1
                                (FStar_Errors.Warning_HitReplayFailed,
                                  (Prims.op_Hat tag1 msg))))))
      else ()
  
let (record_hint : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____69054 =
        let uu____69056 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____69056  in
      if uu____69054
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
                | uu____69083 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____69091 = FStar_ST.op_Bang recorded_hints  in
           match uu____69091 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____69147 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____69154 =
               let uu____69155 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____69155  in
             store_hint uu____69154
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____69162 -> ())
  
let (process_result :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun result  ->
      let errs = query_errors settings result  in
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
                     let uu____69273 = f q res  in
                     match uu____69273 with
                     | FStar_Pervasives_Native.None  -> ()
                     | FStar_Pervasives_Native.Some errs ->
                         aux (errs :: acc) qs2)
             in
          aux [] qs
  
let (ask_and_report_errors :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.error_labels ->
      FStar_SMTEncoding_Term.decl Prims.list ->
        FStar_SMTEncoding_Term.decl ->
          FStar_SMTEncoding_Term.decl Prims.list -> unit)
  =
  fun env  ->
    fun all_labels  ->
      fun prefix1  ->
        fun query  ->
          fun suffix  ->
            FStar_SMTEncoding_Z3.giveZ3 prefix1;
            (let uu____69312 =
               let uu____69319 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____69332,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____69358,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____69381 = FStar_Ident.text_of_lid q  in
                     (uu____69381, n1)
                  in
               match uu____69319 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____69399 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____69401 =
                       let uu____69403 = FStar_Options.z3_rlimit ()  in
                       uu____69403 * (Prims.parse_int "544656")  in
                     uu____69399 * uu____69401  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____69410 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____69411 = FStar_Options.initial_fuel ()  in
                     let uu____69413 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____69410;
                       query_fuel = uu____69411;
                       query_ifuel = uu____69413;
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
                              { FStar_Util.hint_name = uu____69422;
                                FStar_Util.hint_index = uu____69423;
                                FStar_Util.fuel = uu____69424;
                                FStar_Util.ifuel = uu____69425;
                                FStar_Util.unsat_core = uu____69426;
                                FStar_Util.query_elapsed_time = uu____69427;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____69312 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____69455;
                         FStar_Util.hint_index = uu____69456;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____69460;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___1057_69477 = default_settings  in
                         {
                           query_env = (uu___1057_69477.query_env);
                           query_decl = (uu___1057_69477.query_decl);
                           query_name = (uu___1057_69477.query_name);
                           query_index = (uu___1057_69477.query_index);
                           query_range = (uu___1057_69477.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___1057_69477.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___1057_69477.query_errors);
                           query_all_labels =
                             (uu___1057_69477.query_all_labels);
                           query_suffix = (uu___1057_69477.query_suffix);
                           query_hash = (uu___1057_69477.query_hash)
                         })]
                   | uu____69481 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____69487 =
                     let uu____69489 = FStar_Options.max_ifuel ()  in
                     let uu____69491 = FStar_Options.initial_ifuel ()  in
                     uu____69489 > uu____69491  in
                   if uu____69487
                   then
                     let uu____69496 =
                       let uu___1062_69497 = default_settings  in
                       let uu____69498 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1062_69497.query_env);
                         query_decl = (uu___1062_69497.query_decl);
                         query_name = (uu___1062_69497.query_name);
                         query_index = (uu___1062_69497.query_index);
                         query_range = (uu___1062_69497.query_range);
                         query_fuel = (uu___1062_69497.query_fuel);
                         query_ifuel = uu____69498;
                         query_rlimit = (uu___1062_69497.query_rlimit);
                         query_hint = (uu___1062_69497.query_hint);
                         query_errors = (uu___1062_69497.query_errors);
                         query_all_labels =
                           (uu___1062_69497.query_all_labels);
                         query_suffix = (uu___1062_69497.query_suffix);
                         query_hash = (uu___1062_69497.query_hash)
                       }  in
                     [uu____69496]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____69505 =
                     let uu____69507 =
                       let uu____69509 = FStar_Options.max_fuel ()  in
                       uu____69509 / (Prims.parse_int "2")  in
                     let uu____69512 = FStar_Options.initial_fuel ()  in
                     uu____69507 > uu____69512  in
                   if uu____69505
                   then
                     let uu____69517 =
                       let uu___1066_69518 = default_settings  in
                       let uu____69519 =
                         let uu____69521 = FStar_Options.max_fuel ()  in
                         uu____69521 / (Prims.parse_int "2")  in
                       let uu____69524 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1066_69518.query_env);
                         query_decl = (uu___1066_69518.query_decl);
                         query_name = (uu___1066_69518.query_name);
                         query_index = (uu___1066_69518.query_index);
                         query_range = (uu___1066_69518.query_range);
                         query_fuel = uu____69519;
                         query_ifuel = uu____69524;
                         query_rlimit = (uu___1066_69518.query_rlimit);
                         query_hint = (uu___1066_69518.query_hint);
                         query_errors = (uu___1066_69518.query_errors);
                         query_all_labels =
                           (uu___1066_69518.query_all_labels);
                         query_suffix = (uu___1066_69518.query_suffix);
                         query_hash = (uu___1066_69518.query_hash)
                       }  in
                     [uu____69517]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____69531 =
                     (let uu____69537 = FStar_Options.max_fuel ()  in
                      let uu____69539 = FStar_Options.initial_fuel ()  in
                      uu____69537 > uu____69539) &&
                       (let uu____69543 = FStar_Options.max_ifuel ()  in
                        let uu____69545 = FStar_Options.initial_ifuel ()  in
                        uu____69543 >= uu____69545)
                      in
                   if uu____69531
                   then
                     let uu____69550 =
                       let uu___1070_69551 = default_settings  in
                       let uu____69552 = FStar_Options.max_fuel ()  in
                       let uu____69554 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1070_69551.query_env);
                         query_decl = (uu___1070_69551.query_decl);
                         query_name = (uu___1070_69551.query_name);
                         query_index = (uu___1070_69551.query_index);
                         query_range = (uu___1070_69551.query_range);
                         query_fuel = uu____69552;
                         query_ifuel = uu____69554;
                         query_rlimit = (uu___1070_69551.query_rlimit);
                         query_hint = (uu___1070_69551.query_hint);
                         query_errors = (uu___1070_69551.query_errors);
                         query_all_labels =
                           (uu___1070_69551.query_all_labels);
                         query_suffix = (uu___1070_69551.query_suffix);
                         query_hash = (uu___1070_69551.query_hash)
                       }  in
                     [uu____69550]
                   else []  in
                 let min_fuel1 =
                   let uu____69561 =
                     let uu____69563 = FStar_Options.min_fuel ()  in
                     let uu____69565 = FStar_Options.initial_fuel ()  in
                     uu____69563 < uu____69565  in
                   if uu____69561
                   then
                     let uu____69570 =
                       let uu___1074_69571 = default_settings  in
                       let uu____69572 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___1074_69571.query_env);
                         query_decl = (uu___1074_69571.query_decl);
                         query_name = (uu___1074_69571.query_name);
                         query_index = (uu___1074_69571.query_index);
                         query_range = (uu___1074_69571.query_range);
                         query_fuel = uu____69572;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___1074_69571.query_rlimit);
                         query_hint = (uu___1074_69571.query_hint);
                         query_errors = (uu___1074_69571.query_errors);
                         query_all_labels =
                           (uu___1074_69571.query_all_labels);
                         query_suffix = (uu___1074_69571.query_suffix);
                         query_hash = (uu___1074_69571.query_hash)
                       }  in
                     [uu____69570]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____69597 = FStar_Options.z3_refresh ()  in
                    if uu____69597
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____69602 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____69605 =
                      let uu____69608 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____69608  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____69602
                      uu____69605 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___1087_69631 = default_settings  in
                        {
                          query_env = (uu___1087_69631.query_env);
                          query_decl = (uu___1087_69631.query_decl);
                          query_name = (uu___1087_69631.query_name);
                          query_index = (uu___1087_69631.query_index);
                          query_range = (uu___1087_69631.query_range);
                          query_fuel = (uu___1087_69631.query_fuel);
                          query_ifuel = (uu___1087_69631.query_ifuel);
                          query_rlimit = (uu___1087_69631.query_rlimit);
                          query_hint = (uu___1087_69631.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___1087_69631.query_all_labels);
                          query_suffix = (uu___1087_69631.query_suffix);
                          query_hash = (uu___1087_69631.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____69632 =
                   let uu____69641 = FStar_Options.admit_smt_queries ()  in
                   let uu____69643 = FStar_Options.admit_except ()  in
                   (uu____69641, uu____69643)  in
                 (match uu____69632 with
                  | (true ,uu____69651) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____69681 =
                              let uu____69683 =
                                let uu____69685 =
                                  let uu____69687 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____69687 ")"  in
                                Prims.op_Hat ", " uu____69685  in
                              Prims.op_Hat default_settings.query_name
                                uu____69683
                               in
                            Prims.op_Hat "(" uu____69681  in
                          full_query_id <> id1
                        else default_settings.query_name <> id1  in
                      if Prims.op_Negation skip
                      then check_all_configs all_configs
                      else ()))
  
let (solve :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____69727 =
           let uu____69729 =
             let uu____69731 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____69731  in
           FStar_Util.format1 "Starting query at %s" uu____69729  in
         FStar_SMTEncoding_Encode.push uu____69727);
        (let uu____69734 = FStar_Options.no_smt ()  in
         if uu____69734
         then
           let uu____69737 =
             let uu____69747 =
               let uu____69755 =
                 let uu____69757 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____69757
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____69755,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____69747]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____69737
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____69778 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____69778 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____69814 =
                  let uu____69815 =
                    let uu____69817 =
                      let uu____69819 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____69819
                       in
                    FStar_Util.format1 "Ending query at %s" uu____69817  in
                  FStar_SMTEncoding_Encode.pop uu____69815  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____69822);
                           FStar_SMTEncoding_Term.freevars = uu____69823;
                           FStar_SMTEncoding_Term.rng = uu____69824;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____69825;
                       FStar_SMTEncoding_Term.assumption_name = uu____69826;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____69827;_}
                     -> pop1 ()
                 | uu____69847 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____69848 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____69850 -> failwith "Impossible")))
  
let (solver : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init;
    FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push;
    FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop;
    FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot;
    FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback;
    FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig;
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____69858 =
             let uu____69865 = FStar_Options.peek ()  in (e, g, uu____69865)
              in
           [uu____69858]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____69881  -> ());
    FStar_TypeChecker_Env.push = (fun uu____69883  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____69886  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____69889  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____69908  -> fun uu____69909  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____69924  -> fun uu____69925  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____69931 =
             let uu____69938 = FStar_Options.peek ()  in (e, g, uu____69938)
              in
           [uu____69931]);
    FStar_TypeChecker_Env.solve =
      (fun uu____69954  -> fun uu____69955  -> fun uu____69956  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____69963  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____69965  -> ())
  } 
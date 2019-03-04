open Prims
type z3_replay_result =
  (FStar_SMTEncoding_Z3.unsat_core,FStar_SMTEncoding_Term.error_labels)
    FStar_Util.either
let z3_result_as_replay_result :
  'Auu____70900 'Auu____70901 'Auu____70902 .
    ('Auu____70900,('Auu____70901 * 'Auu____70902)) FStar_Util.either ->
      ('Auu____70900,'Auu____70901) FStar_Util.either
  =
  fun uu___633_70919  ->
    match uu___633_70919 with
    | FStar_Util.Inl l -> FStar_Util.Inl l
    | FStar_Util.Inr (r,uu____70934) -> FStar_Util.Inr r
  
let (recorded_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (replaying_hints :
  FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (format_hints_file_name : Prims.string -> Prims.string) =
  fun src_filename  -> FStar_Util.format1 "%s.hints" src_filename 
let initialize_hints_db :
  'Auu____70992 . Prims.string -> 'Auu____70992 -> unit =
  fun src_filename  ->
    fun format_filename  ->
      (let uu____71006 = FStar_Options.record_hints ()  in
       if uu____71006
       then
         FStar_ST.op_Colon_Equals recorded_hints
           (FStar_Pervasives_Native.Some [])
       else ());
      (let uu____71036 = FStar_Options.use_hints ()  in
       if uu____71036
       then
         let norm_src_filename = FStar_Util.normalize_file_path src_filename
            in
         let val_filename =
           let uu____71043 = FStar_Options.hint_file ()  in
           match uu____71043 with
           | FStar_Pervasives_Native.Some fn -> fn
           | FStar_Pervasives_Native.None  ->
               format_hints_file_name norm_src_filename
            in
         let uu____71052 = FStar_Util.read_hints val_filename  in
         match uu____71052 with
         | FStar_Pervasives_Native.Some hints ->
             let expected_digest =
               FStar_Util.digest_of_file norm_src_filename  in
             ((let uu____71059 = FStar_Options.hint_info ()  in
               if uu____71059
               then
                 let uu____71062 =
                   let uu____71064 = FStar_Options.hint_file ()  in
                   match uu____71064 with
                   | FStar_Pervasives_Native.Some fn ->
                       Prims.op_Hat " from '" (Prims.op_Hat val_filename "'")
                   | uu____71074 -> ""  in
                 FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename
                   (if hints.FStar_Util.module_digest = expected_digest
                    then "valid; using hints"
                    else "invalid; using potentially stale hints")
                   uu____71062
               else ());
              FStar_ST.op_Colon_Equals replaying_hints
                (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)))
         | FStar_Pervasives_Native.None  ->
             let uu____71112 = FStar_Options.hint_info ()  in
             (if uu____71112
              then
                FStar_Util.print1 "(%s) Unable to read hint file.\n"
                  norm_src_filename
              else ())
       else ())
  
let (finalize_hints_db : Prims.string -> unit) =
  fun src_filename  ->
    (let uu____71129 = FStar_Options.record_hints ()  in
     if uu____71129
     then
       let hints =
         let uu____71133 = FStar_ST.op_Bang recorded_hints  in
         FStar_Option.get uu____71133  in
       let hints_db =
         let uu____71160 = FStar_Util.digest_of_file src_filename  in
         { FStar_Util.module_digest = uu____71160; FStar_Util.hints = hints }
          in
       let norm_src_filename = FStar_Util.normalize_file_path src_filename
          in
       let val_filename =
         let uu____71166 = FStar_Options.hint_file ()  in
         match uu____71166 with
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
        | uu____71291 ->
            (FStar_All.pipe_right
               a.FStar_SMTEncoding_Term.assumption_fact_ids
               (FStar_Util.for_some
                  (fun uu___634_71299  ->
                     match uu___634_71299 with
                     | FStar_SMTEncoding_Term.Name lid ->
                         FStar_TypeChecker_Env.should_enc_lid e lid
                     | uu____71302 -> false)))
              ||
              (let uu____71305 =
                 FStar_Util.smap_try_find include_assumption_names
                   a.FStar_SMTEncoding_Term.assumption_name
                  in
               FStar_Option.isSome uu____71305)
         in
      let theory_rev = FStar_List.rev theory  in
      let pruned_theory =
        let include_assumption_names =
          FStar_Util.smap_create (Prims.parse_int "10000")  in
        let keep_decl uu___635_71329 =
          match uu___635_71329 with
          | FStar_SMTEncoding_Term.Assume a ->
              matches_fact_ids include_assumption_names a
          | FStar_SMTEncoding_Term.RetainAssumptions names1 ->
              (FStar_List.iter
                 (fun x  ->
                    FStar_Util.smap_add include_assumption_names x true)
                 names1;
               true)
          | FStar_SMTEncoding_Term.Module uu____71344 ->
              failwith
                "Solver.fs::keep_decl should never have been called with a Module decl"
          | uu____71354 -> true  in
        FStar_List.fold_left
          (fun out  ->
             fun d  ->
               match d with
               | FStar_SMTEncoding_Term.Module (name,decls) ->
                   let uu____71377 =
                     FStar_All.pipe_right decls (FStar_List.filter keep_decl)
                      in
                   FStar_All.pipe_right uu____71377
                     (fun decls1  ->
                        (FStar_SMTEncoding_Term.Module (name, decls1)) :: out)
               | uu____71395 ->
                   let uu____71396 = keep_decl d  in
                   if uu____71396 then d :: out else out) [] theory_rev
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
            let uu____71452 = filter_using_facts_from e theory  in
            (uu____71452, false, (Prims.parse_int "0"),
              (Prims.parse_int "0"))
        | FStar_Pervasives_Native.Some core1 ->
            let theory_rev = FStar_List.rev theory  in
            let uu____71473 =
              let uu____71484 =
                let uu____71495 =
                  let uu____71498 =
                    let uu____71499 =
                      let uu____71501 =
                        FStar_All.pipe_right core1 (FStar_String.concat ", ")
                         in
                      Prims.op_Hat "UNSAT CORE: " uu____71501  in
                    FStar_SMTEncoding_Term.Caption uu____71499  in
                  [uu____71498]  in
                (uu____71495, (Prims.parse_int "0"), (Prims.parse_int "0"))
                 in
              FStar_List.fold_left
                (fun uu____71531  ->
                   fun d  ->
                     match uu____71531 with
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
                              let uu____71625 =
                                FStar_All.pipe_right decls
                                  (filter_assertions_with_stats e
                                     (FStar_Pervasives_Native.Some core1))
                                 in
                              FStar_All.pipe_right uu____71625
                                (fun uu____71685  ->
                                   match uu____71685 with
                                   | (decls1,uu____71710,r,p) ->
                                       (((FStar_SMTEncoding_Term.Module
                                            (name, decls1)) :: theory1),
                                         (n_retained + r), (n_pruned + p)))
                          | uu____71730 ->
                              ((d :: theory1), n_retained, n_pruned)))
                uu____71484 theory_rev
               in
            (match uu____71473 with
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
        let uu____71792 = filter_assertions_with_stats e core theory  in
        match uu____71792 with
        | (theory1,b,uu____71815,uu____71816) -> (theory1, b)
  
let (filter_facts_without_core :
  FStar_TypeChecker_Env.env ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool))
  =
  fun e  ->
    fun x  ->
      let uu____71852 = filter_using_facts_from e x  in (uu____71852, false)
  
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
    let uu____72082 = FStar_Util.string_of_int err.error_fuel  in
    let uu____72084 = FStar_Util.string_of_int err.error_ifuel  in
    FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason
      uu____72082 uu____72084
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
      let uu____72623 =
        let uu____72626 =
          let uu____72627 =
            let uu____72629 = FStar_Util.string_of_int n1  in
            let uu____72631 = FStar_Util.string_of_int i  in
            FStar_Util.format2 "<fuel='%s' ifuel='%s'>" uu____72629
              uu____72631
             in
          FStar_SMTEncoding_Term.Caption uu____72627  in
        let uu____72634 =
          let uu____72637 =
            let uu____72638 =
              let uu____72646 =
                let uu____72647 =
                  let uu____72652 =
                    FStar_SMTEncoding_Util.mkApp ("MaxFuel", [])  in
                  let uu____72657 = FStar_SMTEncoding_Term.n_fuel n1  in
                  (uu____72652, uu____72657)  in
                FStar_SMTEncoding_Util.mkEq uu____72647  in
              (uu____72646, FStar_Pervasives_Native.None,
                "@MaxFuel_assumption")
               in
            FStar_SMTEncoding_Util.mkAssume uu____72638  in
          let uu____72661 =
            let uu____72664 =
              let uu____72665 =
                let uu____72673 =
                  let uu____72674 =
                    let uu____72679 =
                      FStar_SMTEncoding_Util.mkApp ("MaxIFuel", [])  in
                    let uu____72684 = FStar_SMTEncoding_Term.n_fuel i  in
                    (uu____72679, uu____72684)  in
                  FStar_SMTEncoding_Util.mkEq uu____72674  in
                (uu____72673, FStar_Pervasives_Native.None,
                  "@MaxIFuel_assumption")
                 in
              FStar_SMTEncoding_Util.mkAssume uu____72665  in
            [uu____72664; settings.query_decl]  in
          uu____72637 :: uu____72661  in
        uu____72626 :: uu____72634  in
      let uu____72688 =
        let uu____72691 =
          let uu____72694 =
            let uu____72697 =
              let uu____72698 =
                let uu____72705 = FStar_Util.string_of_int rlimit  in
                ("rlimit", uu____72705)  in
              FStar_SMTEncoding_Term.SetOption uu____72698  in
            [uu____72697;
            FStar_SMTEncoding_Term.CheckSat;
            FStar_SMTEncoding_Term.GetReasonUnknown;
            FStar_SMTEncoding_Term.GetUnsatCore]  in
          let uu____72710 =
            let uu____72713 =
              let uu____72716 =
                (FStar_Options.print_z3_statistics ()) ||
                  (FStar_Options.query_stats ())
                 in
              if uu____72716
              then [FStar_SMTEncoding_Term.GetStatistics]
              else []  in
            FStar_List.append uu____72713 settings.query_suffix  in
          FStar_List.append uu____72694 uu____72710  in
        FStar_List.append label_assumptions uu____72691  in
      FStar_List.append uu____72623 uu____72688
  
let (used_hint : query_settings -> Prims.bool) =
  fun s  -> FStar_Option.isSome s.query_hint 
let (get_hint_for :
  Prims.string -> Prims.int -> FStar_Util.hint FStar_Pervasives_Native.option)
  =
  fun qname  ->
    fun qindex  ->
      let uu____72750 = FStar_ST.op_Bang replaying_hints  in
      match uu____72750 with
      | FStar_Pervasives_Native.Some hints ->
          FStar_Util.find_map hints
            (fun uu___636_72783  ->
               match uu___636_72783 with
               | FStar_Pervasives_Native.Some hint when
                   (hint.FStar_Util.hint_name = qname) &&
                     (hint.FStar_Util.hint_index = qindex)
                   -> FStar_Pervasives_Native.Some hint
               | uu____72791 -> FStar_Pervasives_Native.None)
      | uu____72794 -> FStar_Pervasives_Native.None
  
let (query_errors :
  query_settings ->
    FStar_SMTEncoding_Z3.z3result -> errors FStar_Pervasives_Native.option)
  =
  fun settings  ->
    fun z3result  ->
      match z3result.FStar_SMTEncoding_Z3.z3result_status with
      | FStar_SMTEncoding_Z3.UNSAT uu____72812 ->
          FStar_Pervasives_Native.None
      | uu____72813 ->
          let uu____72814 =
            FStar_SMTEncoding_Z3.status_string_and_errors
              z3result.FStar_SMTEncoding_Z3.z3result_status
             in
          (match uu____72814 with
           | (msg,error_labels) ->
               let err =
                 let uu____72827 =
                   FStar_List.map
                     (fun uu____72855  ->
                        match uu____72855 with
                        | (uu____72870,x,y) ->
                            (FStar_Errors.Error_Z3SolverError, x, y))
                     error_labels
                    in
                 {
                   error_reason = msg;
                   error_fuel = (settings.query_fuel);
                   error_ifuel = (settings.query_ifuel);
                   error_hint = (settings.query_hint);
                   error_messages = uu____72827
                 }  in
               FStar_Pervasives_Native.Some err)
  
let (detail_hint_replay :
  query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let uu____72887 =
        (used_hint settings) && (FStar_Options.detail_hint_replay ())  in
      if uu____72887
      then
        match z3result.FStar_SMTEncoding_Z3.z3result_status with
        | FStar_SMTEncoding_Z3.UNSAT uu____72890 -> ()
        | _failed ->
            let ask_z3 label_assumptions =
              let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
              (let uu____72910 =
                 with_fuel_and_diagnostics settings label_assumptions  in
               FStar_SMTEncoding_Z3.ask settings.query_range
                 (filter_assertions settings.query_env settings.query_hint)
                 settings.query_hash settings.query_all_labels uu____72910
                 FStar_Pervasives_Native.None
                 (fun r  ->
                    FStar_ST.op_Colon_Equals res
                      (FStar_Pervasives_Native.Some r)) false);
              (let uu____72961 = FStar_ST.op_Bang res  in
               FStar_Option.get uu____72961)
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
            match err.error_messages with | [] -> false | uu____73039 -> true))
  
let (has_localized_errors : errors Prims.list -> Prims.bool) =
  fun errs  ->
    let uu____73061 = find_localized_errors errs  in
    FStar_Option.isSome uu____73061
  
let (report_errors : query_settings -> unit) =
  fun settings  ->
    (let uu____73071 = find_localized_errors settings.query_errors  in
     match uu____73071 with
     | FStar_Pervasives_Native.Some err ->
         (FStar_All.pipe_right settings.query_errors
            (FStar_List.iter
               (fun e  ->
                  let uu____73081 =
                    let uu____73083 = error_to_short_string e  in
                    Prims.op_Hat "SMT solver says: " uu____73083  in
                  FStar_Errors.diag settings.query_range uu____73081));
          FStar_TypeChecker_Err.add_errors settings.query_env
            err.error_messages)
     | FStar_Pervasives_Native.None  ->
         let err_detail =
           let uu____73088 =
             FStar_All.pipe_right settings.query_errors
               (FStar_List.map
                  (fun e  ->
                     let uu____73101 = error_to_short_string e  in
                     Prims.op_Hat "SMT solver says: " uu____73101))
              in
           FStar_All.pipe_right uu____73088 (FStar_String.concat "; ")  in
         let uu____73109 =
           let uu____73119 =
             let uu____73127 =
               FStar_Util.format1 "Unknown assertion failed (%s)" err_detail
                in
             (FStar_Errors.Error_UnknownFatal_AssertionFailure, uu____73127,
               (settings.query_range))
              in
           [uu____73119]  in
         FStar_TypeChecker_Err.add_errors settings.query_env uu____73109);
    (let uu____73145 =
       (FStar_Options.detail_errors ()) &&
         (let uu____73148 = FStar_Options.n_cores ()  in
          uu____73148 = (Prims.parse_int "1"))
        in
     if uu____73145
     then
       let initial_fuel1 =
         let uu___868_73154 = settings  in
         let uu____73155 = FStar_Options.initial_fuel ()  in
         let uu____73157 = FStar_Options.initial_ifuel ()  in
         {
           query_env = (uu___868_73154.query_env);
           query_decl = (uu___868_73154.query_decl);
           query_name = (uu___868_73154.query_name);
           query_index = (uu___868_73154.query_index);
           query_range = (uu___868_73154.query_range);
           query_fuel = uu____73155;
           query_ifuel = uu____73157;
           query_rlimit = (uu___868_73154.query_rlimit);
           query_hint = FStar_Pervasives_Native.None;
           query_errors = (uu___868_73154.query_errors);
           query_all_labels = (uu___868_73154.query_all_labels);
           query_suffix = (uu___868_73154.query_suffix);
           query_hash = (uu___868_73154.query_hash)
         }  in
       let ask_z3 label_assumptions =
         let res = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
         (let uu____73180 =
            with_fuel_and_diagnostics initial_fuel1 label_assumptions  in
          FStar_SMTEncoding_Z3.ask settings.query_range
            (filter_facts_without_core settings.query_env)
            settings.query_hash settings.query_all_labels uu____73180
            FStar_Pervasives_Native.None
            (fun r  ->
               FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some r))
            false);
         (let uu____73231 = FStar_ST.op_Bang res  in
          FStar_Option.get uu____73231)
          in
       FStar_SMTEncoding_ErrorReporting.detail_errors false
         settings.query_env settings.query_all_labels ask_z3
     else ())
  
let (query_info : query_settings -> FStar_SMTEncoding_Z3.z3result -> unit) =
  fun settings  ->
    fun z3result  ->
      let process_unsat_core core =
        let accumulator uu____73318 =
          let r = FStar_Util.mk_ref []  in
          let uu____73329 =
            let module_names = FStar_Util.mk_ref []  in
            ((fun m  ->
                let ms = FStar_ST.op_Bang module_names  in
                if FStar_List.contains m ms
                then ()
                else FStar_ST.op_Colon_Equals module_names (m :: ms)),
              (fun uu____73473  ->
                 let uu____73474 = FStar_ST.op_Bang module_names  in
                 FStar_All.pipe_right uu____73474
                   (FStar_Util.sort_with FStar_String.compare)))
             in
          match uu____73329 with | (add1,get1) -> (add1, get1)  in
        let uu____73578 = accumulator ()  in
        match uu____73578 with
        | (add_module_name,get_module_names) ->
            let uu____73615 = accumulator ()  in
            (match uu____73615 with
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
                                  let uu____73738 =
                                    FStar_List.hd (FStar_Util.split s2 sfx)
                                     in
                                  FStar_Pervasives_Native.Some uu____73738
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
                         | uu____73783 ->
                             let uu____73787 = FStar_Util.prefix components
                                in
                             (match uu____73787 with
                              | (module_name,last1) ->
                                  let components1 =
                                    let uu____73814 = exclude_suffix last1
                                       in
                                    FStar_List.append module_name uu____73814
                                     in
                                  ((match components1 with
                                    | [] -> ()
                                    | uu____73821::[] -> ()
                                    | uu____73825 ->
                                        add_module_name
                                          (FStar_String.concat "."
                                             module_name));
                                   components1))
                          in
                       if components1 = []
                       then (add_discarded_name s; [])
                       else
                         (let uu____73842 =
                            FStar_All.pipe_right components1
                              (FStar_String.concat ".")
                             in
                          [uu____73842])
                    in
                 (match core with
                  | FStar_Pervasives_Native.None  ->
                      FStar_Util.print_string "no unsat core\n"
                  | FStar_Pervasives_Native.Some core1 ->
                      let core2 = FStar_List.collect parse_axiom_name core1
                         in
                      ((let uu____73869 =
                          let uu____73871 = get_module_names ()  in
                          FStar_All.pipe_right uu____73871
                            (FStar_String.concat "\nZ3 Proof Stats:\t")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n"
                          uu____73869);
                       FStar_Util.print1
                         "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n"
                         (FStar_String.concat
                            "\nZ3 Proof Stats (Detail 1):\t" core2);
                       (let uu____73884 =
                          let uu____73886 = get_discarded_names ()  in
                          FStar_All.pipe_right uu____73886
                            (FStar_String.concat ", ")
                           in
                        FStar_Util.print1
                          "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n"
                          uu____73884))))
         in
      let uu____73896 =
        (FStar_Options.hint_info ()) || (FStar_Options.query_stats ())  in
      if uu____73896
      then
        let uu____73899 =
          FStar_SMTEncoding_Z3.status_string_and_errors
            z3result.FStar_SMTEncoding_Z3.z3result_status
           in
        match uu____73899 with
        | (status_string,errs) ->
            let at_log_file =
              match z3result.FStar_SMTEncoding_Z3.z3result_log_file with
              | FStar_Pervasives_Native.None  -> ""
              | FStar_Pervasives_Native.Some s -> Prims.op_Hat "@" s  in
            let uu____73918 =
              match z3result.FStar_SMTEncoding_Z3.z3result_status with
              | FStar_SMTEncoding_Z3.UNSAT core -> ("succeeded", core)
              | uu____73932 ->
                  ((Prims.op_Hat "failed {reason-unknown="
                      (Prims.op_Hat status_string "}")),
                    FStar_Pervasives_Native.None)
               in
            (match uu____73918 with
             | (tag,core) ->
                 let range =
                   let uu____73945 =
                     let uu____73947 =
                       FStar_Range.string_of_range settings.query_range  in
                     Prims.op_Hat uu____73947 (Prims.op_Hat at_log_file ")")
                      in
                   Prims.op_Hat "(" uu____73945  in
                 let used_hint_tag =
                   if used_hint settings then " (with hint)" else ""  in
                 let stats =
                   let uu____73961 = FStar_Options.query_stats ()  in
                   if uu____73961
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
                     let uu____73995 =
                       FStar_Util.substring str (Prims.parse_int "0")
                         ((FStar_String.length str) - (Prims.parse_int "1"))
                        in
                     Prims.op_Hat uu____73995 "}"
                   else ""  in
                 ((let uu____74004 =
                     let uu____74008 =
                       let uu____74012 =
                         let uu____74016 =
                           FStar_Util.string_of_int settings.query_index  in
                         let uu____74018 =
                           let uu____74022 =
                             let uu____74026 =
                               let uu____74030 =
                                 FStar_Util.string_of_int
                                   z3result.FStar_SMTEncoding_Z3.z3result_time
                                  in
                               let uu____74032 =
                                 let uu____74036 =
                                   FStar_Util.string_of_int
                                     settings.query_fuel
                                    in
                                 let uu____74038 =
                                   let uu____74042 =
                                     FStar_Util.string_of_int
                                       settings.query_ifuel
                                      in
                                   let uu____74044 =
                                     let uu____74048 =
                                       FStar_Util.string_of_int
                                         settings.query_rlimit
                                        in
                                     [uu____74048; stats]  in
                                   uu____74042 :: uu____74044  in
                                 uu____74036 :: uu____74038  in
                               uu____74030 :: uu____74032  in
                             used_hint_tag :: uu____74026  in
                           tag :: uu____74022  in
                         uu____74016 :: uu____74018  in
                       (settings.query_name) :: uu____74012  in
                     range :: uu____74008  in
                   FStar_Util.print
                     "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n"
                     uu____74004);
                  (let uu____74063 = FStar_Options.print_z3_statistics ()  in
                   if uu____74063 then process_unsat_core core else ());
                  FStar_All.pipe_right errs
                    (FStar_List.iter
                       (fun uu____74089  ->
                          match uu____74089 with
                          | (uu____74097,msg,range1) ->
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
      let uu____74124 =
        let uu____74126 = FStar_Options.record_hints ()  in
        Prims.op_Negation uu____74126  in
      if uu____74124
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
                | uu____74153 -> FStar_Pervasives_Native.None)
           }  in
         let store_hint hint =
           let uu____74161 = FStar_ST.op_Bang recorded_hints  in
           match uu____74161 with
           | FStar_Pervasives_Native.Some l ->
               FStar_ST.op_Colon_Equals recorded_hints
                 (FStar_Pervasives_Native.Some
                    (FStar_List.append l [FStar_Pervasives_Native.Some hint]))
           | uu____74217 -> ()  in
         match z3result.FStar_SMTEncoding_Z3.z3result_status with
         | FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None ) ->
             let uu____74224 =
               let uu____74225 =
                 get_hint_for settings.query_name settings.query_index  in
               FStar_Option.get uu____74225  in
             store_hint uu____74224
         | FStar_SMTEncoding_Z3.UNSAT unsat_core ->
             if used_hint settings
             then store_hint (mk_hint settings.query_hint)
             else store_hint (mk_hint unsat_core)
         | uu____74232 -> ())
  
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
                     let uu____74343 = f q res  in
                     match uu____74343 with
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
            (let uu____74382 =
               let uu____74389 =
                 match env.FStar_TypeChecker_Env.qtbl_name_and_index with
                 | (uu____74402,FStar_Pervasives_Native.None ) ->
                     failwith "No query name set!"
                 | (uu____74428,FStar_Pervasives_Native.Some (q,n1)) ->
                     let uu____74451 = FStar_Ident.text_of_lid q  in
                     (uu____74451, n1)
                  in
               match uu____74389 with
               | (qname,index1) ->
                   let rlimit =
                     let uu____74469 = FStar_Options.z3_rlimit_factor ()  in
                     let uu____74471 =
                       let uu____74473 = FStar_Options.z3_rlimit ()  in
                       uu____74473 * (Prims.parse_int "544656")  in
                     uu____74469 * uu____74471  in
                   let next_hint = get_hint_for qname index1  in
                   let default_settings =
                     let uu____74480 = FStar_TypeChecker_Env.get_range env
                        in
                     let uu____74481 = FStar_Options.initial_fuel ()  in
                     let uu____74483 = FStar_Options.initial_ifuel ()  in
                     {
                       query_env = env;
                       query_decl = query;
                       query_name = qname;
                       query_index = index1;
                       query_range = uu____74480;
                       query_fuel = uu____74481;
                       query_ifuel = uu____74483;
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
                              { FStar_Util.hint_name = uu____74492;
                                FStar_Util.hint_index = uu____74493;
                                FStar_Util.fuel = uu____74494;
                                FStar_Util.ifuel = uu____74495;
                                FStar_Util.unsat_core = uu____74496;
                                FStar_Util.query_elapsed_time = uu____74497;
                                FStar_Util.hash = h;_}
                              -> h)
                     }  in
                   (default_settings, next_hint)
                in
             match uu____74382 with
             | (default_settings,next_hint) ->
                 let use_hints_setting =
                   match next_hint with
                   | FStar_Pervasives_Native.Some
                       { FStar_Util.hint_name = uu____74525;
                         FStar_Util.hint_index = uu____74526;
                         FStar_Util.fuel = i; FStar_Util.ifuel = j;
                         FStar_Util.unsat_core = FStar_Pervasives_Native.Some
                           core;
                         FStar_Util.query_elapsed_time = uu____74530;
                         FStar_Util.hash = h;_}
                       ->
                       [(let uu___1057_74547 = default_settings  in
                         {
                           query_env = (uu___1057_74547.query_env);
                           query_decl = (uu___1057_74547.query_decl);
                           query_name = (uu___1057_74547.query_name);
                           query_index = (uu___1057_74547.query_index);
                           query_range = (uu___1057_74547.query_range);
                           query_fuel = i;
                           query_ifuel = j;
                           query_rlimit = (uu___1057_74547.query_rlimit);
                           query_hint = (FStar_Pervasives_Native.Some core);
                           query_errors = (uu___1057_74547.query_errors);
                           query_all_labels =
                             (uu___1057_74547.query_all_labels);
                           query_suffix = (uu___1057_74547.query_suffix);
                           query_hash = (uu___1057_74547.query_hash)
                         })]
                   | uu____74551 -> []  in
                 let initial_fuel_max_ifuel =
                   let uu____74557 =
                     let uu____74559 = FStar_Options.max_ifuel ()  in
                     let uu____74561 = FStar_Options.initial_ifuel ()  in
                     uu____74559 > uu____74561  in
                   if uu____74557
                   then
                     let uu____74566 =
                       let uu___1062_74567 = default_settings  in
                       let uu____74568 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1062_74567.query_env);
                         query_decl = (uu___1062_74567.query_decl);
                         query_name = (uu___1062_74567.query_name);
                         query_index = (uu___1062_74567.query_index);
                         query_range = (uu___1062_74567.query_range);
                         query_fuel = (uu___1062_74567.query_fuel);
                         query_ifuel = uu____74568;
                         query_rlimit = (uu___1062_74567.query_rlimit);
                         query_hint = (uu___1062_74567.query_hint);
                         query_errors = (uu___1062_74567.query_errors);
                         query_all_labels =
                           (uu___1062_74567.query_all_labels);
                         query_suffix = (uu___1062_74567.query_suffix);
                         query_hash = (uu___1062_74567.query_hash)
                       }  in
                     [uu____74566]
                   else []  in
                 let half_max_fuel_max_ifuel =
                   let uu____74575 =
                     let uu____74577 =
                       let uu____74579 = FStar_Options.max_fuel ()  in
                       uu____74579 / (Prims.parse_int "2")  in
                     let uu____74582 = FStar_Options.initial_fuel ()  in
                     uu____74577 > uu____74582  in
                   if uu____74575
                   then
                     let uu____74587 =
                       let uu___1066_74588 = default_settings  in
                       let uu____74589 =
                         let uu____74591 = FStar_Options.max_fuel ()  in
                         uu____74591 / (Prims.parse_int "2")  in
                       let uu____74594 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1066_74588.query_env);
                         query_decl = (uu___1066_74588.query_decl);
                         query_name = (uu___1066_74588.query_name);
                         query_index = (uu___1066_74588.query_index);
                         query_range = (uu___1066_74588.query_range);
                         query_fuel = uu____74589;
                         query_ifuel = uu____74594;
                         query_rlimit = (uu___1066_74588.query_rlimit);
                         query_hint = (uu___1066_74588.query_hint);
                         query_errors = (uu___1066_74588.query_errors);
                         query_all_labels =
                           (uu___1066_74588.query_all_labels);
                         query_suffix = (uu___1066_74588.query_suffix);
                         query_hash = (uu___1066_74588.query_hash)
                       }  in
                     [uu____74587]
                   else []  in
                 let max_fuel_max_ifuel =
                   let uu____74601 =
                     (let uu____74607 = FStar_Options.max_fuel ()  in
                      let uu____74609 = FStar_Options.initial_fuel ()  in
                      uu____74607 > uu____74609) &&
                       (let uu____74613 = FStar_Options.max_ifuel ()  in
                        let uu____74615 = FStar_Options.initial_ifuel ()  in
                        uu____74613 >= uu____74615)
                      in
                   if uu____74601
                   then
                     let uu____74620 =
                       let uu___1070_74621 = default_settings  in
                       let uu____74622 = FStar_Options.max_fuel ()  in
                       let uu____74624 = FStar_Options.max_ifuel ()  in
                       {
                         query_env = (uu___1070_74621.query_env);
                         query_decl = (uu___1070_74621.query_decl);
                         query_name = (uu___1070_74621.query_name);
                         query_index = (uu___1070_74621.query_index);
                         query_range = (uu___1070_74621.query_range);
                         query_fuel = uu____74622;
                         query_ifuel = uu____74624;
                         query_rlimit = (uu___1070_74621.query_rlimit);
                         query_hint = (uu___1070_74621.query_hint);
                         query_errors = (uu___1070_74621.query_errors);
                         query_all_labels =
                           (uu___1070_74621.query_all_labels);
                         query_suffix = (uu___1070_74621.query_suffix);
                         query_hash = (uu___1070_74621.query_hash)
                       }  in
                     [uu____74620]
                   else []  in
                 let min_fuel1 =
                   let uu____74631 =
                     let uu____74633 = FStar_Options.min_fuel ()  in
                     let uu____74635 = FStar_Options.initial_fuel ()  in
                     uu____74633 < uu____74635  in
                   if uu____74631
                   then
                     let uu____74640 =
                       let uu___1074_74641 = default_settings  in
                       let uu____74642 = FStar_Options.min_fuel ()  in
                       {
                         query_env = (uu___1074_74641.query_env);
                         query_decl = (uu___1074_74641.query_decl);
                         query_name = (uu___1074_74641.query_name);
                         query_index = (uu___1074_74641.query_index);
                         query_range = (uu___1074_74641.query_range);
                         query_fuel = uu____74642;
                         query_ifuel = (Prims.parse_int "1");
                         query_rlimit = (uu___1074_74641.query_rlimit);
                         query_hint = (uu___1074_74641.query_hint);
                         query_errors = (uu___1074_74641.query_errors);
                         query_all_labels =
                           (uu___1074_74641.query_all_labels);
                         query_suffix = (uu___1074_74641.query_suffix);
                         query_hash = (uu___1074_74641.query_hash)
                       }  in
                     [uu____74640]
                   else []  in
                 let all_configs =
                   FStar_List.append use_hints_setting
                     (FStar_List.append [default_settings]
                        (FStar_List.append initial_fuel_max_ifuel
                           (FStar_List.append half_max_fuel_max_ifuel
                              max_fuel_max_ifuel)))
                    in
                 let check_one_config config1 k =
                   (let uu____74667 = FStar_Options.z3_refresh ()  in
                    if uu____74667
                    then FStar_SMTEncoding_Z3.refresh ()
                    else ());
                   (let uu____74672 = with_fuel_and_diagnostics config1 []
                       in
                    let uu____74675 =
                      let uu____74678 =
                        FStar_SMTEncoding_Z3.mk_fresh_scope ()  in
                      FStar_Pervasives_Native.Some uu____74678  in
                    FStar_SMTEncoding_Z3.ask config1.query_range
                      (filter_assertions config1.query_env config1.query_hint)
                      config1.query_hash config1.query_all_labels uu____74672
                      uu____74675 k (used_hint config1))
                    in
                 let check_all_configs configs =
                   let report1 errs =
                     report_errors
                       (let uu___1087_74701 = default_settings  in
                        {
                          query_env = (uu___1087_74701.query_env);
                          query_decl = (uu___1087_74701.query_decl);
                          query_name = (uu___1087_74701.query_name);
                          query_index = (uu___1087_74701.query_index);
                          query_range = (uu___1087_74701.query_range);
                          query_fuel = (uu___1087_74701.query_fuel);
                          query_ifuel = (uu___1087_74701.query_ifuel);
                          query_rlimit = (uu___1087_74701.query_rlimit);
                          query_hint = (uu___1087_74701.query_hint);
                          query_errors = errs;
                          query_all_labels =
                            (uu___1087_74701.query_all_labels);
                          query_suffix = (uu___1087_74701.query_suffix);
                          query_hash = (uu___1087_74701.query_hash)
                        })
                      in
                   fold_queries configs check_one_config process_result
                     report1
                    in
                 let uu____74702 =
                   let uu____74711 = FStar_Options.admit_smt_queries ()  in
                   let uu____74713 = FStar_Options.admit_except ()  in
                   (uu____74711, uu____74713)  in
                 (match uu____74702 with
                  | (true ,uu____74721) -> ()
                  | (false ,FStar_Pervasives_Native.None ) ->
                      check_all_configs all_configs
                  | (false ,FStar_Pervasives_Native.Some id1) ->
                      let skip =
                        if FStar_Util.starts_with id1 "("
                        then
                          let full_query_id =
                            let uu____74751 =
                              let uu____74753 =
                                let uu____74755 =
                                  let uu____74757 =
                                    FStar_Util.string_of_int
                                      default_settings.query_index
                                     in
                                  Prims.op_Hat uu____74757 ")"  in
                                Prims.op_Hat ", " uu____74755  in
                              Prims.op_Hat default_settings.query_name
                                uu____74753
                               in
                            Prims.op_Hat "(" uu____74751  in
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
        (let uu____74797 =
           let uu____74799 =
             let uu____74801 = FStar_TypeChecker_Env.get_range tcenv  in
             FStar_All.pipe_left FStar_Range.string_of_range uu____74801  in
           FStar_Util.format1 "Starting query at %s" uu____74799  in
         FStar_SMTEncoding_Encode.push uu____74797);
        (let uu____74804 = FStar_Options.no_smt ()  in
         if uu____74804
         then
           let uu____74807 =
             let uu____74817 =
               let uu____74825 =
                 let uu____74827 = FStar_Syntax_Print.term_to_string q  in
                 FStar_Util.format1
                   "Q = %s\nA query could not be solved internally, and --no_smt was given"
                   uu____74827
                  in
               (FStar_Errors.Error_NoSMTButNeeded, uu____74825,
                 (tcenv.FStar_TypeChecker_Env.range))
                in
             [uu____74817]  in
           FStar_TypeChecker_Err.add_errors tcenv uu____74807
         else
           (let tcenv1 = FStar_TypeChecker_Env.incr_query_index tcenv  in
            let uu____74848 =
              FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q  in
            match uu____74848 with
            | (prefix1,labels,qry,suffix) ->
                let pop1 uu____74884 =
                  let uu____74885 =
                    let uu____74887 =
                      let uu____74889 =
                        FStar_TypeChecker_Env.get_range tcenv1  in
                      FStar_All.pipe_left FStar_Range.string_of_range
                        uu____74889
                       in
                    FStar_Util.format1 "Ending query at %s" uu____74887  in
                  FStar_SMTEncoding_Encode.pop uu____74885  in
                (match qry with
                 | FStar_SMTEncoding_Term.Assume
                     {
                       FStar_SMTEncoding_Term.assumption_term =
                         {
                           FStar_SMTEncoding_Term.tm =
                             FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.FalseOp ,uu____74892);
                           FStar_SMTEncoding_Term.freevars = uu____74893;
                           FStar_SMTEncoding_Term.rng = uu____74894;_};
                       FStar_SMTEncoding_Term.assumption_caption =
                         uu____74895;
                       FStar_SMTEncoding_Term.assumption_name = uu____74896;
                       FStar_SMTEncoding_Term.assumption_fact_ids =
                         uu____74897;_}
                     -> pop1 ()
                 | uu____74917 when tcenv1.FStar_TypeChecker_Env.admit ->
                     pop1 ()
                 | FStar_SMTEncoding_Term.Assume uu____74918 ->
                     (ask_and_report_errors tcenv1 labels prefix1 qry suffix;
                      pop1 ())
                 | uu____74920 -> failwith "Impossible")))
  
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
           let uu____74928 =
             let uu____74935 = FStar_Options.peek ()  in (e, g, uu____74935)
              in
           [uu____74928]);
    FStar_TypeChecker_Env.solve = solve;
    FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish;
    FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh
  } 
let (dummy : FStar_TypeChecker_Env.solver_t) =
  {
    FStar_TypeChecker_Env.init = (fun uu____74951  -> ());
    FStar_TypeChecker_Env.push = (fun uu____74953  -> ());
    FStar_TypeChecker_Env.pop = (fun uu____74956  -> ());
    FStar_TypeChecker_Env.snapshot =
      (fun uu____74959  ->
         (((Prims.parse_int "0"), (Prims.parse_int "0"),
            (Prims.parse_int "0")), ()));
    FStar_TypeChecker_Env.rollback =
      (fun uu____74978  -> fun uu____74979  -> ());
    FStar_TypeChecker_Env.encode_sig =
      (fun uu____74994  -> fun uu____74995  -> ());
    FStar_TypeChecker_Env.preprocess =
      (fun e  ->
         fun g  ->
           let uu____75001 =
             let uu____75008 = FStar_Options.peek ()  in (e, g, uu____75008)
              in
           [uu____75001]);
    FStar_TypeChecker_Env.solve =
      (fun uu____75024  -> fun uu____75025  -> fun uu____75026  -> ());
    FStar_TypeChecker_Env.finish = (fun uu____75033  -> ());
    FStar_TypeChecker_Env.refresh = (fun uu____75035  -> ())
  } 
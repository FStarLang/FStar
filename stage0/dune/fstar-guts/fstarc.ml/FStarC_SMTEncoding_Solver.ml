open Prims
let dbg_SMTQuery : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "SMTQuery"
let dbg_SMTFail : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "SMTFail"
type errors =
  {
  error_reason: Prims.string ;
  error_rlimit: Prims.int ;
  error_fuel: Prims.int ;
  error_ifuel: Prims.int }
let __proj__Mkerrors__item__error_reason (projectee : errors) : Prims.string=
  match projectee with
  | { error_reason; error_rlimit; error_fuel; error_ifuel;_} -> error_reason
let __proj__Mkerrors__item__error_rlimit (projectee : errors) : Prims.int=
  match projectee with
  | { error_reason; error_rlimit; error_fuel; error_ifuel;_} -> error_rlimit
let __proj__Mkerrors__item__error_fuel (projectee : errors) : Prims.int=
  match projectee with
  | { error_reason; error_rlimit; error_fuel; error_ifuel;_} -> error_fuel
let __proj__Mkerrors__item__error_ifuel (projectee : errors) : Prims.int=
  match projectee with
  | { error_reason; error_rlimit; error_fuel; error_ifuel;_} -> error_ifuel
let error_to_short_string (err : errors) : Prims.string=
  let uu___ =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_rlimit in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_fuel in
  let uu___2 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_int err.error_ifuel in
  FStarC_Format.fmt4 "%s (rlimit=%s; fuel=%s; ifuel=%s)" err.error_reason
    uu___ uu___1 uu___2
type query_settings =
  {
  query_env: FStarC_SMTEncoding_Env.env_t ;
  query_name: Prims.string ;
  query_index: Prims.int ;
  query_range: FStarC_Range_Type.t ;
  query_fuel: Prims.int ;
  query_ifuel: Prims.int ;
  query_rlimit: Prims.int ;
  query_goals: FStarC_SMTEncoding_ErrorReporting.goal_tree ;
  query_term: FStarC_Syntax_Syntax.term }
let __proj__Mkquery_settings__item__query_env (projectee : query_settings) :
  FStarC_SMTEncoding_Env.env_t=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_env
let __proj__Mkquery_settings__item__query_name (projectee : query_settings) :
  Prims.string=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_name
let __proj__Mkquery_settings__item__query_index (projectee : query_settings)
  : Prims.int=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_index
let __proj__Mkquery_settings__item__query_range (projectee : query_settings)
  : FStarC_Range_Type.t=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_range
let __proj__Mkquery_settings__item__query_fuel (projectee : query_settings) :
  Prims.int=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_fuel
let __proj__Mkquery_settings__item__query_ifuel (projectee : query_settings)
  : Prims.int=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_ifuel
let __proj__Mkquery_settings__item__query_rlimit (projectee : query_settings)
  : Prims.int=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_rlimit
let __proj__Mkquery_settings__item__query_goals (projectee : query_settings)
  : FStarC_SMTEncoding_ErrorReporting.goal_tree=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_goals
let __proj__Mkquery_settings__item__query_term (projectee : query_settings) :
  FStarC_Syntax_Syntax.term=
  match projectee with
  | { query_env; query_name; query_index; query_range; query_fuel;
      query_ifuel; query_rlimit; query_goals; query_term;_} -> query_term
type goal_state =
  {
  gs_goal: FStarC_SMTEncoding_ErrorReporting.goal ;
  gs_nsuccess: Prims.int ;
  gs_nfailure: Prims.int ;
  gs_errors: errors Prims.list }
let __proj__Mkgoal_state__item__gs_goal (projectee : goal_state) :
  FStarC_SMTEncoding_ErrorReporting.goal=
  match projectee with
  | { gs_goal; gs_nsuccess; gs_nfailure; gs_errors;_} -> gs_goal
let __proj__Mkgoal_state__item__gs_nsuccess (projectee : goal_state) :
  Prims.int=
  match projectee with
  | { gs_goal; gs_nsuccess; gs_nfailure; gs_errors;_} -> gs_nsuccess
let __proj__Mkgoal_state__item__gs_nfailure (projectee : goal_state) :
  Prims.int=
  match projectee with
  | { gs_goal; gs_nsuccess; gs_nfailure; gs_errors;_} -> gs_nfailure
let __proj__Mkgoal_state__item__gs_errors (projectee : goal_state) :
  errors Prims.list=
  match projectee with
  | { gs_goal; gs_nsuccess; gs_nfailure; gs_errors;_} -> gs_errors
let initial_goal_state (g : FStarC_SMTEncoding_ErrorReporting.goal) :
  goal_state=
  {
    gs_goal = g;
    gs_nsuccess = Prims.int_zero;
    gs_nfailure = Prims.int_zero;
    gs_errors = []
  }
let convert_rlimit (r : Prims.int) : Prims.int=
  let uu___ =
    let uu___1 = FStarC_Options.z3_version () in
    FStarC_Misc.version_ge uu___1 "4.12.3" in
  if uu___ then (Prims.of_int 500000) * r else (Prims.of_int 544656) * r
let goal_block (settings : query_settings)
  (g : FStarC_SMTEncoding_ErrorReporting.goal) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  let n = settings.query_fuel in
  let i = settings.query_ifuel in
  let rlimit = convert_rlimit settings.query_rlimit in
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int
              g.FStarC_SMTEncoding_ErrorReporting.goal_id in
          let uu___5 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
          let uu___6 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
          FStarC_Format.fmt3 "<goal %s fuel='%s' ifuel='%s'>" uu___4 uu___5
            uu___6 in
        FStarC_SMTEncoding_Term.Caption uu___3 in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 = FStarC_SMTEncoding_Util.mkApp ("MaxFuel", []) in
                let uu___9 = FStarC_SMTEncoding_Term.n_fuel n in
                (uu___8, uu___9) in
              FStarC_SMTEncoding_Util.mkEq uu___7 in
            (uu___6, FStar_Pervasives_Native.None, "@MaxFuel_assumption") in
          FStarC_SMTEncoding_Util.mkAssume uu___5 in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              let uu___8 =
                let uu___9 =
                  let uu___10 =
                    FStarC_SMTEncoding_Util.mkApp ("MaxIFuel", []) in
                  let uu___11 = FStarC_SMTEncoding_Term.n_fuel i in
                  (uu___10, uu___11) in
                FStarC_SMTEncoding_Util.mkEq uu___9 in
              (uu___8, FStar_Pervasives_Native.None, "@MaxIFuel_assumption") in
            FStarC_SMTEncoding_Util.mkAssume uu___7 in
          let uu___7 =
            let uu___8 =
              let uu___9 =
                let uu___10 =
                  FStarC_SMTEncoding_Util.mkNot
                    g.FStarC_SMTEncoding_ErrorReporting.goal_term in
                (uu___10, (FStar_Pervasives_Native.Some "query"), "@query") in
              FStarC_SMTEncoding_Util.mkAssume uu___9 in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int
                    rlimit in
                FStarC_SMTEncoding_Term.SetOption ("rlimit", uu___11) in
              [uu___10;
              FStarC_SMTEncoding_Term.Echo "<goal>";
              FStarC_SMTEncoding_Term.Echo "<initial_stats>";
              FStarC_SMTEncoding_Term.GetStatistics;
              FStarC_SMTEncoding_Term.Echo "</initial_stats>";
              FStarC_SMTEncoding_Term.CheckSat;
              FStarC_SMTEncoding_Term.SetOption ("rlimit", "0");
              FStarC_SMTEncoding_Term.GetReasonUnknown] in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    (FStarC_SMTEncoding_Term.Push Prims.int_zero) :: uu___1 in
  let uu___1 =
    let uu___2 =
      let uu___3 =
        let uu___4 = FStarC_Options.print_z3_statistics () in
        if uu___4 then true else FStarC_Options.query_stats () in
      if uu___3 then [FStarC_SMTEncoding_Term.GetStatistics] else [] in
    FStarC_List.op_At uu___2
      [FStarC_SMTEncoding_Term.Echo "</goal>";
      FStarC_SMTEncoding_Term.Pop Prims.int_zero] in
  FStarC_List.op_At uu___ uu___1
let rec emit_goals (pending : Prims.int -> Prims.bool)
  (settings : query_settings)
  (t : FStarC_SMTEncoding_ErrorReporting.goal_tree) :
  (FStarC_SMTEncoding_Term.decl Prims.list *
    FStarC_SMTEncoding_ErrorReporting.goal Prims.list)=
  match t with
  | FStarC_SMTEncoding_ErrorReporting.GTrivial -> ([], [])
  | FStarC_SMTEncoding_ErrorReporting.GLeaf g ->
      let uu___ = pending g.FStarC_SMTEncoding_ErrorReporting.goal_id in
      if uu___
      then let uu___1 = goal_block settings g in (uu___1, [g])
      else ([], [])
  | FStarC_SMTEncoding_ErrorReporting.GCtx (ds, uu___, t1) ->
      let uu___1 = emit_goals pending settings t1 in
      (match uu___1 with
       | (ds', gs) ->
           (match gs with
            | [] -> ([], [])
            | uu___2 ->
                ((FStarC_List.op_At
                    (FStarC_List.op_At
                       ((FStarC_SMTEncoding_Term.Push Prims.int_zero) :: ds)
                       ds') [FStarC_SMTEncoding_Term.Pop Prims.int_zero]),
                  gs)))
  | FStarC_SMTEncoding_ErrorReporting.GBranch ts ->
      FStarC_List.fold_left
        (fun uu___ t1 ->
           match uu___ with
           | (ds, gs) ->
               let uu___1 = emit_goals pending settings t1 in
               (match uu___1 with
                | (ds', gs') ->
                    ((FStarC_List.op_At ds ds'), (FStarC_List.op_At gs gs'))))
        ([], []) ts
let query_errors (settings : query_settings)
  (z3result : FStarC_SMTEncoding_Z3.z3result) :
  errors FStar_Pervasives_Native.option=
  match z3result.FStarC_SMTEncoding_Z3.z3result_status with
  | FStarC_SMTEncoding_Z3.UNSAT -> FStar_Pervasives_Native.None
  | uu___ ->
      let msg =
        FStarC_SMTEncoding_Z3.status_string
          z3result.FStarC_SMTEncoding_Z3.z3result_status in
      FStar_Pervasives_Native.Some
        {
          error_reason = msg;
          error_rlimit = (settings.query_rlimit);
          error_fuel = (settings.query_fuel);
          error_ifuel = (settings.query_ifuel)
        }
let errors_to_report (tried_recovery : Prims.bool)
  (settings : query_settings) (gst : goal_state) :
  FStarC_Errors.error Prims.list=
  let format_smt_error msg =
    let d =
      let uu___ =
        let uu___1 = FStarC_Errors_Msg.sublist FStar_Pprint.empty msg in
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Errors_Msg.bulleted
                [FStarC_Errors_Msg.text
                   "'canceled' or 'resource limits reached' means the SMT query timed out, so you might want to increase the rlimit";
                FStarC_Errors_Msg.text
                  "'incomplete quantifiers' means Z3 could not prove the query, so try to spell out your proof out in greater detail, increase fuel or ifuel";
                FStarC_Errors_Msg.text
                  "'unknown' means Z3 provided no further reason for the proof failing"] in
            FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "Note:")
              uu___4 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu___3 in
        FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
      FStar_Pprint.op_Hat_Hat (FStar_Pprint.doc_of_string "SMT solver says:")
        uu___ in
    [d] in
  let recovery_failed_msg =
    if tried_recovery
    then
      [FStarC_Errors_Msg.text
         "This query was retried due to the --proof_recovery option, yet it\n               still failed on all attempts."]
    else [] in
  let smt_error =
    let uu___ = FStarC_Options.query_stats () in
    if uu___
    then
      let uu___1 =
        let uu___2 = FStarC_List.map error_to_short_string gst.gs_errors in
        FStarC_List.map FStar_Pprint.doc_of_string uu___2 in
      format_smt_error uu___1
    else
      (let uu___1 =
         FStarC_List.fold_left
           (fun uu___2 err ->
              match uu___2 with
              | (ic, cc, uc, bc) ->
                  let err1 =
                    if
                      FStarC_Util.starts_with err.error_reason
                        "unknown because "
                    then
                      FStarC_Util.substring_from err.error_reason
                        (FStarC_String.length "unknown because ")
                    else err.error_reason in
                  if FStarC_Util.starts_with err1 "(incomplete"
                  then ((ic + Prims.int_one), cc, uc, bc)
                  else
                    if
                      ((FStarC_Util.starts_with err1 "canceled") ||
                         (FStarC_Util.starts_with err1 "(resource"))
                        || (FStarC_Util.starts_with err1 "timeout")
                    then (ic, (cc + Prims.int_one), uc, bc)
                    else
                      if
                        FStarC_Util.starts_with err1
                          "Overflow encountered when expanding old_vector"
                      then (ic, cc, uc, (bc + Prims.int_one))
                      else (ic, cc, (uc + Prims.int_one), bc))
           (Prims.int_zero, Prims.int_zero, Prims.int_zero, Prims.int_zero)
           gst.gs_errors in
       match uu___1 with
       | (incomplete_count, canceled_count, unknown_count,
          z3_overflow_bug_count) ->
           (if z3_overflow_bug_count > Prims.int_zero
            then
              FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range
                (gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_range
                FStarC_Errors_Codes.Warning_UnexpectedZ3Stderr ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic
                   [FStarC_Errors_Msg.text
                      "Z3 ran into an internal overflow while trying to prove this query.";
                   FStarC_Errors_Msg.text
                     "Try breaking it down into smaller pieces."])
            else ();
            (let base =
               match (incomplete_count, canceled_count, unknown_count) with
               | (uu___3, uu___4, uu___5) when
                   ((uu___4 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                     && (incomplete_count > Prims.int_zero)
                   ->
                   [FStarC_Errors_Msg.text
                      "The SMT solver could not prove the query."]
               | (uu___3, uu___4, uu___5) when
                   ((uu___3 = Prims.int_zero) && (uu___5 = Prims.int_zero))
                     && (canceled_count > Prims.int_zero)
                   ->
                   [FStarC_Errors_Msg.text
                      "The SMT query timed out, you might want to increase the rlimit"]
               | (uu___3, uu___4, uu___5) ->
                   [FStarC_Errors_Msg.text
                      "Try with --query_stats to get more details"] in
             FStarC_List.op_At base recovery_failed_msg))) in
  let goal_detail =
    let ctx_doc c =
      match c with
      | FStarC_SMTEncoding_ErrorReporting.CVar x ->
          let uu___ =
            let uu___1 =
              FStarC_Class_PP.pp FStarC_Ident.pretty_ident
                x.FStarC_Syntax_Syntax.ppname in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                    x.FStarC_Syntax_Syntax.sort in
                FStar_Pprint.nest (Prims.of_int 2) uu___4 in
              FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text " :")
                uu___3 in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___
      | FStarC_SMTEncoding_ErrorReporting.CDef (x, e) ->
          let uu___ =
            let uu___1 =
              FStarC_Class_PP.pp FStarC_Ident.pretty_ident
                x.FStarC_Syntax_Syntax.ppname in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term e in
                FStar_Pprint.nest (Prims.of_int 2) uu___4 in
              FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text " =")
                uu___3 in
            FStar_Pprint.op_Hat_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___
      | FStarC_SMTEncoding_ErrorReporting.CHyp p ->
          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term p
      | FStarC_SMTEncoding_ErrorReporting.CMatch (e, p) ->
          let uu___ =
            let uu___1 = FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term e in
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Syntax_Print.showable_pat p in
                  FStar_Pprint.doc_of_string uu___5 in
                FStar_Pprint.nest (Prims.of_int 2) uu___4 in
              FStar_Pprint.op_Hat_Slash_Hat
                (FStarC_Errors_Msg.text "matches") uu___3 in
            FStar_Pprint.op_Hat_Slash_Hat uu___1 uu___2 in
          FStar_Pprint.group uu___ in
    let ctx =
      let uu___ =
        FStarC_SMTEncoding_ErrorReporting.goal_context settings.query_goals
          gst.gs_goal in
      FStarC_List.map ctx_doc uu___ in
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
            (gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_source in
        FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
          (FStarC_Errors_Msg.text "Failed to prove:") uu___2 in
      [uu___1] in
    FStarC_List.op_At uu___
      (if match ctx with | [] -> true | uu___1 -> false
       then []
       else
         [FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
            (FStarC_Errors_Msg.text "In context:")
            (FStar_Pprint.separate FStar_Pprint.hardline ctx)]) in
  let vc_detail =
    let uu___ = FStarC_Options.query_stats () in
    if uu___
    then
      let uu___1 =
        let uu___2 =
          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
            settings.query_term in
        FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
          (FStarC_Errors_Msg.text "VC =") uu___2 in
      [uu___1]
    else [] in
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Errors.get_ctx () in
      (FStarC_Errors_Codes.Error_Z3SolverError,
        ((gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_msg),
        ((gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_range), uu___2) in
    [uu___1] in
  FStarC_TypeChecker_Err.errors_smt_detail
    (settings.query_env).FStarC_SMTEncoding_Env.tcenv uu___
    (FStarC_List.op_At smt_error (FStarC_List.op_At goal_detail vc_detail))
type unique_string_accumulator =
  {
  add: Prims.string -> unit ;
  get: unit -> Prims.string Prims.list ;
  clear: unit -> unit }
let __proj__Mkunique_string_accumulator__item__add
  (projectee : unique_string_accumulator) : Prims.string -> unit=
  match projectee with | { add; get; clear;_} -> add
let __proj__Mkunique_string_accumulator__item__get
  (projectee : unique_string_accumulator) : unit -> Prims.string Prims.list=
  match projectee with | { add; get; clear;_} -> get
let __proj__Mkunique_string_accumulator__item__clear
  (projectee : unique_string_accumulator) : unit -> unit=
  match projectee with | { add; get; clear;_} -> clear
let mk_unique_string_accumulator (uu___ : unit) : unique_string_accumulator=
  let strings = FStarC_Effect.mk_ref [] in
  let add m =
    let ms = FStarC_Effect.op_Bang strings in
    if FStarC_List.contains m ms
    then ()
    else FStarC_Effect.op_Colon_Equals strings (m :: ms) in
  let get uu___1 =
    let uu___2 = FStarC_Effect.op_Bang strings in
    FStarC_Util.sort_with FStarC_String.compare uu___2 in
  let clear uu___1 = FStarC_Effect.op_Colon_Equals strings [] in
  { add; get; clear }
let div_with_decimals (ndec : Prims.nat) (x : Prims.int) (y : Prims.int) :
  Prims.string=
  let mul =
    let rec aux n =
      if n = Prims.int_zero
      then Prims.int_one
      else (Prims.of_int 10) * (aux (n - Prims.int_one)) in
    aux ndec in
  let intg = x / y in
  let frac = (mod) ((mul * x) / y) mul in
  let frac1 =
    let len =
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int frac in
      FStarC_String.length uu___ in
    let pad = ndec - len in
    let uu___ = FStarC_String.make pad 48 in
    let uu___1 = FStarC_Class_Show.show FStarC_Class_Show.showable_int frac in
    Prims.strcat uu___ uu___1 in
  let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int intg in
  Prims.strcat uu___ (Prims.strcat "." frac1)
let full_query_id (settings : query_settings) : Prims.string=
  let uu___ =
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStarC_Class_Show.show FStarC_Class_Show.showable_int
            settings.query_index in
        Prims.strcat uu___3 ")" in
      Prims.strcat ", " uu___2 in
    Prims.strcat settings.query_name uu___1 in
  Prims.strcat "(" uu___
let query_info (settings : query_settings)
  (g : FStarC_SMTEncoding_ErrorReporting.goal)
  (z3result : FStarC_SMTEncoding_Z3.z3result) : unit=
  let uu___ = FStarC_Options.query_stats () in
  if uu___
  then
    let status_string =
      FStarC_SMTEncoding_Z3.status_string
        z3result.FStarC_SMTEncoding_Z3.z3result_status in
    let at_log_file =
      match z3result.FStarC_SMTEncoding_Z3.z3result_log_file with
      | FStar_Pervasives_Native.None -> ""
      | FStar_Pervasives_Native.Some s -> Prims.strcat "@" s in
    let tag =
      match z3result.FStarC_SMTEncoding_Z3.z3result_status with
      | FStarC_SMTEncoding_Z3.UNSAT ->
          FStarC_Format.colorize_green "succeeded"
      | uu___1 ->
          FStarC_Format.colorize_red
            (Prims.strcat "failed {reason-unknown="
               (Prims.strcat status_string "}")) in
    let range =
      let uu___1 =
        let uu___2 =
          FStarC_Class_Show.show FStarC_Range_Ops.showable_range
            g.FStarC_SMTEncoding_ErrorReporting.goal_range in
        Prims.strcat uu___2 (Prims.strcat at_log_file ")") in
      Prims.strcat "(" uu___1 in
    let used_rlimit_str =
      try
        (fun uu___1 ->
           match () with
           | () ->
               let decimals = Prims.of_int 3 in
               let r0 =
                 let uu___2 =
                   let uu___3 =
                     FStarC_SMap.try_find
                       z3result.FStarC_SMTEncoding_Z3.z3result_initial_statistics
                       "rlimit-count" in
                   match uu___3 with | FStar_Pervasives_Native.Some v -> v in
                 FStarC_Util.int_of_string uu___2 in
               let r1 =
                 let uu___2 =
                   let uu___3 =
                     FStarC_SMap.try_find
                       z3result.FStarC_SMTEncoding_Z3.z3result_statistics
                       "rlimit-count" in
                   match uu___3 with | FStar_Pervasives_Native.Some v -> v in
                 FStarC_Util.int_of_string uu___2 in
               let used = r1 - r0 in
               let uu___2 = convert_rlimit Prims.int_one in
               div_with_decimals decimals used uu___2) ()
      with | uu___1 -> "unknown" in
    let time_str =
      let uu___1 =
        FStarC_SMap.try_find
          z3result.FStarC_SMTEncoding_Z3.z3result_statistics "time" in
      match uu___1 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None -> "0.00" in
    ((let uu___2 = FStarC_Options_Ext.enabled "query_stats_trace" in
      if uu___2
      then
        let uu___3 =
          let uu___4 = FStarC_Util.stack_dump () in
          let uu___5 =
            let uu___6 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                settings.query_term in
            [uu___6] in
          uu___4 :: uu___5 in
        FStarC_Format.print "At %s\nQuery term is %s\n" uu___3
      else ());
     (let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 =
              FStarC_Class_Show.show FStarC_Class_Show.showable_int
                settings.query_index in
            let uu___6 =
              let uu___7 =
                FStarC_Class_Show.show FStarC_Class_Show.showable_int
                  g.FStarC_SMTEncoding_ErrorReporting.goal_id in
              let uu___8 =
                let uu___9 =
                  let uu___10 =
                    let uu___11 =
                      FStarC_Class_Show.show FStarC_Class_Show.showable_int
                        settings.query_fuel in
                    let uu___12 =
                      let uu___13 =
                        FStarC_Class_Show.show FStarC_Class_Show.showable_int
                          settings.query_ifuel in
                      let uu___14 =
                        let uu___15 =
                          FStarC_Class_Show.show
                            FStarC_Class_Show.showable_int
                            settings.query_rlimit in
                        [uu___15; used_rlimit_str] in
                      uu___13 :: uu___14 in
                    uu___11 :: uu___12 in
                  time_str :: uu___10 in
                tag :: uu___9 in
              uu___7 :: uu___8 in
            uu___5 :: uu___6 in
          (settings.query_name) :: uu___4 in
        range :: uu___3 in
      FStarC_Format.print
        "%s\tQuery-stats (%s, %s)\tgoal %s %s in %s seconds with fuel %s and ifuel %s and rlimit %s (used rlimit %s)\n"
        uu___2))
  else ()
type answer =
  {
  ok: Prims.bool ;
  cache_hit: Prims.bool ;
  quaking: Prims.bool ;
  quaking_or_retrying: Prims.bool ;
  lo: Prims.int ;
  hi: Prims.int ;
  tried_recovery: Prims.bool ;
  failed: goal_state Prims.list }
let __proj__Mkanswer__item__ok (projectee : answer) : Prims.bool=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> ok
let __proj__Mkanswer__item__cache_hit (projectee : answer) : Prims.bool=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> cache_hit
let __proj__Mkanswer__item__quaking (projectee : answer) : Prims.bool=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> quaking
let __proj__Mkanswer__item__quaking_or_retrying (projectee : answer) :
  Prims.bool=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> quaking_or_retrying
let __proj__Mkanswer__item__lo (projectee : answer) : Prims.int=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> lo
let __proj__Mkanswer__item__hi (projectee : answer) : Prims.int=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> hi
let __proj__Mkanswer__item__tried_recovery (projectee : answer) : Prims.bool=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> tried_recovery
let __proj__Mkanswer__item__failed (projectee : answer) :
  goal_state Prims.list=
  match projectee with
  | { ok; cache_hit; quaking; quaking_or_retrying; lo; hi; tried_recovery;
      failed;_} -> failed
let ans_ok : answer=
  {
    ok = true;
    cache_hit = false;
    quaking = false;
    quaking_or_retrying = false;
    lo = Prims.int_one;
    hi = Prims.int_one;
    tried_recovery = false;
    failed = []
  }
let ans_fail : answer=
  {
    ok = false;
    cache_hit = (ans_ok.cache_hit);
    quaking = (ans_ok.quaking);
    quaking_or_retrying = (ans_ok.quaking_or_retrying);
    lo = (ans_ok.lo);
    hi = (ans_ok.hi);
    tried_recovery = (ans_ok.tried_recovery);
    failed = (ans_ok.failed)
  }
let uu___0 : answer FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun ans ->
         let uu___ =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool ans.ok in
         let uu___1 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int ans.lo in
         let uu___2 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int ans.hi in
         let uu___3 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             ans.tried_recovery in
         FStarC_Format.fmt4 "ok=%s lo=%s hi=%s tried_recovery=%s" uu___
           uu___1 uu___2 uu___3)
  }
let make_solver_configs (env : FStarC_SMTEncoding_Env.env_t)
  (goals : FStarC_SMTEncoding_ErrorReporting.goal_tree)
  (query_term : FStarC_Syntax_Syntax.term) : query_settings Prims.list=
  let uu___ =
    match (env.FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.qtbl_name_and_index
    with
    | (FStar_Pervasives_Native.None, uu___1) ->
        FStarC_Effect.failwith "No query name set!"
    | (FStar_Pervasives_Native.Some (q, _typ, n), uu___1) ->
        ((FStarC_Ident.string_of_lid q), n) in
  match uu___ with
  | (qname, index) ->
      let default_settings =
        let rlimit =
          let uu___1 = FStarC_Options.z3_rlimit_factor () in
          let uu___2 = FStarC_Options.z3_rlimit () in uu___1 * uu___2 in
        let uu___1 = FStarC_Options.initial_fuel () in
        let uu___2 = FStarC_Options.initial_ifuel () in
        {
          query_env = env;
          query_name = qname;
          query_index = index;
          query_range =
            (FStarC_TypeChecker_Env.get_range
               env.FStarC_SMTEncoding_Env.tcenv);
          query_fuel = uu___1;
          query_ifuel = uu___2;
          query_rlimit = rlimit;
          query_goals = goals;
          query_term
        } in
      let initial_fuel_max_ifuel =
        let uu___1 =
          let uu___2 = FStarC_Options.max_ifuel () in
          let uu___3 = FStarC_Options.initial_ifuel () in uu___2 > uu___3 in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStarC_Options.max_ifuel () in
            {
              query_env = (default_settings.query_env);
              query_name = (default_settings.query_name);
              query_index = (default_settings.query_index);
              query_range = (default_settings.query_range);
              query_fuel = (default_settings.query_fuel);
              query_ifuel = uu___3;
              query_rlimit = (default_settings.query_rlimit);
              query_goals = (default_settings.query_goals);
              query_term = (default_settings.query_term)
            } in
          [uu___2]
        else [] in
      let half_max_fuel_max_ifuel =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Options.max_fuel () in
            uu___3 / (Prims.of_int 2) in
          let uu___3 = FStarC_Options.initial_fuel () in uu___2 > uu___3 in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Options.max_fuel () in
              uu___4 / (Prims.of_int 2) in
            let uu___4 = FStarC_Options.max_ifuel () in
            {
              query_env = (default_settings.query_env);
              query_name = (default_settings.query_name);
              query_index = (default_settings.query_index);
              query_range = (default_settings.query_range);
              query_fuel = uu___3;
              query_ifuel = uu___4;
              query_rlimit = (default_settings.query_rlimit);
              query_goals = (default_settings.query_goals);
              query_term = (default_settings.query_term)
            } in
          [uu___2]
        else [] in
      let max_fuel_max_ifuel =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Options.max_fuel () in
            let uu___4 = FStarC_Options.initial_fuel () in uu___3 > uu___4 in
          if uu___2
          then
            let uu___3 = FStarC_Options.max_ifuel () in
            let uu___4 = FStarC_Options.initial_ifuel () in uu___3 >= uu___4
          else false in
        if uu___1
        then
          let uu___2 =
            let uu___3 = FStarC_Options.max_fuel () in
            let uu___4 = FStarC_Options.max_ifuel () in
            {
              query_env = (default_settings.query_env);
              query_name = (default_settings.query_name);
              query_index = (default_settings.query_index);
              query_range = (default_settings.query_range);
              query_fuel = uu___3;
              query_ifuel = uu___4;
              query_rlimit = (default_settings.query_rlimit);
              query_goals = (default_settings.query_goals);
              query_term = (default_settings.query_term)
            } in
          [uu___2]
        else [] in
      FStarC_List.op_At [default_settings]
        (FStarC_List.op_At initial_fuel_max_ifuel
           (FStarC_List.op_At half_max_fuel_max_ifuel max_fuel_max_ifuel))
let killed_result (uu___ : unit) : FStarC_SMTEncoding_Z3.z3result=
  let uu___1 = FStarC_SMap.create Prims.int_zero in
  let uu___2 = FStarC_SMap.create Prims.int_zero in
  {
    FStarC_SMTEncoding_Z3.z3result_status = FStarC_SMTEncoding_Z3.KILLED;
    FStarC_SMTEncoding_Z3.z3result_time = Prims.int_zero;
    FStarC_SMTEncoding_Z3.z3result_initial_statistics = uu___1;
    FStarC_SMTEncoding_Z3.z3result_statistics = uu___2;
    FStarC_SMTEncoding_Z3.z3result_log_file = FStar_Pervasives_Native.None
  }
let rec zip_results (gs : FStarC_SMTEncoding_ErrorReporting.goal Prims.list)
  (rs : FStarC_SMTEncoding_Z3.z3result Prims.list) :
  (FStarC_SMTEncoding_ErrorReporting.goal * FStarC_SMTEncoding_Z3.z3result)
    Prims.list=
  match gs with
  | [] -> []
  | g::gs1 ->
      (match rs with
       | r::rs1 -> let uu___ = zip_results gs1 rs1 in (g, r) :: uu___
       | [] ->
           let uu___ = let uu___1 = killed_result () in (g, uu___1) in
           let uu___1 = zip_results gs1 [] in uu___ :: uu___1)
let run_round (settings : query_settings) (active : goal_state Prims.list) :
  goal_state Prims.list=
  match active with
  | [] -> []
  | uu___ ->
      ((let uu___2 = FStarC_Options.z3_refresh () in
        if uu___2
        then
          FStarC_SMTEncoding_Z3.refresh
            (FStar_Pervasives_Native.Some
               (((settings.query_env).FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.proof_ns))
        else ());
       (let ids =
          FStarC_List.map
            (fun gst ->
               (gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_id)
            active in
        let uu___2 =
          emit_goals (fun id -> FStarC_List.contains id ids) settings
            settings.query_goals in
        match uu___2 with
        | (decls, emitted) ->
            let results =
              let uu___3 =
                let uu___4 =
                  FStarC_Class_Show.show FStarC_Class_Show.showable_int
                    settings.query_index in
                FStarC_Format.fmt2 "(%s, %s)" settings.query_name uu___4 in
              FStarC_SMTEncoding_Z3.ask settings.query_range decls uu___3
                false in
            let results1 = zip_results emitted results in
            FStarC_List.map
              (fun gst ->
                 let uu___3 =
                   FStarC_List.tryFind
                     (fun uu___4 ->
                        match uu___4 with
                        | (g, uu___5) ->
                            g.FStarC_SMTEncoding_ErrorReporting.goal_id =
                              (gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_id)
                     results1 in
                 match uu___3 with
                 | FStar_Pervasives_Native.None -> gst
                 | FStar_Pervasives_Native.Some (g, r) ->
                     (query_info settings g r;
                      (let uu___5 = query_errors settings r in
                       match uu___5 with
                       | FStar_Pervasives_Native.None ->
                           {
                             gs_goal = (gst.gs_goal);
                             gs_nsuccess = (gst.gs_nsuccess + Prims.int_one);
                             gs_nfailure = (gst.gs_nfailure);
                             gs_errors = (gst.gs_errors)
                           }
                       | FStar_Pervasives_Native.Some e ->
                           {
                             gs_goal = (gst.gs_goal);
                             gs_nsuccess = (gst.gs_nsuccess);
                             gs_nfailure = (gst.gs_nfailure + Prims.int_one);
                             gs_errors = (e :: (gst.gs_errors))
                           }))) active))
let quake_bounds (uu___ : unit) : (Prims.int * Prims.int)=
  let lo = FStarC_Options.quake_lo () in
  let hi = FStarC_Options.quake_hi () in
  let hi1 = if hi < Prims.int_one then Prims.int_one else hi in
  let lo1 =
    if lo < Prims.int_one
    then Prims.int_one
    else if lo > hi1 then hi1 else lo in
  (lo1, hi1)
let ask_config (settings : query_settings) (goals : goal_state Prims.list) :
  goal_state Prims.list=
  let uu___ = quake_bounds () in
  match uu___ with
  | (lo, hi) ->
      let decided gst =
        let uu___1 =
          let uu___2 = FStarC_Options.quake_keep () in Prims.not uu___2 in
        if uu___1
        then (gst.gs_nsuccess >= lo) || (gst.gs_nfailure > (hi - lo))
        else false in
      let rec rounds n active acc =
        if n <= Prims.int_zero
        then FStarC_List.op_At active acc
        else
          (let active1 = run_round settings active in
           let uu___1 = FStarC_List.partition decided active1 in
           match uu___1 with
           | (done_, active2) ->
               rounds (n - Prims.int_one) active2
                 (FStarC_List.op_At done_ acc)) in
      rounds hi goals []
let rec ask_configs (configs : query_settings Prims.list)
  (goals : goal_state Prims.list) : goal_state Prims.list=
  let uu___ = quake_bounds () in
  match uu___ with
  | (lo, uu___1) ->
      (match configs with
       | [] -> goals
       | cfg::configs1 ->
           let goals1 = ask_config cfg goals in
           let failed =
             FStarC_List.filter (fun gst -> gst.gs_nsuccess < lo) goals1 in
           (match (failed, configs1) with
            | ([], uu___2) -> []
            | (uu___2, []) -> failed
            | uu___2 ->
                let uu___3 =
                  FStarC_List.map
                    (fun gst ->
                       {
                         gs_goal = (gst.gs_goal);
                         gs_nsuccess = Prims.int_zero;
                         gs_nfailure = Prims.int_zero;
                         gs_errors = (gst.gs_errors)
                       }) failed in
                ask_configs configs1 uu___3))
let mk_answer (failed : goal_state Prims.list) : answer=
  let uu___ = quake_bounds () in
  match uu___ with
  | (lo, hi) ->
      let uu___1 =
        if hi > Prims.int_one
        then let uu___2 = FStarC_Options.retry () in Prims.not uu___2
        else false in
      {
        ok = ((match failed with | [] -> true | uu___2 -> false));
        cache_hit = (ans_ok.cache_hit);
        quaking = uu___1;
        quaking_or_retrying = (hi > Prims.int_one);
        lo;
        hi;
        tried_recovery = (ans_ok.tried_recovery);
        failed
      }
let ask_solver_quake (configs : query_settings Prims.list) : answer=
  let default_settings = FStarC_List.hd configs in
  let goals =
    let uu___ =
      FStarC_SMTEncoding_ErrorReporting.goals_of default_settings.query_goals in
    FStarC_List.map initial_goal_state uu___ in
  let ans = let uu___ = ask_configs configs goals in mk_answer uu___ in
  if ans.quaking
  then
    (let name = full_query_id default_settings in
     let ngoals = FStarC_List.length goals in
     let nfail = FStarC_List.length ans.failed in
     let ratio =
       let uu___1 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_int
           (ngoals - nfail) in
       let uu___2 =
         FStarC_Class_Show.show FStarC_Class_Show.showable_nat ngoals in
       FStarC_Format.fmt2 "%s/%s" uu___1 uu___2 in
     let ratio1 =
       if nfail = Prims.int_zero
       then FStarC_Format.colorize_green ratio
       else FStarC_Format.colorize_red ratio in
     FStarC_Format.print2 "Quake: query %s \tproved %s goals\n" name ratio1)
  else ();
  ans
type recovery_hammer =
  | IncreaseRLimit of Prims.int 
  | RestartAnd of recovery_hammer 
let uu___is_IncreaseRLimit (projectee : recovery_hammer) : Prims.bool=
  match projectee with | IncreaseRLimit _0 -> true | uu___ -> false
let __proj__IncreaseRLimit__item___0 (projectee : recovery_hammer) :
  Prims.int= match projectee with | IncreaseRLimit _0 -> _0
let uu___is_RestartAnd (projectee : recovery_hammer) : Prims.bool=
  match projectee with | RestartAnd _0 -> true | uu___ -> false
let __proj__RestartAnd__item___0 (projectee : recovery_hammer) :
  recovery_hammer= match projectee with | RestartAnd _0 -> _0
let rec pp_hammer (h : recovery_hammer) : FStar_Pprint.document=
  match h with
  | IncreaseRLimit factor ->
      let uu___ =
        let uu___1 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int factor in
        FStar_Pprint.op_Hat_Hat uu___1 (FStar_Pprint.doc_of_string "x") in
      FStar_Pprint.op_Hat_Slash_Hat
        (FStarC_Errors_Msg.text "increasing its rlimit by") uu___
  | RestartAnd h1 ->
      let uu___ = pp_hammer h1 in
      FStar_Pprint.op_Hat_Slash_Hat
        (FStarC_Errors_Msg.text "restarting the solver and") uu___
let ask_solver_recover (configs : query_settings Prims.list) : answer=
  let uu___ = FStarC_Options.proof_recovery () in
  if uu___
  then
    let r = ask_solver_quake configs in
    (if r.ok
     then r
     else
       (let cfg = FStarC_List.last configs in
        FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
          cfg.query_range ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                "This query failed to be solved. Will now retry with higher rlimits due to --proof_recovery."]);
        (let try_factor n =
           (let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Class_PP.pp FStarC_Class_PP.pp_int n in
                FStar_Pprint.op_Hat_Slash_Hat
                  (FStarC_Errors_Msg.text "Retrying query with rlimit factor")
                  uu___5 in
              [uu___4] in
            FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
              cfg.query_range ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___3));
           (let cfg1 =
              {
                query_env = (cfg.query_env);
                query_name = (cfg.query_name);
                query_index = (cfg.query_index);
                query_range = (cfg.query_range);
                query_fuel = (cfg.query_fuel);
                query_ifuel = (cfg.query_ifuel);
                query_rlimit = (n * cfg.query_rlimit);
                query_goals = (cfg.query_goals);
                query_term = (cfg.query_term)
              } in
            ask_solver_quake [cfg1]) in
         let rec try_hammer h =
           match h with
           | IncreaseRLimit factor -> try_factor factor
           | RestartAnd h1 ->
               (FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
                  cfg.query_range ()
                  (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                  (Obj.magic
                     [FStarC_Errors_Msg.text "Trying a solver restart"]);
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
                 tried_recovery = true;
                 failed = (r.failed)
               }
           | h::hs ->
               let r1 = try_hammer h in
               if r1.ok
               then
                 ((let uu___3 =
                     let uu___4 =
                       let uu___5 = pp_hammer h in
                       FStar_Pprint.op_Hat_Slash_Hat
                         (FStarC_Errors_Msg.text
                            "This query succeeded after ") uu___5 in
                     [uu___4;
                     FStarC_Errors_Msg.text
                       "Increase the rlimit in the file or simplify the proof. This is only succeeding due to --proof_recovery being given."] in
                   FStarC_Errors.log_issue
                     FStarC_Class_HasRange.hasRange_range cfg.query_range
                     FStarC_Errors_Codes.Warning_ProofRecovery ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___3));
                  r1)
               else aux hs in
         aux
           [IncreaseRLimit (Prims.of_int 2);
           IncreaseRLimit (Prims.of_int 4);
           IncreaseRLimit (Prims.of_int 8);
           RestartAnd (IncreaseRLimit (Prims.of_int 8))])))
  else ask_solver_quake configs
let failing_query_ctr : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let maybe_save_failing_query (env : FStarC_SMTEncoding_Env.env_t)
  (qs : query_settings) : unit=
  (let uu___1 = FStarC_Options.log_failing_queries () in
   if uu___1
   then
     let mod1 =
       FStarC_Class_Show.show FStarC_Ident.showable_lident
         (FStarC_TypeChecker_Env.current_module
            env.FStarC_SMTEncoding_Env.tcenv) in
     let n =
       (let uu___3 =
          let uu___4 = FStarC_Effect.op_Bang failing_query_ctr in
          uu___4 + Prims.int_one in
        FStarC_Effect.op_Colon_Equals failing_query_ctr uu___3);
       FStarC_Effect.op_Bang failing_query_ctr in
     let file_name =
       let uu___2 = FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
       FStarC_Format.fmt2 "failedQueries-%s-%s.smt2" mod1 uu___2 in
     let uu___2 = emit_goals (fun uu___3 -> true) qs qs.query_goals in
     match uu___2 with
     | (decls, uu___3) ->
         let query_str =
           let uu___4 =
             let uu___5 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_int
                 qs.query_index in
             FStarC_Format.fmt2 "(%s, %s)" qs.query_name uu___5 in
           FStarC_SMTEncoding_Z3.ask_text qs.query_range decls uu___4 in
         FStarC_Util.write_file file_name query_str
   else ());
  (let uu___2 = FStarC_Effect.op_Bang dbg_SMTFail in
   if uu___2
   then
     let uu___3 =
       let uu___4 =
         let uu___5 =
           let uu___6 =
             let uu___7 =
               FStarC_TypeChecker_Env.all_binders
                 (qs.query_env).FStarC_SMTEncoding_Env.tcenv in
             FStarC_Pprint.flow_map (FStar_Pprint.break_ Prims.int_one)
               (fun b ->
                  let uu___8 =
                    let uu___9 =
                      let uu___10 =
                        let uu___11 =
                          FStarC_Class_PP.pp FStarC_Ident.pretty_ident
                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname in
                        let uu___12 =
                          let uu___13 =
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term
                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                            uu___13 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___11 uu___12 in
                      FStar_Pprint.nest (Prims.of_int 2) uu___10 in
                    FStar_Pprint.parens uu___9 in
                  FStar_Pprint.group uu___8) uu___7 in
           FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
             (FStarC_Errors_Msg.text "Env =") uu___6 in
         let uu___6 =
           let uu___7 =
             let uu___8 =
               FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                 qs.query_term in
             FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
               (FStarC_Errors_Msg.text "VC =") uu___8 in
           [uu___7] in
         uu___5 :: uu___6 in
       (FStarC_Errors_Msg.text "A query failed.") :: uu___4 in
     FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range qs.query_range
       () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic uu___3)
   else ())
let ask_solver (env : FStarC_SMTEncoding_Env.env_t)
  (configs : query_settings Prims.list) :
  (query_settings Prims.list * answer)=
  let default_settings = FStarC_List.hd configs in
  let skip =
    if (env.FStarC_SMTEncoding_Env.tcenv).FStarC_TypeChecker_Env.admit
    then true
    else
      (let uu___ = FStarC_Options.admit_except () in
       match uu___ with
       | FStar_Pervasives_Native.Some id ->
           if FStarC_Util.starts_with id "("
           then let uu___1 = full_query_id default_settings in uu___1 <> id
           else default_settings.query_name <> id
       | FStar_Pervasives_Native.None -> false) in
  let ans =
    if skip
    then ans_ok
    else
      (let ans1 = ask_solver_recover configs in
       let cfg = FStarC_List.last configs in
       if Prims.not ans1.ok then maybe_save_failing_query env cfg else ();
       ans1) in
  (configs, ans)
let report (env : FStarC_TypeChecker_Env.env)
  (default_settings : query_settings) (a : answer) : unit=
  let name = full_query_id default_settings in
  FStarC_List.iter
    (fun gst ->
       (let uu___1 = errors_to_report a.tried_recovery default_settings gst in
        FStarC_Errors.add_errors uu___1);
       if a.quaking
       then
         (let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      gst.gs_nsuccess in
                  let uu___6 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      (gst.gs_nsuccess + gst.gs_nfailure) in
                  let uu___7 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      a.lo in
                  let uu___8 =
                    FStarC_Class_Show.show FStarC_Class_Show.showable_int
                      a.hi in
                  FStarC_Format.fmt5
                    "This goal of query %s failed the quake test, %s out of %s attempts succeeded, but the threshold was %s out of %s"
                    name uu___5 uu___6 uu___7 uu___8 in
                FStarC_Errors_Msg.text uu___4 in
              [uu___3] in
            (FStarC_Errors_Codes.Error_QuakeFailed, uu___2) in
          FStarC_TypeChecker_Err.log_issue env
            (gst.gs_goal).FStarC_SMTEncoding_ErrorReporting.goal_range uu___1)
       else ()) a.failed
type solver_cfg =
  {
  seed: Prims.int ;
  cliopt: Prims.string Prims.list ;
  smtopt: Prims.string Prims.list ;
  facts: (Prims.string Prims.list * Prims.bool) Prims.list ;
  z3version: Prims.string ;
  context_pruning: Prims.bool }
let __proj__Mksolver_cfg__item__seed (projectee : solver_cfg) : Prims.int=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} -> seed
let __proj__Mksolver_cfg__item__cliopt (projectee : solver_cfg) :
  Prims.string Prims.list=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} -> cliopt
let __proj__Mksolver_cfg__item__smtopt (projectee : solver_cfg) :
  Prims.string Prims.list=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} -> smtopt
let __proj__Mksolver_cfg__item__facts (projectee : solver_cfg) :
  (Prims.string Prims.list * Prims.bool) Prims.list=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} -> facts
let __proj__Mksolver_cfg__item__z3version (projectee : solver_cfg) :
  Prims.string=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} -> z3version
let __proj__Mksolver_cfg__item__context_pruning (projectee : solver_cfg) :
  Prims.bool=
  match projectee with
  | { seed; cliopt; smtopt; facts; z3version; context_pruning;_} ->
      context_pruning
let _last_cfg : solver_cfg FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let get_cfg (env : FStarC_TypeChecker_Env.env) : solver_cfg=
  let uu___ = FStarC_Options.z3_seed () in
  let uu___1 = FStarC_Options.z3_cliopt () in
  let uu___2 = FStarC_Options.z3_smtopt () in
  let uu___3 = FStarC_Options.z3_version () in
  let uu___4 = FStarC_Options_Ext.enabled "context_pruning" in
  {
    seed = uu___;
    cliopt = uu___1;
    smtopt = uu___2;
    facts = (env.FStarC_TypeChecker_Env.proof_ns);
    z3version = uu___3;
    context_pruning = uu___4
  }
let save_cfg (env : FStarC_TypeChecker_Env.env) : unit=
  let uu___ = let uu___1 = get_cfg env in FStar_Pervasives_Native.Some uu___1 in
  FStarC_Effect.op_Colon_Equals _last_cfg uu___
let maybe_refresh_solver (env : FStarC_TypeChecker_Env.env) : unit=
  let uu___ = FStarC_Effect.op_Bang _last_cfg in
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
let encode_and_ask
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  (query_settings Prims.list * answer)=
  let do1 uu___ =
    maybe_refresh_solver tcenv;
    (let msg =
       let uu___2 =
         FStarC_Range_Ops.string_of_range
           (FStarC_TypeChecker_Env.get_range tcenv) in
       FStarC_Format.fmt1 "Starting query at %s" uu___2 in
     FStarC_SMTEncoding_Encode.push_encoding_state msg;
     (let uu___3 = FStarC_SMTEncoding_Encode.encode_query use_env_msg tcenv q in
      match uu___3 with
      | (prefix, goals) ->
          ((let uu___5 = FStarC_SMTEncoding_ErrorReporting.all_decls goals in
            FStarC_SMTEncoding_Z3.start_query msg prefix uu___5);
           (let finish_query uu___5 =
              let msg1 =
                let uu___6 =
                  FStarC_Range_Ops.string_of_range
                    (FStarC_TypeChecker_Env.get_range tcenv) in
                FStarC_Format.fmt1 "Ending query at %s" uu___6 in
              FStarC_SMTEncoding_Encode.pop_encoding_state msg1;
              FStarC_SMTEncoding_Z3.finish_query msg1 in
            FStarC_Util.finally finish_query
              (fun uu___5 ->
                 let tcenv1 = FStarC_TypeChecker_Env.incr_query_index tcenv in
                 match goals with
                 | FStarC_SMTEncoding_ErrorReporting.GTrivial -> ([], ans_ok)
                 | uu___6 when tcenv1.FStarC_TypeChecker_Env.admit ->
                     ([], ans_ok)
                 | uu___6 ->
                     ((let uu___8 = FStarC_Effect.op_Bang dbg_SMTQuery in
                       if uu___8
                       then
                         let uu___9 =
                           let uu___10 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term q in
                           let uu___11 =
                             let uu___12 =
                               let uu___13 =
                                 FStarC_SMTEncoding_ErrorReporting.goals_of
                                   goals in
                               FStarC_List.length uu___13 in
                             FStarC_Class_Show.show
                               FStarC_Class_Show.showable_nat uu___12 in
                           FStarC_Format.fmt2
                             "Encoded query %s\nwith %s goals" uu___10
                             uu___11 in
                         FStarC_Errors.diag
                           FStarC_Class_HasRange.hasRange_range
                           (FStarC_TypeChecker_Env.get_range tcenv1) ()
                           (Obj.magic
                              FStarC_Errors_Msg.is_error_message_string)
                           (Obj.magic uu___9)
                       else ());
                      (let env =
                         FStarC_SMTEncoding_Encode.get_current_env tcenv1 in
                       let configs = make_solver_configs env goals q in
                       ask_solver env configs))))))) in
  let uu___ = FStarC_Options.admit_smt_queries () in
  if uu___
  then ([], ans_ok)
  else
    (let uu___1 =
       FStarC_SMTEncoding_Solver_Cache.try_find_query_cache tcenv q in
     if uu___1
     then
       ([],
         {
           ok = (ans_ok.ok);
           cache_hit = true;
           quaking = (ans_ok.quaking);
           quaking_or_retrying = (ans_ok.quaking_or_retrying);
           lo = (ans_ok.lo);
           hi = (ans_ok.hi);
           tried_recovery = (ans_ok.tried_recovery);
           failed = (ans_ok.failed)
         })
     else
       (let uu___2 = FStarC_Stats.record "Solver.encode_and_ask" do1 in
        match uu___2 with
        | (cfgs, ans) ->
            (if ans.ok
             then FStarC_SMTEncoding_Solver_Cache.query_cache_add tcenv q
             else ();
             (cfgs, ans))))
let do_solve
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  unit=
  (let uu___1 = FStarC_Effect.op_Bang dbg_SMTQuery in
   if uu___1
   then
     let uu___2 =
       let uu___3 =
         let uu___4 =
           let uu___5 =
             let uu___6 = FStarC_TypeChecker_Env.all_binders tcenv in
             FStarC_Pprint.flow_map (FStar_Pprint.break_ Prims.int_one)
               (fun b ->
                  let uu___7 =
                    let uu___8 =
                      let uu___9 =
                        let uu___10 =
                          FStarC_Class_PP.pp FStarC_Ident.pretty_ident
                            (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname in
                        let uu___11 =
                          let uu___12 =
                            FStarC_Class_PP.pp
                              FStarC_Syntax_Print.pretty_term
                              (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                          FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                            uu___12 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___10 uu___11 in
                      FStar_Pprint.nest (Prims.of_int 2) uu___9 in
                    FStar_Pprint.parens uu___8 in
                  FStar_Pprint.group uu___7) uu___6 in
           FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
             (FStarC_Errors_Msg.text "Env =") uu___5 in
         let uu___5 =
           let uu___6 =
             let uu___7 =
               FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term q in
             FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
               (FStarC_Errors_Msg.text "VC =") uu___7 in
           [uu___6] in
         uu___4 :: uu___5 in
       (FStarC_Errors_Msg.text "Before calling solver.") :: uu___3 in
     FStarC_Errors.diag FStarC_TypeChecker_Env.hasRange_env tcenv ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic uu___2)
   else ());
  (let ans_opt = encode_and_ask use_env_msg tcenv q in
   match ans_opt with
   | (default_settings::uu___1, ans) when Prims.not ans.ok ->
       report tcenv default_settings ans
   | (uu___1, ans) when ans.ok -> ()
   | ([], ans) when Prims.not ans.ok ->
       FStarC_Effect.failwith "impossible: bad answer from encode_and_ask")
let disable_quake_for (f : unit -> 'a) : 'a=
  FStarC_Options.with_saved_options
    (fun uu___ ->
       FStarC_Options.set_option "quake_hi"
         (FStarC_Options.Int Prims.int_one);
       f ())
let solve
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  unit=
  let uu___ = FStarC_Options.no_smt () in
  if uu___
  then
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term q in
            FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text "Query = ")
              uu___5 in
          [uu___4] in
        (FStarC_Errors_Msg.text
           "A query could not be solved internally, and --no_smt was given.")
          :: uu___3 in
      (FStarC_Errors_Codes.Error_NoSMTButNeeded, uu___2) in
    FStarC_TypeChecker_Err.log_issue tcenv tcenv.FStarC_TypeChecker_Env.range
      uu___1
  else
    if tcenv.FStarC_TypeChecker_Env.admit
    then ()
    else
      (FStarC_SMTEncoding_Encode.flush_deferred_encodings ();
       FStarC_Profiling.profile (fun uu___2 -> do_solve use_env_msg tcenv q)
         (FStar_Pervasives_Native.Some
            (FStarC_Ident.string_of_lid
               (FStarC_TypeChecker_Env.current_module tcenv)))
         "FStarC.SMTEncoding.solve_top_level")
let solve_sync
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  answer=
  let uu___ = FStarC_Options.no_smt () in
  if uu___
  then ans_fail
  else
    (FStarC_SMTEncoding_Encode.flush_deferred_encodings ();
     (let go uu___2 =
        (let uu___4 = FStarC_Effect.op_Bang dbg_SMTQuery in
         if uu___4
         then
           let uu___5 =
             let uu___6 =
               let uu___7 =
                 FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term q in
               FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
                 (FStarC_Errors_Msg.text "Running synchronous SMT query. Q =")
                 uu___7 in
             [uu___6] in
           FStarC_Errors.diag FStarC_Class_HasRange.hasRange_range
             q.FStarC_Syntax_Syntax.pos ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___5)
         else ());
        (let uu___4 =
           disable_quake_for
             (fun uu___5 -> encode_and_ask use_env_msg tcenv q) in
         match uu___4 with | (_cfgs, ans) -> ans) in
      FStarC_Profiling.profile go
        (FStar_Pervasives_Native.Some
           (FStarC_Ident.string_of_lid
              (FStarC_TypeChecker_Env.current_module tcenv)))
        "FStarC.SMTEncoding.solve_sync_top_level"))
let solve_sync_bool
  (use_env_msg : (unit -> Prims.string) FStar_Pervasives_Native.option)
  (tcenv : FStarC_TypeChecker_Env.env) (q : FStarC_Syntax_Syntax.term) :
  Prims.bool= let ans = solve_sync use_env_msg tcenv q in ans.ok
let snapshot (msg : Prims.string) :
  ((Prims.int * Prims.int * Prims.int) * unit)=
  let uu___ = FStarC_SMTEncoding_Encode.snapshot_encoding msg in
  match uu___ with
  | (v0, v1) ->
      let v2 = FStarC_SMTEncoding_Z3.snapshot msg in ((v0, v1, v2), ())
let rollback (msg : Prims.string)
  (tok : (Prims.int * Prims.int * Prims.int) FStar_Pervasives_Native.option)
  : unit=
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
let solver : FStarC_TypeChecker_Env.solver_t=
  {
    FStarC_TypeChecker_Env.init =
      (fun e -> save_cfg e; FStarC_SMTEncoding_Encode.init e);
    FStarC_TypeChecker_Env.snapshot = snapshot;
    FStarC_TypeChecker_Env.rollback = rollback;
    FStarC_TypeChecker_Env.encode_sig = FStarC_SMTEncoding_Encode.encode_sig;
    FStarC_TypeChecker_Env.preprocess =
      (fun e g ->
         let uu___ =
           let uu___1 = let uu___2 = FStarC_Options.peek () in (e, g, uu___2) in
           [uu___1] in
         (false, uu___));
    FStarC_TypeChecker_Env.handle_smt_goal = (fun e g -> [(e, g)]);
    FStarC_TypeChecker_Env.solve = solve;
    FStarC_TypeChecker_Env.solve_sync = solve_sync_bool;
    FStarC_TypeChecker_Env.finish = FStarC_SMTEncoding_Z3.stop;
    FStarC_TypeChecker_Env.refresh = FStarC_SMTEncoding_Z3.refresh
  }
let dummy : FStarC_TypeChecker_Env.solver_t=
  {
    FStarC_TypeChecker_Env.init = (fun uu___ -> ());
    FStarC_TypeChecker_Env.snapshot =
      (fun uu___ -> ((Prims.int_zero, Prims.int_zero, Prims.int_zero), ()));
    FStarC_TypeChecker_Env.rollback = (fun uu___ uu___1 -> ());
    FStarC_TypeChecker_Env.encode_sig = (fun uu___ uu___1 -> ());
    FStarC_TypeChecker_Env.preprocess =
      (fun e g ->
         let uu___ =
           let uu___1 = let uu___2 = FStarC_Options.peek () in (e, g, uu___2) in
           [uu___1] in
         (false, uu___));
    FStarC_TypeChecker_Env.handle_smt_goal = (fun e g -> [(e, g)]);
    FStarC_TypeChecker_Env.solve = (fun uu___ uu___1 uu___2 -> ());
    FStarC_TypeChecker_Env.solve_sync = (fun uu___ uu___1 uu___2 -> false);
    FStarC_TypeChecker_Env.finish = (fun uu___ -> ());
    FStarC_TypeChecker_Env.refresh = (fun uu___ -> ())
  }

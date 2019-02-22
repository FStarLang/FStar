open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun msg  ->
      let uu____77303 = FStar_TypeChecker_Tc.snapshot_context env msg  in
      match uu____77303 with
      | (ctx_depth,env1) ->
          let uu____77347 = FStar_Options.snapshot ()  in
          (match uu____77347 with
           | (opt_depth,()) -> ((ctx_depth, opt_depth), env1))
  
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1  ->
    fun msg  ->
      fun uu____77393  ->
        match uu____77393 with
        | (ctx_depth,opt_depth) ->
            let env =
              FStar_TypeChecker_Tc.rollback_context solver1 msg
                (FStar_Pervasives_Native.Some ctx_depth)
               in
            (FStar_Options.rollback (FStar_Pervasives_Native.Some opt_depth);
             env)
  
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck 
let (uu___is_SyntaxCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____77460 -> false
  
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____77471 -> false
  
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____77482 -> false
  
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun check_kind  ->
      let uu___735_77495 = env  in
      let uu____77496 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___735_77495.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___735_77495.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___735_77495.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___735_77495.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___735_77495.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___735_77495.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___735_77495.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___735_77495.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___735_77495.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___735_77495.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___735_77495.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___735_77495.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___735_77495.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___735_77495.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___735_77495.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___735_77495.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___735_77495.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___735_77495.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___735_77495.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___735_77495.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___735_77495.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___735_77495.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___735_77495.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___735_77495.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___735_77495.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___735_77495.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___735_77495.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___735_77495.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___735_77495.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___735_77495.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___735_77495.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___735_77495.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___735_77495.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___735_77495.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___735_77495.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___735_77495.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___735_77495.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___735_77495.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___735_77495.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___735_77495.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____77496;
        FStar_TypeChecker_Env.nbe =
          (uu___735_77495.FStar_TypeChecker_Env.nbe)
      }
  
let with_captured_errors' :
  'Auu____77506 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____77506 FStar_Pervasives_Native.option)
          -> 'Auu____77506 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        try
          (fun uu___741_77536  ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____77542  -> f env)) ()
        with
        | FStar_All.Failure msg ->
            let msg1 =
              Prims.op_Hat "ASSERTION FAILURE: "
                (Prims.op_Hat msg
                   (Prims.op_Hat "\n"
                      (Prims.op_Hat "F* may be in an inconsistent state.\n"
                         (Prims.op_Hat
                            "Please file a bug report, ideally with a "
                            "minimized version of the program that triggered the error."))))
               in
            ((let uu____77560 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.log_issue uu____77560
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt  ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e,msg,r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) ->
            ((let uu____77590 =
                let uu____77600 =
                  let uu____77608 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____77608)  in
                [uu____77600]  in
              FStar_TypeChecker_Err.add_errors env uu____77590);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____77633 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____77633 FStar_Pervasives_Native.option)
          -> 'Auu____77633 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        let uu____77660 = FStar_Options.trace_error ()  in
        if uu____77660
        then f env
        else with_captured_errors' env sigint_handler f
  
type timed_fname = {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee  ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
  
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Util.time) =
  fun projectee  ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
  
let (t0 : FStar_Util.time) = FStar_Util.now () 
let (tf_of_fname : Prims.string -> timed_fname) =
  fun fname  ->
    let uu____77707 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____77707 }
  
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____77722  ->
    match uu____77722 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____77732 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____77732)
  
type push_query =
  {
  push_kind: push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }
let (__proj__Mkpush_query__item__push_kind : push_query -> push_kind) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_kind
  
let (__proj__Mkpush_query__item__push_code : push_query -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_code
  
let (__proj__Mkpush_query__item__push_line : push_query -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_line
  
let (__proj__Mkpush_query__item__push_column : push_query -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_column
  
let (__proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { push_kind; push_code; push_line; push_column; push_peek_only;_} ->
        push_peek_only
  
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of FStar_Parser_ParseIt.input_frag 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | LDInterleaved _0 -> true | uu____77887 -> false
  
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____77919 -> false
  
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____77939 -> false
  
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____77959 -> false
  
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee  -> match projectee with | PushFragment _0 -> _0 
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noop  -> true | uu____77978 -> false
  
type env_t = FStar_TypeChecker_Env.env
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: env_t ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_line
  
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_column
  
let (__proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_fname
  
let (__proj__Mkrepl_state__item__repl_deps_stack :
  repl_state -> (repl_depth_t * (repl_task * repl_state)) Prims.list) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_deps_stack
  
let (__proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_curmod
  
let (__proj__Mkrepl_state__item__repl_env : repl_state -> env_t) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_env
  
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_stdin
  
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_names
  
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
let (repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStar_ST.ref) =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (repl_stack : repl_stack_t FStar_ST.ref) = FStar_Util.mk_ref [] 
let (pop_repl : Prims.string -> repl_state -> repl_state) =
  fun msg  ->
    fun st  ->
      let uu____78349 = FStar_ST.op_Bang repl_stack  in
      match uu____78349 with
      | [] -> failwith "Too many pops"
      | (depth,(uu____78379,st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth
             in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____78426 = FStar_Util.physical_equality env st'.repl_env
               in
            FStar_Common.runtime_assert uu____78426
              "Inconsistent stack state");
           st')
  
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg  ->
    fun push_kind  ->
      fun task  ->
        fun st  ->
          let uu____78452 = snapshot_env st.repl_env msg  in
          match uu____78452 with
          | (depth,env) ->
              ((let uu____78460 =
                  let uu____78461 = FStar_ST.op_Bang repl_stack  in
                  (depth, (task, st)) :: uu____78461  in
                FStar_ST.op_Colon_Equals repl_stack uu____78460);
               (let uu___844_78522 = st  in
                let uu____78523 = set_check_kind env push_kind  in
                {
                  repl_line = (uu___844_78522.repl_line);
                  repl_column = (uu___844_78522.repl_column);
                  repl_fname = (uu___844_78522.repl_fname);
                  repl_deps_stack = (uu___844_78522.repl_deps_stack);
                  repl_curmod = (uu___844_78522.repl_curmod);
                  repl_env = uu____78523;
                  repl_stdin = (uu___844_78522.repl_stdin);
                  repl_names = (uu___844_78522.repl_names)
                }))
  
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st  ->
    let uu____78531 =
      let uu____78532 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____78532  in
    uu____78531 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of
  (FStar_Syntax_Syntax.binding,FStar_TypeChecker_Env.sig_binding)
  FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____78636 -> false
  
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____78678 -> false
  
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____78714 -> false
  
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | NTInclude _0 -> _0 
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____78750 -> false
  
let (__proj__NTBinding__item___0 :
  name_tracking_event ->
    (FStar_Syntax_Syntax.binding,FStar_TypeChecker_Env.sig_binding)
      FStar_Util.either)
  = fun projectee  -> match projectee with | NTBinding _0 -> _0 
let (query_of_ids :
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query) =
  fun ids  -> FStar_List.map FStar_Ident.text_of_id ids 
let (query_of_lid :
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query) =
  fun lid  ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
  
let (update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod_str  ->
    fun table  ->
      fun evt  ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str  in
        match evt with
        | NTAlias (host,id1,included) ->
            if is_cur_mod host
            then
              let uu____78819 = FStar_Ident.text_of_id id1  in
              let uu____78821 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                uu____78819 [] uu____78821
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____78829 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____78829
            else table
        | NTInclude (host,included) ->
            let uu____78835 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____78840 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____78835 uu____78840
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid,uu____78852)) -> [lid]
              | FStar_Util.Inr (lids,uu____78870) -> lids
              | uu____78875 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   let uu____78892 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____78892 lid) table lids
  
let (commit_name_tracking' :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table)
  =
  fun cur_mod  ->
    fun names1  ->
      fun name_events  ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____78923 = FStar_Syntax_Syntax.mod_name md  in
              uu____78923.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___904_78949 = st  in
      {
        repl_line = (uu___904_78949.repl_line);
        repl_column = (uu___904_78949.repl_column);
        repl_fname = (uu___904_78949.repl_fname);
        repl_deps_stack = (uu___904_78949.repl_deps_stack);
        repl_curmod = (uu___904_78949.repl_curmod);
        repl_env = (uu___904_78949.repl_env);
        repl_stdin = (uu___904_78949.repl_stdin);
        repl_names = names1
      }
  
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____78965  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____78979 =
        let uu____78982 = FStar_ST.op_Bang events  in evt :: uu____78982  in
      FStar_ST.op_Colon_Equals events uu____78979  in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1  ->
             fun op  ->
               let uu____79109 =
                 let uu____79110 =
                   let uu____79115 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____79115, op)  in
                 NTOpen uu____79110  in
               push_event uu____79109);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1  ->
             fun ns  ->
               let uu____79121 =
                 let uu____79122 =
                   let uu____79127 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____79127, ns)  in
                 NTInclude uu____79122  in
               push_event uu____79121);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1  ->
             fun x  ->
               fun l  ->
                 let uu____79135 =
                   let uu____79136 =
                     let uu____79143 =
                       FStar_Syntax_DsEnv.current_module dsenv1  in
                     (uu____79143, x, l)  in
                   NTAlias uu____79136  in
                 push_event uu____79135)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____79148  -> fun s  -> push_event (NTBinding s))
      })
  
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____79202 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1  ->
             let uu____79210 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks
                in
             ((), uu____79210))
         in
      match uu____79202 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____79212 =
      let uu____79217 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____79218 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____79217, uu____79218)  in
    match uu____79212 with
    | (old_dshooks,old_tchooks) ->
        let uu____79234 = fresh_name_tracking_hooks ()  in
        (match uu____79234 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____79269 = set_hooks new_dshooks new_tchooks env  in
             (uu____79269,
               ((fun env1  ->
                   let uu____79283 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____79284 =
                     let uu____79287 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____79287  in
                   (uu____79283, uu____79284)))))
  
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___703_79343  ->
    match uu___703_79343 with
    | LDInterleaved (intf,impl) ->
        let uu____79347 = string_of_timed_fname intf  in
        let uu____79349 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____79347 uu____79349
    | LDSingle intf_or_impl ->
        let uu____79353 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____79353
    | LDInterfaceOfCurrentFile intf ->
        let uu____79357 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____79357
    | PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | Noop  -> "Noop {}"
  
let (tc_one :
  env_t ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env_t)
  =
  fun env  ->
    fun intf_opt  ->
      fun modf  ->
        let uu____79387 =
          let uu____79392 =
            let uu____79393 =
              let uu____79399 = FStar_TypeChecker_Env.dep_graph env  in
              FStar_Parser_Dep.parsing_data_of uu____79399  in
            FStar_All.pipe_right modf uu____79393  in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____79392
           in
        match uu____79387 with | (uu____79401,env1) -> env1
  
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____79429 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____79429)
        | LDSingle intf_or_impl ->
            let uu____79432 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____79432)
        | LDInterfaceOfCurrentFile intf ->
            let uu____79435 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____79435)
        | PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
        | Noop  -> (curmod, env)
  
let (repl_ld_tasks_of_deps :
  Prims.string Prims.list -> repl_task Prims.list -> repl_task Prims.list) =
  fun deps  ->
    fun final_tasks  ->
      let wrap = dummy_tf_of_fname  in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____79501 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____79501
        | intf_or_impl::deps' ->
            let uu____79511 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____79511
        | [] -> final_tasks1  in
      aux deps final_tasks
  
let (deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list * repl_task Prims.list * FStar_Parser_Dep.deps))
  =
  fun filename  ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname  in
    let our_mod_name = get_mod_name filename  in
    let has_our_mod_name f =
      let uu____79565 = get_mod_name f  in uu____79565 = our_mod_name  in
    let uu____79568 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_Universal.load_parsing_data_from_cache
       in
    match uu____79568 with
    | (deps,dep_graph1) ->
        let uu____79597 = FStar_List.partition has_our_mod_name deps  in
        (match uu____79597 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____79647 =
                       let uu____79649 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____79649  in
                     if uu____79647
                     then
                       let uu____79652 =
                         let uu____79658 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____79658)
                          in
                       FStar_Errors.raise_err uu____79652
                     else ());
                    (let uu____79665 =
                       let uu____79667 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____79667  in
                     if uu____79665
                     then
                       let uu____79670 =
                         let uu____79676 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____79676)
                          in
                       FStar_Errors.raise_err uu____79670
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____79686 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____79697 =
                       let uu____79703 =
                         FStar_Util.format message [our_mod_name; mods_str]
                          in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____79703)
                        in
                     FStar_Errors.raise_err uu____79697);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___704_79722  ->
    match uu___704_79722 with
    | LDInterleaved (intf,impl) ->
        let uu____79725 =
          let uu____79730 = tf_of_fname intf.tf_fname  in
          let uu____79731 = tf_of_fname impl.tf_fname  in
          (uu____79730, uu____79731)  in
        LDInterleaved uu____79725
    | LDSingle intf_or_impl ->
        let uu____79733 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____79733
    | LDInterfaceOfCurrentFile intf ->
        let uu____79735 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____79735
    | other -> other
  
let (run_repl_transaction :
  repl_state ->
    push_kind -> Prims.bool -> repl_task -> (Prims.bool * repl_state))
  =
  fun st  ->
    fun push_kind  ->
      fun must_rollback  ->
        fun task  ->
          let st1 = push_repl "run_repl_transaction" push_kind task st  in
          let uu____79767 = track_name_changes st1.repl_env  in
          match uu____79767 with
          | (env,finish_name_tracking) ->
              let check_success uu____79812 =
                (let uu____79815 = FStar_Errors.get_err_count ()  in
                 uu____79815 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____79819 =
                let uu____79827 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1  ->
                       let uu____79841 =
                         run_repl_task st1.repl_curmod env1 task  in
                       FStar_All.pipe_left
                         (fun _79860  -> FStar_Pervasives_Native.Some _79860)
                         uu____79841)
                   in
                match uu____79827 with
                | FStar_Pervasives_Native.Some (curmod,env1) when
                    check_success () -> (curmod, env1, true)
                | uu____79876 -> ((st1.repl_curmod), env, false)  in
              (match uu____79819 with
               | (curmod,env1,success) ->
                   let uu____79895 = finish_name_tracking env1  in
                   (match uu____79895 with
                    | (env2,name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___1044_79916 = st1  in
                              {
                                repl_line = (uu___1044_79916.repl_line);
                                repl_column = (uu___1044_79916.repl_column);
                                repl_fname = (uu___1044_79916.repl_fname);
                                repl_deps_stack =
                                  (uu___1044_79916.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___1044_79916.repl_stdin);
                                repl_names = (uu___1044_79916.repl_names)
                              }  in
                            commit_name_tracking st2 name_events
                          else pop_repl "run_repl_transaction" st1  in
                        (success, st2)))
  
let (run_repl_ld_transactions :
  repl_state ->
    repl_task Prims.list ->
      (repl_task -> unit) -> (repl_state,repl_state) FStar_Util.either)
  =
  fun st  ->
    fun tasks  ->
      fun progress_callback  ->
        let debug1 verb task =
          let uu____79963 = FStar_Options.debug_any ()  in
          if uu____79963
          then
            let uu____79966 = string_of_repl_task task  in
            FStar_Util.print2 "%s %s" verb uu____79966
          else ()  in
        let rec revert_many st1 uu___705_79991 =
          match uu___705_79991 with
          | [] -> st1
          | (_id,(task,_st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1  in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env
                   in
                let st'1 =
                  let uu___1070_80044 = st'  in
                  let uu____80045 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1
                     in
                  {
                    repl_line = (uu___1070_80044.repl_line);
                    repl_column = (uu___1070_80044.repl_column);
                    repl_fname = (uu___1070_80044.repl_fname);
                    repl_deps_stack = (uu___1070_80044.repl_deps_stack);
                    repl_curmod = (uu___1070_80044.repl_curmod);
                    repl_env = uu____80045;
                    repl_stdin = (uu___1070_80044.repl_stdin);
                    repl_names = (uu___1070_80044.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____80098 =
                  FStar_Options.restore_cmd_line_options false  in
                FStar_All.pipe_right uu____80098 (fun a1  -> ()));
               (let timestamped_task = update_task_timestamps task  in
                let push_kind =
                  let uu____80102 = FStar_Options.lax ()  in
                  if uu____80102 then LaxCheck else FullCheck  in
                let uu____80107 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____80107 with
                | (success,st2) ->
                    if success
                    then
                      let uu____80127 =
                        let uu___1095_80128 = st2  in
                        let uu____80129 = FStar_ST.op_Bang repl_stack  in
                        {
                          repl_line = (uu___1095_80128.repl_line);
                          repl_column = (uu___1095_80128.repl_column);
                          repl_fname = (uu___1095_80128.repl_fname);
                          repl_deps_stack = uu____80129;
                          repl_curmod = (uu___1095_80128.repl_curmod);
                          repl_env = (uu___1095_80128.repl_env);
                          repl_stdin = (uu___1095_80128.repl_stdin);
                          repl_names = (uu___1095_80128.repl_names)
                        }  in
                      aux uu____80127 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____80173 = update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____80173
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____80190 = revert_many st1 previous1  in
              aux uu____80190 tasks2 []
           in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___706_80205  ->
    match uu___706_80205 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____80219 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____80219
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____80225 -> "list (...)"
    | FStar_Util.JsonAssoc uu____80229 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____80255 -> true
    | uu____80262 -> false
  
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____80281 -> uu____80281
  
let js_fail :
  'Auu____80294 . Prims.string -> FStar_Util.json -> 'Auu____80294 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___707_80314  ->
    match uu___707_80314 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___708_80327  ->
    match uu___708_80327 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____80341 .
    (FStar_Util.json -> 'Auu____80341) ->
      FStar_Util.json -> 'Auu____80341 Prims.list
  =
  fun k  ->
    fun uu___709_80356  ->
      match uu___709_80356 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___710_80378  ->
    match uu___710_80378 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s  ->
    let uu____80409 = js_str s  in
    match uu____80409 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____80414 -> js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____80423 = js_str s  in
    match uu____80423 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____80431 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____80460 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____80473 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____80502 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____80541 = js_str k1  in
        (match uu____80541 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____80569 ->
             js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
  
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode 
let (uu___is_LKSymbolOnly : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKSymbolOnly  -> true | uu____80581 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____80592 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____80603 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____80614 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____80627 = js_str k1  in
        (match uu____80627 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____80637 ->
             js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
  
type position = (Prims.string * Prims.int * Prims.int)
type query' =
  | Exit 
  | DescribeProtocol 
  | DescribeRepl 
  | Segment of Prims.string 
  | Pop 
  | Push of push_query 
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option * Prims.string) 
  | AutoComplete of (Prims.string * completion_context) 
  | Lookup of (Prims.string * lookup_context * position
  FStar_Pervasives_Native.option * Prims.string Prims.list) 
  | Compute of (Prims.string * FStar_TypeChecker_Env.step Prims.list
  FStar_Pervasives_Native.option) 
  | Search of Prims.string 
  | GenericError of Prims.string 
  | ProtocolViolation of Prims.string 
and query = {
  qq: query' ;
  qid: Prims.string }
let (uu___is_Exit : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____80754 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____80765 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____80776 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____80789 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____80811 -> false
  
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____80823 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____80851 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____80900 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____80949 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____81020 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____81068 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____81092 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ProtocolViolation _0 -> true
    | uu____81116 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___711_81155  ->
    match uu___711_81155 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____81160 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____81164; push_code = uu____81165;
          push_line = uu____81166; push_column = uu____81167;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____81173 -> false
    | GenericError uu____81183 -> false
    | ProtocolViolation uu____81186 -> false
    | Push uu____81189 -> true
    | AutoComplete uu____81191 -> true
    | Lookup uu____81198 -> true
    | Compute uu____81214 -> true
    | Search uu____81225 -> true
  
let (interactive_protocol_vernum : Prims.int) = (Prims.parse_int "2") 
let (interactive_protocol_features : Prims.string Prims.list) =
  ["autocomplete";
  "autocomplete/context";
  "compute";
  "compute/reify";
  "compute/pure-subterms";
  "describe-protocol";
  "describe-repl";
  "exit";
  "lookup";
  "lookup/context";
  "lookup/documentation";
  "lookup/definition";
  "peek";
  "pop";
  "push";
  "search";
  "segment";
  "vfs-add";
  "tactic-ranges";
  "interrupt";
  "progress"] 
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____81291 -> true
    | uu____81294 -> false
  
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidQuery uu____81305 -> uu____81305
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____81316 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____81327 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____81338 -> false
  
let try_assoc :
  'Auu____81349 'Auu____81350 .
    'Auu____81349 ->
      ('Auu____81349 * 'Auu____81350) Prims.list ->
        'Auu____81350 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____81375 =
        FStar_Util.try_find
          (fun uu____81389  ->
             match uu____81389 with | (k,uu____81396) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____81375
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____81421 =
          let uu____81422 =
            let uu____81424 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____81424
             in
          ProtocolViolation uu____81422  in
        { qq = uu____81421; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc1 errloc key a =
      let uu____81467 = try_assoc key a  in
      match uu____81467 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____81472 =
            let uu____81473 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____81473  in
          FStar_Exn.raise uu____81472
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____81493 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____81493 js_str  in
    try
      (fun uu___1247_81503  ->
         match () with
         | () ->
             let query =
               let uu____81506 = assoc1 "query" "query" request  in
               FStar_All.pipe_right uu____81506 js_str  in
             let args =
               let uu____81518 = assoc1 "query" "args" request  in
               FStar_All.pipe_right uu____81518 js_assoc  in
             let arg k = assoc1 "[args]" k args  in
             let try_arg k =
               let uu____81547 = try_assoc k args  in
               match uu____81547 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____81556 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____81562 =
                     let uu____81564 = arg "code"  in
                     FStar_All.pipe_right uu____81564 js_str  in
                   Segment uu____81562
               | "peek" ->
                   let uu____81568 =
                     let uu____81569 =
                       let uu____81570 = arg "kind"  in
                       FStar_All.pipe_right uu____81570 js_pushkind  in
                     let uu____81572 =
                       let uu____81574 = arg "code"  in
                       FStar_All.pipe_right uu____81574 js_str  in
                     let uu____81577 =
                       let uu____81579 = arg "line"  in
                       FStar_All.pipe_right uu____81579 js_int  in
                     let uu____81582 =
                       let uu____81584 = arg "column"  in
                       FStar_All.pipe_right uu____81584 js_int  in
                     {
                       push_kind = uu____81569;
                       push_code = uu____81572;
                       push_line = uu____81577;
                       push_column = uu____81582;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____81568
               | "push" ->
                   let uu____81590 =
                     let uu____81591 =
                       let uu____81592 = arg "kind"  in
                       FStar_All.pipe_right uu____81592 js_pushkind  in
                     let uu____81594 =
                       let uu____81596 = arg "code"  in
                       FStar_All.pipe_right uu____81596 js_str  in
                     let uu____81599 =
                       let uu____81601 = arg "line"  in
                       FStar_All.pipe_right uu____81601 js_int  in
                     let uu____81604 =
                       let uu____81606 = arg "column"  in
                       FStar_All.pipe_right uu____81606 js_int  in
                     {
                       push_kind = uu____81591;
                       push_code = uu____81594;
                       push_line = uu____81599;
                       push_column = uu____81604;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____81590
               | "autocomplete" ->
                   let uu____81612 =
                     let uu____81618 =
                       let uu____81620 = arg "partial-symbol"  in
                       FStar_All.pipe_right uu____81620 js_str  in
                     let uu____81623 =
                       let uu____81624 = try_arg "context"  in
                       FStar_All.pipe_right uu____81624
                         js_optional_completion_context
                        in
                     (uu____81618, uu____81623)  in
                   AutoComplete uu____81612
               | "lookup" ->
                   let uu____81632 =
                     let uu____81647 =
                       let uu____81649 = arg "symbol"  in
                       FStar_All.pipe_right uu____81649 js_str  in
                     let uu____81652 =
                       let uu____81653 = try_arg "context"  in
                       FStar_All.pipe_right uu____81653
                         js_optional_lookup_context
                        in
                     let uu____81659 =
                       let uu____81662 =
                         let uu____81672 = try_arg "location"  in
                         FStar_All.pipe_right uu____81672
                           (FStar_Util.map_option js_assoc)
                          in
                       FStar_All.pipe_right uu____81662
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____81733 =
                                 let uu____81735 =
                                   assoc1 "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____81735 js_str  in
                               let uu____81739 =
                                 let uu____81741 =
                                   assoc1 "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____81741 js_int  in
                               let uu____81745 =
                                 let uu____81747 =
                                   assoc1 "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____81747 js_int  in
                               (uu____81733, uu____81739, uu____81745)))
                        in
                     let uu____81754 =
                       let uu____81758 = arg "requested-info"  in
                       FStar_All.pipe_right uu____81758 (js_list js_str)  in
                     (uu____81647, uu____81652, uu____81659, uu____81754)  in
                   Lookup uu____81632
               | "compute" ->
                   let uu____81771 =
                     let uu____81781 =
                       let uu____81783 = arg "term"  in
                       FStar_All.pipe_right uu____81783 js_str  in
                     let uu____81786 =
                       let uu____81791 = try_arg "rules"  in
                       FStar_All.pipe_right uu____81791
                         (FStar_Util.map_option (js_list js_reductionrule))
                        in
                     (uu____81781, uu____81786)  in
                   Compute uu____81771
               | "search" ->
                   let uu____81809 =
                     let uu____81811 = arg "terms"  in
                     FStar_All.pipe_right uu____81811 js_str  in
                   Search uu____81809
               | "vfs-add" ->
                   let uu____81815 =
                     let uu____81824 =
                       let uu____81828 = try_arg "filename"  in
                       FStar_All.pipe_right uu____81828
                         (FStar_Util.map_option js_str)
                        in
                     let uu____81838 =
                       let uu____81840 = arg "contents"  in
                       FStar_All.pipe_right uu____81840 js_str  in
                     (uu____81824, uu____81838)  in
                   VfsAdd uu____81815
               | uu____81847 ->
                   let uu____81849 =
                     FStar_Util.format1 "Unknown query '%s'" query  in
                   ProtocolViolation uu____81849
                in
             { qq = uu____81556; qid }) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___1282_81868  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____81888 = FStar_Util.json_of_string query_str  in
    match uu____81888 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____81900 = FStar_Util.read_line stream  in
    match uu____81900 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____81916 .
    ('Auu____81916 -> FStar_Util.json) ->
      'Auu____81916 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____81936 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____81936
  
let (json_of_issue_level : FStar_Errors.issue_level -> FStar_Util.json) =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
  
let (json_of_issue : FStar_Errors.issue -> FStar_Util.json) =
  fun issue  ->
    let uu____81956 =
      let uu____81964 =
        let uu____81972 =
          let uu____81980 =
            let uu____81986 =
              let uu____81987 =
                let uu____81990 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____81996 = FStar_Range.json_of_use_range r  in
                      [uu____81996]
                   in
                let uu____81997 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____82003 = FStar_Range.def_range r  in
                      let uu____82004 = FStar_Range.use_range r  in
                      uu____82003 <> uu____82004 ->
                      let uu____82005 = FStar_Range.json_of_def_range r  in
                      [uu____82005]
                  | uu____82006 -> []  in
                FStar_List.append uu____81990 uu____81997  in
              FStar_Util.JsonList uu____81987  in
            ("ranges", uu____81986)  in
          [uu____81980]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____81972
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____81964
       in
    FStar_Util.JsonAssoc uu____81956
  
type symbol_lookup_result =
  {
  slr_name: Prims.string ;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mksymbol_lookup_result__item__slr_name :
  symbol_lookup_result -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_name
  
let (__proj__Mksymbol_lookup_result__item__slr_def_range :
  symbol_lookup_result -> FStar_Range.range FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} ->
        slr_def_range
  
let (__proj__Mksymbol_lookup_result__item__slr_typ :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_typ
  
let (__proj__Mksymbol_lookup_result__item__slr_doc :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_doc
  
let (__proj__Mksymbol_lookup_result__item__slr_def :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_def
  
let (alist_of_symbol_lookup_result :
  symbol_lookup_result -> (Prims.string * FStar_Util.json) Prims.list) =
  fun lr  ->
    let uu____82224 =
      let uu____82232 =
        let uu____82238 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____82238)  in
      let uu____82241 =
        let uu____82249 =
          let uu____82255 =
            json_of_opt (fun _82257  -> FStar_Util.JsonStr _82257) lr.slr_typ
             in
          ("type", uu____82255)  in
        let uu____82260 =
          let uu____82268 =
            let uu____82274 =
              json_of_opt (fun _82276  -> FStar_Util.JsonStr _82276)
                lr.slr_doc
               in
            ("documentation", uu____82274)  in
          let uu____82279 =
            let uu____82287 =
              let uu____82293 =
                json_of_opt (fun _82295  -> FStar_Util.JsonStr _82295)
                  lr.slr_def
                 in
              ("definition", uu____82293)  in
            [uu____82287]  in
          uu____82268 :: uu____82279  in
        uu____82249 :: uu____82260  in
      uu____82232 :: uu____82241  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____82224
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____82340 =
      FStar_List.map (fun _82344  -> FStar_Util.JsonStr _82344)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _82347  -> FStar_Util.JsonList _82347)
      uu____82340
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____82376 -> false
  
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____82387 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____82398 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___712_82406  ->
    match uu___712_82406 with
    | OptSet  -> ""
    | OptReset  -> "requires #reset-options"
    | OptReadOnly  -> "read-only"
  
type fstar_option =
  {
  opt_name: Prims.string ;
  opt_sig: Prims.string ;
  opt_value: FStar_Options.option_val ;
  opt_default: FStar_Options.option_val ;
  opt_type: FStar_Options.opt_type ;
  opt_snippets: Prims.string Prims.list ;
  opt_documentation: Prims.string FStar_Pervasives_Native.option ;
  opt_permission_level: fstar_option_permission_level }
let (__proj__Mkfstar_option__item__opt_name : fstar_option -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_name
  
let (__proj__Mkfstar_option__item__opt_sig : fstar_option -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_sig
  
let (__proj__Mkfstar_option__item__opt_value :
  fstar_option -> FStar_Options.option_val) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_value
  
let (__proj__Mkfstar_option__item__opt_default :
  fstar_option -> FStar_Options.option_val) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_default
  
let (__proj__Mkfstar_option__item__opt_type :
  fstar_option -> FStar_Options.opt_type) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_type
  
let (__proj__Mkfstar_option__item__opt_snippets :
  fstar_option -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_snippets
  
let (__proj__Mkfstar_option__item__opt_documentation :
  fstar_option -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_documentation
  
let (__proj__Mkfstar_option__item__opt_permission_level :
  fstar_option -> fstar_option_permission_level) =
  fun projectee  ->
    match projectee with
    | { opt_name; opt_sig; opt_value; opt_default; opt_type; opt_snippets;
        opt_documentation; opt_permission_level;_} -> opt_permission_level
  
let rec (kind_of_fstar_option_type : FStar_Options.opt_type -> Prims.string)
  =
  fun uu___713_82657  ->
    match uu___713_82657 with
    | FStar_Options.Const uu____82659 -> "flag"
    | FStar_Options.IntStr uu____82661 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____82665 -> "path"
    | FStar_Options.SimpleStr uu____82668 -> "string"
    | FStar_Options.EnumStr uu____82671 -> "enum"
    | FStar_Options.OpenEnumStr uu____82676 -> "open enum"
    | FStar_Options.PostProcessed (uu____82686,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____82696,typ) ->
        kind_of_fstar_option_type typ
  
let rec (snippets_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list) =
  fun name  ->
    fun typ  ->
      let mk_field field_name =
        Prims.op_Hat "${" (Prims.op_Hat field_name "}")  in
      let mk_snippet name1 argstring =
        Prims.op_Hat "--"
          (Prims.op_Hat name1
             (if argstring <> "" then Prims.op_Hat " " argstring else ""))
         in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____82768 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____82806,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____82816,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____82824 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____82824
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___714_82835  ->
    match uu___714_82835 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____82847 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____82847
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____82863 =
      let uu____82871 =
        let uu____82879 =
          let uu____82885 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____82885)  in
        let uu____82888 =
          let uu____82896 =
            let uu____82902 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____82902)  in
          let uu____82905 =
            let uu____82913 =
              let uu____82919 =
                json_of_opt (fun _82921  -> FStar_Util.JsonStr _82921)
                  opt.opt_documentation
                 in
              ("documentation", uu____82919)  in
            let uu____82924 =
              let uu____82932 =
                let uu____82938 =
                  let uu____82939 = kind_of_fstar_option_type opt.opt_type
                     in
                  FStar_Util.JsonStr uu____82939  in
                ("type", uu____82938)  in
              [uu____82932;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____82913 :: uu____82924  in
          uu____82896 :: uu____82905  in
        uu____82879 :: uu____82888  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____82871  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____82863
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____82995 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____82995
  
let (write_json : FStar_Util.json -> unit) =
  fun json  ->
    (let uu____83010 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____83010);
    FStar_Util.print_raw "\n"
  
let (json_of_response :
  Prims.string -> query_status -> FStar_Util.json -> FStar_Util.json) =
  fun qid  ->
    fun status  ->
      fun response  ->
        let qid1 = FStar_Util.JsonStr qid  in
        let status1 =
          match status with
          | QueryOK  -> FStar_Util.JsonStr "success"
          | QueryNOK  -> FStar_Util.JsonStr "failure"
          | QueryViolatesProtocol  -> FStar_Util.JsonStr "protocol-violation"
           in
        FStar_Util.JsonAssoc
          [("kind", (FStar_Util.JsonStr "response"));
          ("query-id", qid1);
          ("status", status1);
          ("response", response)]
  
let (write_response :
  Prims.string -> query_status -> FStar_Util.json -> unit) =
  fun qid  ->
    fun status  ->
      fun response  -> write_json (json_of_response qid status response)
  
let (json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json) =
  fun level  ->
    fun js_contents  ->
      let uu____83101 =
        let uu____83109 =
          let uu____83117 =
            let uu____83123 =
              let uu____83124 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _83154  -> FStar_Util.JsonStr _83154)
                uu____83124
               in
            ("query-id", uu____83123)  in
          [uu____83117;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____83109  in
      FStar_Util.JsonAssoc uu____83101
  
let forward_message :
  'Auu____83198 .
    (FStar_Util.json -> 'Auu____83198) ->
      Prims.string -> FStar_Util.json -> 'Auu____83198
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____83221 = json_of_message level contents  in
        callback uu____83221
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____83225 =
      FStar_List.map (fun _83229  -> FStar_Util.JsonStr _83229)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____83225  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____83243  -> write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____83261 = FStar_Options.desc_of_opt_type typ  in
      match uu____83261 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____83277 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____83312  ->
            match uu____83312 with
            | (_shortname,name,typ,doc1) ->
                let uu____83336 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____83336
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____83348 = sig_of_fstar_option name typ  in
                        let uu____83350 = snippets_of_fstar_option name typ
                           in
                        let uu____83354 =
                          let uu____83355 = FStar_Options.settable name  in
                          if uu____83355
                          then OptSet
                          else
                            (let uu____83360 = FStar_Options.resettable name
                                in
                             if uu____83360 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____83348;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____83350;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____83354
                        }))))
     in
  FStar_All.pipe_right uu____83277
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
  
let (fstar_options_map_cache : fstar_option FStar_Util.smap) =
  let cache = FStar_Util.smap_create (Prims.parse_int "50")  in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache 
let (update_option : fstar_option -> fstar_option) =
  fun opt  ->
    let uu___1471_83399 = opt  in
    let uu____83400 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___1471_83399.opt_name);
      opt_sig = (uu___1471_83399.opt_sig);
      opt_value = uu____83400;
      opt_default = (uu___1471_83399.opt_default);
      opt_type = (uu___1471_83399.opt_type);
      opt_snippets = (uu___1471_83399.opt_snippets);
      opt_documentation = (uu___1471_83399.opt_documentation);
      opt_permission_level = (uu___1471_83399.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1  ->
    let uu____83416 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____83416
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____83443 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____83443)
    else ("", opt_name)
  
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____83474 =
      match uu____83474 with
      | (uu____83486,(task,uu____83488)) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____83507 -> [])
       in
    let uu____83509 =
      let uu____83517 =
        let uu____83523 =
          let uu____83524 =
            let uu____83527 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _83541  -> FStar_Util.JsonStr _83541)
              uu____83527
             in
          FStar_Util.JsonList uu____83524  in
        ("loaded-dependencies", uu____83523)  in
      let uu____83544 =
        let uu____83552 =
          let uu____83558 =
            let uu____83559 =
              let uu____83562 =
                current_fstar_options (fun uu____83567  -> true)  in
              FStar_List.map json_of_fstar_option uu____83562  in
            FStar_Util.JsonList uu____83559  in
          ("options", uu____83558)  in
        [uu____83552]  in
      uu____83517 :: uu____83544  in
    FStar_Util.JsonAssoc uu____83509
  
let with_printed_effect_args :
  'Auu____83591 . (unit -> 'Auu____83591) -> 'Auu____83591 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____83604  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____83622  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    with_printed_effect_args
      (fun uu____83632  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____83640 'Auu____83641 .
    'Auu____83640 ->
      ((query_status * FStar_Util.json) * ('Auu____83641,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
  
let run_describe_protocol :
  'Auu____83678 'Auu____83679 .
    'Auu____83678 ->
      ((query_status * FStar_Util.json) * ('Auu____83678,'Auu____83679)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____83710 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____83710)
        FStar_Util.either)
  =
  fun st  ->
    let uu____83728 =
      let uu____83733 = json_of_repl_state st  in (QueryOK, uu____83733)  in
    (uu____83728, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____83751 'Auu____83752 .
    'Auu____83751 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____83751,'Auu____83752)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____83794 'Auu____83795 .
    'Auu____83794 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____83794,'Auu____83795)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____83835  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____83847 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____83847)
          FStar_Util.either)
  =
  fun st  ->
    fun code  ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        }  in
      let collect_decls uu____83882 =
        let uu____83883 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____83883 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____83889,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____83895,decls,uu____83897)) -> decls
         in
      let uu____83904 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____83913  ->
             let uu____83914 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _83925  -> FStar_Pervasives_Native.Some _83925)
               uu____83914)
         in
      match uu____83904 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____83943 = collect_errors ()  in
            FStar_All.pipe_right uu____83943 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____83969 =
              let uu____83977 =
                let uu____83983 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____83983)  in
              [uu____83977]  in
            FStar_Util.JsonAssoc uu____83969  in
          let js_decls =
            let uu____83997 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _84002  -> FStar_Util.JsonList _84002)
              uu____83997
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____84032 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____84032)
            FStar_Util.either)
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____84085 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____84085)
        FStar_Util.either)
  =
  fun st  ->
    let uu____84103 = nothing_left_to_pop st  in
    if uu____84103
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = pop_repl "pop_query" st  in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
  
let (write_progress :
  Prims.string FStar_Pervasives_Native.option ->
    (Prims.string * FStar_Util.json) Prims.list -> unit)
  =
  fun stage  ->
    fun contents_alist  ->
      let stage1 =
        match stage with
        | FStar_Pervasives_Native.Some s -> FStar_Util.JsonStr s
        | FStar_Pervasives_Native.None  -> FStar_Util.JsonNull  in
      let js_contents = ("stage", stage1) :: contents_alist  in
      let uu____84190 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      write_json uu____84190
  
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task  ->
    match task with
    | LDInterleaved (uu____84198,tf) ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname  in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | LDSingle tf ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname  in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | LDInterfaceOfCurrentFile tf ->
        let modname = FStar_Parser_Dep.module_name_of_file tf.tf_fname  in
        write_progress (FStar_Pervasives_Native.Some "loading-dependency")
          [("modname", (FStar_Util.JsonStr modname))]
    | uu____84250 -> ()
  
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list),repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____84268 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____84296 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _84343  -> FStar_Pervasives_Native.Some _84343) uu____84296)
       in
    match uu____84268 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___1569_84398 = st  in
          let uu____84399 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___1569_84398.repl_line);
            repl_column = (uu___1569_84398.repl_column);
            repl_fname = (uu___1569_84398.repl_fname);
            repl_deps_stack = (uu___1569_84398.repl_deps_stack);
            repl_curmod = (uu___1569_84398.repl_curmod);
            repl_env = uu____84399;
            repl_stdin = (uu___1569_84398.repl_stdin);
            repl_names = (uu___1569_84398.repl_names)
          }  in
        let uu____84400 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____84400 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___1579_84455 = issue  in
    let uu____84456 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____84456;
      FStar_Errors.issue_level = (uu___1579_84455.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___1579_84455.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___1579_84455.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____84466 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____84466)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___1586_84502 = st1  in
        {
          repl_line = (uu___1586_84502.repl_line);
          repl_column = (uu___1586_84502.repl_column);
          repl_fname = (uu___1586_84502.repl_fname);
          repl_deps_stack = (uu___1586_84502.repl_deps_stack);
          repl_curmod = (uu___1586_84502.repl_curmod);
          repl_env =
            (let uu___1588_84504 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1588_84504.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1588_84504.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1588_84504.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1588_84504.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1588_84504.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1588_84504.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1588_84504.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1588_84504.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1588_84504.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1588_84504.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1588_84504.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1588_84504.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1588_84504.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1588_84504.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1588_84504.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1588_84504.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1588_84504.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1588_84504.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1588_84504.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1588_84504.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1588_84504.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1588_84504.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1588_84504.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1588_84504.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1588_84504.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1588_84504.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1588_84504.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1588_84504.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1588_84504.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1588_84504.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1588_84504.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1588_84504.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1588_84504.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___1588_84504.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1588_84504.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1588_84504.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1588_84504.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1588_84504.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1588_84504.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1588_84504.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1588_84504.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1588_84504.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___1586_84502.repl_stdin);
          repl_names = (uu___1586_84502.repl_names)
        }  in
      let uu____84505 = query  in
      match uu____84505 with
      | { push_kind; push_code = text; push_line = line;
          push_column = column; push_peek_only = peek_only;_} ->
          let frag =
            {
              FStar_Parser_ParseIt.frag_text = text;
              FStar_Parser_ParseIt.frag_line = line;
              FStar_Parser_ParseIt.frag_col = column
            }  in
          (FStar_TypeChecker_Env.toggle_id_info st.repl_env true;
           (let st1 = set_nosynth_flag st peek_only  in
            let uu____84531 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____84531 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____84560 =
                    let uu____84563 = collect_errors ()  in
                    FStar_All.pipe_right uu____84563
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____84560  in
                let st4 =
                  if success
                  then
                    let uu___1607_84572 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___1607_84572.repl_fname);
                      repl_deps_stack = (uu___1607_84572.repl_deps_stack);
                      repl_curmod = (uu___1607_84572.repl_curmod);
                      repl_env = (uu___1607_84572.repl_env);
                      repl_stdin = (uu___1607_84572.repl_stdin);
                      repl_names = (uu___1607_84572.repl_names)
                    }
                  else st3  in
                ((status, json_errors), (FStar_Util.Inl st4))))
  
let (capitalize : Prims.string -> Prims.string) =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1")
          in
       let uu____84602 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1"))
          in
       Prims.op_Hat (FStar_String.uppercase first) uu____84602)
  
let (add_module_completions :
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table)
  =
  fun this_fname  ->
    fun deps  ->
      fun table  ->
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list ()  in
        let loaded_mods_set =
          let uu____84643 = FStar_Util.psmap_empty ()  in
          let uu____84648 =
            let uu____84652 = FStar_Options.prims ()  in uu____84652 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____84668 =
                   FStar_Parser_Dep.lowercase_module_name dep1  in
                 FStar_Util.psmap_add acc uu____84668 true) uu____84643
            uu____84648
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____84697  ->
               match uu____84697 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____84720 = capitalize modname  in
                        FStar_Util.split uu____84720 "."  in
                      let uu____84723 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____84723 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____84738 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____84738)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      (let uu____84762 = FStar_Options.debug_any ()  in
       if uu____84762
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____84770 = load_deps st  in
       match uu____84770 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____84805 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____84805  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____84839 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____84839 (fun a2  -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___1645_84843 = st1  in
                {
                  repl_line = (uu___1645_84843.repl_line);
                  repl_column = (uu___1645_84843.repl_column);
                  repl_fname = (uu___1645_84843.repl_fname);
                  repl_deps_stack = (uu___1645_84843.repl_deps_stack);
                  repl_curmod = (uu___1645_84843.repl_curmod);
                  repl_env = (uu___1645_84843.repl_env);
                  repl_stdin = (uu___1645_84843.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____84851 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____84851)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let uu____84874 = nothing_left_to_pop st  in
      if uu____84874
      then run_push_with_deps st query
      else run_push_without_deps st query
  
let (run_symbol_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                          Prims.list))
            FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let tcenv = st.repl_env  in
          let info_of_lid_str lid_str =
            let lid =
              let uu____84982 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____84982  in
            let lid1 =
              let uu____84988 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____84988  in
            let uu____84993 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____84993
              (FStar_Util.map_option
                 (fun uu____85050  ->
                    match uu____85050 with
                    | ((uu____85070,typ),r) ->
                        ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____85092 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____85092
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____85158 = FStar_TypeChecker_Env.lookup_qname tcenv lid
               in
            FStar_Util.bind_opt uu____85158
              (fun uu___715_85203  ->
                 match uu___715_85203 with
                 | (FStar_Util.Inr (se,uu____85226),uu____85227) ->
                     let uu____85256 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____85256
                 | uu____85259 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____85317  ->
                 match uu____85317 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____85376 -> info_at_pos_opt
            | FStar_Pervasives_Native.None  ->
                if symbol = ""
                then FStar_Pervasives_Native.None
                else info_of_lid_str symbol
             in
          let response =
            match info_opt with
            | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some (name_or_lid,typ,rng) ->
                let name =
                  match name_or_lid with
                  | FStar_Util.Inl name -> name
                  | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid  in
                let typ_str =
                  if FStar_List.mem "type" requested_info
                  then
                    let uu____85533 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____85533
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____85550 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____85568 -> FStar_Pervasives_Native.None  in
                let def_range1 =
                  if FStar_List.mem "defined-at" requested_info
                  then FStar_Pervasives_Native.Some rng
                  else FStar_Pervasives_Native.None  in
                let result =
                  {
                    slr_name = name;
                    slr_def_range = def_range1;
                    slr_typ = typ_str;
                    slr_doc = doc_str;
                    slr_def = def_str
                  }  in
                let uu____85586 =
                  let uu____85599 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____85599)  in
                FStar_Pervasives_Native.Some uu____85586
             in
          match response with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some info -> FStar_Util.Inr info
  
let (run_option_lookup :
  Prims.string ->
    (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                    Prims.list))
      FStar_Util.either)
  =
  fun opt_name  ->
    let uu____85734 = trim_option_name opt_name  in
    match uu____85734 with
    | (uu____85758,trimmed_name) ->
        let uu____85764 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____85764 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____85799 =
               let uu____85812 =
                 let uu____85820 = update_option opt  in
                 alist_of_fstar_option uu____85820  in
               ("option", uu____85812)  in
             FStar_Util.Inr uu____85799)
  
let (run_module_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                      Prims.list))
        FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "."  in
      let uu____85878 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____85878 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____85913 =
            let uu____85926 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____85926)  in
          FStar_Util.Inr uu____85913
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____85957 =
            let uu____85970 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____85970)  in
          FStar_Util.Inr uu____85957
  
let (run_code_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
        ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                          Prims.list))
            FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____86068 =
            run_symbol_lookup st symbol pos_opt requested_info  in
          match uu____86068 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____86142 ->
              let uu____86157 = run_module_lookup st symbol  in
              (match uu____86157 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
  
let (run_lookup' :
  repl_state ->
    Prims.string ->
      lookup_context ->
        (Prims.string * Prims.int * Prims.int) FStar_Pervasives_Native.option
          ->
          Prims.string Prims.list ->
            (Prims.string,(Prims.string * (Prims.string * FStar_Util.json)
                            Prims.list))
              FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            match context with
            | LKSymbolOnly  ->
                run_symbol_lookup st symbol pos_opt requested_info
            | LKModule  -> run_module_lookup st symbol
            | LKOption  -> run_option_lookup symbol
            | LKCode  -> run_code_lookup st symbol pos_opt requested_info
  
let run_lookup :
  'Auu____86363 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string * Prims.int * Prims.int)
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____86363)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____86431 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____86431 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____86535 .
    ('Auu____86535 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____86535 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___716_86550  ->
    match uu___716_86550 with
    | (uu____86555,FStar_Interactive_CompletionTable.Namespace uu____86556)
        -> FStar_Pervasives_Native.None
    | (uu____86561,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____86562;
         FStar_Interactive_CompletionTable.mod_path = uu____86563;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____86573 =
          let uu____86578 =
            let uu____86579 =
              let uu___1779_86580 = md  in
              let uu____86581 =
                let uu____86583 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.op_Hat uu____86583 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____86581;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___1779_86580.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___1779_86580.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____86579  in
          (pth, uu____86578)  in
        FStar_Pervasives_Native.Some uu____86573
  
let run_code_autocomplete :
  'Auu____86597 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____86597)
          FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      let needle = FStar_Util.split search_term "."  in
      let mods_and_nss =
        FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.repl_names needle code_autocomplete_mod_filter
         in
      let lids =
        FStar_Interactive_CompletionTable.autocomplete_lid st.repl_names
          needle
         in
      let json =
        FStar_List.map
          FStar_Interactive_CompletionTable.json_of_completion_result
          (FStar_List.append lids mods_and_nss)
         in
      ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
  
let run_module_autocomplete :
  'Auu____86659 'Auu____86660 'Auu____86661 .
    repl_state ->
      Prims.string ->
        'Auu____86659 ->
          'Auu____86660 ->
            ((query_status * FStar_Util.json) * (repl_state,'Auu____86661)
              FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun modules1  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "."  in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.repl_names needle
              (fun _86708  -> FStar_Pervasives_Native.Some _86708)
             in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss
             in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
  
let (candidates_of_fstar_option :
  Prims.int ->
    Prims.bool ->
      fstar_option ->
        FStar_Interactive_CompletionTable.completion_result Prims.list)
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____86742 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____86742 with
        | (may_set,explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type  in
            let annot =
              if may_set
              then opt_type
              else
                Prims.op_Hat "("
                  (Prims.op_Hat explanation
                     (Prims.op_Hat " " (Prims.op_Hat opt_type ")")))
               in
            FStar_All.pipe_right opt.opt_snippets
              (FStar_List.map
                 (fun snippet  ->
                    {
                      FStar_Interactive_CompletionTable.completion_match_length
                        = match_len;
                      FStar_Interactive_CompletionTable.completion_candidate
                        = snippet;
                      FStar_Interactive_CompletionTable.completion_annotation
                        = annot
                    }))
  
let run_option_autocomplete :
  'Auu____86805 'Auu____86806 .
    'Auu____86805 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____86805,'Auu____86806)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____86838 = trim_option_name search_term  in
        match uu____86838 with
        | ("--",trimmed_name) ->
            let matcher opt =
              FStar_Util.starts_with opt.opt_name trimmed_name  in
            let options = current_fstar_options matcher  in
            let match_len = FStar_String.length search_term  in
            let collect_candidates =
              candidates_of_fstar_option match_len is_reset  in
            let results = FStar_List.concatMap collect_candidates options  in
            let json =
              FStar_List.map
                FStar_Interactive_CompletionTable.json_of_completion_result
                results
               in
            ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
        | (uu____86900,uu____86901) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____86924 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____86924)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun context  ->
        match context with
        | CKCode  -> run_code_autocomplete st search_term
        | CKOption is_reset ->
            run_option_autocomplete st search_term is_reset
        | CKModuleOrNamespace (modules1,namespaces) ->
            run_module_autocomplete st search_term modules1 namespaces
  
let run_and_rewind :
  'Auu____86975 'Auu____86976 .
    repl_state ->
      'Auu____86975 ->
        (repl_state -> 'Auu____86975) ->
          ('Auu____86975 * (repl_state,'Auu____86976) FStar_Util.either)
  =
  fun st  ->
    fun sigint_default  ->
      fun task  ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st  in
        let results =
          try
            (fun uu___1838_87017  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____87028  ->
                        let uu____87029 = task st1  in
                        FStar_All.pipe_left
                          (fun _87034  -> FStar_Util.Inl _87034) uu____87029))
              ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = pop_repl "run_and_rewind" st1  in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'Auu____87083 'Auu____87084 'Auu____87085 .
    repl_state ->
      Prims.string ->
        'Auu____87083 ->
          'Auu____87084 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____87085)
                FStar_Util.either)
  =
  fun st  ->
    fun term  ->
      fun line  ->
        fun column  ->
          fun continuation  ->
            let dummy_let_fragment term1 =
              let dummy_decl =
                FStar_Util.format1 "let __compute_dummy__ = (%s)" term1  in
              {
                FStar_Parser_ParseIt.frag_text = dummy_decl;
                FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0");
                FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
              }  in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____87186,{ FStar_Syntax_Syntax.lbname = uu____87187;
                                    FStar_Syntax_Syntax.lbunivs = univs1;
                                    FStar_Syntax_Syntax.lbtyp = uu____87189;
                                    FStar_Syntax_Syntax.lbeff = uu____87190;
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs = uu____87192;
                                    FStar_Syntax_Syntax.lbpos = uu____87193;_}::[]),uu____87194);
                  FStar_Syntax_Syntax.sigrng = uu____87195;
                  FStar_Syntax_Syntax.sigquals = uu____87196;
                  FStar_Syntax_Syntax.sigmeta = uu____87197;
                  FStar_Syntax_Syntax.sigattrs = uu____87198;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____87237 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____87258 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____87258 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____87264) ->
                  FStar_Pervasives_Native.Some decls
              | uu____87285 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____87303 =
                let uu____87308 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____87308 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____87303  in
            let typecheck tcenv decls =
              let uu____87332 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____87332 with | (ses,uu____87346,uu____87347) -> ses
               in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____87368 = parse1 frag  in
                 match uu____87368 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____87394 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1,def) ->
                           let uu____87430 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def  in
                           (match uu____87430 with
                            | (univs2,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____87442 = FStar_Options.trace_error ()  in
                     if uu____87442
                     then aux ()
                     else
                       (try
                          (fun uu___1921_87456  ->
                             match () with | () -> aux ()) ()
                        with
                        | uu___1920_87465 ->
                            let uu____87470 =
                              FStar_Errors.issue_of_exn uu___1920_87465  in
                            (match uu____87470 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____87478 =
                                   let uu____87479 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____87479  in
                                 (QueryNOK, uu____87478)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___1920_87465)))
  
let run_compute :
  'Auu____87494 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____87494)
            FStar_Util.either)
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Env.Beta;
                 FStar_TypeChecker_Env.Iota;
                 FStar_TypeChecker_Env.Zeta;
                 FStar_TypeChecker_Env.UnfoldUntil
                   FStar_Syntax_Syntax.delta_constant])
            [FStar_TypeChecker_Env.Inlining;
            FStar_TypeChecker_Env.Eager_unfolding;
            FStar_TypeChecker_Env.UnfoldTac;
            FStar_TypeChecker_Env.Primops]
           in
        let normalize_term1 tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t  in
        run_with_parsed_and_tc_term st term (Prims.parse_int "0")
          (Prims.parse_int "0")
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term1 tcenv rules1 def  in
               let uu____87572 =
                 let uu____87573 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____87573  in
               (QueryOK, uu____87572))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____87608 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____87631 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___717_87667  ->
    match uu___717_87667 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> (Prims.parse_int "1")
  
type search_candidate =
  {
  sc_lid: FStar_Ident.lid ;
  sc_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref ;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
    }
let (__proj__Mksearch_candidate__item__sc_lid :
  search_candidate -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_lid
  
let (__proj__Mksearch_candidate__item__sc_typ :
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_typ
  
let (__proj__Mksearch_candidate__item__sc_fvars :
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with | { sc_lid; sc_typ; sc_fvars;_} -> sc_fvars
  
let (sc_of_lid : FStar_Ident.lid -> search_candidate) =
  fun lid  ->
    let uu____87889 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____87896 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____87889; sc_fvars = uu____87896 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____87964 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____87964 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____87992 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____87992 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____88011,typ),uu____88013) ->
                typ
             in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
  
let (sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lident FStar_Util.set)
  =
  fun tcenv  ->
    fun sc  ->
      let uu____88063 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____88063 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____88107 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____88107  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____88151 = sc_typ tcenv sc  in
        term_to_string tcenv uu____88151  in
      let uu____88152 =
        let uu____88160 =
          let uu____88166 =
            let uu____88167 =
              let uu____88169 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____88169.FStar_Ident.str  in
            FStar_Util.JsonStr uu____88167  in
          ("lid", uu____88166)  in
        [uu____88160; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____88152
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____88202 -> true
    | uu____88205 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____88216 -> uu____88216
  
let run_search :
  'Auu____88225 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____88225)
          FStar_Util.either)
  =
  fun st  ->
    fun search_str  ->
      let tcenv = st.repl_env  in
      let empty_fv_set = FStar_Syntax_Syntax.new_fv_set ()  in
      let st_matches candidate term =
        let found =
          match term.st_term with
          | NameContainsStr str ->
              FStar_Util.contains (candidate.sc_lid).FStar_Ident.str str
          | TypeContainsLid lid ->
              let uu____88272 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____88272
           in
        found <> term.st_negate  in
      let parse1 search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-"  in
          let term1 =
            if negate
            then FStar_Util.substring_from term (Prims.parse_int "1")
            else term  in
          let beg_quote = FStar_Util.starts_with term1 "\""  in
          let end_quote = FStar_Util.ends_with term1 "\""  in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.parse_int "2")
            then FStar_Exn.raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.parse_int "1")
                ((FStar_String.length term1) - (Prims.parse_int "2"))
             in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____88331 =
                let uu____88332 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____88332  in
              FStar_Exn.raise uu____88331
            else
              if beg_quote
              then
                (let uu____88338 = strip_quotes term1  in
                 NameContainsStr uu____88338)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____88343 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____88343 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____88346 =
                       let uu____88347 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____88347  in
                     FStar_Exn.raise uu____88346
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____88375 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____88375  in
      let results =
        try
          (fun uu___2034_88409  ->
             match () with
             | () ->
                 let terms = parse1 search_str  in
                 let all_lidents = FStar_TypeChecker_Env.lidents tcenv  in
                 let all_candidates = FStar_List.map sc_of_lid all_lidents
                    in
                 let matches_all candidate =
                   FStar_List.for_all (st_matches candidate) terms  in
                 let cmp r1 r2 =
                   FStar_Util.compare (r1.sc_lid).FStar_Ident.str
                     (r2.sc_lid).FStar_Ident.str
                    in
                 let results = FStar_List.filter matches_all all_candidates
                    in
                 let sorted1 = FStar_Util.sort_with cmp results  in
                 let js =
                   FStar_List.map (json_of_search_result tcenv) sorted1  in
                 (match results with
                  | [] ->
                      let kwds =
                        let uu____88457 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____88457  in
                      let uu____88463 =
                        let uu____88464 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____88464  in
                      FStar_Exn.raise uu____88463
                  | uu____88471 -> (QueryOK, (FStar_Util.JsonList js)))) ()
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s))  in
      (results, (FStar_Util.Inl st))
  
let (run_query :
  repl_state ->
    query' ->
      ((query_status * FStar_Util.json) * (repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun q  ->
      match q with
      | Exit  -> run_exit st
      | DescribeProtocol  -> run_describe_protocol st
      | DescribeRepl  -> run_describe_repl st
      | GenericError message -> run_generic_error st message
      | ProtocolViolation query -> run_protocol_violation st query
      | Segment c -> run_segment st c
      | VfsAdd (fname,contents) -> run_vfs_add st fname contents
      | Push pquery -> run_push st pquery
      | Pop  -> run_pop st
      | AutoComplete (search_term,context) ->
          run_autocomplete st search_term context
      | Lookup (symbol,context,pos_opt,rq_info) ->
          run_lookup st symbol context pos_opt rq_info
      | Compute (term,rules) -> run_compute st term rules
      | Search term -> run_search st term
  
let (validate_query : repl_state -> query -> query) =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck ; push_code = uu____88602;
            push_line = uu____88603; push_column = uu____88604;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____88610 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____88612 -> q)
  
let (validate_and_run_query :
  repl_state ->
    query ->
      ((query_status * FStar_Util.json) * (repl_state,Prims.int)
        FStar_Util.either))
  =
  fun st  ->
    fun query  ->
      let query1 = validate_query st query  in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query1.qid));
      run_query st query1.qq
  
let (js_repl_eval :
  repl_state ->
    query -> (FStar_Util.json * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query  ->
      let uu____88685 = validate_and_run_query st query  in
      match uu____88685 with
      | ((status,response),st_opt) ->
          let js_response = json_of_response query.qid status response  in
          (js_response, st_opt)
  
let (js_repl_eval_js :
  repl_state ->
    FStar_Util.json ->
      (FStar_Util.json * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query_js  ->
      let uu____88751 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____88751
  
let (js_repl_eval_str :
  repl_state ->
    Prims.string -> (Prims.string * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____88775 =
        let uu____88785 = parse_interactive_query query_str  in
        js_repl_eval st uu____88785  in
      match uu____88775 with
      | (js_response,st_opt) ->
          let uu____88808 = FStar_Util.string_of_json js_response  in
          (uu____88808, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____88821  ->
    let uu____88822 = FStar_Options.parse_cmd_line ()  in
    match uu____88822 with
    | (res,fnames) ->
        (match res with
         | FStar_Getopt.Error msg ->
             failwith (Prims.op_Hat "repl_init: " msg)
         | FStar_Getopt.Help  -> failwith "repl_init: --help unexpected"
         | FStar_Getopt.Success  ->
             (match fnames with
              | [] ->
                  failwith
                    "repl_init: No file name given in --ide invocation"
              | h::uu____88845::uu____88846 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____88855 -> ()))
  
let rec (go : repl_state -> Prims.int) =
  fun st  ->
    let query = read_interactive_query st.repl_stdin  in
    let uu____88868 = validate_and_run_query st query  in
    match uu____88868 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____88921 =
      let uu____88924 = FStar_ST.op_Bang issues  in e :: uu____88924  in
    FStar_ST.op_Colon_Equals issues uu____88921  in
  let count_errors uu____89022 =
    let uu____89023 =
      let uu____89026 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____89026
       in
    FStar_List.length uu____89023  in
  let report uu____89083 =
    let uu____89084 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____89084  in
  let clear1 uu____89137 = FStar_ST.op_Colon_Equals issues []  in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear1
  } 
let (interactive_printer : (FStar_Util.json -> unit) -> FStar_Util.printer) =
  fun printer  ->
    {
      FStar_Util.printer_prinfo =
        (fun s  -> forward_message printer "info" (FStar_Util.JsonStr s));
      FStar_Util.printer_prwarning =
        (fun s  -> forward_message printer "warning" (FStar_Util.JsonStr s));
      FStar_Util.printer_prerror =
        (fun s  -> forward_message printer "error" (FStar_Util.JsonStr s));
      FStar_Util.printer_prgeneric =
        (fun label  ->
           fun get_string  ->
             fun get_json  ->
               let uu____89224 = get_json ()  in
               forward_message printer label uu____89224)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____89238 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  let uu____89241 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  FStar_Range.mk_range "<input>" uu____89238 uu____89241 
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____89255 = FStar_Util.open_stdin ()  in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____89255;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' : 'Auu____89271 . repl_state -> 'Auu____89271 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____89280 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____89280
       then
         let uu____89284 =
           let uu____89286 = FStar_Options.file_list ()  in
           FStar_List.hd uu____89286  in
         FStar_SMTEncoding_Solver.with_hints_db uu____89284
           (fun uu____89293  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____89307 =
       let uu____89309 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____89309  in
     if uu____89307
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____89318 = FStar_Options.trace_error ()  in
     if uu____89318
     then interactive_mode' init1
     else
       (try
          (fun uu___2182_89324  ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___2181_89327 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___2181_89327)))
  
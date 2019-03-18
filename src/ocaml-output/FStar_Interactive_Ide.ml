open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun msg  ->
      let uu____72461 = FStar_TypeChecker_Tc.snapshot_context env msg  in
      match uu____72461 with
      | (ctx_depth,env1) ->
          let uu____72505 = FStar_Options.snapshot ()  in
          (match uu____72505 with
           | (opt_depth,()) -> ((ctx_depth, opt_depth), env1))
  
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1  ->
    fun msg  ->
      fun uu____72551  ->
        match uu____72551 with
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
    match projectee with | SyntaxCheck  -> true | uu____72618 -> false
  
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____72629 -> false
  
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____72640 -> false
  
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun check_kind  ->
      let uu___735_72653 = env  in
      let uu____72654 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___735_72653.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___735_72653.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___735_72653.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___735_72653.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___735_72653.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___735_72653.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___735_72653.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___735_72653.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___735_72653.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___735_72653.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___735_72653.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___735_72653.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___735_72653.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___735_72653.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___735_72653.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___735_72653.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___735_72653.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___735_72653.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___735_72653.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___735_72653.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___735_72653.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___735_72653.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___735_72653.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___735_72653.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___735_72653.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___735_72653.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___735_72653.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___735_72653.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___735_72653.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___735_72653.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___735_72653.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___735_72653.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___735_72653.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___735_72653.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___735_72653.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___735_72653.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___735_72653.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___735_72653.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___735_72653.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___735_72653.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____72654;
        FStar_TypeChecker_Env.nbe =
          (uu___735_72653.FStar_TypeChecker_Env.nbe)
      }
  
let with_captured_errors' :
  'Auu____72664 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____72664 FStar_Pervasives_Native.option)
          -> 'Auu____72664 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        try
          (fun uu___741_72694  ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____72700  -> f env)) ()
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
            ((let uu____72718 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.log_issue uu____72718
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt  ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e,msg,r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) ->
            ((let uu____72748 =
                let uu____72758 =
                  let uu____72766 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____72766)  in
                [uu____72758]  in
              FStar_TypeChecker_Err.add_errors env uu____72748);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____72791 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____72791 FStar_Pervasives_Native.option)
          -> 'Auu____72791 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        let uu____72818 = FStar_Options.trace_error ()  in
        if uu____72818
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
    let uu____72865 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____72865 }
  
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____72880  ->
    match uu____72880 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____72890 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____72890)
  
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
    match projectee with | LDInterleaved _0 -> true | uu____73045 -> false
  
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____73076 -> false
  
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____73095 -> false
  
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____73114 -> false
  
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee  -> match projectee with | PushFragment _0 -> _0 
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noop  -> true | uu____73132 -> false
  
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
      let uu____73481 = FStar_ST.op_Bang repl_stack  in
      match uu____73481 with
      | [] -> failwith "Too many pops"
      | (depth,(uu____73511,st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth
             in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____73558 = FStar_Util.physical_equality env st'.repl_env
               in
            FStar_Common.runtime_assert uu____73558
              "Inconsistent stack state");
           st')
  
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg  ->
    fun push_kind  ->
      fun task  ->
        fun st  ->
          let uu____73584 = snapshot_env st.repl_env msg  in
          match uu____73584 with
          | (depth,env) ->
              ((let uu____73592 =
                  let uu____73593 = FStar_ST.op_Bang repl_stack  in
                  (depth, (task, st)) :: uu____73593  in
                FStar_ST.op_Colon_Equals repl_stack uu____73592);
               (let uu___844_73654 = st  in
                let uu____73655 = set_check_kind env push_kind  in
                {
                  repl_line = (uu___844_73654.repl_line);
                  repl_column = (uu___844_73654.repl_column);
                  repl_fname = (uu___844_73654.repl_fname);
                  repl_deps_stack = (uu___844_73654.repl_deps_stack);
                  repl_curmod = (uu___844_73654.repl_curmod);
                  repl_env = uu____73655;
                  repl_stdin = (uu___844_73654.repl_stdin);
                  repl_names = (uu___844_73654.repl_names)
                }))
  
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st  ->
    let uu____73663 =
      let uu____73664 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____73664  in
    uu____73663 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of
  (FStar_Syntax_Syntax.binding,FStar_TypeChecker_Env.sig_binding)
  FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____73764 -> false
  
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____73805 -> false
  
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____73840 -> false
  
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | NTInclude _0 -> _0 
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____73875 -> false
  
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
              let uu____73943 = FStar_Ident.text_of_id id1  in
              let uu____73945 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                uu____73943 [] uu____73945
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____73953 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____73953
            else table
        | NTInclude (host,included) ->
            let uu____73959 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____73964 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____73959 uu____73964
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid,uu____73976)) -> [lid]
              | FStar_Util.Inr (lids,uu____73994) -> lids
              | uu____73999 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   let uu____74016 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____74016 lid) table lids
  
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
              let uu____74047 = FStar_Syntax_Syntax.mod_name md  in
              uu____74047.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___904_74073 = st  in
      {
        repl_line = (uu___904_74073.repl_line);
        repl_column = (uu___904_74073.repl_column);
        repl_fname = (uu___904_74073.repl_fname);
        repl_deps_stack = (uu___904_74073.repl_deps_stack);
        repl_curmod = (uu___904_74073.repl_curmod);
        repl_env = (uu___904_74073.repl_env);
        repl_stdin = (uu___904_74073.repl_stdin);
        repl_names = names1
      }
  
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____74089  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____74103 =
        let uu____74106 = FStar_ST.op_Bang events  in evt :: uu____74106  in
      FStar_ST.op_Colon_Equals events uu____74103  in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1  ->
             fun op  ->
               let uu____74167 =
                 let uu____74168 =
                   let uu____74173 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____74173, op)  in
                 NTOpen uu____74168  in
               push_event uu____74167);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1  ->
             fun ns  ->
               let uu____74179 =
                 let uu____74180 =
                   let uu____74185 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____74185, ns)  in
                 NTInclude uu____74180  in
               push_event uu____74179);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1  ->
             fun x  ->
               fun l  ->
                 let uu____74193 =
                   let uu____74194 =
                     let uu____74201 =
                       FStar_Syntax_DsEnv.current_module dsenv1  in
                     (uu____74201, x, l)  in
                   NTAlias uu____74194  in
                 push_event uu____74193)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____74206  -> fun s  -> push_event (NTBinding s))
      })
  
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____74260 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1  ->
             let uu____74268 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks
                in
             ((), uu____74268))
         in
      match uu____74260 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____74270 =
      let uu____74275 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____74276 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____74275, uu____74276)  in
    match uu____74270 with
    | (old_dshooks,old_tchooks) ->
        let uu____74292 = fresh_name_tracking_hooks ()  in
        (match uu____74292 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____74327 = set_hooks new_dshooks new_tchooks env  in
             (uu____74327,
               ((fun env1  ->
                   let uu____74341 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____74342 =
                     let uu____74345 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____74345  in
                   (uu____74341, uu____74342)))))
  
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___703_74379  ->
    match uu___703_74379 with
    | LDInterleaved (intf,impl) ->
        let uu____74383 = string_of_timed_fname intf  in
        let uu____74385 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____74383 uu____74385
    | LDSingle intf_or_impl ->
        let uu____74389 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____74389
    | LDInterfaceOfCurrentFile intf ->
        let uu____74393 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____74393
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
        let uu____74423 =
          let uu____74428 =
            let uu____74429 =
              let uu____74435 = FStar_TypeChecker_Env.dep_graph env  in
              FStar_Parser_Dep.parsing_data_of uu____74435  in
            FStar_All.pipe_right modf uu____74429  in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____74428
           in
        match uu____74423 with | (uu____74437,env1) -> env1
  
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____74465 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____74465)
        | LDSingle intf_or_impl ->
            let uu____74468 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____74468)
        | LDInterfaceOfCurrentFile intf ->
            let uu____74471 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____74471)
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
            let uu____74537 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____74537
        | intf_or_impl::deps' ->
            let uu____74547 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____74547
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
      let uu____74601 = get_mod_name f  in uu____74601 = our_mod_name  in
    let uu____74604 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache
       in
    match uu____74604 with
    | (deps,dep_graph1) ->
        let uu____74633 = FStar_List.partition has_our_mod_name deps  in
        (match uu____74633 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____74683 =
                       let uu____74685 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____74685  in
                     if uu____74683
                     then
                       let uu____74688 =
                         let uu____74694 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____74694)
                          in
                       FStar_Errors.raise_err uu____74688
                     else ());
                    (let uu____74701 =
                       let uu____74703 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____74703  in
                     if uu____74701
                     then
                       let uu____74706 =
                         let uu____74712 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____74712)
                          in
                       FStar_Errors.raise_err uu____74706
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____74722 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____74733 =
                       let uu____74739 =
                         FStar_Util.format message [our_mod_name; mods_str]
                          in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____74739)
                        in
                     FStar_Errors.raise_err uu____74733);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___704_74758  ->
    match uu___704_74758 with
    | LDInterleaved (intf,impl) ->
        let uu____74761 =
          let uu____74766 = tf_of_fname intf.tf_fname  in
          let uu____74767 = tf_of_fname impl.tf_fname  in
          (uu____74766, uu____74767)  in
        LDInterleaved uu____74761
    | LDSingle intf_or_impl ->
        let uu____74769 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____74769
    | LDInterfaceOfCurrentFile intf ->
        let uu____74771 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____74771
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
          let uu____74803 = track_name_changes st1.repl_env  in
          match uu____74803 with
          | (env,finish_name_tracking) ->
              let check_success uu____74848 =
                (let uu____74851 = FStar_Errors.get_err_count ()  in
                 uu____74851 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____74855 =
                let uu____74863 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1  ->
                       let uu____74877 =
                         run_repl_task st1.repl_curmod env1 task  in
                       FStar_All.pipe_left
                         (fun _74896  -> FStar_Pervasives_Native.Some _74896)
                         uu____74877)
                   in
                match uu____74863 with
                | FStar_Pervasives_Native.Some (curmod,env1) when
                    check_success () -> (curmod, env1, true)
                | uu____74912 -> ((st1.repl_curmod), env, false)  in
              (match uu____74855 with
               | (curmod,env1,success) ->
                   let uu____74931 = finish_name_tracking env1  in
                   (match uu____74931 with
                    | (env2,name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___1044_74952 = st1  in
                              {
                                repl_line = (uu___1044_74952.repl_line);
                                repl_column = (uu___1044_74952.repl_column);
                                repl_fname = (uu___1044_74952.repl_fname);
                                repl_deps_stack =
                                  (uu___1044_74952.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___1044_74952.repl_stdin);
                                repl_names = (uu___1044_74952.repl_names)
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
          let uu____74999 = FStar_Options.debug_any ()  in
          if uu____74999
          then
            let uu____75002 = string_of_repl_task task  in
            FStar_Util.print2 "%s %s" verb uu____75002
          else ()  in
        let rec revert_many st1 uu___705_75027 =
          match uu___705_75027 with
          | [] -> st1
          | (_id,(task,_st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1  in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env
                   in
                let st'1 =
                  let uu___1070_75080 = st'  in
                  let uu____75081 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1
                     in
                  {
                    repl_line = (uu___1070_75080.repl_line);
                    repl_column = (uu___1070_75080.repl_column);
                    repl_fname = (uu___1070_75080.repl_fname);
                    repl_deps_stack = (uu___1070_75080.repl_deps_stack);
                    repl_curmod = (uu___1070_75080.repl_curmod);
                    repl_env = uu____75081;
                    repl_stdin = (uu___1070_75080.repl_stdin);
                    repl_names = (uu___1070_75080.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____75134 =
                  FStar_Options.restore_cmd_line_options false  in
                FStar_All.pipe_right uu____75134 (fun a1  -> ()));
               (let timestamped_task = update_task_timestamps task  in
                let push_kind =
                  let uu____75138 = FStar_Options.lax ()  in
                  if uu____75138 then LaxCheck else FullCheck  in
                let uu____75143 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____75143 with
                | (success,st2) ->
                    if success
                    then
                      let uu____75163 =
                        let uu___1095_75164 = st2  in
                        let uu____75165 = FStar_ST.op_Bang repl_stack  in
                        {
                          repl_line = (uu___1095_75164.repl_line);
                          repl_column = (uu___1095_75164.repl_column);
                          repl_fname = (uu___1095_75164.repl_fname);
                          repl_deps_stack = uu____75165;
                          repl_curmod = (uu___1095_75164.repl_curmod);
                          repl_env = (uu___1095_75164.repl_env);
                          repl_stdin = (uu___1095_75164.repl_stdin);
                          repl_names = (uu___1095_75164.repl_names)
                        }  in
                      aux uu____75163 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____75209 = update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____75209
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____75226 = revert_many st1 previous1  in
              aux uu____75226 tasks2 []
           in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___706_75241  ->
    match uu___706_75241 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____75255 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____75255
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____75261 -> "list (...)"
    | FStar_Util.JsonAssoc uu____75265 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____75291 -> true
    | uu____75298 -> false
  
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____75316 -> uu____75316
  
let js_fail :
  'Auu____75329 . Prims.string -> FStar_Util.json -> 'Auu____75329 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___707_75349  ->
    match uu___707_75349 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___708_75362  ->
    match uu___708_75362 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____75376 .
    (FStar_Util.json -> 'Auu____75376) ->
      FStar_Util.json -> 'Auu____75376 Prims.list
  =
  fun k  ->
    fun uu___709_75391  ->
      match uu___709_75391 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___710_75413  ->
    match uu___710_75413 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s  ->
    let uu____75444 = js_str s  in
    match uu____75444 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____75449 -> js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____75458 = js_str s  in
    match uu____75458 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____75466 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____75495 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____75508 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____75536 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____75574 = js_str k1  in
        (match uu____75574 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____75602 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____75614 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____75625 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____75636 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____75647 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____75660 = js_str k1  in
        (match uu____75660 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____75670 ->
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
    match projectee with | Exit  -> true | uu____75787 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____75798 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____75809 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____75822 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____75843 -> false
  
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____75855 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____75882 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____75930 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____75978 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____76048 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____76095 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____76118 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ProtocolViolation _0 -> true
    | uu____76141 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___711_76179  ->
    match uu___711_76179 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____76184 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____76188; push_code = uu____76189;
          push_line = uu____76190; push_column = uu____76191;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____76197 -> false
    | GenericError uu____76207 -> false
    | ProtocolViolation uu____76210 -> false
    | Push uu____76213 -> true
    | AutoComplete uu____76215 -> true
    | Lookup uu____76222 -> true
    | Compute uu____76238 -> true
    | Search uu____76249 -> true
  
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
    | InvalidQuery uu____76315 -> true
    | uu____76318 -> false
  
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidQuery uu____76328 -> uu____76328
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____76339 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____76350 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____76361 -> false
  
let try_assoc :
  'Auu____76372 'Auu____76373 .
    'Auu____76372 ->
      ('Auu____76372 * 'Auu____76373) Prims.list ->
        'Auu____76373 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____76398 =
        FStar_Util.try_find
          (fun uu____76412  ->
             match uu____76412 with | (k,uu____76419) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____76398
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____76444 =
          let uu____76445 =
            let uu____76447 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____76447
             in
          ProtocolViolation uu____76445  in
        { qq = uu____76444; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc1 errloc key a =
      let uu____76490 = try_assoc key a  in
      match uu____76490 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____76495 =
            let uu____76496 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____76496  in
          FStar_Exn.raise uu____76495
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____76516 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____76516 js_str  in
    try
      (fun uu___1247_76526  ->
         match () with
         | () ->
             let query =
               let uu____76529 = assoc1 "query" "query" request  in
               FStar_All.pipe_right uu____76529 js_str  in
             let args =
               let uu____76541 = assoc1 "query" "args" request  in
               FStar_All.pipe_right uu____76541 js_assoc  in
             let arg k = assoc1 "[args]" k args  in
             let try_arg k =
               let uu____76570 = try_assoc k args  in
               match uu____76570 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____76579 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____76585 =
                     let uu____76587 = arg "code"  in
                     FStar_All.pipe_right uu____76587 js_str  in
                   Segment uu____76585
               | "peek" ->
                   let uu____76591 =
                     let uu____76592 =
                       let uu____76593 = arg "kind"  in
                       FStar_All.pipe_right uu____76593 js_pushkind  in
                     let uu____76595 =
                       let uu____76597 = arg "code"  in
                       FStar_All.pipe_right uu____76597 js_str  in
                     let uu____76600 =
                       let uu____76602 = arg "line"  in
                       FStar_All.pipe_right uu____76602 js_int  in
                     let uu____76605 =
                       let uu____76607 = arg "column"  in
                       FStar_All.pipe_right uu____76607 js_int  in
                     {
                       push_kind = uu____76592;
                       push_code = uu____76595;
                       push_line = uu____76600;
                       push_column = uu____76605;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____76591
               | "push" ->
                   let uu____76613 =
                     let uu____76614 =
                       let uu____76615 = arg "kind"  in
                       FStar_All.pipe_right uu____76615 js_pushkind  in
                     let uu____76617 =
                       let uu____76619 = arg "code"  in
                       FStar_All.pipe_right uu____76619 js_str  in
                     let uu____76622 =
                       let uu____76624 = arg "line"  in
                       FStar_All.pipe_right uu____76624 js_int  in
                     let uu____76627 =
                       let uu____76629 = arg "column"  in
                       FStar_All.pipe_right uu____76629 js_int  in
                     {
                       push_kind = uu____76614;
                       push_code = uu____76617;
                       push_line = uu____76622;
                       push_column = uu____76627;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____76613
               | "autocomplete" ->
                   let uu____76635 =
                     let uu____76641 =
                       let uu____76643 = arg "partial-symbol"  in
                       FStar_All.pipe_right uu____76643 js_str  in
                     let uu____76646 =
                       let uu____76647 = try_arg "context"  in
                       FStar_All.pipe_right uu____76647
                         js_optional_completion_context
                        in
                     (uu____76641, uu____76646)  in
                   AutoComplete uu____76635
               | "lookup" ->
                   let uu____76655 =
                     let uu____76670 =
                       let uu____76672 = arg "symbol"  in
                       FStar_All.pipe_right uu____76672 js_str  in
                     let uu____76675 =
                       let uu____76676 = try_arg "context"  in
                       FStar_All.pipe_right uu____76676
                         js_optional_lookup_context
                        in
                     let uu____76682 =
                       let uu____76685 =
                         let uu____76695 = try_arg "location"  in
                         FStar_All.pipe_right uu____76695
                           (FStar_Util.map_option js_assoc)
                          in
                       FStar_All.pipe_right uu____76685
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____76756 =
                                 let uu____76758 =
                                   assoc1 "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____76758 js_str  in
                               let uu____76762 =
                                 let uu____76764 =
                                   assoc1 "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____76764 js_int  in
                               let uu____76768 =
                                 let uu____76770 =
                                   assoc1 "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____76770 js_int  in
                               (uu____76756, uu____76762, uu____76768)))
                        in
                     let uu____76777 =
                       let uu____76781 = arg "requested-info"  in
                       FStar_All.pipe_right uu____76781 (js_list js_str)  in
                     (uu____76670, uu____76675, uu____76682, uu____76777)  in
                   Lookup uu____76655
               | "compute" ->
                   let uu____76794 =
                     let uu____76804 =
                       let uu____76806 = arg "term"  in
                       FStar_All.pipe_right uu____76806 js_str  in
                     let uu____76809 =
                       let uu____76814 = try_arg "rules"  in
                       FStar_All.pipe_right uu____76814
                         (FStar_Util.map_option (js_list js_reductionrule))
                        in
                     (uu____76804, uu____76809)  in
                   Compute uu____76794
               | "search" ->
                   let uu____76832 =
                     let uu____76834 = arg "terms"  in
                     FStar_All.pipe_right uu____76834 js_str  in
                   Search uu____76832
               | "vfs-add" ->
                   let uu____76838 =
                     let uu____76847 =
                       let uu____76851 = try_arg "filename"  in
                       FStar_All.pipe_right uu____76851
                         (FStar_Util.map_option js_str)
                        in
                     let uu____76861 =
                       let uu____76863 = arg "contents"  in
                       FStar_All.pipe_right uu____76863 js_str  in
                     (uu____76847, uu____76861)  in
                   VfsAdd uu____76838
               | uu____76870 ->
                   let uu____76872 =
                     FStar_Util.format1 "Unknown query '%s'" query  in
                   ProtocolViolation uu____76872
                in
             { qq = uu____76579; qid }) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___1282_76891  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____76911 = FStar_Util.json_of_string query_str  in
    match uu____76911 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____76923 = FStar_Util.read_line stream  in
    match uu____76923 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____76939 .
    ('Auu____76939 -> FStar_Util.json) ->
      'Auu____76939 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____76959 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____76959
  
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
    let uu____76979 =
      let uu____76987 =
        let uu____76995 =
          let uu____77003 =
            let uu____77009 =
              let uu____77010 =
                let uu____77013 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____77019 = FStar_Range.json_of_use_range r  in
                      [uu____77019]
                   in
                let uu____77020 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____77026 = FStar_Range.def_range r  in
                      let uu____77027 = FStar_Range.use_range r  in
                      uu____77026 <> uu____77027 ->
                      let uu____77028 = FStar_Range.json_of_def_range r  in
                      [uu____77028]
                  | uu____77029 -> []  in
                FStar_List.append uu____77013 uu____77020  in
              FStar_Util.JsonList uu____77010  in
            ("ranges", uu____77009)  in
          [uu____77003]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____76995
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____76987
       in
    FStar_Util.JsonAssoc uu____76979
  
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
    let uu____77247 =
      let uu____77255 =
        let uu____77261 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____77261)  in
      let uu____77264 =
        let uu____77272 =
          let uu____77278 =
            json_of_opt (fun _77280  -> FStar_Util.JsonStr _77280) lr.slr_typ
             in
          ("type", uu____77278)  in
        let uu____77283 =
          let uu____77291 =
            let uu____77297 =
              json_of_opt (fun _77299  -> FStar_Util.JsonStr _77299)
                lr.slr_doc
               in
            ("documentation", uu____77297)  in
          let uu____77302 =
            let uu____77310 =
              let uu____77316 =
                json_of_opt (fun _77318  -> FStar_Util.JsonStr _77318)
                  lr.slr_def
                 in
              ("definition", uu____77316)  in
            [uu____77310]  in
          uu____77291 :: uu____77302  in
        uu____77272 :: uu____77283  in
      uu____77255 :: uu____77264  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____77247
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____77363 =
      FStar_List.map (fun _77367  -> FStar_Util.JsonStr _77367)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _77370  -> FStar_Util.JsonList _77370)
      uu____77363
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____77399 -> false
  
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____77410 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____77421 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___712_77429  ->
    match uu___712_77429 with
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
  fun uu___713_77680  ->
    match uu___713_77680 with
    | FStar_Options.Const uu____77682 -> "flag"
    | FStar_Options.IntStr uu____77684 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____77688 -> "path"
    | FStar_Options.SimpleStr uu____77691 -> "string"
    | FStar_Options.EnumStr uu____77694 -> "enum"
    | FStar_Options.OpenEnumStr uu____77699 -> "open enum"
    | FStar_Options.PostProcessed (uu____77709,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____77719,typ) ->
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
        | FStar_Options.Const uu____77791 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____77829,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____77839,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____77847 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____77847
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___714_77858  ->
    match uu___714_77858 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____77870 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____77870
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____77886 =
      let uu____77894 =
        let uu____77902 =
          let uu____77908 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____77908)  in
        let uu____77911 =
          let uu____77919 =
            let uu____77925 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____77925)  in
          let uu____77928 =
            let uu____77936 =
              let uu____77942 =
                json_of_opt (fun _77944  -> FStar_Util.JsonStr _77944)
                  opt.opt_documentation
                 in
              ("documentation", uu____77942)  in
            let uu____77947 =
              let uu____77955 =
                let uu____77961 =
                  let uu____77962 = kind_of_fstar_option_type opt.opt_type
                     in
                  FStar_Util.JsonStr uu____77962  in
                ("type", uu____77961)  in
              [uu____77955;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____77936 :: uu____77947  in
          uu____77919 :: uu____77928  in
        uu____77902 :: uu____77911  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____77894  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____77886
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____78018 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____78018
  
let (write_json : FStar_Util.json -> unit) =
  fun json  ->
    (let uu____78033 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____78033);
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
      let uu____78124 =
        let uu____78132 =
          let uu____78140 =
            let uu____78146 =
              let uu____78147 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _78177  -> FStar_Util.JsonStr _78177)
                uu____78147
               in
            ("query-id", uu____78146)  in
          [uu____78140;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____78132  in
      FStar_Util.JsonAssoc uu____78124
  
let forward_message :
  'Auu____78221 .
    (FStar_Util.json -> 'Auu____78221) ->
      Prims.string -> FStar_Util.json -> 'Auu____78221
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____78244 = json_of_message level contents  in
        callback uu____78244
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____78248 =
      FStar_List.map (fun _78252  -> FStar_Util.JsonStr _78252)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____78248  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____78266  -> write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____78284 = FStar_Options.desc_of_opt_type typ  in
      match uu____78284 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____78300 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____78335  ->
            match uu____78335 with
            | (_shortname,name,typ,doc1) ->
                let uu____78359 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____78359
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____78371 = sig_of_fstar_option name typ  in
                        let uu____78373 = snippets_of_fstar_option name typ
                           in
                        let uu____78377 =
                          let uu____78378 = FStar_Options.settable name  in
                          if uu____78378
                          then OptSet
                          else
                            (let uu____78383 = FStar_Options.resettable name
                                in
                             if uu____78383 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____78371;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____78373;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____78377
                        }))))
     in
  FStar_All.pipe_right uu____78300
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
    let uu___1471_78422 = opt  in
    let uu____78423 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___1471_78422.opt_name);
      opt_sig = (uu___1471_78422.opt_sig);
      opt_value = uu____78423;
      opt_default = (uu___1471_78422.opt_default);
      opt_type = (uu___1471_78422.opt_type);
      opt_snippets = (uu___1471_78422.opt_snippets);
      opt_documentation = (uu___1471_78422.opt_documentation);
      opt_permission_level = (uu___1471_78422.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1  ->
    let uu____78439 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____78439
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____78466 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____78466)
    else ("", opt_name)
  
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____78497 =
      match uu____78497 with
      | (uu____78509,(task,uu____78511)) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____78530 -> [])
       in
    let uu____78532 =
      let uu____78540 =
        let uu____78546 =
          let uu____78547 =
            let uu____78550 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _78564  -> FStar_Util.JsonStr _78564)
              uu____78550
             in
          FStar_Util.JsonList uu____78547  in
        ("loaded-dependencies", uu____78546)  in
      let uu____78567 =
        let uu____78575 =
          let uu____78581 =
            let uu____78582 =
              let uu____78585 =
                current_fstar_options (fun uu____78590  -> true)  in
              FStar_List.map json_of_fstar_option uu____78585  in
            FStar_Util.JsonList uu____78582  in
          ("options", uu____78581)  in
        [uu____78575]  in
      uu____78540 :: uu____78567  in
    FStar_Util.JsonAssoc uu____78532
  
let with_printed_effect_args :
  'Auu____78614 . (unit -> 'Auu____78614) -> 'Auu____78614 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____78627  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____78645  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    with_printed_effect_args
      (fun uu____78655  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____78663 'Auu____78664 .
    'Auu____78663 ->
      ((query_status * FStar_Util.json) * ('Auu____78664,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
  
let run_describe_protocol :
  'Auu____78701 'Auu____78702 .
    'Auu____78701 ->
      ((query_status * FStar_Util.json) * ('Auu____78701,'Auu____78702)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____78733 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____78733)
        FStar_Util.either)
  =
  fun st  ->
    let uu____78751 =
      let uu____78756 = json_of_repl_state st  in (QueryOK, uu____78756)  in
    (uu____78751, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____78774 'Auu____78775 .
    'Auu____78774 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____78774,'Auu____78775)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____78817 'Auu____78818 .
    'Auu____78817 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____78817,'Auu____78818)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____78858  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____78870 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____78870)
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
      let collect_decls uu____78905 =
        let uu____78906 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____78906 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____78912,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____78918,decls,uu____78920)) -> decls
         in
      let uu____78927 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____78936  ->
             let uu____78937 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _78948  -> FStar_Pervasives_Native.Some _78948)
               uu____78937)
         in
      match uu____78927 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____78966 = collect_errors ()  in
            FStar_All.pipe_right uu____78966 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____78992 =
              let uu____79000 =
                let uu____79006 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____79006)  in
              [uu____79000]  in
            FStar_Util.JsonAssoc uu____78992  in
          let js_decls =
            let uu____79020 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _79025  -> FStar_Util.JsonList _79025)
              uu____79020
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____79055 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____79055)
            FStar_Util.either)
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____79108 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____79108)
        FStar_Util.either)
  =
  fun st  ->
    let uu____79126 = nothing_left_to_pop st  in
    if uu____79126
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
      let uu____79213 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      write_json uu____79213
  
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task  ->
    match task with
    | LDInterleaved (uu____79221,tf) ->
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
    | uu____79273 -> ()
  
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list),repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____79291 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____79319 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _79366  -> FStar_Pervasives_Native.Some _79366) uu____79319)
       in
    match uu____79291 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___1569_79421 = st  in
          let uu____79422 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___1569_79421.repl_line);
            repl_column = (uu___1569_79421.repl_column);
            repl_fname = (uu___1569_79421.repl_fname);
            repl_deps_stack = (uu___1569_79421.repl_deps_stack);
            repl_curmod = (uu___1569_79421.repl_curmod);
            repl_env = uu____79422;
            repl_stdin = (uu___1569_79421.repl_stdin);
            repl_names = (uu___1569_79421.repl_names)
          }  in
        let uu____79423 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____79423 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___1579_79478 = issue  in
    let uu____79479 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____79479;
      FStar_Errors.issue_level = (uu___1579_79478.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___1579_79478.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___1579_79478.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____79489 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____79489)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___1586_79525 = st1  in
        {
          repl_line = (uu___1586_79525.repl_line);
          repl_column = (uu___1586_79525.repl_column);
          repl_fname = (uu___1586_79525.repl_fname);
          repl_deps_stack = (uu___1586_79525.repl_deps_stack);
          repl_curmod = (uu___1586_79525.repl_curmod);
          repl_env =
            (let uu___1588_79527 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___1588_79527.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___1588_79527.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___1588_79527.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___1588_79527.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___1588_79527.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___1588_79527.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___1588_79527.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___1588_79527.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___1588_79527.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___1588_79527.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___1588_79527.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___1588_79527.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___1588_79527.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___1588_79527.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___1588_79527.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___1588_79527.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___1588_79527.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___1588_79527.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___1588_79527.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___1588_79527.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___1588_79527.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___1588_79527.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___1588_79527.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___1588_79527.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___1588_79527.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___1588_79527.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___1588_79527.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___1588_79527.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___1588_79527.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___1588_79527.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___1588_79527.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___1588_79527.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___1588_79527.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___1588_79527.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___1588_79527.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___1588_79527.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___1588_79527.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___1588_79527.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___1588_79527.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___1588_79527.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___1588_79527.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___1588_79527.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___1586_79525.repl_stdin);
          repl_names = (uu___1586_79525.repl_names)
        }  in
      let uu____79528 = query  in
      match uu____79528 with
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
            let uu____79554 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____79554 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____79583 =
                    let uu____79586 = collect_errors ()  in
                    FStar_All.pipe_right uu____79586
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____79583  in
                let st4 =
                  if success
                  then
                    let uu___1607_79595 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___1607_79595.repl_fname);
                      repl_deps_stack = (uu___1607_79595.repl_deps_stack);
                      repl_curmod = (uu___1607_79595.repl_curmod);
                      repl_env = (uu___1607_79595.repl_env);
                      repl_stdin = (uu___1607_79595.repl_stdin);
                      repl_names = (uu___1607_79595.repl_names)
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
       let uu____79625 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1"))
          in
       Prims.op_Hat (FStar_String.uppercase first) uu____79625)
  
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
          let uu____79666 = FStar_Util.psmap_empty ()  in
          let uu____79671 =
            let uu____79675 = FStar_Options.prims ()  in uu____79675 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____79691 =
                   FStar_Parser_Dep.lowercase_module_name dep1  in
                 FStar_Util.psmap_add acc uu____79691 true) uu____79666
            uu____79671
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____79720  ->
               match uu____79720 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____79743 = capitalize modname  in
                        FStar_Util.split uu____79743 "."  in
                      let uu____79746 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____79746 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____79761 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____79761)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      (let uu____79785 = FStar_Options.debug_any ()  in
       if uu____79785
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____79793 = load_deps st  in
       match uu____79793 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____79828 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____79828  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____79862 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____79862 (fun a2  -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___1645_79866 = st1  in
                {
                  repl_line = (uu___1645_79866.repl_line);
                  repl_column = (uu___1645_79866.repl_column);
                  repl_fname = (uu___1645_79866.repl_fname);
                  repl_deps_stack = (uu___1645_79866.repl_deps_stack);
                  repl_curmod = (uu___1645_79866.repl_curmod);
                  repl_env = (uu___1645_79866.repl_env);
                  repl_stdin = (uu___1645_79866.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____79874 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____79874)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let uu____79897 = nothing_left_to_pop st  in
      if uu____79897
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
              let uu____80005 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____80005  in
            let lid1 =
              let uu____80011 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____80011  in
            let uu____80016 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____80016
              (FStar_Util.map_option
                 (fun uu____80073  ->
                    match uu____80073 with
                    | ((uu____80093,typ),r) ->
                        ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____80115 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____80115
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____80181 = FStar_TypeChecker_Env.lookup_qname tcenv lid
               in
            FStar_Util.bind_opt uu____80181
              (fun uu___715_80226  ->
                 match uu___715_80226 with
                 | (FStar_Util.Inr (se,uu____80249),uu____80250) ->
                     let uu____80279 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____80279
                 | uu____80282 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____80340  ->
                 match uu____80340 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____80399 -> info_at_pos_opt
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
                    let uu____80556 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____80556
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____80573 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____80591 -> FStar_Pervasives_Native.None  in
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
                let uu____80609 =
                  let uu____80622 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____80622)  in
                FStar_Pervasives_Native.Some uu____80609
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
    let uu____80757 = trim_option_name opt_name  in
    match uu____80757 with
    | (uu____80781,trimmed_name) ->
        let uu____80787 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____80787 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____80822 =
               let uu____80835 =
                 let uu____80843 = update_option opt  in
                 alist_of_fstar_option uu____80843  in
               ("option", uu____80835)  in
             FStar_Util.Inr uu____80822)
  
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
      let uu____80901 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____80901 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____80936 =
            let uu____80949 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____80949)  in
          FStar_Util.Inr uu____80936
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____80980 =
            let uu____80993 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____80993)  in
          FStar_Util.Inr uu____80980
  
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
          let uu____81091 =
            run_symbol_lookup st symbol pos_opt requested_info  in
          match uu____81091 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____81165 ->
              let uu____81180 = run_module_lookup st symbol  in
              (match uu____81180 with
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
  'Auu____81386 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string * Prims.int * Prims.int)
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____81386)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____81454 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____81454 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____81558 .
    ('Auu____81558 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____81558 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___716_81573  ->
    match uu___716_81573 with
    | (uu____81578,FStar_Interactive_CompletionTable.Namespace uu____81579)
        -> FStar_Pervasives_Native.None
    | (uu____81584,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____81585;
         FStar_Interactive_CompletionTable.mod_path = uu____81586;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____81596 =
          let uu____81601 =
            let uu____81602 =
              let uu___1779_81603 = md  in
              let uu____81604 =
                let uu____81606 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.op_Hat uu____81606 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____81604;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___1779_81603.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___1779_81603.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____81602  in
          (pth, uu____81601)  in
        FStar_Pervasives_Native.Some uu____81596
  
let run_code_autocomplete :
  'Auu____81620 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____81620)
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
  'Auu____81682 'Auu____81683 'Auu____81684 .
    repl_state ->
      Prims.string ->
        'Auu____81682 ->
          'Auu____81683 ->
            ((query_status * FStar_Util.json) * (repl_state,'Auu____81684)
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
              (fun _81731  -> FStar_Pervasives_Native.Some _81731)
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
        let uu____81765 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____81765 with
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
  'Auu____81828 'Auu____81829 .
    'Auu____81828 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____81828,'Auu____81829)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____81861 = trim_option_name search_term  in
        match uu____81861 with
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
        | (uu____81917,uu____81918) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____81941 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____81941)
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
  'Auu____81992 'Auu____81993 .
    repl_state ->
      'Auu____81992 ->
        (repl_state -> 'Auu____81992) ->
          ('Auu____81992 * (repl_state,'Auu____81993) FStar_Util.either)
  =
  fun st  ->
    fun sigint_default  ->
      fun task  ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st  in
        let results =
          try
            (fun uu___1838_82034  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____82045  ->
                        let uu____82046 = task st1  in
                        FStar_All.pipe_left
                          (fun _82051  -> FStar_Util.Inl _82051) uu____82046))
              ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = pop_repl "run_and_rewind" st1  in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'Auu____82100 'Auu____82101 'Auu____82102 .
    repl_state ->
      Prims.string ->
        'Auu____82100 ->
          'Auu____82101 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____82102)
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
                    ((uu____82203,{ FStar_Syntax_Syntax.lbname = uu____82204;
                                    FStar_Syntax_Syntax.lbunivs = univs1;
                                    FStar_Syntax_Syntax.lbtyp = uu____82206;
                                    FStar_Syntax_Syntax.lbeff = uu____82207;
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs = uu____82209;
                                    FStar_Syntax_Syntax.lbpos = uu____82210;_}::[]),uu____82211);
                  FStar_Syntax_Syntax.sigrng = uu____82212;
                  FStar_Syntax_Syntax.sigquals = uu____82213;
                  FStar_Syntax_Syntax.sigmeta = uu____82214;
                  FStar_Syntax_Syntax.sigattrs = uu____82215;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____82254 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____82275 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____82275 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____82281) ->
                  FStar_Pervasives_Native.Some decls
              | uu____82302 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____82320 =
                let uu____82325 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____82325 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____82320  in
            let typecheck tcenv decls =
              let uu____82347 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____82347 with | (ses,uu____82361,uu____82362) -> ses
               in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____82383 = parse1 frag  in
                 match uu____82383 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____82409 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1,def) ->
                           let uu____82445 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def  in
                           (match uu____82445 with
                            | (univs2,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____82457 = FStar_Options.trace_error ()  in
                     if uu____82457
                     then aux ()
                     else
                       (try
                          (fun uu___1921_82471  ->
                             match () with | () -> aux ()) ()
                        with
                        | uu___1920_82480 ->
                            let uu____82485 =
                              FStar_Errors.issue_of_exn uu___1920_82480  in
                            (match uu____82485 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____82493 =
                                   let uu____82494 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____82494  in
                                 (QueryNOK, uu____82493)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___1920_82480)))
  
let run_compute :
  'Auu____82509 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____82509)
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
               let uu____82587 =
                 let uu____82588 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____82588  in
               (QueryOK, uu____82587))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____82623 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____82645 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___717_82680  ->
    match uu___717_82680 with
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
    let uu____82814 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____82821 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____82814; sc_fvars = uu____82821 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____82845 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____82845 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____82873 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____82873 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____82892,typ),uu____82894) ->
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
      let uu____82944 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____82944 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____82988 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____82988  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____83032 = sc_typ tcenv sc  in
        term_to_string tcenv uu____83032  in
      let uu____83033 =
        let uu____83041 =
          let uu____83047 =
            let uu____83048 =
              let uu____83050 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____83050.FStar_Ident.str  in
            FStar_Util.JsonStr uu____83048  in
          ("lid", uu____83047)  in
        [uu____83041; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____83033
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____83083 -> true
    | uu____83086 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____83096 -> uu____83096
  
let run_search :
  'Auu____83105 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____83105)
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
              let uu____83152 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____83152
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
              let uu____83211 =
                let uu____83212 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____83212  in
              FStar_Exn.raise uu____83211
            else
              if beg_quote
              then
                (let uu____83218 = strip_quotes term1  in
                 NameContainsStr uu____83218)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____83223 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____83223 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____83226 =
                       let uu____83227 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____83227  in
                     FStar_Exn.raise uu____83226
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____83255 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____83255  in
      let results =
        try
          (fun uu___2034_83289  ->
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
                        let uu____83337 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____83337  in
                      let uu____83343 =
                        let uu____83344 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____83344  in
                      FStar_Exn.raise uu____83343
                  | uu____83351 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = SyntaxCheck ; push_code = uu____83482;
            push_line = uu____83483; push_column = uu____83484;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____83490 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____83492 -> q)
  
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
      let uu____83565 = validate_and_run_query st query  in
      match uu____83565 with
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
      let uu____83631 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____83631
  
let (js_repl_eval_str :
  repl_state ->
    Prims.string -> (Prims.string * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____83655 =
        let uu____83665 = parse_interactive_query query_str  in
        js_repl_eval st uu____83665  in
      match uu____83655 with
      | (js_response,st_opt) ->
          let uu____83688 = FStar_Util.string_of_json js_response  in
          (uu____83688, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____83701  ->
    let uu____83702 = FStar_Options.parse_cmd_line ()  in
    match uu____83702 with
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
              | h::uu____83725::uu____83726 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____83735 -> ()))
  
let rec (go : repl_state -> Prims.int) =
  fun st  ->
    let query = read_interactive_query st.repl_stdin  in
    let uu____83748 = validate_and_run_query st query  in
    match uu____83748 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____83801 =
      let uu____83804 = FStar_ST.op_Bang issues  in e :: uu____83804  in
    FStar_ST.op_Colon_Equals issues uu____83801  in
  let count_errors uu____83858 =
    let uu____83859 =
      let uu____83862 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____83862
       in
    FStar_List.length uu____83859  in
  let report uu____83897 =
    let uu____83898 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____83898  in
  let clear1 uu____83929 = FStar_ST.op_Colon_Equals issues []  in
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
               let uu____83990 = get_json ()  in
               forward_message printer label uu____83990)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____84004 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  let uu____84007 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  FStar_Range.mk_range "<input>" uu____84004 uu____84007 
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____84021 = FStar_Util.open_stdin ()  in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____84021;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' : 'Auu____84037 . repl_state -> 'Auu____84037 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____84046 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____84046
       then
         let uu____84050 =
           let uu____84052 = FStar_Options.file_list ()  in
           FStar_List.hd uu____84052  in
         FStar_SMTEncoding_Solver.with_hints_db uu____84050
           (fun uu____84059  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____84073 =
       let uu____84075 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____84075  in
     if uu____84073
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____84084 = FStar_Options.trace_error ()  in
     if uu____84084
     then interactive_mode' init1
     else
       (try
          (fun uu___2182_84090  ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___2181_84093 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___2181_84093)))
  
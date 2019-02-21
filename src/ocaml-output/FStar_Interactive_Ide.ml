open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun msg  ->
      let uu____26 = FStar_TypeChecker_Tc.snapshot_context env msg  in
      match uu____26 with
      | (ctx_depth,env1) ->
          let uu____70 = FStar_Options.snapshot ()  in
          (match uu____70 with
           | (opt_depth,()) -> ((ctx_depth, opt_depth), env1))
  
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1  ->
    fun msg  ->
      fun uu____116  ->
        match uu____116 with
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
    match projectee with | SyntaxCheck  -> true | uu____183 -> false
  
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____194 -> false
  
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____205 -> false
  
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun check_kind  ->
      let uu___32_218 = env  in
      let uu____219 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___32_218.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___32_218.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___32_218.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___32_218.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___32_218.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___32_218.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___32_218.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___32_218.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___32_218.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___32_218.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___32_218.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___32_218.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___32_218.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___32_218.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___32_218.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___32_218.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___32_218.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___32_218.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___32_218.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___32_218.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___32_218.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___32_218.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___32_218.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___32_218.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___32_218.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___32_218.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___32_218.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___32_218.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___32_218.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___32_218.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___32_218.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___32_218.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___32_218.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___32_218.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___32_218.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___32_218.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___32_218.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___32_218.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___32_218.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___32_218.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____219;
        FStar_TypeChecker_Env.nbe = (uu___32_218.FStar_TypeChecker_Env.nbe)
      }
  
let with_captured_errors' :
  'Auu____229 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____229 FStar_Pervasives_Native.option)
          -> 'Auu____229 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        try
          (fun uu___34_259  ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____265  -> f env)) ()
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
            ((let uu____283 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.log_issue uu____283
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt  ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e,msg,r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) ->
            ((let uu____313 =
                let uu____323 =
                  let uu____331 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____331)  in
                [uu____323]  in
              FStar_TypeChecker_Err.add_errors env uu____313);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____356 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____356 FStar_Pervasives_Native.option)
          -> 'Auu____356 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        let uu____383 = FStar_Options.trace_error ()  in
        if uu____383
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
    let uu____430 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____430 }
  
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____445  ->
    match uu____445 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____455 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____455)
  
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
    match projectee with | LDInterleaved _0 -> true | uu____610 -> false
  
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____642 -> false
  
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____662 -> false
  
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____682 -> false
  
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee  -> match projectee with | PushFragment _0 -> _0 
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee  -> match projectee with | Noop  -> true | uu____701 -> false 
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
      let uu____1072 = FStar_ST.op_Bang repl_stack  in
      match uu____1072 with
      | [] -> failwith "Too many pops"
      | (depth,(uu____1102,st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth
             in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____1149 = FStar_Util.physical_equality env st'.repl_env
               in
            FStar_Common.runtime_assert uu____1149 "Inconsistent stack state");
           st')
  
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg  ->
    fun push_kind  ->
      fun task  ->
        fun st  ->
          let uu____1175 = snapshot_env st.repl_env msg  in
          match uu____1175 with
          | (depth,env) ->
              ((let uu____1183 =
                  let uu____1184 = FStar_ST.op_Bang repl_stack  in
                  (depth, (task, st)) :: uu____1184  in
                FStar_ST.op_Colon_Equals repl_stack uu____1183);
               (let uu___35_1245 = st  in
                let uu____1246 = set_check_kind env push_kind  in
                {
                  repl_line = (uu___35_1245.repl_line);
                  repl_column = (uu___35_1245.repl_column);
                  repl_fname = (uu___35_1245.repl_fname);
                  repl_deps_stack = (uu___35_1245.repl_deps_stack);
                  repl_curmod = (uu___35_1245.repl_curmod);
                  repl_env = uu____1246;
                  repl_stdin = (uu___35_1245.repl_stdin);
                  repl_names = (uu___35_1245.repl_names)
                }))
  
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st  ->
    let uu____1254 =
      let uu____1255 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____1255  in
    uu____1254 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of
  (FStar_Syntax_Syntax.binding,FStar_TypeChecker_Env.sig_binding)
  FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____1359 -> false
  
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____1401 -> false
  
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____1437 -> false
  
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | NTInclude _0 -> _0 
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____1473 -> false
  
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
              let uu____1542 = FStar_Ident.text_of_id id1  in
              let uu____1544 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                uu____1542 [] uu____1544
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____1552 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____1552
            else table
        | NTInclude (host,included) ->
            let uu____1558 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____1563 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____1558 uu____1563
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid,uu____1575)) -> [lid]
              | FStar_Util.Inr (lids,uu____1593) -> lids
              | uu____1598 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   let uu____1615 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____1615 lid) table lids
  
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
              let uu____1646 = FStar_Syntax_Syntax.mod_name md  in
              uu____1646.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___36_1672 = st  in
      {
        repl_line = (uu___36_1672.repl_line);
        repl_column = (uu___36_1672.repl_column);
        repl_fname = (uu___36_1672.repl_fname);
        repl_deps_stack = (uu___36_1672.repl_deps_stack);
        repl_curmod = (uu___36_1672.repl_curmod);
        repl_env = (uu___36_1672.repl_env);
        repl_stdin = (uu___36_1672.repl_stdin);
        repl_names = names1
      }
  
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____1688  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____1702 =
        let uu____1705 = FStar_ST.op_Bang events  in evt :: uu____1705  in
      FStar_ST.op_Colon_Equals events uu____1702  in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1  ->
             fun op  ->
               let uu____1832 =
                 let uu____1833 =
                   let uu____1838 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____1838, op)  in
                 NTOpen uu____1833  in
               push_event uu____1832);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1  ->
             fun ns  ->
               let uu____1844 =
                 let uu____1845 =
                   let uu____1850 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____1850, ns)  in
                 NTInclude uu____1845  in
               push_event uu____1844);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1  ->
             fun x  ->
               fun l  ->
                 let uu____1858 =
                   let uu____1859 =
                     let uu____1866 =
                       FStar_Syntax_DsEnv.current_module dsenv1  in
                     (uu____1866, x, l)  in
                   NTAlias uu____1859  in
                 push_event uu____1858)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1871  -> fun s  -> push_event (NTBinding s))
      })
  
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____1925 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1  ->
             let uu____1933 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks
                in
             ((), uu____1933))
         in
      match uu____1925 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____1935 =
      let uu____1940 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____1941 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____1940, uu____1941)  in
    match uu____1935 with
    | (old_dshooks,old_tchooks) ->
        let uu____1957 = fresh_name_tracking_hooks ()  in
        (match uu____1957 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1992 = set_hooks new_dshooks new_tchooks env  in
             (uu____1992,
               ((fun env1  ->
                   let uu____2006 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____2007 =
                     let uu____2010 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____2010  in
                   (uu____2006, uu____2007)))))
  
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___17_2066  ->
    match uu___17_2066 with
    | LDInterleaved (intf,impl) ->
        let uu____2070 = string_of_timed_fname intf  in
        let uu____2072 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____2070 uu____2072
    | LDSingle intf_or_impl ->
        let uu____2076 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____2076
    | LDInterfaceOfCurrentFile intf ->
        let uu____2080 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____2080
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
        let uu____2110 =
          let uu____2115 =
            let uu____2116 =
              let uu____2122 = FStar_TypeChecker_Env.dep_graph env  in
              FStar_Parser_Dep.parsing_data_of uu____2122  in
            FStar_All.pipe_right modf uu____2116  in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____2115
           in
        match uu____2110 with | (uu____2124,env1) -> env1
  
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____2152 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____2152)
        | LDSingle intf_or_impl ->
            let uu____2155 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____2155)
        | LDInterfaceOfCurrentFile intf ->
            let uu____2158 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____2158)
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
            let uu____2224 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____2224
        | intf_or_impl::deps' ->
            let uu____2234 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____2234
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
      let uu____2288 = get_mod_name f  in uu____2288 = our_mod_name  in
    let uu____2291 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_Universal.load_parsing_data_from_cache
       in
    match uu____2291 with
    | (deps,dep_graph1) ->
        let uu____2320 = FStar_List.partition has_our_mod_name deps  in
        (match uu____2320 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____2370 =
                       let uu____2372 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____2372  in
                     if uu____2370
                     then
                       let uu____2375 =
                         let uu____2381 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____2381)
                          in
                       FStar_Errors.raise_err uu____2375
                     else ());
                    (let uu____2388 =
                       let uu____2390 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____2390  in
                     if uu____2388
                     then
                       let uu____2393 =
                         let uu____2399 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____2399)
                          in
                       FStar_Errors.raise_err uu____2393
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____2409 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____2420 =
                       let uu____2426 =
                         FStar_Util.format message [our_mod_name; mods_str]
                          in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____2426)
                        in
                     FStar_Errors.raise_err uu____2420);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___18_2445  ->
    match uu___18_2445 with
    | LDInterleaved (intf,impl) ->
        let uu____2448 =
          let uu____2453 = tf_of_fname intf.tf_fname  in
          let uu____2454 = tf_of_fname impl.tf_fname  in
          (uu____2453, uu____2454)  in
        LDInterleaved uu____2448
    | LDSingle intf_or_impl ->
        let uu____2456 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____2456
    | LDInterfaceOfCurrentFile intf ->
        let uu____2458 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____2458
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
          let uu____2490 = track_name_changes st1.repl_env  in
          match uu____2490 with
          | (env,finish_name_tracking) ->
              let check_success uu____2535 =
                (let uu____2538 = FStar_Errors.get_err_count ()  in
                 uu____2538 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____2542 =
                let uu____2550 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1  ->
                       let uu____2564 =
                         run_repl_task st1.repl_curmod env1 task  in
                       FStar_All.pipe_left
                         (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                         uu____2564)
                   in
                match uu____2550 with
                | FStar_Pervasives_Native.Some (curmod,env1) when
                    check_success () -> (curmod, env1, true)
                | uu____2598 -> ((st1.repl_curmod), env, false)  in
              (match uu____2542 with
               | (curmod,env1,success) ->
                   let uu____2617 = finish_name_tracking env1  in
                   (match uu____2617 with
                    | (env2,name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___37_2638 = st1  in
                              {
                                repl_line = (uu___37_2638.repl_line);
                                repl_column = (uu___37_2638.repl_column);
                                repl_fname = (uu___37_2638.repl_fname);
                                repl_deps_stack =
                                  (uu___37_2638.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___37_2638.repl_stdin);
                                repl_names = (uu___37_2638.repl_names)
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
          let uu____2685 = FStar_Options.debug_any ()  in
          if uu____2685
          then
            let uu____2688 = string_of_repl_task task  in
            FStar_Util.print2 "%s %s" verb uu____2688
          else ()  in
        let rec revert_many st1 uu___19_2713 =
          match uu___19_2713 with
          | [] -> st1
          | (_id,(task,_st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1  in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env
                   in
                let st'1 =
                  let uu___38_2766 = st'  in
                  let uu____2767 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1
                     in
                  {
                    repl_line = (uu___38_2766.repl_line);
                    repl_column = (uu___38_2766.repl_column);
                    repl_fname = (uu___38_2766.repl_fname);
                    repl_deps_stack = (uu___38_2766.repl_deps_stack);
                    repl_curmod = (uu___38_2766.repl_curmod);
                    repl_env = uu____2767;
                    repl_stdin = (uu___38_2766.repl_stdin);
                    repl_names = (uu___38_2766.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____2820 = FStar_Options.restore_cmd_line_options false
                   in
                FStar_All.pipe_right uu____2820 (fun a1  -> ()));
               (let timestamped_task = update_task_timestamps task  in
                let push_kind =
                  let uu____2824 = FStar_Options.lax ()  in
                  if uu____2824 then LaxCheck else FullCheck  in
                let uu____2829 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____2829 with
                | (success,st2) ->
                    if success
                    then
                      let uu____2849 =
                        let uu___39_2850 = st2  in
                        let uu____2851 = FStar_ST.op_Bang repl_stack  in
                        {
                          repl_line = (uu___39_2850.repl_line);
                          repl_column = (uu___39_2850.repl_column);
                          repl_fname = (uu___39_2850.repl_fname);
                          repl_deps_stack = uu____2851;
                          repl_curmod = (uu___39_2850.repl_curmod);
                          repl_env = (uu___39_2850.repl_env);
                          repl_stdin = (uu___39_2850.repl_stdin);
                          repl_names = (uu___39_2850.repl_names)
                        }  in
                      aux uu____2849 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____2895 = update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____2895
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____2912 = revert_many st1 previous1  in
              aux uu____2912 tasks2 []
           in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___20_2927  ->
    match uu___20_2927 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2941 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____2941
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2947 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2951 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2977 -> true
    | uu____2984 -> false
  
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____3003 -> uu____3003
  
let js_fail : 'Auu____3016 . Prims.string -> FStar_Util.json -> 'Auu____3016
  =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___21_3036  ->
    match uu___21_3036 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___22_3049  ->
    match uu___22_3049 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____3063 .
    (FStar_Util.json -> 'Auu____3063) ->
      FStar_Util.json -> 'Auu____3063 Prims.list
  =
  fun k  ->
    fun uu___23_3078  ->
      match uu___23_3078 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___24_3100  ->
    match uu___24_3100 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s  ->
    let uu____3131 = js_str s  in
    match uu____3131 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____3136 -> js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____3145 = js_str s  in
    match uu____3145 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____3153 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____3182 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____3195 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____3224 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____3263 = js_str k1  in
        (match uu____3263 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____3291 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____3303 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____3314 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____3325 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____3336 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____3349 = js_str k1  in
        (match uu____3349 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____3359 ->
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
    match projectee with | Exit  -> true | uu____3476 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____3487 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____3498 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____3511 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  -> match projectee with | Pop  -> true | uu____3533 -> false 
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____3545 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____3573 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____3622 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____3671 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____3742 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____3790 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____3814 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____3838 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___25_3877  ->
    match uu___25_3877 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____3882 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____3886; push_code = uu____3887;
          push_line = uu____3888; push_column = uu____3889;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____3895 -> false
    | GenericError uu____3905 -> false
    | ProtocolViolation uu____3908 -> false
    | Push uu____3911 -> true
    | AutoComplete uu____3913 -> true
    | Lookup uu____3920 -> true
    | Compute uu____3936 -> true
    | Search uu____3947 -> true
  
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
    | InvalidQuery uu____4013 -> true
    | uu____4016 -> false
  
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidQuery uu____4027 -> uu____4027
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____4038 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____4049 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____4060 -> false
  
let try_assoc :
  'Auu____4071 'Auu____4072 .
    'Auu____4071 ->
      ('Auu____4071 * 'Auu____4072) Prims.list ->
        'Auu____4072 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____4097 =
        FStar_Util.try_find
          (fun uu____4111  ->
             match uu____4111 with | (k,uu____4118) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____4097
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____4143 =
          let uu____4144 =
            let uu____4146 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____4146
             in
          ProtocolViolation uu____4144  in
        { qq = uu____4143; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc1 errloc key a =
      let uu____4189 = try_assoc key a  in
      match uu____4189 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____4194 =
            let uu____4195 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____4195  in
          FStar_Exn.raise uu____4194
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____4215 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____4215 js_str  in
    try
      (fun uu___41_4225  ->
         match () with
         | () ->
             let query =
               let uu____4228 = assoc1 "query" "query" request  in
               FStar_All.pipe_right uu____4228 js_str  in
             let args =
               let uu____4240 = assoc1 "query" "args" request  in
               FStar_All.pipe_right uu____4240 js_assoc  in
             let arg k = assoc1 "[args]" k args  in
             let try_arg k =
               let uu____4269 = try_assoc k args  in
               match uu____4269 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____4278 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____4284 =
                     let uu____4286 = arg "code"  in
                     FStar_All.pipe_right uu____4286 js_str  in
                   Segment uu____4284
               | "peek" ->
                   let uu____4290 =
                     let uu____4291 =
                       let uu____4292 = arg "kind"  in
                       FStar_All.pipe_right uu____4292 js_pushkind  in
                     let uu____4294 =
                       let uu____4296 = arg "code"  in
                       FStar_All.pipe_right uu____4296 js_str  in
                     let uu____4299 =
                       let uu____4301 = arg "line"  in
                       FStar_All.pipe_right uu____4301 js_int  in
                     let uu____4304 =
                       let uu____4306 = arg "column"  in
                       FStar_All.pipe_right uu____4306 js_int  in
                     {
                       push_kind = uu____4291;
                       push_code = uu____4294;
                       push_line = uu____4299;
                       push_column = uu____4304;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____4290
               | "push" ->
                   let uu____4312 =
                     let uu____4313 =
                       let uu____4314 = arg "kind"  in
                       FStar_All.pipe_right uu____4314 js_pushkind  in
                     let uu____4316 =
                       let uu____4318 = arg "code"  in
                       FStar_All.pipe_right uu____4318 js_str  in
                     let uu____4321 =
                       let uu____4323 = arg "line"  in
                       FStar_All.pipe_right uu____4323 js_int  in
                     let uu____4326 =
                       let uu____4328 = arg "column"  in
                       FStar_All.pipe_right uu____4328 js_int  in
                     {
                       push_kind = uu____4313;
                       push_code = uu____4316;
                       push_line = uu____4321;
                       push_column = uu____4326;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____4312
               | "autocomplete" ->
                   let uu____4334 =
                     let uu____4340 =
                       let uu____4342 = arg "partial-symbol"  in
                       FStar_All.pipe_right uu____4342 js_str  in
                     let uu____4345 =
                       let uu____4346 = try_arg "context"  in
                       FStar_All.pipe_right uu____4346
                         js_optional_completion_context
                        in
                     (uu____4340, uu____4345)  in
                   AutoComplete uu____4334
               | "lookup" ->
                   let uu____4354 =
                     let uu____4369 =
                       let uu____4371 = arg "symbol"  in
                       FStar_All.pipe_right uu____4371 js_str  in
                     let uu____4374 =
                       let uu____4375 = try_arg "context"  in
                       FStar_All.pipe_right uu____4375
                         js_optional_lookup_context
                        in
                     let uu____4381 =
                       let uu____4384 =
                         let uu____4394 = try_arg "location"  in
                         FStar_All.pipe_right uu____4394
                           (FStar_Util.map_option js_assoc)
                          in
                       FStar_All.pipe_right uu____4384
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____4455 =
                                 let uu____4457 =
                                   assoc1 "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____4457 js_str  in
                               let uu____4461 =
                                 let uu____4463 =
                                   assoc1 "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____4463 js_int  in
                               let uu____4467 =
                                 let uu____4469 =
                                   assoc1 "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____4469 js_int  in
                               (uu____4455, uu____4461, uu____4467)))
                        in
                     let uu____4476 =
                       let uu____4480 = arg "requested-info"  in
                       FStar_All.pipe_right uu____4480 (js_list js_str)  in
                     (uu____4369, uu____4374, uu____4381, uu____4476)  in
                   Lookup uu____4354
               | "compute" ->
                   let uu____4493 =
                     let uu____4503 =
                       let uu____4505 = arg "term"  in
                       FStar_All.pipe_right uu____4505 js_str  in
                     let uu____4508 =
                       let uu____4513 = try_arg "rules"  in
                       FStar_All.pipe_right uu____4513
                         (FStar_Util.map_option (js_list js_reductionrule))
                        in
                     (uu____4503, uu____4508)  in
                   Compute uu____4493
               | "search" ->
                   let uu____4531 =
                     let uu____4533 = arg "terms"  in
                     FStar_All.pipe_right uu____4533 js_str  in
                   Search uu____4531
               | "vfs-add" ->
                   let uu____4537 =
                     let uu____4546 =
                       let uu____4550 = try_arg "filename"  in
                       FStar_All.pipe_right uu____4550
                         (FStar_Util.map_option js_str)
                        in
                     let uu____4560 =
                       let uu____4562 = arg "contents"  in
                       FStar_All.pipe_right uu____4562 js_str  in
                     (uu____4546, uu____4560)  in
                   VfsAdd uu____4537
               | uu____4569 ->
                   let uu____4571 =
                     FStar_Util.format1 "Unknown query '%s'" query  in
                   ProtocolViolation uu____4571
                in
             { qq = uu____4278; qid }) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___43_4590  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____4610 = FStar_Util.json_of_string query_str  in
    match uu____4610 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____4622 = FStar_Util.read_line stream  in
    match uu____4622 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____4638 .
    ('Auu____4638 -> FStar_Util.json) ->
      'Auu____4638 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____4658 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____4658
  
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
    let uu____4678 =
      let uu____4686 =
        let uu____4694 =
          let uu____4702 =
            let uu____4708 =
              let uu____4709 =
                let uu____4712 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____4718 = FStar_Range.json_of_use_range r  in
                      [uu____4718]
                   in
                let uu____4719 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____4725 = FStar_Range.def_range r  in
                      let uu____4726 = FStar_Range.use_range r  in
                      uu____4725 <> uu____4726 ->
                      let uu____4727 = FStar_Range.json_of_def_range r  in
                      [uu____4727]
                  | uu____4728 -> []  in
                FStar_List.append uu____4712 uu____4719  in
              FStar_Util.JsonList uu____4709  in
            ("ranges", uu____4708)  in
          [uu____4702]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____4694
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____4686
       in
    FStar_Util.JsonAssoc uu____4678
  
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
    let uu____4946 =
      let uu____4954 =
        let uu____4960 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____4960)  in
      let uu____4963 =
        let uu____4971 =
          let uu____4977 =
            json_of_opt (fun _0_2  -> FStar_Util.JsonStr _0_2) lr.slr_typ  in
          ("type", uu____4977)  in
        let uu____4981 =
          let uu____4989 =
            let uu____4995 =
              json_of_opt (fun _0_3  -> FStar_Util.JsonStr _0_3) lr.slr_doc
               in
            ("documentation", uu____4995)  in
          let uu____4999 =
            let uu____5007 =
              let uu____5013 =
                json_of_opt (fun _0_4  -> FStar_Util.JsonStr _0_4) lr.slr_def
                 in
              ("definition", uu____5013)  in
            [uu____5007]  in
          uu____4989 :: uu____4999  in
        uu____4971 :: uu____4981  in
      uu____4954 :: uu____4963  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____4946
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____5059 =
      FStar_List.map (fun _0_5  -> FStar_Util.JsonStr _0_5)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _0_6  -> FStar_Util.JsonList _0_6) uu____5059
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____5093 -> false
  
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____5104 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____5115 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___26_5123  ->
    match uu___26_5123 with
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
  fun uu___27_5374  ->
    match uu___27_5374 with
    | FStar_Options.Const uu____5376 -> "flag"
    | FStar_Options.IntStr uu____5378 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____5382 -> "path"
    | FStar_Options.SimpleStr uu____5385 -> "string"
    | FStar_Options.EnumStr uu____5388 -> "enum"
    | FStar_Options.OpenEnumStr uu____5393 -> "open enum"
    | FStar_Options.PostProcessed (uu____5403,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____5413,typ) ->
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
        | FStar_Options.Const uu____5485 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____5523,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____5533,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____5541 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____5541
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___28_5552  ->
    match uu___28_5552 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____5564 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____5564
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____5580 =
      let uu____5588 =
        let uu____5596 =
          let uu____5602 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____5602)  in
        let uu____5605 =
          let uu____5613 =
            let uu____5619 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____5619)  in
          let uu____5622 =
            let uu____5630 =
              let uu____5636 =
                json_of_opt (fun _0_7  -> FStar_Util.JsonStr _0_7)
                  opt.opt_documentation
                 in
              ("documentation", uu____5636)  in
            let uu____5640 =
              let uu____5648 =
                let uu____5654 =
                  let uu____5655 = kind_of_fstar_option_type opt.opt_type  in
                  FStar_Util.JsonStr uu____5655  in
                ("type", uu____5654)  in
              [uu____5648;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____5630 :: uu____5640  in
          uu____5613 :: uu____5622  in
        uu____5596 :: uu____5605  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____5588  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____5580
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____5711 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____5711
  
let (write_json : FStar_Util.json -> unit) =
  fun json  ->
    (let uu____5726 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____5726);
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
      let uu____5817 =
        let uu____5825 =
          let uu____5833 =
            let uu____5839 =
              let uu____5840 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _0_8  -> FStar_Util.JsonStr _0_8) uu____5840
               in
            ("query-id", uu____5839)  in
          [uu____5833;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____5825  in
      FStar_Util.JsonAssoc uu____5817
  
let forward_message :
  'Auu____5913 .
    (FStar_Util.json -> 'Auu____5913) ->
      Prims.string -> FStar_Util.json -> 'Auu____5913
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____5936 = json_of_message level contents  in
        callback uu____5936
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____5940 =
      FStar_List.map (fun _0_9  -> FStar_Util.JsonStr _0_9)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____5940  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____5957  -> write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____5975 = FStar_Options.desc_of_opt_type typ  in
      match uu____5975 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____5991 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____6026  ->
            match uu____6026 with
            | (_shortname,name,typ,doc1) ->
                let uu____6050 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____6050
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____6062 = sig_of_fstar_option name typ  in
                        let uu____6064 = snippets_of_fstar_option name typ
                           in
                        let uu____6068 =
                          let uu____6069 = FStar_Options.settable name  in
                          if uu____6069
                          then OptSet
                          else
                            (let uu____6074 = FStar_Options.resettable name
                                in
                             if uu____6074 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____6062;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____6064;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____6068
                        }))))
     in
  FStar_All.pipe_right uu____5991
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
    let uu___44_6113 = opt  in
    let uu____6114 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___44_6113.opt_name);
      opt_sig = (uu___44_6113.opt_sig);
      opt_value = uu____6114;
      opt_default = (uu___44_6113.opt_default);
      opt_type = (uu___44_6113.opt_type);
      opt_snippets = (uu___44_6113.opt_snippets);
      opt_documentation = (uu___44_6113.opt_documentation);
      opt_permission_level = (uu___44_6113.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1  ->
    let uu____6130 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____6130
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____6157 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____6157)
    else ("", opt_name)
  
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____6188 =
      match uu____6188 with
      | (uu____6200,(task,uu____6202)) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____6221 -> [])
       in
    let uu____6223 =
      let uu____6231 =
        let uu____6237 =
          let uu____6238 =
            let uu____6241 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _0_10  -> FStar_Util.JsonStr _0_10)
              uu____6241
             in
          FStar_Util.JsonList uu____6238  in
        ("loaded-dependencies", uu____6237)  in
      let uu____6257 =
        let uu____6265 =
          let uu____6271 =
            let uu____6272 =
              let uu____6275 =
                current_fstar_options (fun uu____6280  -> true)  in
              FStar_List.map json_of_fstar_option uu____6275  in
            FStar_Util.JsonList uu____6272  in
          ("options", uu____6271)  in
        [uu____6265]  in
      uu____6231 :: uu____6257  in
    FStar_Util.JsonAssoc uu____6223
  
let with_printed_effect_args :
  'Auu____6304 . (unit -> 'Auu____6304) -> 'Auu____6304 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____6317  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____6335  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    with_printed_effect_args
      (fun uu____6345  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____6353 'Auu____6354 .
    'Auu____6353 ->
      ((query_status * FStar_Util.json) * ('Auu____6354,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
  
let run_describe_protocol :
  'Auu____6391 'Auu____6392 .
    'Auu____6391 ->
      ((query_status * FStar_Util.json) * ('Auu____6391,'Auu____6392)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____6423 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____6423)
        FStar_Util.either)
  =
  fun st  ->
    let uu____6441 =
      let uu____6446 = json_of_repl_state st  in (QueryOK, uu____6446)  in
    (uu____6441, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____6464 'Auu____6465 .
    'Auu____6464 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____6464,'Auu____6465)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____6507 'Auu____6508 .
    'Auu____6507 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____6507,'Auu____6508)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____6548  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____6560 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____6560)
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
      let collect_decls uu____6595 =
        let uu____6596 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____6596 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____6602,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____6608,decls,uu____6610)) -> decls
         in
      let uu____6617 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____6626  ->
             let uu____6627 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _0_11  -> FStar_Pervasives_Native.Some _0_11) uu____6627)
         in
      match uu____6617 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____6655 = collect_errors ()  in
            FStar_All.pipe_right uu____6655 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____6681 =
              let uu____6689 =
                let uu____6695 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____6695)  in
              [uu____6689]  in
            FStar_Util.JsonAssoc uu____6681  in
          let js_decls =
            let uu____6709 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _0_12  -> FStar_Util.JsonList _0_12)
              uu____6709
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____6743 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____6743)
            FStar_Util.either)
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____6796 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____6796)
        FStar_Util.either)
  =
  fun st  ->
    let uu____6814 = nothing_left_to_pop st  in
    if uu____6814
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
      let uu____6901 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      write_json uu____6901
  
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task  ->
    match task with
    | LDInterleaved (uu____6909,tf) ->
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
    | uu____6961 -> ()
  
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list),repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____6979 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____7007 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _0_13  -> FStar_Pervasives_Native.Some _0_13) uu____7007)
       in
    match uu____6979 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___45_7108 = st  in
          let uu____7109 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___45_7108.repl_line);
            repl_column = (uu___45_7108.repl_column);
            repl_fname = (uu___45_7108.repl_fname);
            repl_deps_stack = (uu___45_7108.repl_deps_stack);
            repl_curmod = (uu___45_7108.repl_curmod);
            repl_env = uu____7109;
            repl_stdin = (uu___45_7108.repl_stdin);
            repl_names = (uu___45_7108.repl_names)
          }  in
        let uu____7110 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____7110 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___46_7165 = issue  in
    let uu____7166 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____7166;
      FStar_Errors.issue_level = (uu___46_7165.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___46_7165.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___46_7165.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____7176 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____7176)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___47_7212 = st1  in
        {
          repl_line = (uu___47_7212.repl_line);
          repl_column = (uu___47_7212.repl_column);
          repl_fname = (uu___47_7212.repl_fname);
          repl_deps_stack = (uu___47_7212.repl_deps_stack);
          repl_curmod = (uu___47_7212.repl_curmod);
          repl_env =
            (let uu___48_7214 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___48_7214.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___48_7214.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___48_7214.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___48_7214.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___48_7214.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___48_7214.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___48_7214.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___48_7214.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___48_7214.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___48_7214.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___48_7214.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___48_7214.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___48_7214.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___48_7214.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___48_7214.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___48_7214.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___48_7214.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___48_7214.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___48_7214.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___48_7214.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___48_7214.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___48_7214.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___48_7214.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___48_7214.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___48_7214.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___48_7214.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___48_7214.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___48_7214.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___48_7214.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___48_7214.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___48_7214.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___48_7214.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___48_7214.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___48_7214.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___48_7214.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___48_7214.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___48_7214.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___48_7214.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___48_7214.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___48_7214.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___48_7214.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___48_7214.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___47_7212.repl_stdin);
          repl_names = (uu___47_7212.repl_names)
        }  in
      let uu____7215 = query  in
      match uu____7215 with
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
            let uu____7241 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____7241 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____7270 =
                    let uu____7273 = collect_errors ()  in
                    FStar_All.pipe_right uu____7273
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____7270  in
                let st4 =
                  if success
                  then
                    let uu___49_7282 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___49_7282.repl_fname);
                      repl_deps_stack = (uu___49_7282.repl_deps_stack);
                      repl_curmod = (uu___49_7282.repl_curmod);
                      repl_env = (uu___49_7282.repl_env);
                      repl_stdin = (uu___49_7282.repl_stdin);
                      repl_names = (uu___49_7282.repl_names)
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
       let uu____7312 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1"))
          in
       Prims.op_Hat (FStar_String.uppercase first) uu____7312)
  
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
          let uu____7353 = FStar_Util.psmap_empty ()  in
          let uu____7358 =
            let uu____7362 = FStar_Options.prims ()  in uu____7362 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____7378 = FStar_Parser_Dep.lowercase_module_name dep1
                    in
                 FStar_Util.psmap_add acc uu____7378 true) uu____7353
            uu____7358
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____7407  ->
               match uu____7407 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____7430 = capitalize modname  in
                        FStar_Util.split uu____7430 "."  in
                      let uu____7433 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____7433 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____7448 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____7448)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      (let uu____7472 = FStar_Options.debug_any ()  in
       if uu____7472
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____7480 = load_deps st  in
       match uu____7480 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____7515 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____7515  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____7549 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____7549 (fun a2  -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___50_7553 = st1  in
                {
                  repl_line = (uu___50_7553.repl_line);
                  repl_column = (uu___50_7553.repl_column);
                  repl_fname = (uu___50_7553.repl_fname);
                  repl_deps_stack = (uu___50_7553.repl_deps_stack);
                  repl_curmod = (uu___50_7553.repl_curmod);
                  repl_env = (uu___50_7553.repl_env);
                  repl_stdin = (uu___50_7553.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____7561 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____7561)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let uu____7584 = nothing_left_to_pop st  in
      if uu____7584
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
              let uu____7692 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____7692  in
            let lid1 =
              let uu____7698 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____7698  in
            let uu____7703 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____7703
              (FStar_Util.map_option
                 (fun uu____7760  ->
                    match uu____7760 with
                    | ((uu____7780,typ),r) -> ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____7802 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____7802
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____7868 = FStar_TypeChecker_Env.lookup_qname tcenv lid  in
            FStar_Util.bind_opt uu____7868
              (fun uu___29_7913  ->
                 match uu___29_7913 with
                 | (FStar_Util.Inr (se,uu____7936),uu____7937) ->
                     let uu____7966 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____7966
                 | uu____7969 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____8027  ->
                 match uu____8027 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____8086 -> info_at_pos_opt
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
                    let uu____8243 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____8243
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____8260 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____8278 -> FStar_Pervasives_Native.None  in
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
                let uu____8296 =
                  let uu____8309 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____8309)  in
                FStar_Pervasives_Native.Some uu____8296
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
    let uu____8444 = trim_option_name opt_name  in
    match uu____8444 with
    | (uu____8468,trimmed_name) ->
        let uu____8474 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____8474 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____8509 =
               let uu____8522 =
                 let uu____8530 = update_option opt  in
                 alist_of_fstar_option uu____8530  in
               ("option", uu____8522)  in
             FStar_Util.Inr uu____8509)
  
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
      let uu____8588 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____8588 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____8623 =
            let uu____8636 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____8636)  in
          FStar_Util.Inr uu____8623
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____8667 =
            let uu____8680 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____8680)  in
          FStar_Util.Inr uu____8667
  
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
          let uu____8778 = run_symbol_lookup st symbol pos_opt requested_info
             in
          match uu____8778 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____8852 ->
              let uu____8867 = run_module_lookup st symbol  in
              (match uu____8867 with
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
  'Auu____9073 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string * Prims.int * Prims.int)
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____9073)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____9141 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____9141 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____9245 .
    ('Auu____9245 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____9245 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___30_9260  ->
    match uu___30_9260 with
    | (uu____9265,FStar_Interactive_CompletionTable.Namespace uu____9266) ->
        FStar_Pervasives_Native.None
    | (uu____9271,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____9272;
         FStar_Interactive_CompletionTable.mod_path = uu____9273;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____9283 =
          let uu____9288 =
            let uu____9289 =
              let uu___51_9290 = md  in
              let uu____9291 =
                let uu____9293 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.op_Hat uu____9293 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____9291;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___51_9290.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___51_9290.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____9289  in
          (pth, uu____9288)  in
        FStar_Pervasives_Native.Some uu____9283
  
let run_code_autocomplete :
  'Auu____9307 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____9307)
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
  'Auu____9369 'Auu____9370 'Auu____9371 .
    repl_state ->
      Prims.string ->
        'Auu____9369 ->
          'Auu____9370 ->
            ((query_status * FStar_Util.json) * (repl_state,'Auu____9371)
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
              (fun _0_14  -> FStar_Pervasives_Native.Some _0_14)
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
        let uu____9451 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____9451 with
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
  'Auu____9514 'Auu____9515 .
    'Auu____9514 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____9514,'Auu____9515)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____9547 = trim_option_name search_term  in
        match uu____9547 with
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
        | (uu____9609,uu____9610) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____9633 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____9633)
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
  'Auu____9684 'Auu____9685 .
    repl_state ->
      'Auu____9684 ->
        (repl_state -> 'Auu____9684) ->
          ('Auu____9684 * (repl_state,'Auu____9685) FStar_Util.either)
  =
  fun st  ->
    fun sigint_default  ->
      fun task  ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st  in
        let results =
          try
            (fun uu___53_9726  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____9737  ->
                        let uu____9738 = task st1  in
                        FStar_All.pipe_left
                          (fun _0_15  -> FStar_Util.Inl _0_15) uu____9738))
              ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = pop_repl "run_and_rewind" st1  in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'Auu____9791 'Auu____9792 'Auu____9793 .
    repl_state ->
      Prims.string ->
        'Auu____9791 ->
          'Auu____9792 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____9793)
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
                    ((uu____9894,{ FStar_Syntax_Syntax.lbname = uu____9895;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____9897;
                                   FStar_Syntax_Syntax.lbeff = uu____9898;
                                   FStar_Syntax_Syntax.lbdef = def;
                                   FStar_Syntax_Syntax.lbattrs = uu____9900;
                                   FStar_Syntax_Syntax.lbpos = uu____9901;_}::[]),uu____9902);
                  FStar_Syntax_Syntax.sigrng = uu____9903;
                  FStar_Syntax_Syntax.sigquals = uu____9904;
                  FStar_Syntax_Syntax.sigmeta = uu____9905;
                  FStar_Syntax_Syntax.sigattrs = uu____9906;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____9945 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____9966 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____9966 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____9972) ->
                  FStar_Pervasives_Native.Some decls
              | uu____9993 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____10011 =
                let uu____10016 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____10016 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____10011  in
            let typecheck tcenv decls =
              let uu____10040 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____10040 with | (ses,uu____10054,uu____10055) -> ses
               in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____10076 = parse1 frag  in
                 match uu____10076 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____10102 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1,def) ->
                           let uu____10138 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def  in
                           (match uu____10138 with
                            | (univs2,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____10150 = FStar_Options.trace_error ()  in
                     if uu____10150
                     then aux ()
                     else
                       (try
                          (fun uu___55_10164  -> match () with | () -> aux ())
                            ()
                        with
                        | uu___54_10173 ->
                            let uu____10178 =
                              FStar_Errors.issue_of_exn uu___54_10173  in
                            (match uu____10178 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____10186 =
                                   let uu____10187 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____10187  in
                                 (QueryNOK, uu____10186)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___54_10173)))
  
let run_compute :
  'Auu____10202 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____10202)
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
               let uu____10280 =
                 let uu____10281 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____10281  in
               (QueryOK, uu____10280))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____10316 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____10339 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___31_10375  ->
    match uu___31_10375 with
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
    let uu____10597 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____10604 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____10597; sc_fvars = uu____10604 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____10672 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____10672 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____10700 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____10700 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____10719,typ),uu____10721) ->
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
      let uu____10771 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____10771 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____10815 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____10815  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____10859 = sc_typ tcenv sc  in
        term_to_string tcenv uu____10859  in
      let uu____10860 =
        let uu____10868 =
          let uu____10874 =
            let uu____10875 =
              let uu____10877 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____10877.FStar_Ident.str  in
            FStar_Util.JsonStr uu____10875  in
          ("lid", uu____10874)  in
        [uu____10868; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____10860
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____10910 -> true
    | uu____10913 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____10924 -> uu____10924
  
let run_search :
  'Auu____10933 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____10933)
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
              let uu____10980 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____10980
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
              let uu____11039 =
                let uu____11040 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____11040  in
              FStar_Exn.raise uu____11039
            else
              if beg_quote
              then
                (let uu____11046 = strip_quotes term1  in
                 NameContainsStr uu____11046)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____11051 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____11051 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____11054 =
                       let uu____11055 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____11055  in
                     FStar_Exn.raise uu____11054
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____11083 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____11083  in
      let results =
        try
          (fun uu___57_11117  ->
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
                        let uu____11165 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____11165  in
                      let uu____11171 =
                        let uu____11172 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____11172  in
                      FStar_Exn.raise uu____11171
                  | uu____11179 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = SyntaxCheck ; push_code = uu____11310;
            push_line = uu____11311; push_column = uu____11312;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____11318 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____11320 -> q)
  
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
      let uu____11393 = validate_and_run_query st query  in
      match uu____11393 with
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
      let uu____11459 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____11459
  
let (js_repl_eval_str :
  repl_state ->
    Prims.string -> (Prims.string * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____11483 =
        let uu____11493 = parse_interactive_query query_str  in
        js_repl_eval st uu____11493  in
      match uu____11483 with
      | (js_response,st_opt) ->
          let uu____11516 = FStar_Util.string_of_json js_response  in
          (uu____11516, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____11529  ->
    let uu____11530 = FStar_Options.parse_cmd_line ()  in
    match uu____11530 with
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
              | h::uu____11553::uu____11554 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____11563 -> ()))
  
let rec (go : repl_state -> Prims.int) =
  fun st  ->
    let query = read_interactive_query st.repl_stdin  in
    let uu____11576 = validate_and_run_query st query  in
    match uu____11576 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____11629 =
      let uu____11632 = FStar_ST.op_Bang issues  in e :: uu____11632  in
    FStar_ST.op_Colon_Equals issues uu____11629  in
  let count_errors uu____11730 =
    let uu____11731 =
      let uu____11734 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____11734
       in
    FStar_List.length uu____11731  in
  let report uu____11791 =
    let uu____11792 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____11792  in
  let clear1 uu____11845 = FStar_ST.op_Colon_Equals issues []  in
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
               let uu____11932 = get_json ()  in
               forward_message printer label uu____11932)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____11946 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  let uu____11949 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  FStar_Range.mk_range "<input>" uu____11946 uu____11949 
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____11963 = FStar_Util.open_stdin ()  in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____11963;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' : 'Auu____11979 . repl_state -> 'Auu____11979 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____11988 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____11988
       then
         let uu____11992 =
           let uu____11994 = FStar_Options.file_list ()  in
           FStar_List.hd uu____11994  in
         FStar_SMTEncoding_Solver.with_hints_db uu____11992
           (fun uu____12001  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____12015 =
       let uu____12017 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____12017  in
     if uu____12015
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____12026 = FStar_Options.trace_error ()  in
     if uu____12026
     then interactive_mode' init1
     else
       (try
          (fun uu___59_12032  ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___58_12035 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___58_12035)))
  
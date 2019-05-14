open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
let (snapshot_env :
  FStar_TypeChecker_Env.env ->
    Prims.string -> (repl_depth_t * FStar_TypeChecker_Env.env_t))
  =
  fun env  ->
    fun msg  ->
      let uu____276 = FStar_TypeChecker_Tc.snapshot_context env msg  in
      match uu____276 with
      | (ctx_depth,env1) ->
          let uu____536 = FStar_Options.snapshot ()  in
          (match uu____536 with
           | (opt_depth,()) -> ((ctx_depth, opt_depth), env1))
  
let (rollback_env :
  FStar_TypeChecker_Env.solver_t ->
    Prims.string ->
      ((Prims.int * Prims.int * FStar_TypeChecker_Env.solver_depth_t *
        Prims.int) * Prims.int) -> FStar_TypeChecker_Env.env)
  =
  fun solver1  ->
    fun msg  ->
      fun uu____755  ->
        match uu____755 with
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
    match projectee with | SyntaxCheck  -> true | uu____995 -> false
  
let (uu___is_LaxCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____1006 -> false
  
let (uu___is_FullCheck : push_kind -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____1017 -> false
  
let (set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env) =
  fun env  ->
    fun check_kind  ->
      let uu___32_1192 = env  in
      let uu____1301 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___32_1192.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___32_1192.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___32_1192.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___32_1192.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_sig =
          (uu___32_1192.FStar_TypeChecker_Env.gamma_sig);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___32_1192.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___32_1192.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___32_1192.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___32_1192.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.attrtab =
          (uu___32_1192.FStar_TypeChecker_Env.attrtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___32_1192.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___32_1192.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___32_1192.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___32_1192.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___32_1192.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___32_1192.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___32_1192.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___32_1192.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___32_1192.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___32_1192.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___32_1192.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.phase1 =
          (uu___32_1192.FStar_TypeChecker_Env.phase1);
        FStar_TypeChecker_Env.failhard =
          (uu___32_1192.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___32_1192.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.uvar_subtyping =
          (uu___32_1192.FStar_TypeChecker_Env.uvar_subtyping);
        FStar_TypeChecker_Env.tc_term =
          (uu___32_1192.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___32_1192.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___32_1192.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___32_1192.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___32_1192.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___32_1192.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___32_1192.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.fv_delta_depths =
          (uu___32_1192.FStar_TypeChecker_Env.fv_delta_depths);
        FStar_TypeChecker_Env.proof_ns =
          (uu___32_1192.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___32_1192.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___32_1192.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.postprocess =
          (uu___32_1192.FStar_TypeChecker_Env.postprocess);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___32_1192.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___32_1192.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___32_1192.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____1301;
        FStar_TypeChecker_Env.nbe = (uu___32_1192.FStar_TypeChecker_Env.nbe)
      }
  
let with_captured_errors' :
  'Auu____1311 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____1311 FStar_Pervasives_Native.option)
          -> 'Auu____1311 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        try
          (fun uu___38_1557  ->
             match () with
             | () ->
                 FStar_Util.with_sigint_handler sigint_handler
                   (fun uu____1563  -> f env)) ()
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
            ((let uu____1581 = FStar_TypeChecker_Env.get_range env  in
              FStar_Errors.log_issue uu____1581
                (FStar_Errors.Error_IDEAssertionFailure, msg1));
             FStar_Pervasives_Native.None)
        | FStar_Util.SigInt  ->
            (FStar_Util.print_string "Interrupted";
             FStar_Pervasives_Native.None)
        | FStar_Errors.Error (e,msg,r) ->
            (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
             FStar_Pervasives_Native.None)
        | FStar_Errors.Err (e,msg) ->
            ((let uu____1611 =
                let uu____1621 =
                  let uu____1629 = FStar_TypeChecker_Env.get_range env  in
                  (e, msg, uu____1629)  in
                [uu____1621]  in
              FStar_TypeChecker_Err.add_errors env uu____1611);
             FStar_Pervasives_Native.None)
        | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____1654 .
    FStar_TypeChecker_Env.env ->
      FStar_Util.sigint_handler ->
        (FStar_TypeChecker_Env.env ->
           'Auu____1654 FStar_Pervasives_Native.option)
          -> 'Auu____1654 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun sigint_handler  ->
      fun f  ->
        let uu____1897 = FStar_Options.trace_error ()  in
        if uu____1897
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
    let uu____1960 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____1960 }
  
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu____1983  ->
    match uu____1983 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____1995 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____1995)
  
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
    match projectee with | LDInterleaved _0 -> true | uu____2238 -> false
  
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____2283 -> false
  
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____2314 -> false
  
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____2346 -> false
  
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee  -> match projectee with | PushFragment _0 -> _0 
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee  ->
    match projectee with | Noop  -> true | uu____2379 -> false
  
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
      let uu____3772 = FStar_ST.op_Bang repl_stack  in
      match uu____3772 with
      | [] -> failwith "Too many pops"
      | (depth,(uu____3826,st'))::stack_tl ->
          let env =
            rollback_env (st.repl_env).FStar_TypeChecker_Env.solver msg depth
             in
          (FStar_ST.op_Colon_Equals repl_stack stack_tl;
           (let uu____4021 = FStar_Util.physical_equality env st'.repl_env
               in
            FStar_Common.runtime_assert uu____4021 "Inconsistent stack state");
           st')
  
let (push_repl :
  Prims.string -> push_kind -> repl_task -> repl_state -> repl_state) =
  fun msg  ->
    fun push_kind  ->
      fun task  ->
        fun st  ->
          let uu____4125 = snapshot_env st.repl_env msg  in
          match uu____4125 with
          | (depth,env) ->
              ((let uu____4303 =
                  let uu____4304 = FStar_ST.op_Bang repl_stack  in
                  (depth, (task, st)) :: uu____4304  in
                FStar_ST.op_Colon_Equals repl_stack uu____4303);
               (let uu___141_4397 = st  in
                let uu____4414 = set_check_kind env push_kind  in
                {
                  repl_line = (uu___141_4397.repl_line);
                  repl_column = (uu___141_4397.repl_column);
                  repl_fname = (uu___141_4397.repl_fname);
                  repl_deps_stack = (uu___141_4397.repl_deps_stack);
                  repl_curmod = (uu___141_4397.repl_curmod);
                  repl_env = uu____4414;
                  repl_stdin = (uu___141_4397.repl_stdin);
                  repl_names = (uu___141_4397.repl_names)
                }))
  
let (nothing_left_to_pop : repl_state -> Prims.bool) =
  fun st  ->
    let uu____4546 =
      let uu____4547 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____4547  in
    uu____4546 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid) 
  | NTOpen of (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace)
  
  | NTInclude of (FStar_Ident.lid * FStar_Ident.lid) 
  | NTBinding of
  (FStar_Syntax_Syntax.binding,FStar_TypeChecker_Env.sig_binding)
  FStar_Util.either 
let (uu___is_NTAlias : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____4703 -> false
  
let (__proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Ident.ident * FStar_Ident.lid))
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let (uu___is_NTOpen : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____4778 -> false
  
let (__proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid * FStar_Syntax_DsEnv.open_module_or_namespace))
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let (uu___is_NTInclude : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____4833 -> false
  
let (__proj__NTInclude__item___0 :
  name_tracking_event -> (FStar_Ident.lid * FStar_Ident.lid)) =
  fun projectee  -> match projectee with | NTInclude _0 -> _0 
let (uu___is_NTBinding : name_tracking_event -> Prims.bool) =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____4892 -> false
  
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
              let uu____5008 = FStar_Ident.text_of_id id1  in
              let uu____5010 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                uu____5008 [] uu____5010
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____5034 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____5034
            else table
        | NTInclude (host,included) ->
            let uu____5056 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____5061 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____5056 uu____5061
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_Util.Inl (FStar_Syntax_Syntax.Binding_lid
                  (lid,uu____5081)) -> [lid]
              | FStar_Util.Inr (lids,uu____5127) -> lids
              | uu____5150 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   let uu____5179 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____5179 lid) table lids
  
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
              let uu____5250 = FStar_Syntax_Syntax.mod_name md  in
              uu____5250.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let (commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state) =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___201_5308 = st  in
      {
        repl_line = (uu___201_5308.repl_line);
        repl_column = (uu___201_5308.repl_column);
        repl_fname = (uu___201_5308.repl_fname);
        repl_deps_stack = (uu___201_5308.repl_deps_stack);
        repl_curmod = (uu___201_5308.repl_curmod);
        repl_env = (uu___201_5308.repl_env);
        repl_stdin = (uu___201_5308.repl_stdin);
        repl_names = names1
      }
  
let (fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref *
      FStar_Syntax_DsEnv.dsenv_hooks * FStar_TypeChecker_Env.tcenv_hooks))
  =
  fun uu____5348  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____5362 =
        let uu____5365 = FStar_ST.op_Bang events  in evt :: uu____5365  in
      FStar_ST.op_Colon_Equals events uu____5362  in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1  ->
             fun op  ->
               let uu____5434 =
                 let uu____5435 =
                   let uu____5444 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____5444, op)  in
                 NTOpen uu____5435  in
               push_event uu____5434);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1  ->
             fun ns  ->
               let uu____5466 =
                 let uu____5467 =
                   let uu____5480 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____5480, ns)  in
                 NTInclude uu____5467  in
               push_event uu____5466);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1  ->
             fun x  ->
               fun l  ->
                 let uu____5510 =
                   let uu____5511 =
                     let uu____5528 =
                       FStar_Syntax_DsEnv.current_module dsenv1  in
                     (uu____5528, x, l)  in
                   NTAlias uu____5511  in
                 push_event uu____5510)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____5551  -> fun s  -> push_event (NTBinding s))
      })
  
let (track_name_changes :
  env_t -> (env_t * (env_t -> (env_t * name_tracking_event Prims.list)))) =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____6269 =
        FStar_Universal.with_dsenv_of_tcenv env1
          (fun dsenv1  ->
             let uu____6331 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks
                in
             ((), uu____6331))
         in
      match uu____6269 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____6495 =
      let uu____6508 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____6519 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____6508, uu____6519)  in
    match uu____6495 with
    | (old_dshooks,old_tchooks) ->
        let uu____6727 = fresh_name_tracking_hooks ()  in
        (match uu____6727 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____6948 = set_hooks new_dshooks new_tchooks env  in
             (uu____6948,
               ((fun env1  ->
                   let uu____7286 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____7395 =
                     let uu____7398 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____7398  in
                   (uu____7286, uu____7395)))))
  
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___0_7486  ->
    match uu___0_7486 with
    | LDInterleaved (intf,impl) ->
        let uu____7498 = string_of_timed_fname intf  in
        let uu____7500 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____7498 uu____7500
    | LDSingle intf_or_impl ->
        let uu____7506 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____7506
    | LDInterfaceOfCurrentFile intf ->
        let uu____7512 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____7512
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
        let uu____7707 =
          let uu____7779 =
            let uu____7780 =
              let uu____7786 = FStar_TypeChecker_Env.dep_graph env  in
              FStar_Parser_Dep.parsing_data_of uu____7786  in
            FStar_All.pipe_right modf uu____7780  in
          FStar_Universal.tc_one_file_for_ide env intf_opt modf uu____7779
           in
        match uu____7707 with | (uu____7842,env1) -> env1
  
let (run_repl_task : optmod_t -> env_t -> repl_task -> (optmod_t * env_t)) =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____8228 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____8228)
        | LDSingle intf_or_impl ->
            let uu____8395 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____8395)
        | LDInterfaceOfCurrentFile intf ->
            let uu____8562 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____8562)
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
            let uu____8853 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____8853
        | intf_or_impl::deps' ->
            let uu____8867 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____8867
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
      let uu____8921 = get_mod_name f  in uu____8921 = our_mod_name  in
    let uu____8924 =
      FStar_Dependencies.find_deps_if_needed [filename]
        FStar_CheckedFiles.load_parsing_data_from_cache
       in
    match uu____8924 with
    | (deps,dep_graph1) ->
        let uu____8953 = FStar_List.partition has_our_mod_name deps  in
        (match uu____8953 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____9003 =
                       let uu____9005 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____9005  in
                     if uu____9003
                     then
                       let uu____9008 =
                         let uu____9014 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____9014)
                          in
                       FStar_Errors.raise_err uu____9008
                     else ());
                    (let uu____9021 =
                       let uu____9023 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____9023  in
                     if uu____9021
                     then
                       let uu____9026 =
                         let uu____9032 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____9032)
                          in
                       FStar_Errors.raise_err uu____9026
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____9042 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____9053 =
                       let uu____9059 =
                         FStar_Util.format message [our_mod_name; mods_str]
                          in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____9059)
                        in
                     FStar_Errors.raise_err uu____9053);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let (update_task_timestamps : repl_task -> repl_task) =
  fun uu___1_9078  ->
    match uu___1_9078 with
    | LDInterleaved (intf,impl) ->
        let uu____9089 =
          let uu____9098 = tf_of_fname intf.tf_fname  in
          let uu____9103 = tf_of_fname impl.tf_fname  in
          (uu____9098, uu____9103)  in
        LDInterleaved uu____9089
    | LDSingle intf_or_impl ->
        let uu____9115 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____9115
    | LDInterfaceOfCurrentFile intf ->
        let uu____9123 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____9123
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
          let uu____9199 = track_name_changes st1.repl_env  in
          match uu____9199 with
          | (env,finish_name_tracking) ->
              let check_success uu____9738 =
                (let uu____9741 = FStar_Errors.get_err_count ()  in
                 uu____9741 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____9745 =
                let uu____9807 =
                  with_captured_errors env FStar_Util.sigint_raise
                    (fun env1  ->
                       let uu____9983 =
                         run_repl_task st1.repl_curmod env1 task  in
                       FStar_All.pipe_left
                         (fun _10218  -> FStar_Pervasives_Native.Some _10218)
                         uu____9983)
                   in
                match uu____9807 with
                | FStar_Pervasives_Native.Some (curmod,env1) when
                    check_success () -> (curmod, env1, true)
                | uu____10504 -> ((st1.repl_curmod), env, false)  in
              (match uu____9745 with
               | (curmod,env1,success) ->
                   let uu____10747 = finish_name_tracking env1  in
                   (match uu____10747 with
                    | (env2,name_events) ->
                        let st2 =
                          if success
                          then
                            let st2 =
                              let uu___341_10978 = st1  in
                              {
                                repl_line = (uu___341_10978.repl_line);
                                repl_column = (uu___341_10978.repl_column);
                                repl_fname = (uu___341_10978.repl_fname);
                                repl_deps_stack =
                                  (uu___341_10978.repl_deps_stack);
                                repl_curmod = curmod;
                                repl_env = env2;
                                repl_stdin = (uu___341_10978.repl_stdin);
                                repl_names = (uu___341_10978.repl_names)
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
          let uu____11081 = FStar_Options.debug_any ()  in
          if uu____11081
          then
            let uu____11084 = string_of_repl_task task  in
            FStar_Util.print2 "%s %s" verb uu____11084
          else ()  in
        let rec revert_many st1 uu___2_11133 =
          match uu___2_11133 with
          | [] -> st1
          | (_id,(task,_st'))::entries ->
              (debug1 "Reverting" task;
               (let st' = pop_repl "run_repl_ls_transactions" st1  in
                let dep_graph1 = FStar_TypeChecker_Env.dep_graph st1.repl_env
                   in
                let st'1 =
                  let uu___367_11290 = st'  in
                  let uu____11307 =
                    FStar_TypeChecker_Env.set_dep_graph st'.repl_env
                      dep_graph1
                     in
                  {
                    repl_line = (uu___367_11290.repl_line);
                    repl_column = (uu___367_11290.repl_column);
                    repl_fname = (uu___367_11290.repl_fname);
                    repl_deps_stack = (uu___367_11290.repl_deps_stack);
                    repl_curmod = (uu___367_11290.repl_curmod);
                    repl_env = uu____11307;
                    repl_stdin = (uu___367_11290.repl_stdin);
                    repl_names = (uu___367_11290.repl_names)
                  }  in
                revert_many st'1 entries))
           in
        let rec aux st1 tasks1 previous =
          match (tasks1, previous) with
          | ([],[]) -> FStar_Util.Inl st1
          | (task::tasks2,[]) ->
              (debug1 "Loading" task;
               progress_callback task;
               (let uu____11532 =
                  FStar_Options.restore_cmd_line_options false  in
                FStar_All.pipe_right uu____11532 (fun a1  -> ()));
               (let timestamped_task = update_task_timestamps task  in
                let push_kind =
                  let uu____11536 = FStar_Options.lax ()  in
                  if uu____11536 then LaxCheck else FullCheck  in
                let uu____11541 =
                  run_repl_transaction st1 push_kind false timestamped_task
                   in
                match uu____11541 with
                | (success,st2) ->
                    if success
                    then
                      let uu____11617 =
                        let uu___392_11634 = st2  in
                        let uu____11651 = FStar_ST.op_Bang repl_stack  in
                        {
                          repl_line = (uu___392_11634.repl_line);
                          repl_column = (uu___392_11634.repl_column);
                          repl_fname = (uu___392_11634.repl_fname);
                          repl_deps_stack = uu____11651;
                          repl_curmod = (uu___392_11634.repl_curmod);
                          repl_env = (uu___392_11634.repl_env);
                          repl_stdin = (uu___392_11634.repl_stdin);
                          repl_names = (uu___392_11634.repl_names)
                        }  in
                      aux uu____11617 tasks2 []
                    else FStar_Util.Inr st2))
          | (task::tasks2,prev::previous1) when
              let uu____11719 = update_task_timestamps task  in
              (FStar_Pervasives_Native.fst (FStar_Pervasives_Native.snd prev))
                = uu____11719
              -> (debug1 "Skipping" task; aux st1 tasks2 previous1)
          | (tasks2,previous1) ->
              let uu____11752 = revert_many st1 previous1  in
              aux uu____11752 tasks2 []
           in
        aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___3_11791  ->
    match uu___3_11791 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____11805 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____11805
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____11811 -> "list (...)"
    | FStar_Util.JsonAssoc uu____11815 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____11841 -> true
    | uu____11848 -> false
  
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____11866 -> uu____11866
  
let js_fail :
  'Auu____11879 . Prims.string -> FStar_Util.json -> 'Auu____11879 =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___4_11899  ->
    match uu___4_11899 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___5_11912  ->
    match uu___5_11912 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____11926 .
    (FStar_Util.json -> 'Auu____11926) ->
      FStar_Util.json -> 'Auu____11926 Prims.list
  =
  fun k  ->
    fun uu___6_11941  ->
      match uu___6_11941 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___7_11963  ->
    match uu___7_11963 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let (js_pushkind : FStar_Util.json -> push_kind) =
  fun s  ->
    let uu____11994 = js_str s  in
    match uu____11994 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____11999 -> js_fail "push_kind" s
  
let (js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Env.step) =
  fun s  ->
    let uu____12008 = js_str s  in
    match uu____12008 with
    | "beta" -> FStar_TypeChecker_Env.Beta
    | "delta" ->
        FStar_TypeChecker_Env.UnfoldUntil FStar_Syntax_Syntax.delta_constant
    | "iota" -> FStar_TypeChecker_Env.Iota
    | "zeta" -> FStar_TypeChecker_Env.Zeta
    | "reify" -> FStar_TypeChecker_Env.Reify
    | "pure-subterms" -> FStar_TypeChecker_Env.PureSubtermsWithinComputations
    | uu____12016 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool * Prims.bool) 
let (uu___is_CKCode : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____12045 -> false
  
let (uu___is_CKOption : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____12058 -> false
  
let (__proj__CKOption__item___0 : completion_context -> Prims.bool) =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let (uu___is_CKModuleOrNamespace : completion_context -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____12086 -> false
  
let (__proj__CKModuleOrNamespace__item___0 :
  completion_context -> (Prims.bool * Prims.bool)) =
  fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let (js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____12124 = js_str k1  in
        (match uu____12124 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____12152 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____12164 -> false
  
let (uu___is_LKModule : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____12175 -> false
  
let (uu___is_LKOption : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____12186 -> false
  
let (uu___is_LKCode : lookup_context -> Prims.bool) =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____12197 -> false
  
let (js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context) =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____12210 = js_str k1  in
        (match uu____12210 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____12220 ->
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
    match projectee with | Exit  -> true | uu____12348 -> false
  
let (uu___is_DescribeProtocol : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____12359 -> false
  
let (uu___is_DescribeRepl : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____12370 -> false
  
let (uu___is_Segment : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____12383 -> false
  
let (__proj__Segment__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let (uu___is_Pop : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pop  -> true | uu____12404 -> false
  
let (uu___is_Push : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____12421 -> false
  
let (__proj__Push__item___0 : query' -> push_query) =
  fun projectee  -> match projectee with | Push _0 -> _0 
let (uu___is_VfsAdd : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____12473 -> false
  
let (__proj__VfsAdd__item___0 :
  query' -> (Prims.string FStar_Pervasives_Native.option * Prims.string)) =
  fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let (uu___is_AutoComplete : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____12521 -> false
  
let (__proj__AutoComplete__item___0 :
  query' -> (Prims.string * completion_context)) =
  fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let (uu___is_Lookup : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____12569 -> false
  
let (__proj__Lookup__item___0 :
  query' ->
    (Prims.string * lookup_context * position FStar_Pervasives_Native.option
      * Prims.string Prims.list))
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let (uu___is_Compute : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____12639 -> false
  
let (__proj__Compute__item___0 :
  query' ->
    (Prims.string * FStar_TypeChecker_Env.step Prims.list
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let (uu___is_Search : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____12686 -> false
  
let (__proj__Search__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | Search _0 -> _0 
let (uu___is_GenericError : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____12709 -> false
  
let (__proj__GenericError__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let (uu___is_ProtocolViolation : query' -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ProtocolViolation _0 -> true
    | uu____12732 -> false
  
let (__proj__ProtocolViolation__item___0 : query' -> Prims.string) =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let (__proj__Mkquery__item__qq : query -> query') =
  fun projectee  -> match projectee with | { qq; qid;_} -> qq 
let (__proj__Mkquery__item__qid : query -> Prims.string) =
  fun projectee  -> match projectee with | { qq; qid;_} -> qid 
let (query_needs_current_module : query' -> Prims.bool) =
  fun uu___8_12778  ->
    match uu___8_12778 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____12783 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____12787; push_code = uu____12788;
          push_line = uu____12789; push_column = uu____12790;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____12796 -> false
    | GenericError uu____12806 -> false
    | ProtocolViolation uu____12809 -> false
    | Push uu____12812 -> true
    | AutoComplete uu____12819 -> true
    | Lookup uu____12826 -> true
    | Compute uu____12842 -> true
    | Search uu____12853 -> true
  
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
    | InvalidQuery uu____12919 -> true
    | uu____12922 -> false
  
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidQuery uu____12932 -> uu____12932
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol 
let (uu___is_QueryOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____12943 -> false
  
let (uu___is_QueryNOK : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____12954 -> false
  
let (uu___is_QueryViolatesProtocol : query_status -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____12965 -> false
  
let try_assoc :
  'Auu____12976 'Auu____12977 .
    'Auu____12976 ->
      ('Auu____12976 * 'Auu____12977) Prims.list ->
        'Auu____12977 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____13002 =
        FStar_Util.try_find
          (fun uu____13016  ->
             match uu____13016 with | (k,uu____13023) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____13002
  
let (wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query) =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____13050 =
          let uu____13051 =
            let uu____13053 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____13053
             in
          ProtocolViolation uu____13051  in
        { qq = uu____13050; qid }
  
let (unpack_interactive_query : FStar_Util.json -> query) =
  fun json  ->
    let assoc1 errloc key a =
      let uu____13098 = try_assoc key a  in
      match uu____13098 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____13103 =
            let uu____13104 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____13104  in
          FStar_Exn.raise uu____13103
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____13124 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____13124 js_str  in
    try
      (fun uu___544_13136  ->
         match () with
         | () ->
             let query =
               let uu____13141 = assoc1 "query" "query" request  in
               FStar_All.pipe_right uu____13141 js_str  in
             let args =
               let uu____13153 = assoc1 "query" "args" request  in
               FStar_All.pipe_right uu____13153 js_assoc  in
             let arg k = assoc1 "[args]" k args  in
             let try_arg k =
               let uu____13182 = try_assoc k args  in
               match uu____13182 with
               | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
                   FStar_Pervasives_Native.None
               | other -> other  in
             let uu____13191 =
               match query with
               | "exit" -> Exit
               | "pop" -> Pop
               | "describe-protocol" -> DescribeProtocol
               | "describe-repl" -> DescribeRepl
               | "segment" ->
                   let uu____13197 =
                     let uu____13199 = arg "code"  in
                     FStar_All.pipe_right uu____13199 js_str  in
                   Segment uu____13197
               | "peek" ->
                   let uu____13203 =
                     let uu____13214 =
                       let uu____13215 = arg "kind"  in
                       FStar_All.pipe_right uu____13215 js_pushkind  in
                     let uu____13217 =
                       let uu____13219 = arg "code"  in
                       FStar_All.pipe_right uu____13219 js_str  in
                     let uu____13222 =
                       let uu____13224 = arg "line"  in
                       FStar_All.pipe_right uu____13224 js_int  in
                     let uu____13227 =
                       let uu____13229 = arg "column"  in
                       FStar_All.pipe_right uu____13229 js_int  in
                     {
                       push_kind = uu____13214;
                       push_code = uu____13217;
                       push_line = uu____13222;
                       push_column = uu____13227;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____13203
               | "push" ->
                   let uu____13235 =
                     let uu____13246 =
                       let uu____13247 = arg "kind"  in
                       FStar_All.pipe_right uu____13247 js_pushkind  in
                     let uu____13249 =
                       let uu____13251 = arg "code"  in
                       FStar_All.pipe_right uu____13251 js_str  in
                     let uu____13254 =
                       let uu____13256 = arg "line"  in
                       FStar_All.pipe_right uu____13256 js_int  in
                     let uu____13259 =
                       let uu____13261 = arg "column"  in
                       FStar_All.pipe_right uu____13261 js_int  in
                     {
                       push_kind = uu____13246;
                       push_code = uu____13249;
                       push_line = uu____13254;
                       push_column = uu____13259;
                       push_peek_only = (query = "peek")
                     }  in
                   Push uu____13235
               | "autocomplete" ->
                   let uu____13267 =
                     let uu____13273 =
                       let uu____13275 = arg "partial-symbol"  in
                       FStar_All.pipe_right uu____13275 js_str  in
                     let uu____13278 =
                       let uu____13279 = try_arg "context"  in
                       FStar_All.pipe_right uu____13279
                         js_optional_completion_context
                        in
                     (uu____13273, uu____13278)  in
                   AutoComplete uu____13267
               | "lookup" ->
                   let uu____13287 =
                     let uu____13302 =
                       let uu____13304 = arg "symbol"  in
                       FStar_All.pipe_right uu____13304 js_str  in
                     let uu____13307 =
                       let uu____13308 = try_arg "context"  in
                       FStar_All.pipe_right uu____13308
                         js_optional_lookup_context
                        in
                     let uu____13314 =
                       let uu____13317 =
                         let uu____13327 = try_arg "location"  in
                         FStar_All.pipe_right uu____13327
                           (FStar_Util.map_option js_assoc)
                          in
                       FStar_All.pipe_right uu____13317
                         (FStar_Util.map_option
                            (fun loc  ->
                               let uu____13388 =
                                 let uu____13390 =
                                   assoc1 "[location]" "filename" loc  in
                                 FStar_All.pipe_right uu____13390 js_str  in
                               let uu____13394 =
                                 let uu____13396 =
                                   assoc1 "[location]" "line" loc  in
                                 FStar_All.pipe_right uu____13396 js_int  in
                               let uu____13400 =
                                 let uu____13402 =
                                   assoc1 "[location]" "column" loc  in
                                 FStar_All.pipe_right uu____13402 js_int  in
                               (uu____13388, uu____13394, uu____13400)))
                        in
                     let uu____13409 =
                       let uu____13413 = arg "requested-info"  in
                       FStar_All.pipe_right uu____13413 (js_list js_str)  in
                     (uu____13302, uu____13307, uu____13314, uu____13409)  in
                   Lookup uu____13287
               | "compute" ->
                   let uu____13426 =
                     let uu____13436 =
                       let uu____13438 = arg "term"  in
                       FStar_All.pipe_right uu____13438 js_str  in
                     let uu____13441 =
                       let uu____13446 = try_arg "rules"  in
                       FStar_All.pipe_right uu____13446
                         (FStar_Util.map_option (js_list js_reductionrule))
                        in
                     (uu____13436, uu____13441)  in
                   Compute uu____13426
               | "search" ->
                   let uu____13464 =
                     let uu____13466 = arg "terms"  in
                     FStar_All.pipe_right uu____13466 js_str  in
                   Search uu____13464
               | "vfs-add" ->
                   let uu____13470 =
                     let uu____13479 =
                       let uu____13483 = try_arg "filename"  in
                       FStar_All.pipe_right uu____13483
                         (FStar_Util.map_option js_str)
                        in
                     let uu____13493 =
                       let uu____13495 = arg "contents"  in
                       FStar_All.pipe_right uu____13495 js_str  in
                     (uu____13479, uu____13493)  in
                   VfsAdd uu____13470
               | uu____13502 ->
                   let uu____13504 =
                     FStar_Util.format1 "Unknown query '%s'" query  in
                   ProtocolViolation uu____13504
                in
             { qq = uu____13191; qid }) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let (deserialize_interactive_query : FStar_Util.json -> query) =
  fun js_query  ->
    try
      (fun uu___579_13529  ->
         match () with | () -> unpack_interactive_query js_query) ()
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let (parse_interactive_query : Prims.string -> query) =
  fun query_str  ->
    let uu____13557 = FStar_Util.json_of_string query_str  in
    match uu____13557 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let (read_interactive_query : FStar_Util.stream_reader -> query) =
  fun stream  ->
    let uu____13575 = FStar_Util.read_line stream  in
    match uu____13575 with
    | FStar_Pervasives_Native.None  -> FStar_All.exit (Prims.parse_int "0")
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____13595 .
    ('Auu____13595 -> FStar_Util.json) ->
      'Auu____13595 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____13615 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____13615
  
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
    let uu____13643 =
      let uu____13651 =
        let uu____13659 =
          let uu____13667 =
            let uu____13673 =
              let uu____13674 =
                let uu____13677 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____13683 = FStar_Range.json_of_use_range r  in
                      [uu____13683]
                   in
                let uu____13684 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____13690 = FStar_Range.def_range r  in
                      let uu____13691 = FStar_Range.use_range r  in
                      uu____13690 <> uu____13691 ->
                      let uu____13692 = FStar_Range.json_of_def_range r  in
                      [uu____13692]
                  | uu____13693 -> []  in
                FStar_List.append uu____13677 uu____13684  in
              FStar_Util.JsonList uu____13674  in
            ("ranges", uu____13673)  in
          [uu____13667]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____13659
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____13651
       in
    FStar_Util.JsonAssoc uu____13643
  
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
    let uu____13986 =
      let uu____13994 =
        let uu____14000 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____14000)  in
      let uu____14003 =
        let uu____14011 =
          let uu____14017 =
            json_of_opt (fun _14019  -> FStar_Util.JsonStr _14019) lr.slr_typ
             in
          ("type", uu____14017)  in
        let uu____14022 =
          let uu____14030 =
            let uu____14036 =
              json_of_opt (fun _14038  -> FStar_Util.JsonStr _14038)
                lr.slr_doc
               in
            ("documentation", uu____14036)  in
          let uu____14041 =
            let uu____14049 =
              let uu____14055 =
                json_of_opt (fun _14057  -> FStar_Util.JsonStr _14057)
                  lr.slr_def
                 in
              ("definition", uu____14055)  in
            [uu____14049]  in
          uu____14030 :: uu____14041  in
        uu____14011 :: uu____14022  in
      uu____13994 :: uu____14003  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____13986
  
let (alist_of_protocol_info : (Prims.string * FStar_Util.json) Prims.list) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____14102 =
      FStar_List.map (fun _14106  -> FStar_Util.JsonStr _14106)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _14109  -> FStar_Util.JsonList _14109)
      uu____14102
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly 
let (uu___is_OptSet : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____14138 -> false
  
let (uu___is_OptReset : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____14149 -> false
  
let (uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool) =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____14160 -> false
  
let (string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string) =
  fun uu___9_14168  ->
    match uu___9_14168 with
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
  fun uu___10_14571  ->
    match uu___10_14571 with
    | FStar_Options.Const uu____14573 -> "flag"
    | FStar_Options.IntStr uu____14575 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____14579 -> "path"
    | FStar_Options.SimpleStr uu____14582 -> "string"
    | FStar_Options.EnumStr uu____14585 -> "enum"
    | FStar_Options.OpenEnumStr uu____14590 -> "open enum"
    | FStar_Options.PostProcessed (uu____14600,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____14610,typ) ->
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
        | FStar_Options.Const uu____14682 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____14720,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____14730,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____14738 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____14738
  
let rec (json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json) =
  fun uu___11_14749  ->
    match uu___11_14749 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____14761 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____14761
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let (alist_of_fstar_option :
  fstar_option -> (Prims.string * FStar_Util.json) Prims.list) =
  fun opt  ->
    let uu____14793 =
      let uu____14801 =
        let uu____14809 =
          let uu____14815 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____14815)  in
        let uu____14818 =
          let uu____14826 =
            let uu____14832 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____14832)  in
          let uu____14835 =
            let uu____14843 =
              let uu____14849 =
                json_of_opt (fun _14851  -> FStar_Util.JsonStr _14851)
                  opt.opt_documentation
                 in
              ("documentation", uu____14849)  in
            let uu____14854 =
              let uu____14862 =
                let uu____14868 =
                  let uu____14869 = kind_of_fstar_option_type opt.opt_type
                     in
                  FStar_Util.JsonStr uu____14869  in
                ("type", uu____14868)  in
              [uu____14862;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____14843 :: uu____14854  in
          uu____14826 :: uu____14835  in
        uu____14809 :: uu____14818  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____14801  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____14793
  
let (json_of_fstar_option : fstar_option -> FStar_Util.json) =
  fun opt  ->
    let uu____14941 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____14941
  
let (write_json : FStar_Util.json -> unit) =
  fun json  ->
    (let uu____14956 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____14956);
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
      let uu____15047 =
        let uu____15055 =
          let uu____15063 =
            let uu____15069 =
              let uu____15070 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _15100  -> FStar_Util.JsonStr _15100)
                uu____15070
               in
            ("query-id", uu____15069)  in
          [uu____15063;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____15055  in
      FStar_Util.JsonAssoc uu____15047
  
let forward_message :
  'Auu____15144 .
    (FStar_Util.json -> 'Auu____15144) ->
      Prims.string -> FStar_Util.json -> 'Auu____15144
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____15167 = json_of_message level contents  in
        callback uu____15167
  
let (json_of_hello : FStar_Util.json) =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____15171 =
      FStar_List.map (fun _15175  -> FStar_Util.JsonStr _15175)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____15171  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let (write_hello : unit -> unit) =
  fun uu____15189  -> write_json json_of_hello 
let (sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string) =
  fun name  ->
    fun typ  ->
      let flag = Prims.op_Hat "--" name  in
      let uu____15207 = FStar_Options.desc_of_opt_type typ  in
      match uu____15207 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.op_Hat flag (Prims.op_Hat " " arg_sig)
  
let (fstar_options_list_cache : fstar_option Prims.list) =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____15231 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____15290  ->
            match uu____15290 with
            | (_shortname,name,typ,doc1) ->
                let uu____15322 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____15322
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____15350 = sig_of_fstar_option name typ  in
                        let uu____15352 = snippets_of_fstar_option name typ
                           in
                        let uu____15356 =
                          let uu____15357 = FStar_Options.settable name  in
                          if uu____15357
                          then OptSet
                          else
                            (let uu____15362 = FStar_Options.resettable name
                                in
                             if uu____15362 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____15350;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____15352;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____15356
                        }))))
     in
  FStar_All.pipe_right uu____15231
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
    let uu___768_15513 = opt  in
    let uu____15530 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___768_15513.opt_name);
      opt_sig = (uu___768_15513.opt_sig);
      opt_value = uu____15530;
      opt_default = (uu___768_15513.opt_default);
      opt_type = (uu___768_15513.opt_type);
      opt_snippets = (uu___768_15513.opt_snippets);
      opt_documentation = (uu___768_15513.opt_documentation);
      opt_permission_level = (uu___768_15513.opt_permission_level)
    }
  
let (current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list) =
  fun filter1  ->
    let uu____15570 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____15570
  
let (trim_option_name : Prims.string -> (Prims.string * Prims.string)) =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____15629 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____15629)
    else ("", opt_name)
  
let (json_of_repl_state : repl_state -> FStar_Util.json) =
  fun st  ->
    let filenames uu____15684 =
      match uu____15684 with
      | (uu____15704,(task,uu____15706)) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | uu____15761 -> [])
       in
    let uu____15763 =
      let uu____15771 =
        let uu____15777 =
          let uu____15778 =
            let uu____15781 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _15803  -> FStar_Util.JsonStr _15803)
              uu____15781
             in
          FStar_Util.JsonList uu____15778  in
        ("loaded-dependencies", uu____15777)  in
      let uu____15806 =
        let uu____15814 =
          let uu____15820 =
            let uu____15821 =
              let uu____15824 =
                current_fstar_options (fun uu____15837  -> true)  in
              FStar_List.map json_of_fstar_option uu____15824  in
            FStar_Util.JsonList uu____15821  in
          ("options", uu____15820)  in
        [uu____15814]  in
      uu____15771 :: uu____15806  in
    FStar_Util.JsonAssoc uu____15763
  
let with_printed_effect_args :
  'Auu____15877 . (unit -> 'Auu____15877) -> 'Auu____15877 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____15890  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____16024  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se  ->
    with_printed_effect_args
      (fun uu____16044  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____16052 'Auu____16053 .
    'Auu____16052 ->
      ((query_status * FStar_Util.json) * ('Auu____16053,Prims.int)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
  
let run_describe_protocol :
  'Auu____16090 'Auu____16091 .
    'Auu____16090 ->
      ((query_status * FStar_Util.json) * ('Auu____16090,'Auu____16091)
        FStar_Util.either)
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____16122 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____16122)
        FStar_Util.either)
  =
  fun st  ->
    let uu____16164 =
      let uu____16169 = json_of_repl_state st  in (QueryOK, uu____16169)  in
    (uu____16164, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____16203 'Auu____16204 .
    'Auu____16203 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____16203,'Auu____16204)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____16246 'Auu____16247 .
    'Auu____16246 ->
      Prims.string ->
        ((query_status * FStar_Util.json) * ('Auu____16246,'Auu____16247)
          FStar_Util.either)
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let (collect_errors : unit -> FStar_Errors.issue Prims.list) =
  fun uu____16291  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____16307 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____16307)
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
      let collect_decls uu____16377 =
        let uu____16378 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____16378 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____16399,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____16423,decls,uu____16425)) -> decls
         in
      let uu____16450 =
        with_captured_errors st.repl_env FStar_Util.sigint_ignore
          (fun uu____16469  ->
             let uu____16524 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _16555  -> FStar_Pervasives_Native.Some _16555)
               uu____16524)
         in
      match uu____16450 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____16586 = collect_errors ()  in
            FStar_All.pipe_right uu____16586 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____16660 =
              let uu____16668 =
                let uu____16674 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____16674)  in
              [uu____16668]  in
            FStar_Util.JsonAssoc uu____16660  in
          let js_decls =
            let uu____16688 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _16698  -> FStar_Util.JsonList _16698)
              uu____16688
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____16744 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____16744)
            FStar_Util.either)
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____16837 .
    repl_state ->
      ((query_status * FStar_Util.json) * (repl_state,'Auu____16837)
        FStar_Util.either)
  =
  fun st  ->
    let uu____16879 = nothing_left_to_pop st  in
    if uu____16879
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
      let uu____17022 =
        json_of_message "progress" (FStar_Util.JsonAssoc js_contents)  in
      write_json uu____17022
  
let (write_repl_ld_task_progress : repl_task -> unit) =
  fun task  ->
    match task with
    | LDInterleaved (uu____17030,tf) ->
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
    | uu____17094 -> ()
  
let (load_deps :
  repl_state ->
    ((repl_state * Prims.string Prims.list),repl_state) FStar_Util.either)
  =
  fun st  ->
    let uu____17144 =
      with_captured_errors st.repl_env FStar_Util.sigint_ignore
        (fun _env  ->
           let uu____17226 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _17273  -> FStar_Pervasives_Native.Some _17273) uu____17226)
       in
    match uu____17144 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___866_17376 = st  in
          let uu____17393 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___866_17376.repl_line);
            repl_column = (uu___866_17376.repl_column);
            repl_fname = (uu___866_17376.repl_fname);
            repl_deps_stack = (uu___866_17376.repl_deps_stack);
            repl_curmod = (uu___866_17376.repl_curmod);
            repl_env = uu____17393;
            repl_stdin = (uu___866_17376.repl_stdin);
            repl_names = (uu___866_17376.repl_names)
          }  in
        let uu____17502 =
          run_repl_ld_transactions st1 tasks write_repl_ld_task_progress  in
        (match uu____17502 with
         | FStar_Util.Inr st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inr st2)
         | FStar_Util.Inl st2 ->
             (write_progress FStar_Pervasives_Native.None [];
              FStar_Util.Inl (st2, deps)))
  
let (rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue) =
  fun issue  ->
    let uu___876_17689 = issue  in
    let uu____17698 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____17698;
      FStar_Errors.issue_level = (uu___876_17689.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___876_17689.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___876_17689.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____17708 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____17708)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___883_17818 = st1  in
        {
          repl_line = (uu___883_17818.repl_line);
          repl_column = (uu___883_17818.repl_column);
          repl_fname = (uu___883_17818.repl_fname);
          repl_deps_stack = (uu___883_17818.repl_deps_stack);
          repl_curmod = (uu___883_17818.repl_curmod);
          repl_env =
            (let uu___885_17836 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___885_17836.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___885_17836.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___885_17836.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___885_17836.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___885_17836.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___885_17836.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___885_17836.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___885_17836.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___885_17836.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___885_17836.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___885_17836.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___885_17836.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___885_17836.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___885_17836.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___885_17836.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___885_17836.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___885_17836.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___885_17836.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___885_17836.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___885_17836.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___885_17836.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___885_17836.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___885_17836.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___885_17836.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___885_17836.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___885_17836.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___885_17836.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___885_17836.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___885_17836.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___885_17836.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___885_17836.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___885_17836.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___885_17836.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___885_17836.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___885_17836.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___885_17836.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___885_17836.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___885_17836.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___885_17836.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___885_17836.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___885_17836.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___885_17836.FStar_TypeChecker_Env.nbe)
             });
          repl_stdin = (uu___883_17818.repl_stdin);
          repl_names = (uu___883_17818.repl_names)
        }  in
      let uu____17945 = query  in
      match uu____17945 with
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
            let uu____18011 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____18011 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____18088 =
                    let uu____18091 = collect_errors ()  in
                    FStar_All.pipe_right uu____18091
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____18088  in
                let st4 =
                  if success
                  then
                    let uu___904_18136 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___904_18136.repl_fname);
                      repl_deps_stack = (uu___904_18136.repl_deps_stack);
                      repl_curmod = (uu___904_18136.repl_curmod);
                      repl_env = (uu___904_18136.repl_env);
                      repl_stdin = (uu___904_18136.repl_stdin);
                      repl_names = (uu___904_18136.repl_names)
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
       let uu____18198 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1"))
          in
       Prims.op_Hat (FStar_String.uppercase first) uu____18198)
  
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
          let uu____18239 = FStar_Util.psmap_empty ()  in
          let uu____18244 =
            let uu____18248 = FStar_Options.prims ()  in uu____18248 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____18264 =
                   FStar_Parser_Dep.lowercase_module_name dep1  in
                 FStar_Util.psmap_add acc uu____18264 true) uu____18239
            uu____18244
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____18293  ->
               match uu____18293 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____18316 = capitalize modname  in
                        FStar_Util.split uu____18316 "."  in
                      let uu____18319 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____18319 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____18334 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____18334)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      (let uu____18392 = FStar_Options.debug_any ()  in
       if uu____18392
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____18400 = load_deps st  in
       match uu____18400 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____18487 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____18487  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____18589 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____18589 (fun a2  -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___942_18593 = st1  in
                {
                  repl_line = (uu___942_18593.repl_line);
                  repl_column = (uu___942_18593.repl_column);
                  repl_fname = (uu___942_18593.repl_fname);
                  repl_deps_stack = (uu___942_18593.repl_deps_stack);
                  repl_curmod = (uu___942_18593.repl_curmod);
                  repl_env = (uu___942_18593.repl_env);
                  repl_stdin = (uu___942_18593.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____18617 .
    repl_state ->
      push_query ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____18617)
          FStar_Util.either)
  =
  fun st  ->
    fun query  ->
      let uu____18674 = nothing_left_to_pop st  in
      if uu____18674
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
              let uu____18930 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____18930  in
            let lid1 =
              let uu____18948 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____18948  in
            let uu____18969 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____18969
              (FStar_Util.map_option
                 (fun uu____19054  ->
                    match uu____19054 with
                    | ((uu____19086,typ),r) ->
                        ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____19140 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____19140
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____19214 = FStar_TypeChecker_Env.lookup_qname tcenv lid
               in
            FStar_Util.bind_opt uu____19214
              (fun uu___12_19277  ->
                 match uu___12_19277 with
                 | (FStar_Util.Inr (se,uu____19309),uu____19310) ->
                     let uu____19367 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____19367
                 | uu____19370 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____19453  ->
                 match uu____19453 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____19536 -> info_at_pos_opt
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
                    let uu____19777 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____19777
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____19802 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____19832 -> FStar_Pervasives_Native.None  in
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
                let uu____19864 =
                  let uu____19877 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____19877)  in
                FStar_Pervasives_Native.Some uu____19864
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
    let uu____20012 = trim_option_name opt_name  in
    match uu____20012 with
    | (uu____20036,trimmed_name) ->
        let uu____20042 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____20042 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.op_Hat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____20117 =
               let uu____20130 =
                 let uu____20138 = update_option opt  in
                 alist_of_fstar_option uu____20138  in
               ("option", uu____20130)  in
             FStar_Util.Inr uu____20117)
  
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
      let uu____20228 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____20228 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____20266 =
            let uu____20279 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____20279)  in
          FStar_Util.Inr uu____20266
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____20312 =
            let uu____20325 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____20325)  in
          FStar_Util.Inr uu____20312
  
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
          let uu____20439 =
            run_symbol_lookup st symbol pos_opt requested_info  in
          match uu____20439 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____20513 ->
              let uu____20528 = run_module_lookup st symbol  in
              (match uu____20528 with
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
  'Auu____20750 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string * Prims.int * Prims.int)
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____20750)
                FStar_Util.either)
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____20842 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____20842 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____20986 .
    ('Auu____20986 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('Auu____20986 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___13_21001  ->
    match uu___13_21001 with
    | (uu____21006,FStar_Interactive_CompletionTable.Namespace uu____21007)
        -> FStar_Pervasives_Native.None
    | (uu____21014,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____21015;
         FStar_Interactive_CompletionTable.mod_path = uu____21016;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____21029 =
          let uu____21034 =
            let uu____21035 =
              let uu___1076_21042 = md  in
              let uu____21049 =
                let uu____21051 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.op_Hat uu____21051 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____21049;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___1076_21042.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___1076_21042.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____21035  in
          (pth, uu____21034)  in
        FStar_Pervasives_Native.Some uu____21029
  
let run_code_autocomplete :
  'Auu____21065 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____21065)
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
  'Auu____21179 'Auu____21180 'Auu____21181 .
    repl_state ->
      Prims.string ->
        'Auu____21179 ->
          'Auu____21180 ->
            ((query_status * FStar_Util.json) * (repl_state,'Auu____21181)
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
              (fun _21255  -> FStar_Pervasives_Native.Some _21255)
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
        let uu____21327 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____21327 with
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
  'Auu____21399 'Auu____21400 .
    'Auu____21399 ->
      Prims.string ->
        Prims.bool ->
          ((query_status * FStar_Util.json) * ('Auu____21399,'Auu____21400)
            FStar_Util.either)
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____21432 = trim_option_name search_term  in
        match uu____21432 with
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
        | (uu____21540,uu____21541) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____21564 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____21564)
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
  'Auu____21647 'Auu____21648 .
    repl_state ->
      'Auu____21647 ->
        (repl_state -> 'Auu____21647) ->
          ('Auu____21647 * (repl_state,'Auu____21648) FStar_Util.either)
  =
  fun st  ->
    fun sigint_default  ->
      fun task  ->
        let st1 = push_repl "run_and_rewind" FullCheck Noop st  in
        let results =
          try
            (fun uu___1135_21745  ->
               match () with
               | () ->
                   FStar_Util.with_sigint_handler FStar_Util.sigint_raise
                     (fun uu____21756  ->
                        let uu____21757 = task st1  in
                        FStar_All.pipe_left
                          (fun _21762  -> FStar_Util.Inl _21762) uu____21757))
              ()
          with | FStar_Util.SigInt  -> FStar_Util.Inl sigint_default
          | e -> FStar_Util.Inr e  in
        let st2 = pop_repl "run_and_rewind" st1  in
        match results with
        | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st2))
        | FStar_Util.Inr e -> FStar_Exn.raise e
  
let run_with_parsed_and_tc_term :
  'Auu____21859 'Auu____21860 'Auu____21861 .
    repl_state ->
      Prims.string ->
        'Auu____21859 ->
          'Auu____21860 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term -> (query_status * FStar_Util.json))
              ->
              ((query_status * FStar_Util.json) * (repl_state,'Auu____21861)
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
                    ((uu____22127,{ FStar_Syntax_Syntax.lbname = uu____22128;
                                    FStar_Syntax_Syntax.lbunivs = univs1;
                                    FStar_Syntax_Syntax.lbtyp = uu____22130;
                                    FStar_Syntax_Syntax.lbeff = uu____22131;
                                    FStar_Syntax_Syntax.lbdef = def;
                                    FStar_Syntax_Syntax.lbattrs = uu____22133;
                                    FStar_Syntax_Syntax.lbpos = uu____22134;_}::[]),uu____22135);
                  FStar_Syntax_Syntax.sigrng = uu____22136;
                  FStar_Syntax_Syntax.sigquals = uu____22137;
                  FStar_Syntax_Syntax.sigmeta = uu____22138;
                  FStar_Syntax_Syntax.sigattrs = uu____22139;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____22261 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____22304 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____22304 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____22315) ->
                  FStar_Pervasives_Native.Some decls
              | uu____22351 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____22492 =
                let uu____22497 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____22497 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____22492  in
            let typecheck tcenv decls =
              let uu____22642 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____22642 with | (ses,uu____22725,uu____22726) -> ses
               in
            run_and_rewind st
              (QueryNOK, (FStar_Util.JsonStr "Computation interrupted"))
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 let uu____22997 = parse1 frag  in
                 match uu____22997 with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK,
                       (FStar_Util.JsonStr "Could not parse this term"))
                 | FStar_Pervasives_Native.Some decls ->
                     let aux uu____23043 =
                       let decls1 = desugar tcenv decls  in
                       let ses = typecheck tcenv decls1  in
                       match find_let_body ses with
                       | FStar_Pervasives_Native.None  ->
                           (QueryNOK,
                             (FStar_Util.JsonStr
                                "Typechecking yielded an unexpected term"))
                       | FStar_Pervasives_Native.Some (univs1,def) ->
                           let uu____23108 =
                             FStar_Syntax_Subst.open_univ_vars univs1 def  in
                           (match uu____23108 with
                            | (univs2,def1) ->
                                let tcenv1 =
                                  FStar_TypeChecker_Env.push_univ_vars tcenv
                                    univs2
                                   in
                                continuation tcenv1 def1)
                        in
                     let uu____23240 = FStar_Options.trace_error ()  in
                     if uu____23240
                     then aux ()
                     else
                       (try
                          (fun uu___1218_23254  ->
                             match () with | () -> aux ()) ()
                        with
                        | uu___1217_23263 ->
                            let uu____23268 =
                              FStar_Errors.issue_of_exn uu___1217_23263  in
                            (match uu____23268 with
                             | FStar_Pervasives_Native.Some issue ->
                                 let uu____23288 =
                                   let uu____23289 =
                                     FStar_Errors.format_issue issue  in
                                   FStar_Util.JsonStr uu____23289  in
                                 (QueryNOK, uu____23288)
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Exn.raise uu___1217_23263)))
  
let run_compute :
  'Auu____23308 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Env.step Prims.list FStar_Pervasives_Native.option
          ->
          ((query_status * FStar_Util.json) * (repl_state,'Auu____23308)
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
            FStar_TypeChecker_Env.Eager_unfolding false;
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
               let uu____23597 =
                 let uu____23598 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____23598  in
               (QueryOK, uu____23597))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid 
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }
let (uu___is_NameContainsStr : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____23643 -> false
  
let (__proj__NameContainsStr__item___0 : search_term' -> Prims.string) =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let (uu___is_TypeContainsLid : search_term' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____23669 -> false
  
let (__proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let (__proj__Mksearch_term__item__st_negate : search_term -> Prims.bool) =
  fun projectee  ->
    match projectee with | { st_negate; st_term;_} -> st_negate
  
let (__proj__Mksearch_term__item__st_term : search_term -> search_term') =
  fun projectee  -> match projectee with | { st_negate; st_term;_} -> st_term 
let (st_cost : search_term' -> Prims.int) =
  fun uu___14_23732  ->
    match uu___14_23732 with
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
    let uu____24028 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____24047 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____24028; sc_fvars = uu____24047 }
  
let (sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ) =
  fun tcenv  ->
    fun sc  ->
      let uu____24209 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____24209 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____24273 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____24273 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____24304,typ),uu____24306) ->
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
      let uu____24510 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____24510 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____24586 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____24586  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let (json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json) =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____24772 = sc_typ tcenv sc  in
        term_to_string tcenv uu____24772  in
      let uu____24781 =
        let uu____24789 =
          let uu____24795 =
            let uu____24796 =
              let uu____24798 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____24798.FStar_Ident.str  in
            FStar_Util.JsonStr uu____24796  in
          ("lid", uu____24795)  in
        [uu____24789; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____24781
  
exception InvalidSearch of Prims.string 
let (uu___is_InvalidSearch : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____24839 -> true
    | uu____24842 -> false
  
let (__proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidSearch uu____24852 -> uu____24852
  
let run_search :
  'Auu____24861 .
    repl_state ->
      Prims.string ->
        ((query_status * FStar_Util.json) * (repl_state,'Auu____24861)
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
              let uu____25066 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____25066
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
              let uu____25137 =
                let uu____25138 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____25138  in
              FStar_Exn.raise uu____25137
            else
              if beg_quote
              then
                (let uu____25144 = strip_quotes term1  in
                 NameContainsStr uu____25144)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____25157 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____25157 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____25168 =
                       let uu____25169 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____25169  in
                     FStar_Exn.raise uu____25168
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____25223 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.op_Hat (if term.st_negate then "-" else "") uu____25223  in
      let results =
        try
          (fun uu___1331_25261  ->
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
                        let uu____25419 = FStar_List.map pprint_one terms  in
                        FStar_Util.concat_l " " uu____25419  in
                      let uu____25427 =
                        let uu____25428 =
                          FStar_Util.format1
                            "No results found for query [%s]" kwds
                           in
                        InvalidSearch uu____25428  in
                      FStar_Exn.raise uu____25427
                  | uu____25435 -> (QueryOK, (FStar_Util.JsonList js)))) ()
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
          { push_kind = SyntaxCheck ; push_code = uu____25692;
            push_line = uu____25693; push_column = uu____25694;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____25700 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____25712 -> q)
  
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
      let uu____25845 = validate_and_run_query st query  in
      match uu____25845 with
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
      let uu____25975 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____25975
  
let (js_repl_eval_str :
  repl_state ->
    Prims.string -> (Prims.string * (repl_state,Prims.int) FStar_Util.either))
  =
  fun st  ->
    fun query_str  ->
      let uu____26027 =
        let uu____26045 = parse_interactive_query query_str  in
        js_repl_eval st uu____26045  in
      match uu____26027 with
      | (js_response,st_opt) ->
          let uu____26096 = FStar_Util.string_of_json js_response  in
          (uu____26096, st_opt)
  
let (js_repl_init_opts : unit -> unit) =
  fun uu____26117  ->
    let uu____26118 = FStar_Options.parse_cmd_line ()  in
    match uu____26118 with
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
              | h::uu____26141::uu____26142 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____26151 -> ()))
  
let rec (go : repl_state -> Prims.int) =
  fun st  ->
    let query = read_interactive_query st.repl_stdin  in
    let uu____26184 = validate_and_run_query st query  in
    match uu____26184 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let (interactive_error_handler : FStar_Errors.error_handler) =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____26315 =
      let uu____26322 = FStar_ST.op_Bang issues  in e :: uu____26322  in
    FStar_ST.op_Colon_Equals issues uu____26315  in
  let count_errors uu____26400 =
    let uu____26401 =
      let uu____26408 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____26408
       in
    FStar_List.length uu____26401  in
  let report uu____26471 =
    let uu____26472 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____26472  in
  let clear1 uu____26519 = FStar_ST.op_Colon_Equals issues []  in
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
               let uu____26607 = get_json ()  in
               forward_message printer label uu____26607)
    }
  
let (install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit) =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let (initial_range : FStar_Range.range) =
  let uu____26621 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  let uu____26624 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  FStar_Range.mk_range "<input>" uu____26621 uu____26624 
let (build_initial_repl_state : Prims.string -> repl_state) =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____26862 = FStar_Util.open_stdin ()  in
    {
      repl_line = (Prims.parse_int "1");
      repl_column = (Prims.parse_int "0");
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____26862;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' : 'Auu____26894 . repl_state -> 'Auu____26894 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____26919 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____26919
       then
         let uu____26923 =
           let uu____26925 = FStar_Options.file_list ()  in
           FStar_List.hd uu____26925  in
         FStar_SMTEncoding_Solver.with_hints_db uu____26923
           (fun uu____26932  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let (interactive_mode : Prims.string -> unit) =
  fun filename  ->
    install_ide_mode_hooks write_json;
    FStar_Util.set_sigint_handler FStar_Util.sigint_ignore;
    (let uu____26946 =
       let uu____26948 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____26948  in
     if uu____26946
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____26973 = FStar_Options.trace_error ()  in
     if uu____26973
     then interactive_mode' init1
     else
       (try
          (fun uu___1479_26979  ->
             match () with | () -> interactive_mode' init1) ()
        with
        | uu___1478_26982 ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise uu___1478_26982)))
  
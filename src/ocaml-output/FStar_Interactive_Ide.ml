open Prims
exception ExitREPL of Prims.int 
let uu___is_ExitREPL : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | ExitREPL uu____7 -> true | uu____8 -> false
  
let __proj__ExitREPL__item__uu___ : Prims.exn -> Prims.int =
  fun projectee  -> match projectee with | ExitREPL uu____15 -> uu____15 
let push :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let res = FStar_Universal.push_context env msg  in
      FStar_Options.push (); res
  
let pop : FStar_TypeChecker_Env.env -> Prims.string -> Prims.unit =
  fun env  ->
    fun msg  -> FStar_Universal.pop_context env msg; FStar_Options.pop ()
  
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck [@@deriving show]
let uu___is_SyntaxCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____34 -> false
  
let uu___is_LaxCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____38 -> false
  
let uu___is_FullCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____42 -> false
  
let set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun check_kind  ->
      let uu___385_49 = env  in
      let uu____50 =
        FStar_ToSyntax_Env.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___385_49.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___385_49.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___385_49.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___385_49.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___385_49.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___385_49.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___385_49.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___385_49.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___385_49.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___385_49.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___385_49.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___385_49.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___385_49.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___385_49.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___385_49.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___385_49.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___385_49.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___385_49.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___385_49.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___385_49.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___385_49.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___385_49.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___385_49.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___385_49.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___385_49.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qname_and_index =
          (uu___385_49.FStar_TypeChecker_Env.qname_and_index);
        FStar_TypeChecker_Env.proof_ns =
          (uu___385_49.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth =
          (uu___385_49.FStar_TypeChecker_Env.synth);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___385_49.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___385_49.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___385_49.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____50;
        FStar_TypeChecker_Env.dep_graph =
          (uu___385_49.FStar_TypeChecker_Env.dep_graph)
      }
  
let with_captured_errors' :
  'Auu____54 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env -> 'Auu____54 FStar_Pervasives_Native.option)
        -> 'Auu____54 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      try f env
      with
      | FStar_All.Failure msg ->
          let msg1 =
            Prims.strcat "ASSERTION FAILURE: "
              (Prims.strcat msg
                 (Prims.strcat "\n"
                    (Prims.strcat "F* may be in an inconsistent state.\n"
                       (Prims.strcat
                          "Please file a bug report, ideally with a "
                          "minimized version of the program that triggered the error."))))
             in
          ((let uu____90 = FStar_TypeChecker_Env.get_range env  in
            FStar_Errors.log_issue uu____90
              (FStar_Errors.Error_IDEAssertionFailure, msg1));
           FStar_Pervasives_Native.None)
      | FStar_Errors.Error (e,msg,r) ->
          (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
           FStar_Pervasives_Native.None)
      | FStar_Errors.Err (e,msg) ->
          ((let uu____110 =
              let uu____119 =
                let uu____126 = FStar_TypeChecker_Env.get_range env  in
                (e, msg, uu____126)  in
              [uu____119]  in
            FStar_TypeChecker_Err.add_errors env uu____110);
           FStar_Pervasives_Native.None)
      | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____142 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env ->
         'Auu____142 FStar_Pervasives_Native.option)
        -> 'Auu____142 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let uu____162 = FStar_Options.trace_error ()  in
      if uu____162 then f env else with_captured_errors' env f
  
type timed_fname = {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Util.time }[@@deriving show]
let __proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string =
  fun projectee  ->
    match projectee with
    | { tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime;_} ->
        __fname__tf_fname
  
let __proj__Mktimed_fname__item__tf_modtime : timed_fname -> FStar_Util.time
  =
  fun projectee  ->
    match projectee with
    | { tf_fname = __fname__tf_fname; tf_modtime = __fname__tf_modtime;_} ->
        __fname__tf_modtime
  
let t0 : FStar_Util.time = FStar_Util.now () 
let tf_of_fname : Prims.string -> timed_fname =
  fun fname  ->
    let uu____187 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____187 }
  
let dummy_tf_of_fname : Prims.string -> timed_fname =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let string_of_timed_fname : timed_fname -> Prims.string =
  fun uu____193  ->
    match uu____193 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____197 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____197)
  
type push_query =
  {
  push_kind: push_kind ;
  push_code: Prims.string ;
  push_line: Prims.int ;
  push_column: Prims.int ;
  push_peek_only: Prims.bool }[@@deriving show]
let __proj__Mkpush_query__item__push_kind : push_query -> push_kind =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_kind
  
let __proj__Mkpush_query__item__push_code : push_query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_code
  
let __proj__Mkpush_query__item__push_line : push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_line
  
let __proj__Mkpush_query__item__push_column : push_query -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} -> __fname__push_column
  
let __proj__Mkpush_query__item__push_peek_only : push_query -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { push_kind = __fname__push_kind; push_code = __fname__push_code;
        push_line = __fname__push_line; push_column = __fname__push_column;
        push_peek_only = __fname__push_peek_only;_} ->
        __fname__push_peek_only
  
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
[@@deriving show]
type repl_task =
  | LDInterleaved of (timed_fname,timed_fname) FStar_Pervasives_Native.tuple2
  
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of FStar_Parser_ParseIt.input_frag [@@deriving show]
let uu___is_LDInterleaved : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDInterleaved _0 -> true | uu____288 -> false
  
let __proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname,timed_fname) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let uu___is_LDSingle : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____312 -> false
  
let __proj__LDSingle__item___0 : repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____324 -> false
  
let __proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let uu___is_PushFragment : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____336 -> false
  
let __proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag =
  fun projectee  -> match projectee with | PushFragment _0 -> _0 
type env_t = FStar_TypeChecker_Env.env[@@deriving show]
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack:
    (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: env_t ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table }[@@deriving show]
let __proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_line
  
let __proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_column
  
let __proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_fname
  
let __proj__Mkrepl_state__item__repl_deps_stack :
  repl_state ->
    (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_deps_stack
  
let __proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_curmod
  
let __proj__Mkrepl_state__item__repl_env : repl_state -> env_t =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_env
  
let __proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_stdin
  
let __proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table =
  fun projectee  ->
    match projectee with
    | { repl_line = __fname__repl_line; repl_column = __fname__repl_column;
        repl_fname = __fname__repl_fname;
        repl_deps_stack = __fname__repl_deps_stack;
        repl_curmod = __fname__repl_curmod; repl_env = __fname__repl_env;
        repl_stdin = __fname__repl_stdin; repl_names = __fname__repl_names;_}
        -> __fname__repl_names
  
type completed_repl_task =
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2[@@deriving show]
type repl_stack_t =
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list[@@deriving
                                                                    show]
let repl_stack :
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let pop_repl : repl_state -> repl_state =
  fun st  ->
    let uu____568 = FStar_ST.op_Bang repl_stack  in
    match uu____568 with
    | [] -> failwith "Too many pops"
    | (uu____639,st')::stack ->
        (pop st.repl_env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         st')
  
let push_repl :
  push_kind -> repl_task -> repl_state -> FStar_TypeChecker_Env.env =
  fun push_kind  ->
    fun task  ->
      fun st  ->
        (let uu____724 =
           let uu____731 = FStar_ST.op_Bang repl_stack  in (task, st) ::
             uu____731
            in
         FStar_ST.op_Colon_Equals repl_stack uu____724);
        (let uu____862 = set_check_kind st.repl_env push_kind  in
         push uu____862 "")
  
let nothing_left_to_pop : repl_state -> Prims.bool =
  fun st  ->
    let uu____866 =
      let uu____867 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____867  in
    uu____866 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple3 
  | NTOpen of (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
  FStar_Pervasives_Native.tuple2 
  | NTInclude of (FStar_Ident.lid,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2 
  | NTBinding of FStar_TypeChecker_Env.binding [@@deriving show]
let uu___is_NTAlias : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____986 -> false
  
let __proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let uu___is_NTOpen : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____1020 -> false
  
let __proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_ToSyntax_Env.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let uu___is_NTInclude : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____1048 -> false
  
let __proj__NTInclude__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0 
let uu___is_NTBinding : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____1072 -> false
  
let __proj__NTBinding__item___0 :
  name_tracking_event -> FStar_TypeChecker_Env.binding =
  fun projectee  -> match projectee with | NTBinding _0 -> _0 
let query_of_ids :
  FStar_Ident.ident Prims.list -> FStar_Interactive_CompletionTable.query =
  fun ids  -> FStar_List.map FStar_Ident.text_of_id ids 
let query_of_lid :
  FStar_Ident.lident -> FStar_Interactive_CompletionTable.query =
  fun lid  ->
    query_of_ids
      (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident])
  
let update_names_from_event :
  Prims.string ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event -> FStar_Interactive_CompletionTable.table
  =
  fun cur_mod_str  ->
    fun table  ->
      fun evt  ->
        let is_cur_mod lid = lid.FStar_Ident.str = cur_mod_str  in
        match evt with
        | NTAlias (host,id1,included) ->
            if is_cur_mod host
            then
              let uu____1106 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                (FStar_Ident.text_of_id id1) [] uu____1106
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____1115 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_ToSyntax_Env.Open_module) [] uu____1115
            else table
        | NTInclude (host,included) ->
            let uu____1119 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____1121 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____1119 uu____1121
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____1129) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____1131) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____1137,uu____1138) -> lids
              | uu____1143 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     (FStar_Ident.text_of_id lid.FStar_Ident.ident) lid)
              table lids
  
let commit_name_tracking' :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Interactive_CompletionTable.table ->
      name_tracking_event Prims.list ->
        FStar_Interactive_CompletionTable.table
  =
  fun cur_mod  ->
    fun names1  ->
      fun name_events  ->
        let cur_mod_str =
          match cur_mod with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some md ->
              let uu____1174 = FStar_Syntax_Syntax.mod_name md  in
              uu____1174.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___388_1191 = st  in
      {
        repl_line = (uu___388_1191.repl_line);
        repl_column = (uu___388_1191.repl_column);
        repl_fname = (uu___388_1191.repl_fname);
        repl_deps_stack = (uu___388_1191.repl_deps_stack);
        repl_curmod = (uu___388_1191.repl_curmod);
        repl_env = (uu___388_1191.repl_env);
        repl_stdin = (uu___388_1191.repl_stdin);
        repl_names = names1
      }
  
let fresh_name_tracking_hooks :
  Prims.unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_ToSyntax_Env.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____1204  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____1216 =
        let uu____1219 = FStar_ST.op_Bang events  in evt :: uu____1219  in
      FStar_ST.op_Colon_Equals events uu____1216  in
    (events,
      {
        FStar_ToSyntax_Env.ds_push_open_hook =
          (fun dsenv  ->
             fun op  ->
               let uu____1380 =
                 let uu____1381 =
                   let uu____1386 = FStar_ToSyntax_Env.current_module dsenv
                      in
                   (uu____1386, op)  in
                 NTOpen uu____1381  in
               push_event uu____1380);
        FStar_ToSyntax_Env.ds_push_include_hook =
          (fun dsenv  ->
             fun ns  ->
               let uu____1392 =
                 let uu____1393 =
                   let uu____1398 = FStar_ToSyntax_Env.current_module dsenv
                      in
                   (uu____1398, ns)  in
                 NTInclude uu____1393  in
               push_event uu____1392);
        FStar_ToSyntax_Env.ds_push_module_abbrev_hook =
          (fun dsenv  ->
             fun x  ->
               fun l  ->
                 let uu____1406 =
                   let uu____1407 =
                     let uu____1414 = FStar_ToSyntax_Env.current_module dsenv
                        in
                     (uu____1414, x, l)  in
                   NTAlias uu____1407  in
                 push_event uu____1406)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1419  -> fun s  -> push_event (NTBinding s))
      })
  
let track_name_changes :
  env_t ->
    (env_t,env_t ->
             (env_t,name_tracking_event Prims.list)
               FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    let set_hooks dshooks tchooks env1 =
      let uu____1458 =
        FStar_Universal.with_tcenv env1
          (fun dsenv  ->
             let uu____1466 = FStar_ToSyntax_Env.set_ds_hooks dsenv dshooks
                in
             ((), uu____1466))
         in
      match uu____1458 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____1468 =
      let uu____1473 =
        FStar_ToSyntax_Env.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____1474 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____1473, uu____1474)  in
    match uu____1468 with
    | (old_dshooks,old_tchooks) ->
        let uu____1489 = fresh_name_tracking_hooks ()  in
        (match uu____1489 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1523 = set_hooks new_dshooks new_tchooks env  in
             (uu____1523,
               ((fun env1  ->
                   let uu____1536 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____1537 =
                     let uu____1540 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____1540  in
                   (uu____1536, uu____1537)))))
  
let string_of_repl_task : repl_task -> Prims.string =
  fun uu___370_1613  ->
    match uu___370_1613 with
    | LDInterleaved (intf,impl) ->
        let uu____1616 = string_of_timed_fname intf  in
        let uu____1617 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1616 uu____1617
    | LDSingle intf_or_impl ->
        let uu____1619 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____1619
    | LDInterfaceOfCurrentFile intf ->
        let uu____1621 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1621
    | PushFragment frag ->
        FStar_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
  
let tc_one :
  FStar_TypeChecker_Env.env ->
    Prims.string FStar_Pervasives_Native.option ->
      Prims.string -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun intf_opt  ->
      fun modf  ->
        let uu____1636 = FStar_Universal.tc_one_file env intf_opt modf  in
        match uu____1636 with | (uu____1645,env1) -> env1
  
let run_repl_task :
  optmod_t ->
    env_t -> repl_task -> (optmod_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____1674 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____1674)
        | LDSingle intf_or_impl ->
            let uu____1676 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____1676)
        | LDInterfaceOfCurrentFile intf ->
            let uu____1678 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____1678)
        | PushFragment frag ->
            FStar_Universal.tc_one_fragment curmod env frag
  
let repl_ld_tasks_of_deps :
  Prims.string Prims.list -> repl_task Prims.list -> repl_task Prims.list =
  fun deps  ->
    fun final_tasks  ->
      let wrap = dummy_tf_of_fname  in
      let rec aux deps1 final_tasks1 =
        match deps1 with
        | intf::impl::deps' when FStar_Universal.needs_interleaving intf impl
            ->
            let uu____1723 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____1723
        | intf_or_impl::deps' ->
            let uu____1730 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____1730
        | [] -> final_tasks1  in
      aux deps final_tasks
  
let deps_and_repl_ld_tasks_of_our_file :
  Prims.string ->
    (Prims.string Prims.list,repl_task Prims.list,FStar_Parser_Dep.deps)
      FStar_Pervasives_Native.tuple3
  =
  fun filename  ->
    let get_mod_name fname = FStar_Parser_Dep.lowercase_module_name fname  in
    let our_mod_name = get_mod_name filename  in
    let has_our_mod_name f =
      let uu____1765 = get_mod_name f  in uu____1765 = our_mod_name  in
    let uu____1766 = FStar_Dependencies.find_deps_if_needed [filename]  in
    match uu____1766 with
    | (deps,dep_graph1) ->
        let uu____1789 = FStar_List.partition has_our_mod_name deps  in
        (match uu____1789 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1826 =
                       let uu____1827 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____1827  in
                     if uu____1826
                     then
                       let uu____1828 =
                         let uu____1833 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____1833)
                          in
                       FStar_Errors.raise_err uu____1828
                     else ());
                    (let uu____1836 =
                       let uu____1837 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____1837  in
                     if uu____1836
                     then
                       let uu____1838 =
                         let uu____1843 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____1843)
                          in
                       FStar_Errors.raise_err uu____1838
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____1846 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____1852 =
                       let uu____1857 =
                         FStar_Util.format2 message our_mod_name mods_str  in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____1857)
                        in
                     FStar_Errors.raise_err uu____1852);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let update_task_timestamps : repl_task -> repl_task =
  fun uu___371_1867  ->
    match uu___371_1867 with
    | LDInterleaved (intf,impl) ->
        let uu____1870 =
          let uu____1875 = tf_of_fname intf.tf_fname  in
          let uu____1876 = tf_of_fname impl.tf_fname  in
          (uu____1875, uu____1876)  in
        LDInterleaved uu____1870
    | LDSingle intf_or_impl ->
        let uu____1878 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____1878
    | LDInterfaceOfCurrentFile intf ->
        let uu____1880 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____1880
    | PushFragment frag -> PushFragment frag
  
let run_repl_transaction :
  repl_state ->
    push_kind ->
      Prims.bool ->
        repl_task -> (Prims.bool,repl_state) FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun push_kind  ->
      fun must_rollback  ->
        fun task  ->
          let env = push_repl push_kind task st  in
          let uu____1899 = track_name_changes env  in
          match uu____1899 with
          | (env1,finish_name_tracking) ->
              let check_success uu____1937 =
                (let uu____1940 = FStar_Errors.get_err_count ()  in
                 uu____1940 = (Prims.parse_int "0")) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____1941 =
                let uu____1948 =
                  with_captured_errors env1
                    (fun env2  ->
                       let uu____1962 =
                         run_repl_task st.repl_curmod env2 task  in
                       FStar_All.pipe_left
                         (fun _0_64  -> FStar_Pervasives_Native.Some _0_64)
                         uu____1962)
                   in
                match uu____1948 with
                | FStar_Pervasives_Native.Some (curmod,env2) when
                    check_success () -> (curmod, env2, true)
                | uu____1993 -> ((st.repl_curmod), env1, false)  in
              (match uu____1941 with
               | (curmod,env2,success) ->
                   let uu____2007 = finish_name_tracking env2  in
                   (match uu____2007 with
                    | (env',name_events) ->
                        let st1 =
                          let uu___389_2025 = st  in
                          {
                            repl_line = (uu___389_2025.repl_line);
                            repl_column = (uu___389_2025.repl_column);
                            repl_fname = (uu___389_2025.repl_fname);
                            repl_deps_stack = (uu___389_2025.repl_deps_stack);
                            repl_curmod = curmod;
                            repl_env = env2;
                            repl_stdin = (uu___389_2025.repl_stdin);
                            repl_names = (uu___389_2025.repl_names)
                          }  in
                        let st2 =
                          if success
                          then commit_name_tracking st1 name_events
                          else pop_repl st1  in
                        (success, st2)))
  
let run_repl_ld_transactions :
  repl_state ->
    repl_task Prims.list -> (repl_state,repl_state) FStar_Util.either
  =
  fun st  ->
    fun tasks  ->
      let debug1 verb task =
        let uu____2049 = FStar_Options.debug_any ()  in
        if uu____2049
        then
          let uu____2050 = string_of_repl_task task  in
          FStar_Util.print2 "%s %s" verb uu____2050
        else ()  in
      let rec revert_many st1 uu___372_2064 =
        match uu___372_2064 with
        | [] -> st1
        | (task,_st')::entries ->
            ((let uu____2089 = Obj.magic ()  in ());
             debug1 "Reverting" task;
             (let uu____2091 = pop_repl st1  in
              revert_many uu____2091 entries))
         in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([],[]) -> FStar_Util.Inl st1
        | (task::tasks2,[]) ->
            (debug1 "Loading" task;
             (let uu____2136 = FStar_Options.restore_cmd_line_options false
                 in
              FStar_All.pipe_right uu____2136 FStar_Pervasives.ignore);
             (let timestamped_task = update_task_timestamps task  in
              let push_kind =
                let uu____2139 = FStar_Options.lax ()  in
                if uu____2139 then LaxCheck else FullCheck  in
              let uu____2141 =
                run_repl_transaction st1 push_kind false timestamped_task  in
              match uu____2141 with
              | (success,st2) ->
                  if success
                  then
                    let uu____2156 =
                      let uu___390_2157 = st2  in
                      let uu____2158 = FStar_ST.op_Bang repl_stack  in
                      {
                        repl_line = (uu___390_2157.repl_line);
                        repl_column = (uu___390_2157.repl_column);
                        repl_fname = (uu___390_2157.repl_fname);
                        repl_deps_stack = uu____2158;
                        repl_curmod = (uu___390_2157.repl_curmod);
                        repl_env = (uu___390_2157.repl_env);
                        repl_stdin = (uu___390_2157.repl_stdin);
                        repl_names = (uu___390_2157.repl_names)
                      }  in
                    aux uu____2156 tasks2 []
                  else FStar_Util.Inr st2))
        | (task::tasks2,prev::previous1) when
            let uu____2238 = update_task_timestamps task  in
            (FStar_Pervasives_Native.fst prev) = uu____2238 ->
            (debug1 "Skipping" task; aux st1 tasks2 previous1)
        | (tasks2,previous1) ->
            let uu____2250 = revert_many st1 previous1  in
            aux uu____2250 tasks2 []
         in
      aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let json_to_str : FStar_Util.json -> Prims.string =
  fun uu___373_2257  ->
    match uu___373_2257 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2261 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____2261
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2263 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2266 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2 
let uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2283 -> true
    | uu____2288 -> false
  
let __proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____2303 -> uu____2303
  
let js_fail : 'Auu____2311 . Prims.string -> FStar_Util.json -> 'Auu____2311
  =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let js_int : FStar_Util.json -> Prims.int =
  fun uu___374_2322  ->
    match uu___374_2322 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let js_str : FStar_Util.json -> Prims.string =
  fun uu___375_2327  ->
    match uu___375_2327 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____2333 .
    (FStar_Util.json -> 'Auu____2333) ->
      FStar_Util.json -> 'Auu____2333 Prims.list
  =
  fun k  ->
    fun uu___376_2346  ->
      match uu___376_2346 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let js_assoc :
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___377_2363  ->
    match uu___377_2363 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let js_pushkind : FStar_Util.json -> push_kind =
  fun s  ->
    let uu____2387 = js_str s  in
    match uu____2387 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2388 -> js_fail "push_kind" s
  
let js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____2392 = js_str s  in
    match uu____2392 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____2393 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_CKCode : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____2409 -> false
  
let uu___is_CKOption : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____2414 -> false
  
let __proj__CKOption__item___0 : completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let uu___is_CKModuleOrNamespace : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2430 -> false
  
let __proj__CKModuleOrNamespace__item___0 :
  completion_context ->
    (Prims.bool,Prims.bool) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | CKModuleOrNamespace _0 -> _0 
let js_optional_completion_context :
  FStar_Util.json FStar_Pervasives_Native.option -> completion_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> CKCode
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2458 = js_str k1  in
        (match uu____2458 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2459 ->
             js_fail
               "completion context (code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
  
type lookup_context =
  | LKSymbolOnly 
  | LKModule 
  | LKOption 
  | LKCode [@@deriving show]
let uu___is_LKSymbolOnly : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKSymbolOnly  -> true | uu____2463 -> false
  
let uu___is_LKModule : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____2467 -> false
  
let uu___is_LKOption : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____2471 -> false
  
let uu___is_LKCode : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____2475 -> false
  
let js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2484 = js_str k1  in
        (match uu____2484 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2485 ->
             js_fail
               "lookup context (symbol-only, code, set-options, reset-options, open, let-open, include, module-alias)"
               k1)
  
type position =
  (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3[@@deriving
                                                                    show]
type query' =
  | Exit 
  | DescribeProtocol 
  | DescribeRepl 
  | Segment of Prims.string 
  | Pop 
  | Push of push_query 
  | VfsAdd of (Prims.string FStar_Pervasives_Native.option,Prims.string)
  FStar_Pervasives_Native.tuple2 
  | AutoComplete of (Prims.string,completion_context)
  FStar_Pervasives_Native.tuple2 
  | Lookup of
  (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
  Prims.string Prims.list) FStar_Pervasives_Native.tuple4 
  | Compute of
  (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                  FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Search of Prims.string 
  | GenericError of Prims.string 
  | ProtocolViolation of Prims.string [@@deriving show]
and query = {
  qq: query' ;
  qid: Prims.string }[@@deriving show]
let uu___is_Exit : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Exit  -> true | uu____2569 -> false
  
let uu___is_DescribeProtocol : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____2573 -> false
  
let uu___is_DescribeRepl : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____2577 -> false
  
let uu___is_Segment : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____2582 -> false
  
let __proj__Segment__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let uu___is_Pop : query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____2593 -> false 
let uu___is_Push : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2598 -> false
  
let __proj__Push__item___0 : query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0 
let uu___is_VfsAdd : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____2616 -> false
  
let __proj__VfsAdd__item___0 :
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let uu___is_AutoComplete : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2650 -> false
  
let __proj__AutoComplete__item___0 :
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let uu___is_Lookup : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2686 -> false
  
let __proj__Lookup__item___0 :
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let uu___is_Compute : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2742 -> false
  
let __proj__Compute__item___0 :
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let uu___is_Search : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2778 -> false
  
let __proj__Search__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0 
let uu___is_GenericError : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2790 -> false
  
let __proj__GenericError__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let uu___is_ProtocolViolation : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2802 -> false
  
let __proj__ProtocolViolation__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | ProtocolViolation _0 -> _0 
let __proj__Mkquery__item__qq : query -> query' =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qq
  
let __proj__Mkquery__item__qid : query -> Prims.string =
  fun projectee  ->
    match projectee with
    | { qq = __fname__qq; qid = __fname__qid;_} -> __fname__qid
  
let query_needs_current_module : query' -> Prims.bool =
  fun uu___378_2822  ->
    match uu___378_2822 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____2823 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2824; push_code = uu____2825;
          push_line = uu____2826; push_column = uu____2827;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2828 -> false
    | GenericError uu____2835 -> false
    | ProtocolViolation uu____2836 -> false
    | Push uu____2837 -> true
    | AutoComplete uu____2838 -> true
    | Lookup uu____2843 -> true
    | Compute uu____2856 -> true
    | Search uu____2865 -> true
  
let interactive_protocol_vernum : Prims.int = (Prims.parse_int "2") 
let interactive_protocol_features : Prims.string Prims.list =
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
  "vfs-add"] 
exception InvalidQuery of Prims.string 
let uu___is_InvalidQuery : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____2874 -> true
    | uu____2875 -> false
  
let __proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____2882 -> uu____2882
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol [@@deriving show]
let uu___is_QueryOK : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____2886 -> false
  
let uu___is_QueryNOK : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____2890 -> false
  
let uu___is_QueryViolatesProtocol : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____2894 -> false
  
let try_assoc :
  'Auu____2899 'Auu____2900 .
    'Auu____2900 ->
      ('Auu____2900,'Auu____2899) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____2899 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____2923 =
        FStar_Util.try_find
          (fun uu____2937  ->
             match uu____2937 with | (k,uu____2943) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____2923
  
let wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____2957 =
          let uu____2958 =
            let uu____2959 = json_to_str got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2959
             in
          ProtocolViolation uu____2958  in
        { qq = uu____2957; qid }
  
let unpack_interactive_query : FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____2985 = try_assoc key a  in
      match uu____2985 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____2989 =
            let uu____2990 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____2990  in
          FStar_Exn.raise uu____2989
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____3005 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____3005 js_str  in
    try
      let query =
        let uu____3014 = assoc1 "query" "query" request  in
        FStar_All.pipe_right uu____3014 js_str  in
      let args =
        let uu____3022 = assoc1 "query" "args" request  in
        FStar_All.pipe_right uu____3022 js_assoc  in
      let arg k = assoc1 "[args]" k args  in
      let try_arg k =
        let uu____3039 = try_assoc k args  in
        match uu____3039 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other  in
      let uu____3047 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "segment" ->
            let uu____3048 =
              let uu____3049 = arg "code"  in
              FStar_All.pipe_right uu____3049 js_str  in
            Segment uu____3048
        | "peek" ->
            let uu____3050 =
              let uu____3051 =
                let uu____3052 = arg "kind"  in
                FStar_All.pipe_right uu____3052 js_pushkind  in
              let uu____3053 =
                let uu____3054 = arg "code"  in
                FStar_All.pipe_right uu____3054 js_str  in
              let uu____3055 =
                let uu____3056 = arg "line"  in
                FStar_All.pipe_right uu____3056 js_int  in
              let uu____3057 =
                let uu____3058 = arg "column"  in
                FStar_All.pipe_right uu____3058 js_int  in
              {
                push_kind = uu____3051;
                push_code = uu____3053;
                push_line = uu____3055;
                push_column = uu____3057;
                push_peek_only = (query = "peek")
              }  in
            Push uu____3050
        | "push" ->
            let uu____3059 =
              let uu____3060 =
                let uu____3061 = arg "kind"  in
                FStar_All.pipe_right uu____3061 js_pushkind  in
              let uu____3062 =
                let uu____3063 = arg "code"  in
                FStar_All.pipe_right uu____3063 js_str  in
              let uu____3064 =
                let uu____3065 = arg "line"  in
                FStar_All.pipe_right uu____3065 js_int  in
              let uu____3066 =
                let uu____3067 = arg "column"  in
                FStar_All.pipe_right uu____3067 js_int  in
              {
                push_kind = uu____3060;
                push_code = uu____3062;
                push_line = uu____3064;
                push_column = uu____3066;
                push_peek_only = (query = "peek")
              }  in
            Push uu____3059
        | "autocomplete" ->
            let uu____3068 =
              let uu____3073 =
                let uu____3074 = arg "partial-symbol"  in
                FStar_All.pipe_right uu____3074 js_str  in
              let uu____3075 =
                let uu____3076 = try_arg "context"  in
                FStar_All.pipe_right uu____3076
                  js_optional_completion_context
                 in
              (uu____3073, uu____3075)  in
            AutoComplete uu____3068
        | "lookup" ->
            let uu____3081 =
              let uu____3094 =
                let uu____3095 = arg "symbol"  in
                FStar_All.pipe_right uu____3095 js_str  in
              let uu____3096 =
                let uu____3097 = try_arg "context"  in
                FStar_All.pipe_right uu____3097 js_optional_lookup_context
                 in
              let uu____3102 =
                let uu____3111 =
                  let uu____3120 = try_arg "location"  in
                  FStar_All.pipe_right uu____3120
                    (FStar_Util.map_option js_assoc)
                   in
                FStar_All.pipe_right uu____3111
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____3178 =
                          let uu____3179 = assoc1 "[location]" "filename" loc
                             in
                          FStar_All.pipe_right uu____3179 js_str  in
                        let uu____3180 =
                          let uu____3181 = assoc1 "[location]" "line" loc  in
                          FStar_All.pipe_right uu____3181 js_int  in
                        let uu____3182 =
                          let uu____3183 = assoc1 "[location]" "column" loc
                             in
                          FStar_All.pipe_right uu____3183 js_int  in
                        (uu____3178, uu____3180, uu____3182)))
                 in
              let uu____3184 =
                let uu____3187 = arg "requested-info"  in
                FStar_All.pipe_right uu____3187 (js_list js_str)  in
              (uu____3094, uu____3096, uu____3102, uu____3184)  in
            Lookup uu____3081
        | "compute" ->
            let uu____3200 =
              let uu____3209 =
                let uu____3210 = arg "term"  in
                FStar_All.pipe_right uu____3210 js_str  in
              let uu____3211 =
                let uu____3216 = try_arg "rules"  in
                FStar_All.pipe_right uu____3216
                  (FStar_Util.map_option (js_list js_reductionrule))
                 in
              (uu____3209, uu____3211)  in
            Compute uu____3200
        | "search" ->
            let uu____3231 =
              let uu____3232 = arg "terms"  in
              FStar_All.pipe_right uu____3232 js_str  in
            Search uu____3231
        | "vfs-add" ->
            let uu____3233 =
              let uu____3240 =
                let uu____3243 = try_arg "filename"  in
                FStar_All.pipe_right uu____3243
                  (FStar_Util.map_option js_str)
                 in
              let uu____3250 =
                let uu____3251 = arg "contents"  in
                FStar_All.pipe_right uu____3251 js_str  in
              (uu____3240, uu____3250)  in
            VfsAdd uu____3233
        | uu____3254 ->
            let uu____3255 = FStar_Util.format1 "Unknown query '%s'" query
               in
            ProtocolViolation uu____3255
         in
      { qq = uu____3047; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let read_interactive_query : FStar_Util.stream_reader -> query =
  fun stream  ->
    try
      let uu____3268 = FStar_Util.read_line stream  in
      match uu____3268 with
      | FStar_Pervasives_Native.None  ->
          FStar_Exn.raise (ExitREPL (Prims.parse_int "0"))
      | FStar_Pervasives_Native.Some line ->
          let uu____3272 = FStar_Util.json_of_string line  in
          (match uu____3272 with
           | FStar_Pervasives_Native.None  ->
               { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
           | FStar_Pervasives_Native.Some request ->
               unpack_interactive_query request)
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let json_of_opt :
  'Auu____3285 .
    ('Auu____3285 -> FStar_Util.json) ->
      'Auu____3285 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____3303 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____3303
  
let json_of_pos : FStar_Range.pos -> FStar_Util.json =
  fun pos  ->
    let uu____3309 =
      let uu____3312 =
        let uu____3313 = FStar_Range.line_of_pos pos  in
        FStar_Util.JsonInt uu____3313  in
      let uu____3314 =
        let uu____3317 =
          let uu____3318 = FStar_Range.col_of_pos pos  in
          FStar_Util.JsonInt uu____3318  in
        [uu____3317]  in
      uu____3312 :: uu____3314  in
    FStar_Util.JsonList uu____3309
  
let json_of_range_fields :
  Prims.string -> FStar_Range.pos -> FStar_Range.pos -> FStar_Util.json =
  fun file  ->
    fun b  ->
      fun e  ->
        let uu____3328 =
          let uu____3335 =
            let uu____3342 =
              let uu____3347 = json_of_pos b  in ("beg", uu____3347)  in
            let uu____3348 =
              let uu____3355 =
                let uu____3360 = json_of_pos e  in ("end", uu____3360)  in
              [uu____3355]  in
            uu____3342 :: uu____3348  in
          ("fname", (FStar_Util.JsonStr file)) :: uu____3335  in
        FStar_Util.JsonAssoc uu____3328
  
let json_of_use_range : FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3380 = FStar_Range.file_of_use_range r  in
    let uu____3381 = FStar_Range.start_of_use_range r  in
    let uu____3382 = FStar_Range.end_of_use_range r  in
    json_of_range_fields uu____3380 uu____3381 uu____3382
  
let json_of_def_range : FStar_Range.range -> FStar_Util.json =
  fun r  ->
    let uu____3386 = FStar_Range.file_of_range r  in
    let uu____3387 = FStar_Range.start_of_range r  in
    let uu____3388 = FStar_Range.end_of_range r  in
    json_of_range_fields uu____3386 uu____3387 uu____3388
  
let json_of_issue_level : FStar_Errors.issue_level -> FStar_Util.json =
  fun i  ->
    FStar_Util.JsonStr
      (match i with
       | FStar_Errors.ENotImplemented  -> "not-implemented"
       | FStar_Errors.EInfo  -> "info"
       | FStar_Errors.EWarning  -> "warning"
       | FStar_Errors.EError  -> "error")
  
let json_of_issue : FStar_Errors.issue -> FStar_Util.json =
  fun issue  ->
    let uu____3395 =
      let uu____3402 =
        let uu____3409 =
          let uu____3416 =
            let uu____3421 =
              let uu____3422 =
                let uu____3425 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3431 = json_of_use_range r  in [uu____3431]
                   in
                let uu____3432 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3438 = FStar_Range.def_range r  in
                      let uu____3439 = FStar_Range.use_range r  in
                      uu____3438 <> uu____3439 ->
                      let uu____3440 = json_of_def_range r  in [uu____3440]
                  | uu____3441 -> []  in
                FStar_List.append uu____3425 uu____3432  in
              FStar_Util.JsonList uu____3422  in
            ("ranges", uu____3421)  in
          [uu____3416]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3409
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3402
       in
    FStar_Util.JsonAssoc uu____3395
  
type symbol_lookup_result =
  {
  slr_name: Prims.string ;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }[@@deriving show]
let __proj__Mksymbol_lookup_result__item__slr_name :
  symbol_lookup_result -> Prims.string =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_name
  
let __proj__Mksymbol_lookup_result__item__slr_def_range :
  symbol_lookup_result -> FStar_Range.range FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def_range
  
let __proj__Mksymbol_lookup_result__item__slr_typ :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_typ
  
let __proj__Mksymbol_lookup_result__item__slr_doc :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_doc
  
let __proj__Mksymbol_lookup_result__item__slr_def :
  symbol_lookup_result -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { slr_name = __fname__slr_name; slr_def_range = __fname__slr_def_range;
        slr_typ = __fname__slr_typ; slr_doc = __fname__slr_doc;
        slr_def = __fname__slr_def;_} -> __fname__slr_def
  
let alist_of_symbol_lookup_result :
  symbol_lookup_result ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun lr  ->
    let uu____3593 =
      let uu____3600 =
        let uu____3605 = json_of_opt json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____3605)  in
      let uu____3606 =
        let uu____3613 =
          let uu____3618 =
            json_of_opt (fun _0_65  -> FStar_Util.JsonStr _0_65) lr.slr_typ
             in
          ("type", uu____3618)  in
        let uu____3619 =
          let uu____3626 =
            let uu____3631 =
              json_of_opt (fun _0_66  -> FStar_Util.JsonStr _0_66) lr.slr_doc
               in
            ("documentation", uu____3631)  in
          let uu____3632 =
            let uu____3639 =
              let uu____3644 =
                json_of_opt (fun _0_67  -> FStar_Util.JsonStr _0_67)
                  lr.slr_def
                 in
              ("definition", uu____3644)  in
            [uu____3639]  in
          uu____3626 :: uu____3632  in
        uu____3613 :: uu____3619  in
      uu____3600 :: uu____3606  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____3593
  
let alist_of_protocol_info :
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____3677 =
      FStar_List.map (fun _0_68  -> FStar_Util.JsonStr _0_68)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _0_69  -> FStar_Util.JsonList _0_69) uu____3677
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly [@@deriving show]
let uu___is_OptSet : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3697 -> false
  
let uu___is_OptReset : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3701 -> false
  
let uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3705 -> false
  
let string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string =
  fun uu___379_3708  ->
    match uu___379_3708 with
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
  opt_permission_level: fstar_option_permission_level }[@@deriving show]
let __proj__Mkfstar_option__item__opt_name : fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_name
  
let __proj__Mkfstar_option__item__opt_sig : fstar_option -> Prims.string =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_sig
  
let __proj__Mkfstar_option__item__opt_value :
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_value
  
let __proj__Mkfstar_option__item__opt_default :
  fstar_option -> FStar_Options.option_val =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_default
  
let __proj__Mkfstar_option__item__opt_type :
  fstar_option -> FStar_Options.opt_type =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_type
  
let __proj__Mkfstar_option__item__opt_snippets :
  fstar_option -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_snippets
  
let __proj__Mkfstar_option__item__opt_documentation :
  fstar_option -> Prims.string FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_documentation
  
let __proj__Mkfstar_option__item__opt_permission_level :
  fstar_option -> fstar_option_permission_level =
  fun projectee  ->
    match projectee with
    | { opt_name = __fname__opt_name; opt_sig = __fname__opt_sig;
        opt_value = __fname__opt_value; opt_default = __fname__opt_default;
        opt_type = __fname__opt_type; opt_snippets = __fname__opt_snippets;
        opt_documentation = __fname__opt_documentation;
        opt_permission_level = __fname__opt_permission_level;_} ->
        __fname__opt_permission_level
  
let rec kind_of_fstar_option_type : FStar_Options.opt_type -> Prims.string =
  fun uu___380_3875  ->
    match uu___380_3875 with
    | FStar_Options.Const uu____3876 -> "flag"
    | FStar_Options.IntStr uu____3877 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____3878 -> "path"
    | FStar_Options.SimpleStr uu____3879 -> "string"
    | FStar_Options.EnumStr uu____3880 -> "enum"
    | FStar_Options.OpenEnumStr uu____3883 -> "open enum"
    | FStar_Options.PostProcessed (uu____3890,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____3898,typ) ->
        kind_of_fstar_option_type typ
  
let rec snippets_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string Prims.list =
  fun name  ->
    fun typ  ->
      let mk_field field_name =
        Prims.strcat "${" (Prims.strcat field_name "}")  in
      let mk_snippet name1 argstring =
        Prims.strcat "--"
          (Prims.strcat name1
             (if argstring <> "" then Prims.strcat " " argstring else ""))
         in
      let rec arg_snippets_of_type typ1 =
        match typ1 with
        | FStar_Options.Const uu____3932 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____3945,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____3953,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____3959 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____3959
  
let rec json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___381_3964  ->
    match uu___381_3964 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____3972 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____3972
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let alist_of_fstar_option :
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____3984 =
      let uu____3991 =
        let uu____3998 =
          let uu____4003 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____4003)  in
        let uu____4004 =
          let uu____4011 =
            let uu____4016 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____4016)  in
          let uu____4017 =
            let uu____4024 =
              let uu____4029 =
                json_of_opt (fun _0_70  -> FStar_Util.JsonStr _0_70)
                  opt.opt_documentation
                 in
              ("documentation", uu____4029)  in
            let uu____4030 =
              let uu____4037 =
                let uu____4042 =
                  let uu____4043 = kind_of_fstar_option_type opt.opt_type  in
                  FStar_Util.JsonStr uu____4043  in
                ("type", uu____4042)  in
              [uu____4037;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____4024 :: uu____4030  in
          uu____4011 :: uu____4017  in
        uu____3998 :: uu____4004  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____3991  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____3984
  
let json_of_fstar_option : fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____4079 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____4079
  
let write_json : FStar_Util.json -> Prims.unit =
  fun json  ->
    (let uu____4090 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____4090);
    FStar_Util.print_raw "\n"
  
let write_response :
  Prims.string -> query_status -> FStar_Util.json -> Prims.unit =
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
        write_json
          (FStar_Util.JsonAssoc
             [("kind", (FStar_Util.JsonStr "response"));
             ("query-id", qid1);
             ("status", status1);
             ("response", response)])
  
let write_message : Prims.string -> FStar_Util.json -> Prims.unit =
  fun level  ->
    fun contents  ->
      write_json
        (FStar_Util.JsonAssoc
           [("kind", (FStar_Util.JsonStr "message"));
           ("level", (FStar_Util.JsonStr level));
           ("contents", contents)])
  
let write_hello : Prims.unit -> Prims.unit =
  fun uu____4146  ->
    let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
    let js_features =
      let uu____4149 =
        FStar_List.map (fun _0_71  -> FStar_Util.JsonStr _0_71)
          interactive_protocol_features
         in
      FStar_Util.JsonList uu____4149  in
    write_json
      (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info"))
         :: alist_of_protocol_info))
  
let sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name  in
      let uu____4163 = FStar_Options.desc_of_opt_type typ  in
      match uu____4163 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
  
let fstar_options_list_cache : fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____4172 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4201  ->
            match uu____4201 with
            | (_shortname,name,typ,doc1) ->
                let uu____4216 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____4216
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____4228 = sig_of_fstar_option name typ  in
                        let uu____4229 = snippets_of_fstar_option name typ
                           in
                        let uu____4232 =
                          let uu____4233 = FStar_Options.settable name  in
                          if uu____4233
                          then OptSet
                          else
                            (let uu____4235 = FStar_Options.resettable name
                                in
                             if uu____4235 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____4228;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4229;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4232
                        }))))
     in
  FStar_All.pipe_right uu____4172
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
  
let fstar_options_map_cache : fstar_option FStar_Util.smap =
  let cache = FStar_Util.smap_create (Prims.parse_int "50")  in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache 
let update_option : fstar_option -> fstar_option =
  fun opt  ->
    let uu___395_4259 = opt  in
    let uu____4260 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___395_4259.opt_name);
      opt_sig = (uu___395_4259.opt_sig);
      opt_value = uu____4260;
      opt_default = (uu___395_4259.opt_default);
      opt_type = (uu___395_4259.opt_type);
      opt_snippets = (uu___395_4259.opt_snippets);
      opt_documentation = (uu___395_4259.opt_documentation);
      opt_permission_level = (uu___395_4259.opt_permission_level)
    }
  
let current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____4271 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____4271
  
let trim_option_name :
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4286 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____4286)
    else ("", opt_name)
  
let json_of_repl_state : repl_state -> FStar_Util.json =
  fun st  ->
    let filenames uu____4300 =
      match uu____4300 with
      | (task,uu____4308) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | PushFragment uu____4315 -> [])
       in
    let uu____4316 =
      let uu____4323 =
        let uu____4328 =
          let uu____4329 =
            let uu____4332 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _0_72  -> FStar_Util.JsonStr _0_72)
              uu____4332
             in
          FStar_Util.JsonList uu____4329  in
        ("loaded-dependencies", uu____4328)  in
      let uu____4339 =
        let uu____4346 =
          let uu____4351 =
            let uu____4352 =
              let uu____4355 =
                current_fstar_options (fun uu____4360  -> true)  in
              FStar_List.map json_of_fstar_option uu____4355  in
            FStar_Util.JsonList uu____4352  in
          ("options", uu____4351)  in
        [uu____4346]  in
      uu____4323 :: uu____4339  in
    FStar_Util.JsonAssoc uu____4316
  
let with_printed_effect_args :
  'Auu____4375 . (Prims.unit -> 'Auu____4375) -> 'Auu____4375 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4387  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4396  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4401  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____4405 'Auu____4406 .
    'Auu____4406 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4405,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inr (Prims.parse_int "0")))
  
let run_describe_protocol :
  'Auu____4434 'Auu____4435 .
    'Auu____4435 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4435,'Auu____4434) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____4462 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4462) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4479 =
      let uu____4484 = json_of_repl_state st  in (QueryOK, uu____4484)  in
    (uu____4479, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____4497 'Auu____4498 .
    'Auu____4498 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4498,'Auu____4497) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____4531 'Auu____4532 .
    'Auu____4532 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4532,'Auu____4531) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let collect_errors : Prims.unit -> FStar_Errors.issue Prims.list =
  fun uu____4565  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____4573 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4573) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun code  ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.parse_int "1");
          FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")
        }  in
      let collect_decls uu____4600 =
        let uu____4601 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____4601 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4607,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4613,decls,uu____4615)) -> decls
         in
      let uu____4620 =
        with_captured_errors st.repl_env
          (fun uu____4629  ->
             let uu____4630 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _0_73  -> FStar_Pervasives_Native.Some _0_73) uu____4630)
         in
      match uu____4620 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____4658 = collect_errors ()  in
            FStar_All.pipe_right uu____4658 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____4682 =
              let uu____4689 =
                let uu____4694 =
                  json_of_def_range (FStar_Parser_AST.decl_drange decl)  in
                ("def_range", uu____4694)  in
              [uu____4689]  in
            FStar_Util.JsonAssoc uu____4682  in
          let js_decls =
            let uu____4704 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _0_74  -> FStar_Util.JsonList _0_74)
              uu____4704
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____4729 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____4729) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____4770 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4770) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4787 = nothing_left_to_pop st  in
    if uu____4787
    then
      ((QueryNOK, (FStar_Util.JsonStr "Too many pops")), (FStar_Util.Inl st))
    else
      (let st' = pop_repl st  in
       ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st')))
  
let load_deps :
  repl_state ->
    ((repl_state,Prims.string Prims.list) FStar_Pervasives_Native.tuple2,
      repl_state) FStar_Util.either
  =
  fun st  ->
    let uu____4831 =
      with_captured_errors st.repl_env
        (fun _env  ->
           let uu____4857 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _0_75  -> FStar_Pervasives_Native.Some _0_75) uu____4857)
       in
    match uu____4831 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___396_4948 = st  in
          let uu____4949 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___396_4948.repl_line);
            repl_column = (uu___396_4948.repl_column);
            repl_fname = (uu___396_4948.repl_fname);
            repl_deps_stack = (uu___396_4948.repl_deps_stack);
            repl_curmod = (uu___396_4948.repl_curmod);
            repl_env = uu____4949;
            repl_stdin = (uu___396_4948.repl_stdin);
            repl_names = (uu___396_4948.repl_names)
          }  in
        let uu____4950 = run_repl_ld_transactions st1 tasks  in
        (match uu____4950 with
         | FStar_Util.Inr st2 -> FStar_Util.Inr st2
         | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps))
  
let rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___397_4984 = issue  in
    let uu____4985 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____4985;
      FStar_Errors.issue_level = (uu___397_4984.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___397_4984.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___397_4984.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____4989 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4989) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___398_5017 = st1  in
        {
          repl_line = (uu___398_5017.repl_line);
          repl_column = (uu___398_5017.repl_column);
          repl_fname = (uu___398_5017.repl_fname);
          repl_deps_stack = (uu___398_5017.repl_deps_stack);
          repl_curmod = (uu___398_5017.repl_curmod);
          repl_env =
            (let uu___399_5019 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___399_5019.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___399_5019.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___399_5019.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___399_5019.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___399_5019.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___399_5019.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___399_5019.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___399_5019.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___399_5019.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___399_5019.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___399_5019.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___399_5019.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___399_5019.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___399_5019.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___399_5019.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___399_5019.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___399_5019.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___399_5019.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___399_5019.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___399_5019.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___399_5019.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.tc_term =
                 (uu___399_5019.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___399_5019.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___399_5019.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___399_5019.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qname_and_index =
                 (uu___399_5019.FStar_TypeChecker_Env.qname_and_index);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___399_5019.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth =
                 (uu___399_5019.FStar_TypeChecker_Env.synth);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___399_5019.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___399_5019.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___399_5019.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___399_5019.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.dep_graph =
                 (uu___399_5019.FStar_TypeChecker_Env.dep_graph)
             });
          repl_stdin = (uu___398_5017.repl_stdin);
          repl_names = (uu___398_5017.repl_names)
        }  in
      let uu____5020 = query  in
      match uu____5020 with
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
            let uu____5041 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____5041 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____5064 =
                    let uu____5067 = collect_errors ()  in
                    FStar_All.pipe_right uu____5067
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____5064  in
                let st4 =
                  if success
                  then
                    let uu___400_5075 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___400_5075.repl_fname);
                      repl_deps_stack = (uu___400_5075.repl_deps_stack);
                      repl_curmod = (uu___400_5075.repl_curmod);
                      repl_env = (uu___400_5075.repl_env);
                      repl_stdin = (uu___400_5075.repl_stdin);
                      repl_names = (uu___400_5075.repl_names)
                    }
                  else st3  in
                ((status, json_errors), (FStar_Util.Inl st4))))
  
let capitalize : Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.parse_int "0")
           (Prims.parse_int "1")
          in
       let uu____5090 =
         FStar_String.substring str (Prims.parse_int "1")
           ((FStar_String.length str) - (Prims.parse_int "1"))
          in
       Prims.strcat (FStar_String.uppercase first) uu____5090)
  
let add_module_completions :
  Prims.string ->
    Prims.string Prims.list ->
      FStar_Interactive_CompletionTable.table ->
        FStar_Interactive_CompletionTable.table
  =
  fun this_fname  ->
    fun deps  ->
      fun table  ->
        let mods = FStar_Parser_Dep.build_inclusion_candidates_list ()  in
        let loaded_mods_set =
          let uu____5114 = FStar_Util.psmap_empty ()  in
          let uu____5117 =
            let uu____5120 = FStar_Options.prims ()  in uu____5120 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____5130 = FStar_Parser_Dep.lowercase_module_name dep1
                    in
                 FStar_Util.psmap_add acc uu____5130 true) uu____5114
            uu____5117
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____5146  ->
               match uu____5146 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____5158 = capitalize modname  in
                        FStar_Util.split uu____5158 "."  in
                      let uu____5159 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____5159 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____5167 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5167) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      (let uu____5189 = FStar_Options.debug_any ()  in
       if uu____5189
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____5192 = load_deps st  in
       match uu____5192 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5225 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____5225  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____5256 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____5256 FStar_Pervasives.ignore);
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___401_5259 = st1  in
                {
                  repl_line = (uu___401_5259.repl_line);
                  repl_column = (uu___401_5259.repl_column);
                  repl_fname = (uu___401_5259.repl_fname);
                  repl_deps_stack = (uu___401_5259.repl_deps_stack);
                  repl_curmod = (uu___401_5259.repl_curmod);
                  repl_env = (uu___401_5259.repl_env);
                  repl_stdin = (uu___401_5259.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____5263 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5263) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5284 = nothing_left_to_pop st  in
      if uu____5284
      then run_push_with_deps st query
      else run_push_without_deps st query
  
let run_symbol_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let tcenv = st.repl_env  in
          let info_of_lid_str lid_str =
            let lid =
              let uu____5362 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____5362  in
            let lid1 =
              let uu____5366 =
                FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____5366  in
            let uu____5371 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____5371
              (FStar_Util.map_option
                 (fun uu____5426  ->
                    match uu____5426 with
                    | ((uu____5445,typ),r) -> ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____5462 =
              FStar_ToSyntax_Env.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____5462
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____5491 = FStar_TypeChecker_Env.lookup_qname tcenv lid  in
            FStar_Util.bind_opt uu____5491
              (fun uu___382_5535  ->
                 match uu___382_5535 with
                 | (FStar_Util.Inr (se,uu____5557),uu____5558) ->
                     let uu____5587 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____5587
                 | uu____5588 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____5640  ->
                 match uu____5640 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____5687 -> info_at_pos_opt
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
                    let uu____5815 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____5815
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____5823 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____5834 -> FStar_Pervasives_Native.None  in
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
                let uu____5846 =
                  let uu____5857 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____5857)  in
                FStar_Pervasives_Native.Some uu____5846
             in
          match response with
          | FStar_Pervasives_Native.None  ->
              FStar_Util.Inl "Symbol not found"
          | FStar_Pervasives_Native.Some info -> FStar_Util.Inr info
  
let run_option_lookup :
  Prims.string ->
    (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                  FStar_Pervasives_Native.tuple2 Prims.list)
                    FStar_Pervasives_Native.tuple2)
      FStar_Util.either
  =
  fun opt_name  ->
    let uu____5962 = trim_option_name opt_name  in
    match uu____5962 with
    | (uu____5981,trimmed_name) ->
        let uu____5983 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____5983 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____6011 =
               let uu____6022 =
                 let uu____6029 = update_option opt  in
                 alist_of_fstar_option uu____6029  in
               ("option", uu____6022)  in
             FStar_Util.Inr uu____6011)
  
let run_module_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                    FStar_Pervasives_Native.tuple2 Prims.list)
                      FStar_Pervasives_Native.tuple2)
        FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      let query = FStar_Util.split symbol "."  in
      let uu____6069 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____6069 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6097 =
            let uu____6108 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____6108)  in
          FStar_Util.Inr uu____6097
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6132 =
            let uu____6143 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____6143)  in
          FStar_Util.Inr uu____6132
  
let run_code_lookup :
  repl_state ->
    Prims.string ->
      (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
        FStar_Pervasives_Native.option ->
        Prims.string Prims.list ->
          (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
                          FStar_Pervasives_Native.tuple2)
            FStar_Util.either
  =
  fun st  ->
    fun symbol  ->
      fun pos_opt  ->
        fun requested_info  ->
          let uu____6212 = run_symbol_lookup st symbol pos_opt requested_info
             in
          match uu____6212 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6272 ->
              let uu____6283 = run_module_lookup st symbol  in
              (match uu____6283 with
               | FStar_Util.Inr alist -> FStar_Util.Inr alist
               | FStar_Util.Inl err_msg ->
                   FStar_Util.Inl "No such symbol, module, or namespace.")
  
let run_lookup' :
  repl_state ->
    Prims.string ->
      lookup_context ->
        (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
          FStar_Pervasives_Native.option ->
          Prims.string Prims.list ->
            (Prims.string,(Prims.string,(Prims.string,FStar_Util.json)
                                          FStar_Pervasives_Native.tuple2
                                          Prims.list)
                            FStar_Pervasives_Native.tuple2)
              FStar_Util.either
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
  'Auu____6433 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6433) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6486 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____6486 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____6570 .
    ('Auu____6570,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____6570,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___383_6584  ->
    match uu___383_6584 with
    | (uu____6589,FStar_Interactive_CompletionTable.Namespace uu____6590) ->
        FStar_Pervasives_Native.None
    | (uu____6595,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____6596;
         FStar_Interactive_CompletionTable.mod_path = uu____6597;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____6604 =
          let uu____6609 =
            let uu____6610 =
              let uu___402_6611 = md  in
              let uu____6612 =
                let uu____6613 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.strcat uu____6613 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____6612;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___402_6611.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___402_6611.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____6610  in
          (pth, uu____6609)  in
        FStar_Pervasives_Native.Some uu____6604
  
let run_code_autocomplete :
  'Auu____6621 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____6621) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
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
  'Auu____6669 'Auu____6670 'Auu____6671 .
    repl_state ->
      Prims.string ->
        'Auu____6671 ->
          'Auu____6670 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____6669) FStar_Util.either)
              FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun modules1  ->
        fun namespaces  ->
          let needle = FStar_Util.split search_term "."  in
          let mods_and_nss =
            FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
              st.repl_names needle
              (fun _0_76  -> FStar_Pervasives_Native.Some _0_76)
             in
          let json =
            FStar_List.map
              FStar_Interactive_CompletionTable.json_of_completion_result
              mods_and_nss
             in
          ((QueryOK, (FStar_Util.JsonList json)), (FStar_Util.Inl st))
  
let candidates_of_fstar_option :
  Prims.int ->
    Prims.bool ->
      fstar_option ->
        FStar_Interactive_CompletionTable.completion_result Prims.list
  =
  fun match_len  ->
    fun is_reset  ->
      fun opt  ->
        let uu____6732 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____6732 with
        | (may_set,explanation) ->
            let opt_type = kind_of_fstar_option_type opt.opt_type  in
            let annot =
              if may_set
              then opt_type
              else
                Prims.strcat "("
                  (Prims.strcat explanation
                     (Prims.strcat " " (Prims.strcat opt_type ")")))
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
  'Auu____6759 'Auu____6760 .
    'Auu____6760 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____6760,'Auu____6759) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____6785 = trim_option_name search_term  in
        match uu____6785 with
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
        | (uu____6836,uu____6837) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____6850 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____6850) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
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
  'Auu____6882 'Auu____6883 .
    repl_state ->
      (repl_state -> 'Auu____6883) ->
        ('Auu____6883,(repl_state,'Auu____6882) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun task  ->
      let env' = push st.repl_env "#compute"  in
      let results =
        try
          let uu____6922 = task st  in
          FStar_All.pipe_left (fun _0_77  -> FStar_Util.Inl _0_77) uu____6922
        with | e -> FStar_Util.Inr e  in
      pop env' "#compute";
      (match results with
       | FStar_Util.Inl results1 -> (results1, (FStar_Util.Inl st))
       | FStar_Util.Inr e -> FStar_Exn.raise e)
  
let run_with_parsed_and_tc_term :
  'Auu____6966 'Auu____6967 'Auu____6968 .
    repl_state ->
      Prims.string ->
        'Auu____6968 ->
          'Auu____6967 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term ->
                 (query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2)
              ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6966) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
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
                    ((uu____7052,{ FStar_Syntax_Syntax.lbname = uu____7053;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____7055;
                                   FStar_Syntax_Syntax.lbeff = uu____7056;
                                   FStar_Syntax_Syntax.lbdef = def;_}::[]),uu____7058);
                  FStar_Syntax_Syntax.sigrng = uu____7059;
                  FStar_Syntax_Syntax.sigquals = uu____7060;
                  FStar_Syntax_Syntax.sigmeta = uu____7061;
                  FStar_Syntax_Syntax.sigattrs = uu____7062;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____7101 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____7120 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____7120 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____7126) ->
                  FStar_Pervasives_Native.Some decls
              | uu____7151 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____7165 =
                let uu____7170 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____7170 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____7165  in
            let typecheck tcenv decls =
              let uu____7188 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____7188 with | (ses,uu____7202,uu____7203) -> ses  in
            run_and_rewind st
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 match st1.repl_curmod with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                 | uu____7226 ->
                     let uu____7227 = parse1 frag  in
                     (match uu____7227 with
                      | FStar_Pervasives_Native.None  ->
                          (QueryNOK,
                            (FStar_Util.JsonStr "Could not parse this term"))
                      | FStar_Pervasives_Native.Some decls ->
                          let aux uu____7250 =
                            let decls1 = desugar tcenv decls  in
                            let ses = typecheck tcenv decls1  in
                            match find_let_body ses with
                            | FStar_Pervasives_Native.None  ->
                                (QueryNOK,
                                  (FStar_Util.JsonStr
                                     "Typechecking yielded an unexpected term"))
                            | FStar_Pervasives_Native.Some (univs1,def) ->
                                let uu____7285 =
                                  FStar_Syntax_Subst.open_univ_vars univs1
                                    def
                                   in
                                (match uu____7285 with
                                 | (univs2,def1) ->
                                     let tcenv1 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         tcenv univs2
                                        in
                                     continuation tcenv1 def1)
                             in
                          let uu____7297 = FStar_Options.trace_error ()  in
                          if uu____7297
                          then aux ()
                          else
                            (try aux ()
                             with
                             | e ->
                                 let uu____7322 =
                                   let uu____7323 =
                                     FStar_Errors.issue_of_exn e  in
                                   match uu____7323 with
                                   | FStar_Pervasives_Native.Some issue ->
                                       let uu____7327 =
                                         FStar_Errors.format_issue issue  in
                                       FStar_Util.JsonStr uu____7327
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Exn.raise e
                                    in
                                 (QueryNOK, uu____7322))))
  
let run_compute :
  'Auu____7332 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7332) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun term  ->
      fun rules  ->
        let rules1 =
          FStar_List.append
            (match rules with
             | FStar_Pervasives_Native.Some rules1 -> rules1
             | FStar_Pervasives_Native.None  ->
                 [FStar_TypeChecker_Normalize.Beta;
                 FStar_TypeChecker_Normalize.Iota;
                 FStar_TypeChecker_Normalize.Zeta;
                 FStar_TypeChecker_Normalize.UnfoldUntil
                   FStar_Syntax_Syntax.Delta_constant])
            [FStar_TypeChecker_Normalize.Inlining;
            FStar_TypeChecker_Normalize.Eager_unfolding;
            FStar_TypeChecker_Normalize.Primops]
           in
        let normalize_term1 tcenv rules2 t =
          FStar_TypeChecker_Normalize.normalize rules2 tcenv t  in
        run_with_parsed_and_tc_term st term (Prims.parse_int "0")
          (Prims.parse_int "0")
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term1 tcenv rules1 def  in
               let uu____7395 =
                 let uu____7396 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____7396  in
               (QueryOK, uu____7395))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid [@@deriving show]
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }[@@deriving show]
let uu___is_NameContainsStr : search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7417 -> false
  
let __proj__NameContainsStr__item___0 : search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let uu___is_TypeContainsLid : search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7429 -> false
  
let __proj__TypeContainsLid__item___0 : search_term' -> FStar_Ident.lid =
  fun projectee  -> match projectee with | TypeContainsLid _0 -> _0 
let __proj__Mksearch_term__item__st_negate : search_term -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_negate
  
let __proj__Mksearch_term__item__st_term : search_term -> search_term' =
  fun projectee  ->
    match projectee with
    | { st_negate = __fname__st_negate; st_term = __fname__st_term;_} ->
        __fname__st_term
  
let st_cost : search_term' -> Prims.int =
  fun uu___384_7449  ->
    match uu___384_7449 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> (Prims.parse_int "1")
  
type search_candidate =
  {
  sc_lid: FStar_Ident.lid ;
  sc_typ: FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref ;
  sc_fvars:
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
    }[@@deriving show]
let __proj__Mksearch_candidate__item__sc_lid :
  search_candidate -> FStar_Ident.lid =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_lid
  
let __proj__Mksearch_candidate__item__sc_typ :
  search_candidate ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_typ
  
let __proj__Mksearch_candidate__item__sc_fvars :
  search_candidate ->
    FStar_Ident.lid FStar_Util.set FStar_Pervasives_Native.option
      FStar_ST.ref
  =
  fun projectee  ->
    match projectee with
    | { sc_lid = __fname__sc_lid; sc_typ = __fname__sc_typ;
        sc_fvars = __fname__sc_fvars;_} -> __fname__sc_fvars
  
let sc_of_lid : FStar_Ident.lid -> search_candidate =
  fun lid  ->
    let uu____7613 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____7620 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____7613; sc_fvars = uu____7620 }
  
let sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____7667 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____7667 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____7726 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____7726 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____7747,typ),uu____7749) ->
                typ
             in
          (FStar_ST.op_Colon_Equals sc.sc_typ
             (FStar_Pervasives_Native.Some typ);
           typ)
  
let sc_fvars :
  FStar_TypeChecker_Env.env ->
    search_candidate -> FStar_Ident.lid FStar_Util.set
  =
  fun tcenv  ->
    fun sc  ->
      let uu____7825 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____7825 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____7898 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____7898  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____7965 = sc_typ tcenv sc  in term_to_string tcenv uu____7965
         in
      let uu____7966 =
        let uu____7973 =
          let uu____7978 =
            let uu____7979 =
              let uu____7980 =
                FStar_ToSyntax_Env.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____7980.FStar_Ident.str  in
            FStar_Util.JsonStr uu____7979  in
          ("lid", uu____7978)  in
        [uu____7973; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____7966
  
exception InvalidSearch of Prims.string 
let uu___is_InvalidSearch : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____7999 -> true
    | uu____8000 -> false
  
let __proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____8007 -> uu____8007
  
let run_search :
  'Auu____8011 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____8011) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
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
              let uu____8046 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____8046
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
              let uu____8070 =
                let uu____8071 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____8071  in
              FStar_Exn.raise uu____8070
            else
              if beg_quote
              then
                (let uu____8073 = strip_quotes term1  in
                 NameContainsStr uu____8073)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____8076 =
                   FStar_ToSyntax_Env.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____8076 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8079 =
                       let uu____8080 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____8080  in
                     FStar_Exn.raise uu____8079
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____8096 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.strcat (if term.st_negate then "-" else "") uu____8096  in
      let results =
        try
          let terms = parse1 search_str  in
          let all_lidents = FStar_TypeChecker_Env.lidents tcenv  in
          let all_candidates = FStar_List.map sc_of_lid all_lidents  in
          let matches_all candidate =
            FStar_List.for_all (st_matches candidate) terms  in
          let cmp r1 r2 =
            FStar_Util.compare (r1.sc_lid).FStar_Ident.str
              (r2.sc_lid).FStar_Ident.str
             in
          let results = FStar_List.filter matches_all all_candidates  in
          let sorted1 = FStar_Util.sort_with cmp results  in
          let js = FStar_List.map (json_of_search_result tcenv) sorted1  in
          match results with
          | [] ->
              let kwds =
                let uu____8159 = FStar_List.map pprint_one terms  in
                FStar_Util.concat_l " " uu____8159  in
              let uu____8162 =
                let uu____8163 =
                  FStar_Util.format1 "No results found for query [%s]" kwds
                   in
                InvalidSearch uu____8163  in
              FStar_Exn.raise uu____8162
          | uu____8168 -> (QueryOK, (FStar_Util.JsonList js))
        with | InvalidSearch s -> (QueryNOK, (FStar_Util.JsonStr s))  in
      (results, (FStar_Util.Inl st))
  
let run_query :
  repl_state ->
    query' ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
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
  
let validate_query : repl_state -> query -> query =
  fun st  ->
    fun q  ->
      match q.qq with
      | Push
          { push_kind = SyntaxCheck ; push_code = uu____8258;
            push_line = uu____8259; push_column = uu____8260;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8261 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____8262 -> q)
  
let rec go : repl_state -> Prims.int =
  fun st  ->
    let rec loop st1 =
      let query =
        let uu____8271 = read_interactive_query st1.repl_stdin  in
        validate_query st1 uu____8271  in
      let uu____8272 = run_query st1 query.qq  in
      match uu____8272 with
      | ((status,response),state_opt) ->
          (write_response query.qid status response;
           (match state_opt with
            | FStar_Util.Inl st' -> loop st'
            | FStar_Util.Inr exitcode -> FStar_Exn.raise (ExitREPL exitcode)))
       in
    let uu____8303 = FStar_Options.trace_error ()  in
    if uu____8303 then loop st else (try loop st with | ExitREPL n1 -> n1)
  
let interactive_error_handler : FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____8322 =
      let uu____8325 = FStar_ST.op_Bang issues  in e :: uu____8325  in
    FStar_ST.op_Colon_Equals issues uu____8322  in
  let count_errors uu____8463 =
    let uu____8464 =
      let uu____8467 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____8467
       in
    FStar_List.length uu____8464  in
  let report1 uu____8543 =
    let uu____8544 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____8544  in
  let clear1 uu____8616 = FStar_ST.op_Colon_Equals issues []  in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report1;
    FStar_Errors.eh_clear = clear1
  } 
let interactive_printer : FStar_Util.printer =
  {
    FStar_Util.printer_prinfo =
      (fun s  -> write_message "info" (FStar_Util.JsonStr s));
    FStar_Util.printer_prwarning =
      (fun s  -> write_message "warning" (FStar_Util.JsonStr s));
    FStar_Util.printer_prerror =
      (fun s  -> write_message "error" (FStar_Util.JsonStr s));
    FStar_Util.printer_prgeneric =
      (fun label1  ->
         fun get_string  ->
           fun get_json  ->
             let uu____8705 = get_json ()  in write_message label1 uu____8705)
  } 
let initial_range : FStar_Range.range =
  let uu____8706 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  let uu____8707 =
    FStar_Range.mk_pos (Prims.parse_int "1") (Prims.parse_int "0")  in
  FStar_Range.mk_range "<input>" uu____8706 uu____8707 
let interactive_mode' : Prims.string -> Prims.unit =
  fun filename  ->
    write_hello ();
    (let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
     let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
     let init_st =
       let uu____8715 = FStar_Util.open_stdin ()  in
       {
         repl_line = (Prims.parse_int "1");
         repl_column = (Prims.parse_int "0");
         repl_fname = filename;
         repl_deps_stack = [];
         repl_curmod = FStar_Pervasives_Native.None;
         repl_env = env1;
         repl_stdin = uu____8715;
         repl_names = FStar_Interactive_CompletionTable.empty
       }  in
     let exit_code =
       let uu____8721 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____8721
       then
         let uu____8722 =
           let uu____8723 = FStar_Options.file_list ()  in
           FStar_List.hd uu____8723  in
         FStar_SMTEncoding_Solver.with_hints_db uu____8722
           (fun uu____8727  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let interactive_mode : Prims.string -> Prims.unit =
  fun filename  ->
    FStar_Util.set_printer interactive_printer;
    (let uu____8734 =
       let uu____8735 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____8735  in
     if uu____8734
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let uu____8739 = FStar_Options.trace_error ()  in
     if uu____8739
     then interactive_mode' filename
     else
       (try
          FStar_Errors.set_handler interactive_error_handler;
          interactive_mode' filename
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))
  
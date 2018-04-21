open Prims
let push :
  FStar_TypeChecker_Env.env -> Prims.string -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun msg  ->
      let res = FStar_Universal.push_context env msg  in
      FStar_Options.push (); res
  
let pop : FStar_TypeChecker_Env.env -> Prims.string -> unit =
  fun env  ->
    fun msg  -> FStar_Universal.pop_context env msg; FStar_Options.pop ()
  
type push_kind =
  | SyntaxCheck 
  | LaxCheck 
  | FullCheck [@@deriving show]
let uu___is_SyntaxCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | SyntaxCheck  -> true | uu____29 -> false
  
let uu___is_LaxCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | LaxCheck  -> true | uu____35 -> false
  
let uu___is_FullCheck : push_kind -> Prims.bool =
  fun projectee  ->
    match projectee with | FullCheck  -> true | uu____41 -> false
  
let set_check_kind :
  FStar_TypeChecker_Env.env -> push_kind -> FStar_TypeChecker_Env.env =
  fun env  ->
    fun check_kind  ->
      let uu___88_52 = env  in
      let uu____53 =
        FStar_Syntax_DsEnv.set_syntax_only env.FStar_TypeChecker_Env.dsenv
          (check_kind = SyntaxCheck)
         in
      {
        FStar_TypeChecker_Env.solver =
          (uu___88_52.FStar_TypeChecker_Env.solver);
        FStar_TypeChecker_Env.range =
          (uu___88_52.FStar_TypeChecker_Env.range);
        FStar_TypeChecker_Env.curmodule =
          (uu___88_52.FStar_TypeChecker_Env.curmodule);
        FStar_TypeChecker_Env.gamma =
          (uu___88_52.FStar_TypeChecker_Env.gamma);
        FStar_TypeChecker_Env.gamma_cache =
          (uu___88_52.FStar_TypeChecker_Env.gamma_cache);
        FStar_TypeChecker_Env.modules =
          (uu___88_52.FStar_TypeChecker_Env.modules);
        FStar_TypeChecker_Env.expected_typ =
          (uu___88_52.FStar_TypeChecker_Env.expected_typ);
        FStar_TypeChecker_Env.sigtab =
          (uu___88_52.FStar_TypeChecker_Env.sigtab);
        FStar_TypeChecker_Env.is_pattern =
          (uu___88_52.FStar_TypeChecker_Env.is_pattern);
        FStar_TypeChecker_Env.instantiate_imp =
          (uu___88_52.FStar_TypeChecker_Env.instantiate_imp);
        FStar_TypeChecker_Env.effects =
          (uu___88_52.FStar_TypeChecker_Env.effects);
        FStar_TypeChecker_Env.generalize =
          (uu___88_52.FStar_TypeChecker_Env.generalize);
        FStar_TypeChecker_Env.letrecs =
          (uu___88_52.FStar_TypeChecker_Env.letrecs);
        FStar_TypeChecker_Env.top_level =
          (uu___88_52.FStar_TypeChecker_Env.top_level);
        FStar_TypeChecker_Env.check_uvars =
          (uu___88_52.FStar_TypeChecker_Env.check_uvars);
        FStar_TypeChecker_Env.use_eq =
          (uu___88_52.FStar_TypeChecker_Env.use_eq);
        FStar_TypeChecker_Env.is_iface =
          (uu___88_52.FStar_TypeChecker_Env.is_iface);
        FStar_TypeChecker_Env.admit =
          (uu___88_52.FStar_TypeChecker_Env.admit);
        FStar_TypeChecker_Env.lax = (check_kind = LaxCheck);
        FStar_TypeChecker_Env.lax_universes =
          (uu___88_52.FStar_TypeChecker_Env.lax_universes);
        FStar_TypeChecker_Env.failhard =
          (uu___88_52.FStar_TypeChecker_Env.failhard);
        FStar_TypeChecker_Env.nosynth =
          (uu___88_52.FStar_TypeChecker_Env.nosynth);
        FStar_TypeChecker_Env.tc_term =
          (uu___88_52.FStar_TypeChecker_Env.tc_term);
        FStar_TypeChecker_Env.type_of =
          (uu___88_52.FStar_TypeChecker_Env.type_of);
        FStar_TypeChecker_Env.universe_of =
          (uu___88_52.FStar_TypeChecker_Env.universe_of);
        FStar_TypeChecker_Env.check_type_of =
          (uu___88_52.FStar_TypeChecker_Env.check_type_of);
        FStar_TypeChecker_Env.use_bv_sorts =
          (uu___88_52.FStar_TypeChecker_Env.use_bv_sorts);
        FStar_TypeChecker_Env.qtbl_name_and_index =
          (uu___88_52.FStar_TypeChecker_Env.qtbl_name_and_index);
        FStar_TypeChecker_Env.normalized_eff_names =
          (uu___88_52.FStar_TypeChecker_Env.normalized_eff_names);
        FStar_TypeChecker_Env.proof_ns =
          (uu___88_52.FStar_TypeChecker_Env.proof_ns);
        FStar_TypeChecker_Env.synth_hook =
          (uu___88_52.FStar_TypeChecker_Env.synth_hook);
        FStar_TypeChecker_Env.splice =
          (uu___88_52.FStar_TypeChecker_Env.splice);
        FStar_TypeChecker_Env.is_native_tactic =
          (uu___88_52.FStar_TypeChecker_Env.is_native_tactic);
        FStar_TypeChecker_Env.identifier_info =
          (uu___88_52.FStar_TypeChecker_Env.identifier_info);
        FStar_TypeChecker_Env.tc_hooks =
          (uu___88_52.FStar_TypeChecker_Env.tc_hooks);
        FStar_TypeChecker_Env.dsenv = uu____53;
        FStar_TypeChecker_Env.dep_graph =
          (uu___88_52.FStar_TypeChecker_Env.dep_graph)
      }
  
let with_captured_errors' :
  'Auu____60 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env -> 'Auu____60 FStar_Pervasives_Native.option)
        -> 'Auu____60 FStar_Pervasives_Native.option
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
          ((let uu____98 = FStar_TypeChecker_Env.get_range env  in
            FStar_Errors.log_issue uu____98
              (FStar_Errors.Error_IDEAssertionFailure, msg1));
           FStar_Pervasives_Native.None)
      | FStar_Errors.Error (e,msg,r) ->
          (FStar_TypeChecker_Err.add_errors env [(e, msg, r)];
           FStar_Pervasives_Native.None)
      | FStar_Errors.Err (e,msg) ->
          ((let uu____118 =
              let uu____127 =
                let uu____134 = FStar_TypeChecker_Env.get_range env  in
                (e, msg, uu____134)  in
              [uu____127]  in
            FStar_TypeChecker_Err.add_errors env uu____118);
           FStar_Pervasives_Native.None)
      | FStar_Errors.Stop  -> FStar_Pervasives_Native.None
  
let with_captured_errors :
  'Auu____153 .
    FStar_TypeChecker_Env.env ->
      (FStar_TypeChecker_Env.env ->
         'Auu____153 FStar_Pervasives_Native.option)
        -> 'Auu____153 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun f  ->
      let uu____175 = FStar_Options.trace_error ()  in
      if uu____175 then f env else with_captured_errors' env f
  
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
    let uu____208 =
      FStar_Parser_ParseIt.get_file_last_modification_time fname  in
    { tf_fname = fname; tf_modtime = uu____208 }
  
let dummy_tf_of_fname : Prims.string -> timed_fname =
  fun fname  -> { tf_fname = fname; tf_modtime = t0 } 
let string_of_timed_fname : timed_fname -> Prims.string =
  fun uu____218  ->
    match uu____218 with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Util.format1 "{ %s }" fname
        else
          (let uu____222 = FStar_Util.string_of_time modtime  in
           FStar_Util.format2 "{ %s; %s }" fname uu____222)
  
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
    match projectee with | LDInterleaved _0 -> true | uu____334 -> false
  
let __proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname,timed_fname) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | LDInterleaved _0 -> _0 
let uu___is_LDSingle : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | LDSingle _0 -> true | uu____360 -> false
  
let __proj__LDSingle__item___0 : repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDSingle _0 -> _0 
let uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____374 -> false
  
let __proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname =
  fun projectee  -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0 
let uu___is_PushFragment : repl_task -> Prims.bool =
  fun projectee  ->
    match projectee with | PushFragment _0 -> true | uu____388 -> false
  
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
let repl_current_qid :
  Prims.string FStar_Pervasives_Native.option FStar_ST.ref =
  FStar_Util.mk_ref FStar_Pervasives_Native.None 
let repl_stack :
  (repl_task,repl_state) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let pop_repl : repl_state -> repl_state =
  fun st  ->
    let uu____667 = FStar_ST.op_Bang repl_stack  in
    match uu____667 with
    | [] -> failwith "Too many pops"
    | (uu____713,st')::stack ->
        (pop st.repl_env "#pop";
         FStar_ST.op_Colon_Equals repl_stack stack;
         st')
  
let push_repl :
  push_kind -> repl_task -> repl_state -> FStar_TypeChecker_Env.env =
  fun push_kind  ->
    fun task  ->
      fun st  ->
        (let uu____779 =
           let uu____786 = FStar_ST.op_Bang repl_stack  in (task, st) ::
             uu____786
            in
         FStar_ST.op_Colon_Equals repl_stack uu____779);
        (let uu____867 = set_check_kind st.repl_env push_kind  in
         push uu____867 "")
  
let nothing_left_to_pop : repl_state -> Prims.bool =
  fun st  ->
    let uu____873 =
      let uu____874 = FStar_ST.op_Bang repl_stack  in
      FStar_List.length uu____874  in
    uu____873 = (FStar_List.length st.repl_deps_stack)
  
type name_tracking_event =
  | NTAlias of (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple3 
  | NTOpen of (FStar_Ident.lid,FStar_Syntax_DsEnv.open_module_or_namespace)
  FStar_Pervasives_Native.tuple2 
  | NTInclude of (FStar_Ident.lid,FStar_Ident.lid)
  FStar_Pervasives_Native.tuple2 
  | NTBinding of FStar_TypeChecker_Env.binding [@@deriving show]
let uu___is_NTAlias : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTAlias _0 -> true | uu____974 -> false
  
let __proj__NTAlias__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.ident,FStar_Ident.lid)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | NTAlias _0 -> _0 
let uu___is_NTOpen : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTOpen _0 -> true | uu____1010 -> false
  
let __proj__NTOpen__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Syntax_DsEnv.open_module_or_namespace)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTOpen _0 -> _0 
let uu___is_NTInclude : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTInclude _0 -> true | uu____1040 -> false
  
let __proj__NTInclude__item___0 :
  name_tracking_event ->
    (FStar_Ident.lid,FStar_Ident.lid) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | NTInclude _0 -> _0 
let uu___is_NTBinding : name_tracking_event -> Prims.bool =
  fun projectee  ->
    match projectee with | NTBinding _0 -> true | uu____1066 -> false
  
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
              let uu____1112 = FStar_Ident.text_of_id id1  in
              let uu____1113 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_alias table
                uu____1112 [] uu____1113
            else table
        | NTOpen (host,(included,kind)) ->
            if is_cur_mod host
            then
              let uu____1122 = query_of_lid included  in
              FStar_Interactive_CompletionTable.register_open table
                (kind = FStar_Syntax_DsEnv.Open_module) [] uu____1122
            else table
        | NTInclude (host,included) ->
            let uu____1126 =
              if is_cur_mod host then [] else query_of_lid host  in
            let uu____1128 = query_of_lid included  in
            FStar_Interactive_CompletionTable.register_include table
              uu____1126 uu____1128
        | NTBinding binding ->
            let lids =
              match binding with
              | FStar_TypeChecker_Env.Binding_lid (lid,uu____1136) -> [lid]
              | FStar_TypeChecker_Env.Binding_sig (lids,uu____1138) -> lids
              | FStar_TypeChecker_Env.Binding_sig_inst
                  (lids,uu____1144,uu____1145) -> lids
              | uu____1150 -> []  in
            FStar_List.fold_left
              (fun tbl  ->
                 fun lid  ->
                   let ns_query =
                     if lid.FStar_Ident.nsstr = cur_mod_str
                     then []
                     else query_of_ids lid.FStar_Ident.ns  in
                   let uu____1163 =
                     FStar_Ident.text_of_id lid.FStar_Ident.ident  in
                   FStar_Interactive_CompletionTable.insert tbl ns_query
                     uu____1163 lid) table lids
  
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
              let uu____1189 = FStar_Syntax_Syntax.mod_name md  in
              uu____1189.FStar_Ident.str
           in
        let updater = update_names_from_event cur_mod_str  in
        FStar_List.fold_left updater names1 name_events
  
let commit_name_tracking :
  repl_state -> name_tracking_event Prims.list -> repl_state =
  fun st  ->
    fun name_events  ->
      let names1 =
        commit_name_tracking' st.repl_curmod st.repl_names name_events  in
      let uu___91_1214 = st  in
      {
        repl_line = (uu___91_1214.repl_line);
        repl_column = (uu___91_1214.repl_column);
        repl_fname = (uu___91_1214.repl_fname);
        repl_deps_stack = (uu___91_1214.repl_deps_stack);
        repl_curmod = (uu___91_1214.repl_curmod);
        repl_env = (uu___91_1214.repl_env);
        repl_stdin = (uu___91_1214.repl_stdin);
        repl_names = names1
      }
  
let fresh_name_tracking_hooks :
  unit ->
    (name_tracking_event Prims.list FStar_ST.ref,FStar_Syntax_DsEnv.dsenv_hooks,
      FStar_TypeChecker_Env.tcenv_hooks) FStar_Pervasives_Native.tuple3
  =
  fun uu____1229  ->
    let events = FStar_Util.mk_ref []  in
    let push_event evt =
      let uu____1243 =
        let uu____1246 = FStar_ST.op_Bang events  in evt :: uu____1246  in
      FStar_ST.op_Colon_Equals events uu____1243  in
    (events,
      {
        FStar_Syntax_DsEnv.ds_push_open_hook =
          (fun dsenv1  ->
             fun op  ->
               let uu____1381 =
                 let uu____1382 =
                   let uu____1387 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____1387, op)  in
                 NTOpen uu____1382  in
               push_event uu____1381);
        FStar_Syntax_DsEnv.ds_push_include_hook =
          (fun dsenv1  ->
             fun ns  ->
               let uu____1393 =
                 let uu____1394 =
                   let uu____1399 = FStar_Syntax_DsEnv.current_module dsenv1
                      in
                   (uu____1399, ns)  in
                 NTInclude uu____1394  in
               push_event uu____1393);
        FStar_Syntax_DsEnv.ds_push_module_abbrev_hook =
          (fun dsenv1  ->
             fun x  ->
               fun l  ->
                 let uu____1407 =
                   let uu____1408 =
                     let uu____1415 =
                       FStar_Syntax_DsEnv.current_module dsenv1  in
                     (uu____1415, x, l)  in
                   NTAlias uu____1408  in
                 push_event uu____1407)
      },
      {
        FStar_TypeChecker_Env.tc_push_in_gamma_hook =
          (fun uu____1420  -> fun s  -> push_event (NTBinding s))
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
      let uu____1469 =
        FStar_Universal.with_tcenv env1
          (fun dsenv1  ->
             let uu____1477 = FStar_Syntax_DsEnv.set_ds_hooks dsenv1 dshooks
                in
             ((), uu____1477))
         in
      match uu____1469 with
      | ((),tcenv') -> FStar_TypeChecker_Env.set_tc_hooks tcenv' tchooks  in
    let uu____1479 =
      let uu____1484 =
        FStar_Syntax_DsEnv.ds_hooks env.FStar_TypeChecker_Env.dsenv  in
      let uu____1485 = FStar_TypeChecker_Env.tc_hooks env  in
      (uu____1484, uu____1485)  in
    match uu____1479 with
    | (old_dshooks,old_tchooks) ->
        let uu____1501 = fresh_name_tracking_hooks ()  in
        (match uu____1501 with
         | (events,new_dshooks,new_tchooks) ->
             let uu____1536 = set_hooks new_dshooks new_tchooks env  in
             (uu____1536,
               ((fun env1  ->
                   let uu____1550 = set_hooks old_dshooks old_tchooks env1
                      in
                   let uu____1551 =
                     let uu____1554 = FStar_ST.op_Bang events  in
                     FStar_List.rev uu____1554  in
                   (uu____1550, uu____1551)))))
  
let string_of_repl_task : repl_task -> Prims.string =
  fun uu___73_1612  ->
    match uu___73_1612 with
    | LDInterleaved (intf,impl) ->
        let uu____1615 = string_of_timed_fname intf  in
        let uu____1616 = string_of_timed_fname impl  in
        FStar_Util.format2 "LDInterleaved (%s, %s)" uu____1615 uu____1616
    | LDSingle intf_or_impl ->
        let uu____1618 = string_of_timed_fname intf_or_impl  in
        FStar_Util.format1 "LDSingle %s" uu____1618
    | LDInterfaceOfCurrentFile intf ->
        let uu____1620 = string_of_timed_fname intf  in
        FStar_Util.format1 "LDInterfaceOfCurrentFile %s" uu____1620
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
        let uu____1641 =
          FStar_Universal.tc_one_file env FStar_Pervasives_Native.None
            intf_opt modf
           in
        match uu____1641 with
        | (uu____1655,env1,delta1) ->
            let env2 = FStar_Universal.apply_delta_env env1 delta1  in env2
  
let run_repl_task :
  optmod_t ->
    env_t -> repl_task -> (optmod_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun curmod  ->
    fun env  ->
      fun task  ->
        match task with
        | LDInterleaved (intf,impl) ->
            let uu____1694 =
              tc_one env (FStar_Pervasives_Native.Some (intf.tf_fname))
                impl.tf_fname
               in
            (curmod, uu____1694)
        | LDSingle intf_or_impl ->
            let uu____1696 =
              tc_one env FStar_Pervasives_Native.None intf_or_impl.tf_fname
               in
            (curmod, uu____1696)
        | LDInterfaceOfCurrentFile intf ->
            let uu____1698 =
              FStar_Universal.load_interface_decls env intf.tf_fname  in
            (curmod, uu____1698)
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
            let uu____1753 = aux deps' final_tasks1  in
            (LDInterleaved ((wrap intf), (wrap impl))) :: uu____1753
        | intf_or_impl::deps' ->
            let uu____1760 = aux deps' final_tasks1  in
            (LDSingle (wrap intf_or_impl)) :: uu____1760
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
      let uu____1801 = get_mod_name f  in uu____1801 = our_mod_name  in
    let uu____1802 = FStar_Dependencies.find_deps_if_needed [filename]  in
    match uu____1802 with
    | (deps,dep_graph1) ->
        let uu____1825 = FStar_List.partition has_our_mod_name deps  in
        (match uu____1825 with
         | (same_name,real_deps) ->
             let intf_tasks =
               match same_name with
               | intf::impl::[] ->
                   ((let uu____1862 =
                       let uu____1863 = FStar_Parser_Dep.is_interface intf
                          in
                       Prims.op_Negation uu____1863  in
                     if uu____1862
                     then
                       let uu____1864 =
                         let uu____1869 =
                           FStar_Util.format1
                             "Expecting an interface, got %s" intf
                            in
                         (FStar_Errors.Fatal_MissingInterface, uu____1869)
                          in
                       FStar_Errors.raise_err uu____1864
                     else ());
                    (let uu____1872 =
                       let uu____1873 =
                         FStar_Parser_Dep.is_implementation impl  in
                       Prims.op_Negation uu____1873  in
                     if uu____1872
                     then
                       let uu____1874 =
                         let uu____1879 =
                           FStar_Util.format1
                             "Expecting an implementation, got %s" impl
                            in
                         (FStar_Errors.Fatal_MissingImplementation,
                           uu____1879)
                          in
                       FStar_Errors.raise_err uu____1874
                     else ());
                    [LDInterfaceOfCurrentFile (dummy_tf_of_fname intf)])
               | impl::[] -> []
               | uu____1882 ->
                   let mods_str = FStar_String.concat " " same_name  in
                   let message = "Too many or too few files matching %s: %s"
                      in
                   ((let uu____1888 =
                       let uu____1893 =
                         FStar_Util.format message [our_mod_name; mods_str]
                          in
                       (FStar_Errors.Fatal_TooManyOrTooFewFileMatch,
                         uu____1893)
                        in
                     FStar_Errors.raise_err uu____1888);
                    [])
                in
             let tasks = repl_ld_tasks_of_deps real_deps intf_tasks  in
             (real_deps, tasks, dep_graph1))
  
let update_task_timestamps : repl_task -> repl_task =
  fun uu___74_1905  ->
    match uu___74_1905 with
    | LDInterleaved (intf,impl) ->
        let uu____1908 =
          let uu____1913 = tf_of_fname intf.tf_fname  in
          let uu____1914 = tf_of_fname impl.tf_fname  in
          (uu____1913, uu____1914)  in
        LDInterleaved uu____1908
    | LDSingle intf_or_impl ->
        let uu____1916 = tf_of_fname intf_or_impl.tf_fname  in
        LDSingle uu____1916
    | LDInterfaceOfCurrentFile intf ->
        let uu____1918 = tf_of_fname intf.tf_fname  in
        LDInterfaceOfCurrentFile uu____1918
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
          let uu____1945 = track_name_changes env  in
          match uu____1945 with
          | (env1,finish_name_tracking) ->
              let check_success uu____1988 =
                (let uu____1991 = FStar_Errors.get_err_count ()  in
                 uu____1991 = (Prims.lift_native_int (0))) &&
                  (Prims.op_Negation must_rollback)
                 in
              let uu____1992 =
                let uu____1999 =
                  with_captured_errors env1
                    (fun env2  ->
                       let uu____2013 =
                         run_repl_task st.repl_curmod env2 task  in
                       FStar_All.pipe_left
                         (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
                         uu____2013)
                   in
                match uu____1999 with
                | FStar_Pervasives_Native.Some (curmod,env2) when
                    check_success () -> (curmod, env2, true)
                | uu____2044 -> ((st.repl_curmod), env1, false)  in
              (match uu____1992 with
               | (curmod,env2,success) ->
                   let uu____2058 = finish_name_tracking env2  in
                   (match uu____2058 with
                    | (env',name_events) ->
                        let st1 =
                          let uu___92_2076 = st  in
                          {
                            repl_line = (uu___92_2076.repl_line);
                            repl_column = (uu___92_2076.repl_column);
                            repl_fname = (uu___92_2076.repl_fname);
                            repl_deps_stack = (uu___92_2076.repl_deps_stack);
                            repl_curmod = curmod;
                            repl_env = env2;
                            repl_stdin = (uu___92_2076.repl_stdin);
                            repl_names = (uu___92_2076.repl_names)
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
        let uu____2108 = FStar_Options.debug_any ()  in
        if uu____2108
        then
          let uu____2109 = string_of_repl_task task  in
          FStar_Util.print2 "%s %s" verb uu____2109
        else ()  in
      let rec revert_many st1 uu___75_2127 =
        match uu___75_2127 with
        | [] -> st1
        | (task,_st')::entries ->
            (debug1 "Reverting" task;
             (let uu____2154 = pop_repl st1  in
              revert_many uu____2154 entries))
         in
      let rec aux st1 tasks1 previous =
        match (tasks1, previous) with
        | ([],[]) -> FStar_Util.Inl st1
        | (task::tasks2,[]) ->
            (debug1 "Loading" task;
             (let uu____2205 = FStar_Options.restore_cmd_line_options false
                 in
              FStar_All.pipe_right uu____2205 (fun a240  -> ()));
             (let timestamped_task = update_task_timestamps task  in
              let push_kind =
                let uu____2208 = FStar_Options.lax ()  in
                if uu____2208 then LaxCheck else FullCheck  in
              let uu____2210 =
                run_repl_transaction st1 push_kind false timestamped_task  in
              match uu____2210 with
              | (success,st2) ->
                  if success
                  then
                    let uu____2225 =
                      let uu___93_2226 = st2  in
                      let uu____2227 = FStar_ST.op_Bang repl_stack  in
                      {
                        repl_line = (uu___93_2226.repl_line);
                        repl_column = (uu___93_2226.repl_column);
                        repl_fname = (uu___93_2226.repl_fname);
                        repl_deps_stack = uu____2227;
                        repl_curmod = (uu___93_2226.repl_curmod);
                        repl_env = (uu___93_2226.repl_env);
                        repl_stdin = (uu___93_2226.repl_stdin);
                        repl_names = (uu___93_2226.repl_names)
                      }  in
                    aux uu____2225 tasks2 []
                  else FStar_Util.Inr st2))
        | (task::tasks2,prev::previous1) when
            let uu____2282 = update_task_timestamps task  in
            (FStar_Pervasives_Native.fst prev) = uu____2282 ->
            (debug1 "Skipping" task; aux st1 tasks2 previous1)
        | (tasks2,previous1) ->
            let uu____2294 = revert_many st1 previous1  in
            aux uu____2294 tasks2 []
         in
      aux st tasks (FStar_List.rev st.repl_deps_stack)
  
let json_debug : FStar_Util.json -> Prims.string =
  fun uu___76_2303  ->
    match uu___76_2303 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2307 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____2307
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2309 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2312 -> "dictionary (...)"
  
exception UnexpectedJsonType of (Prims.string,FStar_Util.json)
  FStar_Pervasives_Native.tuple2 
let uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____2332 -> true
    | uu____2337 -> false
  
let __proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____2352 -> uu____2352
  
let js_fail : 'Auu____2363 . Prims.string -> FStar_Util.json -> 'Auu____2363
  =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let js_int : FStar_Util.json -> Prims.int =
  fun uu___77_2378  ->
    match uu___77_2378 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let js_str : FStar_Util.json -> Prims.string =
  fun uu___78_2385  ->
    match uu___78_2385 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'Auu____2394 .
    (FStar_Util.json -> 'Auu____2394) ->
      FStar_Util.json -> 'Auu____2394 Prims.list
  =
  fun k  ->
    fun uu___79_2409  ->
      match uu___79_2409 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let js_assoc :
  FStar_Util.json ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu___80_2428  ->
    match uu___80_2428 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let js_pushkind : FStar_Util.json -> push_kind =
  fun s  ->
    let uu____2454 = js_str s  in
    match uu____2454 with
    | "syntax" -> SyntaxCheck
    | "lax" -> LaxCheck
    | "full" -> FullCheck
    | uu____2455 -> js_fail "push_kind" s
  
let js_reductionrule : FStar_Util.json -> FStar_TypeChecker_Normalize.step =
  fun s  ->
    let uu____2461 = js_str s  in
    match uu____2461 with
    | "beta" -> FStar_TypeChecker_Normalize.Beta
    | "delta" ->
        FStar_TypeChecker_Normalize.UnfoldUntil
          FStar_Syntax_Syntax.Delta_constant
    | "iota" -> FStar_TypeChecker_Normalize.Iota
    | "zeta" -> FStar_TypeChecker_Normalize.Zeta
    | "reify" -> FStar_TypeChecker_Normalize.Reify
    | "pure-subterms" ->
        FStar_TypeChecker_Normalize.PureSubtermsWithinComputations
    | uu____2462 -> js_fail "reduction rule" s
  
type completion_context =
  | CKCode 
  | CKOption of Prims.bool 
  | CKModuleOrNamespace of (Prims.bool,Prims.bool)
  FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_CKCode : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKCode  -> true | uu____2482 -> false
  
let uu___is_CKOption : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with | CKOption _0 -> true | uu____2489 -> false
  
let __proj__CKOption__item___0 : completion_context -> Prims.bool =
  fun projectee  -> match projectee with | CKOption _0 -> _0 
let uu___is_CKModuleOrNamespace : completion_context -> Prims.bool =
  fun projectee  ->
    match projectee with
    | CKModuleOrNamespace _0 -> true
    | uu____2507 -> false
  
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
        let uu____2537 = js_str k1  in
        (match uu____2537 with
         | "symbol" -> CKCode
         | "code" -> CKCode
         | "set-options" -> CKOption false
         | "reset-options" -> CKOption true
         | "open" -> CKModuleOrNamespace (true, true)
         | "let-open" -> CKModuleOrNamespace (true, true)
         | "include" -> CKModuleOrNamespace (true, false)
         | "module-alias" -> CKModuleOrNamespace (true, false)
         | uu____2538 ->
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
    match projectee with | LKSymbolOnly  -> true | uu____2544 -> false
  
let uu___is_LKModule : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKModule  -> true | uu____2550 -> false
  
let uu___is_LKOption : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKOption  -> true | uu____2556 -> false
  
let uu___is_LKCode : lookup_context -> Prims.bool =
  fun projectee  ->
    match projectee with | LKCode  -> true | uu____2562 -> false
  
let js_optional_lookup_context :
  FStar_Util.json FStar_Pervasives_Native.option -> lookup_context =
  fun k  ->
    match k with
    | FStar_Pervasives_Native.None  -> LKSymbolOnly
    | FStar_Pervasives_Native.Some k1 ->
        let uu____2573 = js_str k1  in
        (match uu____2573 with
         | "symbol-only" -> LKSymbolOnly
         | "code" -> LKCode
         | "set-options" -> LKOption
         | "reset-options" -> LKOption
         | "open" -> LKModule
         | "let-open" -> LKModule
         | "include" -> LKModule
         | "module-alias" -> LKModule
         | uu____2574 ->
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
    match projectee with | Exit  -> true | uu____2671 -> false
  
let uu___is_DescribeProtocol : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeProtocol  -> true | uu____2677 -> false
  
let uu___is_DescribeRepl : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | DescribeRepl  -> true | uu____2683 -> false
  
let uu___is_Segment : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Segment _0 -> true | uu____2690 -> false
  
let __proj__Segment__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | Segment _0 -> _0 
let uu___is_Pop : query' -> Prims.bool =
  fun projectee  -> match projectee with | Pop  -> true | uu____2703 -> false 
let uu___is_Push : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Push _0 -> true | uu____2710 -> false
  
let __proj__Push__item___0 : query' -> push_query =
  fun projectee  -> match projectee with | Push _0 -> _0 
let uu___is_VfsAdd : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | VfsAdd _0 -> true | uu____2730 -> false
  
let __proj__VfsAdd__item___0 :
  query' ->
    (Prims.string FStar_Pervasives_Native.option,Prims.string)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | VfsAdd _0 -> _0 
let uu___is_AutoComplete : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | AutoComplete _0 -> true | uu____2766 -> false
  
let __proj__AutoComplete__item___0 :
  query' -> (Prims.string,completion_context) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | AutoComplete _0 -> _0 
let uu___is_Lookup : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Lookup _0 -> true | uu____2804 -> false
  
let __proj__Lookup__item___0 :
  query' ->
    (Prims.string,lookup_context,position FStar_Pervasives_Native.option,
      Prims.string Prims.list) FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Lookup _0 -> _0 
let uu___is_Compute : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Compute _0 -> true | uu____2862 -> false
  
let __proj__Compute__item___0 :
  query' ->
    (Prims.string,FStar_TypeChecker_Normalize.step Prims.list
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Compute _0 -> _0 
let uu___is_Search : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | Search _0 -> true | uu____2900 -> false
  
let __proj__Search__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | Search _0 -> _0 
let uu___is_GenericError : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | GenericError _0 -> true | uu____2914 -> false
  
let __proj__GenericError__item___0 : query' -> Prims.string =
  fun projectee  -> match projectee with | GenericError _0 -> _0 
let uu___is_ProtocolViolation : query' -> Prims.bool =
  fun projectee  ->
    match projectee with | ProtocolViolation _0 -> true | uu____2928 -> false
  
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
  fun uu___81_2954  ->
    match uu___81_2954 with
    | Exit  -> false
    | DescribeProtocol  -> false
    | DescribeRepl  -> false
    | Segment uu____2955 -> false
    | Pop  -> false
    | Push
        { push_kind = uu____2956; push_code = uu____2957;
          push_line = uu____2958; push_column = uu____2959;
          push_peek_only = false ;_}
        -> false
    | VfsAdd uu____2960 -> false
    | GenericError uu____2967 -> false
    | ProtocolViolation uu____2968 -> false
    | Push uu____2969 -> true
    | AutoComplete uu____2970 -> true
    | Lookup uu____2975 -> true
    | Compute uu____2988 -> true
    | Search uu____2997 -> true
  
let interactive_protocol_vernum : Prims.int = (Prims.lift_native_int (2)) 
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
  "vfs-add";
  "tactic-ranges"] 
exception InvalidQuery of Prims.string 
let uu___is_InvalidQuery : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____3009 -> true
    | uu____3010 -> false
  
let __proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidQuery uu____3017 -> uu____3017
  
type query_status =
  | QueryOK 
  | QueryNOK 
  | QueryViolatesProtocol [@@deriving show]
let uu___is_QueryOK : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryOK  -> true | uu____3023 -> false
  
let uu___is_QueryNOK : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with | QueryNOK  -> true | uu____3029 -> false
  
let uu___is_QueryViolatesProtocol : query_status -> Prims.bool =
  fun projectee  ->
    match projectee with
    | QueryViolatesProtocol  -> true
    | uu____3035 -> false
  
let try_assoc :
  'Auu____3044 'Auu____3045 .
    'Auu____3044 ->
      ('Auu____3044,'Auu____3045) FStar_Pervasives_Native.tuple2 Prims.list
        -> 'Auu____3045 FStar_Pervasives_Native.option
  =
  fun key  ->
    fun a  ->
      let uu____3070 =
        FStar_Util.try_find
          (fun uu____3084  ->
             match uu____3084 with | (k,uu____3090) -> k = key) a
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____3070
  
let wrap_js_failure :
  Prims.string -> Prims.string -> FStar_Util.json -> query =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____3110 =
          let uu____3111 =
            let uu____3112 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____3112
             in
          ProtocolViolation uu____3111  in
        { qq = uu____3110; qid }
  
let unpack_interactive_query : FStar_Util.json -> query =
  fun json  ->
    let assoc1 errloc key a =
      let uu____3146 = try_assoc key a  in
      match uu____3146 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____3150 =
            let uu____3151 =
              FStar_Util.format2 "Missing key [%s] in %s." key errloc  in
            InvalidQuery uu____3151  in
          FStar_Exn.raise uu____3150
       in
    let request = FStar_All.pipe_right json js_assoc  in
    let qid =
      let uu____3166 = assoc1 "query" "query-id" request  in
      FStar_All.pipe_right uu____3166 js_str  in
    try
      let query =
        let uu____3175 = assoc1 "query" "query" request  in
        FStar_All.pipe_right uu____3175 js_str  in
      let args =
        let uu____3183 = assoc1 "query" "args" request  in
        FStar_All.pipe_right uu____3183 js_assoc  in
      let arg k = assoc1 "[args]" k args  in
      let try_arg k =
        let uu____3204 = try_assoc k args  in
        match uu____3204 with
        | FStar_Pervasives_Native.Some (FStar_Util.JsonNull ) ->
            FStar_Pervasives_Native.None
        | other -> other  in
      let uu____3212 =
        match query with
        | "exit" -> Exit
        | "pop" -> Pop
        | "describe-protocol" -> DescribeProtocol
        | "describe-repl" -> DescribeRepl
        | "segment" ->
            let uu____3213 =
              let uu____3214 = arg "code"  in
              FStar_All.pipe_right uu____3214 js_str  in
            Segment uu____3213
        | "peek" ->
            let uu____3215 =
              let uu____3216 =
                let uu____3217 = arg "kind"  in
                FStar_All.pipe_right uu____3217 js_pushkind  in
              let uu____3218 =
                let uu____3219 = arg "code"  in
                FStar_All.pipe_right uu____3219 js_str  in
              let uu____3220 =
                let uu____3221 = arg "line"  in
                FStar_All.pipe_right uu____3221 js_int  in
              let uu____3222 =
                let uu____3223 = arg "column"  in
                FStar_All.pipe_right uu____3223 js_int  in
              {
                push_kind = uu____3216;
                push_code = uu____3218;
                push_line = uu____3220;
                push_column = uu____3222;
                push_peek_only = (query = "peek")
              }  in
            Push uu____3215
        | "push" ->
            let uu____3224 =
              let uu____3225 =
                let uu____3226 = arg "kind"  in
                FStar_All.pipe_right uu____3226 js_pushkind  in
              let uu____3227 =
                let uu____3228 = arg "code"  in
                FStar_All.pipe_right uu____3228 js_str  in
              let uu____3229 =
                let uu____3230 = arg "line"  in
                FStar_All.pipe_right uu____3230 js_int  in
              let uu____3231 =
                let uu____3232 = arg "column"  in
                FStar_All.pipe_right uu____3232 js_int  in
              {
                push_kind = uu____3225;
                push_code = uu____3227;
                push_line = uu____3229;
                push_column = uu____3231;
                push_peek_only = (query = "peek")
              }  in
            Push uu____3224
        | "autocomplete" ->
            let uu____3233 =
              let uu____3238 =
                let uu____3239 = arg "partial-symbol"  in
                FStar_All.pipe_right uu____3239 js_str  in
              let uu____3240 =
                let uu____3241 = try_arg "context"  in
                FStar_All.pipe_right uu____3241
                  js_optional_completion_context
                 in
              (uu____3238, uu____3240)  in
            AutoComplete uu____3233
        | "lookup" ->
            let uu____3246 =
              let uu____3259 =
                let uu____3260 = arg "symbol"  in
                FStar_All.pipe_right uu____3260 js_str  in
              let uu____3261 =
                let uu____3262 = try_arg "context"  in
                FStar_All.pipe_right uu____3262 js_optional_lookup_context
                 in
              let uu____3267 =
                let uu____3276 =
                  let uu____3285 = try_arg "location"  in
                  FStar_All.pipe_right uu____3285
                    (FStar_Util.map_option js_assoc)
                   in
                FStar_All.pipe_right uu____3276
                  (FStar_Util.map_option
                     (fun loc  ->
                        let uu____3343 =
                          let uu____3344 = assoc1 "[location]" "filename" loc
                             in
                          FStar_All.pipe_right uu____3344 js_str  in
                        let uu____3345 =
                          let uu____3346 = assoc1 "[location]" "line" loc  in
                          FStar_All.pipe_right uu____3346 js_int  in
                        let uu____3347 =
                          let uu____3348 = assoc1 "[location]" "column" loc
                             in
                          FStar_All.pipe_right uu____3348 js_int  in
                        (uu____3343, uu____3345, uu____3347)))
                 in
              let uu____3349 =
                let uu____3352 = arg "requested-info"  in
                FStar_All.pipe_right uu____3352 (js_list js_str)  in
              (uu____3259, uu____3261, uu____3267, uu____3349)  in
            Lookup uu____3246
        | "compute" ->
            let uu____3365 =
              let uu____3374 =
                let uu____3375 = arg "term"  in
                FStar_All.pipe_right uu____3375 js_str  in
              let uu____3376 =
                let uu____3381 = try_arg "rules"  in
                FStar_All.pipe_right uu____3381
                  (FStar_Util.map_option (js_list js_reductionrule))
                 in
              (uu____3374, uu____3376)  in
            Compute uu____3365
        | "search" ->
            let uu____3396 =
              let uu____3397 = arg "terms"  in
              FStar_All.pipe_right uu____3397 js_str  in
            Search uu____3396
        | "vfs-add" ->
            let uu____3398 =
              let uu____3405 =
                let uu____3408 = try_arg "filename"  in
                FStar_All.pipe_right uu____3408
                  (FStar_Util.map_option js_str)
                 in
              let uu____3415 =
                let uu____3416 = arg "contents"  in
                FStar_All.pipe_right uu____3416 js_str  in
              (uu____3405, uu____3415)  in
            VfsAdd uu____3398
        | uu____3419 ->
            let uu____3420 = FStar_Util.format1 "Unknown query '%s'" query
               in
            ProtocolViolation uu____3420
         in
      { qq = uu____3212; qid }
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure qid expected got
  
let deserialize_interactive_query : FStar_Util.json -> query =
  fun js_query  ->
    try unpack_interactive_query js_query
    with | InvalidQuery msg -> { qq = (ProtocolViolation msg); qid = "?" }
    | UnexpectedJsonType (expected,got) -> wrap_js_failure "?" expected got
  
let parse_interactive_query : Prims.string -> query =
  fun query_str  ->
    let uu____3445 = FStar_Util.json_of_string query_str  in
    match uu____3445 with
    | FStar_Pervasives_Native.None  ->
        { qq = (ProtocolViolation "Json parsing failed."); qid = "?" }
    | FStar_Pervasives_Native.Some request ->
        deserialize_interactive_query request
  
let read_interactive_query : FStar_Util.stream_reader -> query =
  fun stream  ->
    let uu____3454 = FStar_Util.read_line stream  in
    match uu____3454 with
    | FStar_Pervasives_Native.None  ->
        FStar_All.exit (Prims.lift_native_int (0))
    | FStar_Pervasives_Native.Some line -> parse_interactive_query line
  
let json_of_opt :
  'Auu____3464 .
    ('Auu____3464 -> FStar_Util.json) ->
      'Auu____3464 FStar_Pervasives_Native.option -> FStar_Util.json
  =
  fun json_of_a  ->
    fun opt_a  ->
      let uu____3484 = FStar_Util.map_option json_of_a opt_a  in
      FStar_Util.dflt FStar_Util.JsonNull uu____3484
  
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
    let uu____3497 =
      let uu____3504 =
        let uu____3511 =
          let uu____3518 =
            let uu____3523 =
              let uu____3524 =
                let uu____3527 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.None  -> []
                  | FStar_Pervasives_Native.Some r ->
                      let uu____3533 = FStar_Range.json_of_use_range r  in
                      [uu____3533]
                   in
                let uu____3534 =
                  match issue.FStar_Errors.issue_range with
                  | FStar_Pervasives_Native.Some r when
                      let uu____3540 = FStar_Range.def_range r  in
                      let uu____3541 = FStar_Range.use_range r  in
                      uu____3540 <> uu____3541 ->
                      let uu____3542 = FStar_Range.json_of_def_range r  in
                      [uu____3542]
                  | uu____3543 -> []  in
                FStar_List.append uu____3527 uu____3534  in
              FStar_Util.JsonList uu____3524  in
            ("ranges", uu____3523)  in
          [uu____3518]  in
        ("message", (FStar_Util.JsonStr (issue.FStar_Errors.issue_message)))
          :: uu____3511
         in
      ("level", (json_of_issue_level issue.FStar_Errors.issue_level)) ::
        uu____3504
       in
    FStar_Util.JsonAssoc uu____3497
  
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
    let uu____3712 =
      let uu____3719 =
        let uu____3724 =
          json_of_opt FStar_Range.json_of_def_range lr.slr_def_range  in
        ("defined-at", uu____3724)  in
      let uu____3725 =
        let uu____3732 =
          let uu____3737 =
            json_of_opt (fun _0_18  -> FStar_Util.JsonStr _0_18) lr.slr_typ
             in
          ("type", uu____3737)  in
        let uu____3738 =
          let uu____3745 =
            let uu____3750 =
              json_of_opt (fun _0_19  -> FStar_Util.JsonStr _0_19) lr.slr_doc
               in
            ("documentation", uu____3750)  in
          let uu____3751 =
            let uu____3758 =
              let uu____3763 =
                json_of_opt (fun _0_20  -> FStar_Util.JsonStr _0_20)
                  lr.slr_def
                 in
              ("definition", uu____3763)  in
            [uu____3758]  in
          uu____3745 :: uu____3751  in
        uu____3732 :: uu____3738  in
      uu____3719 :: uu____3725  in
    ("name", (FStar_Util.JsonStr (lr.slr_name))) :: uu____3712
  
let alist_of_protocol_info :
  (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____3796 =
      FStar_List.map (fun _0_21  -> FStar_Util.JsonStr _0_21)
        interactive_protocol_features
       in
    FStar_All.pipe_left (fun _0_22  -> FStar_Util.JsonList _0_22) uu____3796
     in
  [("version", js_version); ("features", js_features)] 
type fstar_option_permission_level =
  | OptSet 
  | OptReset 
  | OptReadOnly [@@deriving show]
let uu___is_OptSet : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptSet  -> true | uu____3818 -> false
  
let uu___is_OptReset : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReset  -> true | uu____3824 -> false
  
let uu___is_OptReadOnly : fstar_option_permission_level -> Prims.bool =
  fun projectee  ->
    match projectee with | OptReadOnly  -> true | uu____3830 -> false
  
let string_of_option_permission_level :
  fstar_option_permission_level -> Prims.string =
  fun uu___82_3835  ->
    match uu___82_3835 with
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
  fun uu___83_4028  ->
    match uu___83_4028 with
    | FStar_Options.Const uu____4029 -> "flag"
    | FStar_Options.IntStr uu____4030 -> "int"
    | FStar_Options.BoolStr  -> "bool"
    | FStar_Options.PathStr uu____4031 -> "path"
    | FStar_Options.SimpleStr uu____4032 -> "string"
    | FStar_Options.EnumStr uu____4033 -> "enum"
    | FStar_Options.OpenEnumStr uu____4036 -> "open enum"
    | FStar_Options.PostProcessed (uu____4043,typ) ->
        kind_of_fstar_option_type typ
    | FStar_Options.Accumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.ReverseAccumulated typ -> kind_of_fstar_option_type typ
    | FStar_Options.WithSideEffect (uu____4053,typ) ->
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
        | FStar_Options.Const uu____4101 -> [""]
        | FStar_Options.BoolStr  -> ["true"; "false"]
        | FStar_Options.IntStr desc -> [mk_field desc]
        | FStar_Options.PathStr desc -> [mk_field desc]
        | FStar_Options.SimpleStr desc -> [mk_field desc]
        | FStar_Options.EnumStr strs -> strs
        | FStar_Options.OpenEnumStr (strs,desc) ->
            FStar_List.append strs [mk_field desc]
        | FStar_Options.PostProcessed (uu____4114,elem_spec) ->
            arg_snippets_of_type elem_spec
        | FStar_Options.Accumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.ReverseAccumulated elem_spec ->
            arg_snippets_of_type elem_spec
        | FStar_Options.WithSideEffect (uu____4124,elem_spec) ->
            arg_snippets_of_type elem_spec
         in
      let uu____4132 = arg_snippets_of_type typ  in
      FStar_List.map (mk_snippet name) uu____4132
  
let rec json_of_fstar_option_value :
  FStar_Options.option_val -> FStar_Util.json =
  fun uu___84_4139  ->
    match uu___84_4139 with
    | FStar_Options.Bool b -> FStar_Util.JsonBool b
    | FStar_Options.String s -> FStar_Util.JsonStr s
    | FStar_Options.Path s -> FStar_Util.JsonStr s
    | FStar_Options.Int n1 -> FStar_Util.JsonInt n1
    | FStar_Options.List vs ->
        let uu____4147 = FStar_List.map json_of_fstar_option_value vs  in
        FStar_Util.JsonList uu____4147
    | FStar_Options.Unset  -> FStar_Util.JsonNull
  
let alist_of_fstar_option :
  fstar_option ->
    (Prims.string,FStar_Util.json) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun opt  ->
    let uu____4161 =
      let uu____4168 =
        let uu____4175 =
          let uu____4180 = json_of_fstar_option_value opt.opt_value  in
          ("value", uu____4180)  in
        let uu____4181 =
          let uu____4188 =
            let uu____4193 = json_of_fstar_option_value opt.opt_default  in
            ("default", uu____4193)  in
          let uu____4194 =
            let uu____4201 =
              let uu____4206 =
                json_of_opt (fun _0_23  -> FStar_Util.JsonStr _0_23)
                  opt.opt_documentation
                 in
              ("documentation", uu____4206)  in
            let uu____4207 =
              let uu____4214 =
                let uu____4219 =
                  let uu____4220 = kind_of_fstar_option_type opt.opt_type  in
                  FStar_Util.JsonStr uu____4220  in
                ("type", uu____4219)  in
              [uu____4214;
              ("permission-level",
                (FStar_Util.JsonStr
                   (string_of_option_permission_level
                      opt.opt_permission_level)))]
               in
            uu____4201 :: uu____4207  in
          uu____4188 :: uu____4194  in
        uu____4175 :: uu____4181  in
      ("signature", (FStar_Util.JsonStr (opt.opt_sig))) :: uu____4168  in
    ("name", (FStar_Util.JsonStr (opt.opt_name))) :: uu____4161
  
let json_of_fstar_option : fstar_option -> FStar_Util.json =
  fun opt  ->
    let uu____4258 = alist_of_fstar_option opt  in
    FStar_Util.JsonAssoc uu____4258
  
let write_json : FStar_Util.json -> unit =
  fun json  ->
    (let uu____4271 = FStar_Util.string_of_json json  in
     FStar_Util.print_raw uu____4271);
    FStar_Util.print_raw "\n"
  
let json_of_response :
  Prims.string -> query_status -> FStar_Util.json -> FStar_Util.json =
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
  
let write_response : Prims.string -> query_status -> FStar_Util.json -> unit
  =
  fun qid  ->
    fun status  ->
      fun response  -> write_json (json_of_response qid status response)
  
let json_of_message : Prims.string -> FStar_Util.json -> FStar_Util.json =
  fun level  ->
    fun js_contents  ->
      let uu____4334 =
        let uu____4341 =
          let uu____4348 =
            let uu____4353 =
              let uu____4354 = FStar_ST.op_Bang repl_current_qid  in
              json_of_opt (fun _0_24  -> FStar_Util.JsonStr _0_24) uu____4354
               in
            ("query-id", uu____4353)  in
          [uu____4348;
          ("level", (FStar_Util.JsonStr level));
          ("contents", js_contents)]  in
        ("kind", (FStar_Util.JsonStr "message")) :: uu____4341  in
      FStar_Util.JsonAssoc uu____4334
  
let forward_message :
  'Auu____4412 .
    (FStar_Util.json -> 'Auu____4412) ->
      Prims.string -> FStar_Util.json -> 'Auu____4412
  =
  fun callback  ->
    fun level  ->
      fun contents  ->
        let uu____4433 = json_of_message level contents  in
        callback uu____4433
  
let json_of_hello : FStar_Util.json =
  let js_version = FStar_Util.JsonInt interactive_protocol_vernum  in
  let js_features =
    let uu____4436 =
      FStar_List.map (fun _0_25  -> FStar_Util.JsonStr _0_25)
        interactive_protocol_features
       in
    FStar_Util.JsonList uu____4436  in
  FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr "protocol-info")) ::
    alist_of_protocol_info)
  
let write_hello : unit -> unit = fun uu____4447  -> write_json json_of_hello 
let sig_of_fstar_option :
  Prims.string -> FStar_Options.opt_type -> Prims.string =
  fun name  ->
    fun typ  ->
      let flag = Prims.strcat "--" name  in
      let uu____4459 = FStar_Options.desc_of_opt_type typ  in
      match uu____4459 with
      | FStar_Pervasives_Native.None  -> flag
      | FStar_Pervasives_Native.Some arg_sig ->
          Prims.strcat flag (Prims.strcat " " arg_sig)
  
let fstar_options_list_cache : fstar_option Prims.list =
  let defaults1 = FStar_Util.smap_of_list FStar_Options.defaults  in
  let uu____4468 =
    FStar_All.pipe_right FStar_Options.all_specs_with_types
      (FStar_List.filter_map
         (fun uu____4497  ->
            match uu____4497 with
            | (_shortname,name,typ,doc1) ->
                let uu____4512 = FStar_Util.smap_try_find defaults1 name  in
                FStar_All.pipe_right uu____4512
                  (FStar_Util.map_option
                     (fun default_value  ->
                        let uu____4524 = sig_of_fstar_option name typ  in
                        let uu____4525 = snippets_of_fstar_option name typ
                           in
                        let uu____4528 =
                          let uu____4529 = FStar_Options.settable name  in
                          if uu____4529
                          then OptSet
                          else
                            (let uu____4531 = FStar_Options.resettable name
                                in
                             if uu____4531 then OptReset else OptReadOnly)
                           in
                        {
                          opt_name = name;
                          opt_sig = uu____4524;
                          opt_value = FStar_Options.Unset;
                          opt_default = default_value;
                          opt_type = typ;
                          opt_snippets = uu____4525;
                          opt_documentation =
                            (if doc1 = ""
                             then FStar_Pervasives_Native.None
                             else FStar_Pervasives_Native.Some doc1);
                          opt_permission_level = uu____4528
                        }))))
     in
  FStar_All.pipe_right uu____4468
    (FStar_List.sortWith
       (fun o1  ->
          fun o2  ->
            FStar_String.compare (FStar_String.lowercase o1.opt_name)
              (FStar_String.lowercase o2.opt_name)))
  
let fstar_options_map_cache : fstar_option FStar_Util.smap =
  let cache = FStar_Util.smap_create (Prims.lift_native_int (50))  in
  FStar_List.iter (fun opt  -> FStar_Util.smap_add cache opt.opt_name opt)
    fstar_options_list_cache;
  cache 
let update_option : fstar_option -> fstar_option =
  fun opt  ->
    let uu___98_4557 = opt  in
    let uu____4558 = FStar_Options.get_option opt.opt_name  in
    {
      opt_name = (uu___98_4557.opt_name);
      opt_sig = (uu___98_4557.opt_sig);
      opt_value = uu____4558;
      opt_default = (uu___98_4557.opt_default);
      opt_type = (uu___98_4557.opt_type);
      opt_snippets = (uu___98_4557.opt_snippets);
      opt_documentation = (uu___98_4557.opt_documentation);
      opt_permission_level = (uu___98_4557.opt_permission_level)
    }
  
let current_fstar_options :
  (fstar_option -> Prims.bool) -> fstar_option Prims.list =
  fun filter1  ->
    let uu____4571 = FStar_List.filter filter1 fstar_options_list_cache  in
    FStar_List.map update_option uu____4571
  
let trim_option_name :
  Prims.string -> (Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun opt_name  ->
    let opt_prefix = "--"  in
    if FStar_Util.starts_with opt_name opt_prefix
    then
      let uu____4588 =
        FStar_Util.substring_from opt_name (FStar_String.length opt_prefix)
         in
      (opt_prefix, uu____4588)
    else ("", opt_name)
  
let json_of_repl_state : repl_state -> FStar_Util.json =
  fun st  ->
    let filenames uu____4606 =
      match uu____4606 with
      | (task,uu____4614) ->
          (match task with
           | LDInterleaved (intf,impl) -> [intf.tf_fname; impl.tf_fname]
           | LDSingle intf_or_impl -> [intf_or_impl.tf_fname]
           | LDInterfaceOfCurrentFile intf -> [intf.tf_fname]
           | PushFragment uu____4621 -> [])
       in
    let uu____4622 =
      let uu____4629 =
        let uu____4634 =
          let uu____4635 =
            let uu____4638 =
              FStar_List.concatMap filenames st.repl_deps_stack  in
            FStar_List.map (fun _0_26  -> FStar_Util.JsonStr _0_26)
              uu____4638
             in
          FStar_Util.JsonList uu____4635  in
        ("loaded-dependencies", uu____4634)  in
      let uu____4645 =
        let uu____4652 =
          let uu____4657 =
            let uu____4658 =
              let uu____4661 =
                current_fstar_options (fun uu____4666  -> true)  in
              FStar_List.map json_of_fstar_option uu____4661  in
            FStar_Util.JsonList uu____4658  in
          ("options", uu____4657)  in
        [uu____4652]  in
      uu____4629 :: uu____4645  in
    FStar_Util.JsonAssoc uu____4622
  
let with_printed_effect_args :
  'Auu____4683 . (unit -> 'Auu____4683) -> 'Auu____4683 =
  fun k  ->
    FStar_Options.with_saved_options
      (fun uu____4696  ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
  
let term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string =
  fun tcenv  ->
    fun t  ->
      with_printed_effect_args
        (fun uu____4709  ->
           FStar_TypeChecker_Normalize.term_to_string tcenv t)
  
let sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string =
  fun se  ->
    with_printed_effect_args
      (fun uu____4716  -> FStar_Syntax_Print.sigelt_to_string se)
  
let run_exit :
  'Auu____4723 'Auu____4724 .
    'Auu____4723 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4724,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, FStar_Util.JsonNull),
      (FStar_Util.Inr (Prims.lift_native_int (0))))
  
let run_describe_protocol :
  'Auu____4756 'Auu____4757 .
    'Auu____4756 ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        ('Auu____4756,'Auu____4757) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    ((QueryOK, (FStar_Util.JsonAssoc alist_of_protocol_info)),
      (FStar_Util.Inl st))
  
let run_describe_repl :
  'Auu____4787 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____4787) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____4805 =
      let uu____4810 = json_of_repl_state st  in (QueryOK, uu____4810)  in
    (uu____4805, (FStar_Util.Inl st))
  
let run_protocol_violation :
  'Auu____4827 'Auu____4828 .
    'Auu____4827 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4827,'Auu____4828) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryViolatesProtocol, (FStar_Util.JsonStr message)),
        (FStar_Util.Inl st))
  
let run_generic_error :
  'Auu____4867 'Auu____4868 .
    'Auu____4867 ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          ('Auu____4867,'Auu____4868) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun message  ->
      ((QueryNOK, (FStar_Util.JsonStr message)), (FStar_Util.Inl st))
  
let collect_errors : unit -> FStar_Errors.issue Prims.list =
  fun uu____4905  ->
    let errors = FStar_Errors.report_all ()  in FStar_Errors.clear (); errors
  
let run_segment :
  'Auu____4916 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____4916) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun code  ->
      let frag =
        {
          FStar_Parser_ParseIt.frag_text = code;
          FStar_Parser_ParseIt.frag_line = (Prims.lift_native_int (1));
          FStar_Parser_ParseIt.frag_col = (Prims.lift_native_int (0))
        }  in
      let collect_decls uu____4947 =
        let uu____4948 = FStar_Parser_Driver.parse_fragment frag  in
        match uu____4948 with
        | FStar_Parser_Driver.Empty  -> []
        | FStar_Parser_Driver.Decls decls -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Module
            (uu____4954,decls)) -> decls
        | FStar_Parser_Driver.Modul (FStar_Parser_AST.Interface
            (uu____4960,decls,uu____4962)) -> decls
         in
      let uu____4967 =
        with_captured_errors st.repl_env
          (fun uu____4976  ->
             let uu____4977 = collect_decls ()  in
             FStar_All.pipe_left
               (fun _0_27  -> FStar_Pervasives_Native.Some _0_27) uu____4977)
         in
      match uu____4967 with
      | FStar_Pervasives_Native.None  ->
          let errors =
            let uu____5005 = collect_errors ()  in
            FStar_All.pipe_right uu____5005 (FStar_List.map json_of_issue)
             in
          ((QueryNOK, (FStar_Util.JsonList errors)), (FStar_Util.Inl st))
      | FStar_Pervasives_Native.Some decls ->
          let json_of_decl decl =
            let uu____5031 =
              let uu____5038 =
                let uu____5043 =
                  FStar_Range.json_of_def_range
                    (FStar_Parser_AST.decl_drange decl)
                   in
                ("def_range", uu____5043)  in
              [uu____5038]  in
            FStar_Util.JsonAssoc uu____5031  in
          let js_decls =
            let uu____5053 = FStar_List.map json_of_decl decls  in
            FStar_All.pipe_left (fun _0_28  -> FStar_Util.JsonList _0_28)
              uu____5053
             in
          ((QueryOK, (FStar_Util.JsonAssoc [("decls", js_decls)])),
            (FStar_Util.Inl st))
  
let run_vfs_add :
  'Auu____5082 .
    repl_state ->
      Prims.string FStar_Pervasives_Native.option ->
        Prims.string ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____5082) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun opt_fname  ->
      fun contents  ->
        let fname = FStar_Util.dflt st.repl_fname opt_fname  in
        FStar_Parser_ParseIt.add_vfs_entry fname contents;
        ((QueryOK, FStar_Util.JsonNull), (FStar_Util.Inl st))
  
let run_pop :
  'Auu____5128 .
    repl_state ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,'Auu____5128) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    let uu____5146 = nothing_left_to_pop st  in
    if uu____5146
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
    let uu____5192 =
      with_captured_errors st.repl_env
        (fun _env  ->
           let uu____5218 = deps_and_repl_ld_tasks_of_our_file st.repl_fname
              in
           FStar_All.pipe_left
             (fun _0_29  -> FStar_Pervasives_Native.Some _0_29) uu____5218)
       in
    match uu____5192 with
    | FStar_Pervasives_Native.None  -> FStar_Util.Inr st
    | FStar_Pervasives_Native.Some (deps,tasks,dep_graph1) ->
        let st1 =
          let uu___99_5309 = st  in
          let uu____5310 =
            FStar_TypeChecker_Env.set_dep_graph st.repl_env dep_graph1  in
          {
            repl_line = (uu___99_5309.repl_line);
            repl_column = (uu___99_5309.repl_column);
            repl_fname = (uu___99_5309.repl_fname);
            repl_deps_stack = (uu___99_5309.repl_deps_stack);
            repl_curmod = (uu___99_5309.repl_curmod);
            repl_env = uu____5310;
            repl_stdin = (uu___99_5309.repl_stdin);
            repl_names = (uu___99_5309.repl_names)
          }  in
        let uu____5311 = run_repl_ld_transactions st1 tasks  in
        (match uu____5311 with
         | FStar_Util.Inr st2 -> FStar_Util.Inr st2
         | FStar_Util.Inl st2 -> FStar_Util.Inl (st2, deps))
  
let rephrase_dependency_error : FStar_Errors.issue -> FStar_Errors.issue =
  fun issue  ->
    let uu___100_5347 = issue  in
    let uu____5348 =
      FStar_Util.format1 "Error while computing or loading dependencies:\n%s"
        issue.FStar_Errors.issue_message
       in
    {
      FStar_Errors.issue_message = uu____5348;
      FStar_Errors.issue_level = (uu___100_5347.FStar_Errors.issue_level);
      FStar_Errors.issue_range = (uu___100_5347.FStar_Errors.issue_range);
      FStar_Errors.issue_number = (uu___100_5347.FStar_Errors.issue_number)
    }
  
let run_push_without_deps :
  'Auu____5355 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5355) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let set_nosynth_flag st1 flag =
        let uu___101_5389 = st1  in
        {
          repl_line = (uu___101_5389.repl_line);
          repl_column = (uu___101_5389.repl_column);
          repl_fname = (uu___101_5389.repl_fname);
          repl_deps_stack = (uu___101_5389.repl_deps_stack);
          repl_curmod = (uu___101_5389.repl_curmod);
          repl_env =
            (let uu___102_5391 = st1.repl_env  in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___102_5391.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___102_5391.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___102_5391.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___102_5391.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___102_5391.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___102_5391.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___102_5391.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___102_5391.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___102_5391.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___102_5391.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___102_5391.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___102_5391.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___102_5391.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___102_5391.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___102_5391.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq =
                 (uu___102_5391.FStar_TypeChecker_Env.use_eq);
               FStar_TypeChecker_Env.is_iface =
                 (uu___102_5391.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___102_5391.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___102_5391.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___102_5391.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.failhard =
                 (uu___102_5391.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth = flag;
               FStar_TypeChecker_Env.tc_term =
                 (uu___102_5391.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___102_5391.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___102_5391.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___102_5391.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___102_5391.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___102_5391.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___102_5391.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___102_5391.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___102_5391.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___102_5391.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___102_5391.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___102_5391.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___102_5391.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___102_5391.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.dep_graph =
                 (uu___102_5391.FStar_TypeChecker_Env.dep_graph)
             });
          repl_stdin = (uu___101_5389.repl_stdin);
          repl_names = (uu___101_5389.repl_names)
        }  in
      let uu____5392 = query  in
      match uu____5392 with
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
            let uu____5413 =
              run_repl_transaction st1 push_kind peek_only
                (PushFragment frag)
               in
            match uu____5413 with
            | (success,st2) ->
                let st3 = set_nosynth_flag st2 false  in
                let status =
                  if success || peek_only then QueryOK else QueryNOK  in
                let json_errors =
                  let uu____5436 =
                    let uu____5439 = collect_errors ()  in
                    FStar_All.pipe_right uu____5439
                      (FStar_List.map json_of_issue)
                     in
                  FStar_Util.JsonList uu____5436  in
                let st4 =
                  if success
                  then
                    let uu___103_5447 = st3  in
                    {
                      repl_line = line;
                      repl_column = column;
                      repl_fname = (uu___103_5447.repl_fname);
                      repl_deps_stack = (uu___103_5447.repl_deps_stack);
                      repl_curmod = (uu___103_5447.repl_curmod);
                      repl_env = (uu___103_5447.repl_env);
                      repl_stdin = (uu___103_5447.repl_stdin);
                      repl_names = (uu___103_5447.repl_names)
                    }
                  else st3  in
                ((status, json_errors), (FStar_Util.Inl st4))))
  
let capitalize : Prims.string -> Prims.string =
  fun str  ->
    if str = ""
    then str
    else
      (let first =
         FStar_String.substring str (Prims.lift_native_int (0))
           (Prims.lift_native_int (1))
          in
       let uu____5464 =
         FStar_String.substring str (Prims.lift_native_int (1))
           ((FStar_String.length str) - (Prims.lift_native_int (1)))
          in
       Prims.strcat (FStar_String.uppercase first) uu____5464)
  
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
          let uu____5494 = FStar_Util.psmap_empty ()  in
          let uu____5497 =
            let uu____5500 = FStar_Options.prims ()  in uu____5500 :: deps
             in
          FStar_List.fold_left
            (fun acc  ->
               fun dep1  ->
                 let uu____5510 = FStar_Parser_Dep.lowercase_module_name dep1
                    in
                 FStar_Util.psmap_add acc uu____5510 true) uu____5494
            uu____5497
           in
        let loaded modname =
          FStar_Util.psmap_find_default loaded_mods_set modname false  in
        let this_mod_key = FStar_Parser_Dep.lowercase_module_name this_fname
           in
        FStar_List.fold_left
          (fun table1  ->
             fun uu____5528  ->
               match uu____5528 with
               | (modname,mod_path) ->
                   let mod_key = FStar_String.lowercase modname  in
                   if this_mod_key = mod_key
                   then table1
                   else
                     (let ns_query =
                        let uu____5540 = capitalize modname  in
                        FStar_Util.split uu____5540 "."  in
                      let uu____5541 = loaded mod_key  in
                      FStar_Interactive_CompletionTable.register_module_path
                        table1 uu____5541 mod_path ns_query)) table
          (FStar_List.rev mods)
  
let run_push_with_deps :
  'Auu____5552 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5552) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      (let uu____5576 = FStar_Options.debug_any ()  in
       if uu____5576
       then FStar_Util.print_string "Reloading dependencies"
       else ());
      FStar_TypeChecker_Env.toggle_id_info st.repl_env false;
      (let uu____5579 = load_deps st  in
       match uu____5579 with
       | FStar_Util.Inr st1 ->
           let errors =
             let uu____5612 = collect_errors ()  in
             FStar_List.map rephrase_dependency_error uu____5612  in
           let js_errors =
             FStar_All.pipe_right errors (FStar_List.map json_of_issue)  in
           ((QueryNOK, (FStar_Util.JsonList js_errors)),
             (FStar_Util.Inl st1))
       | FStar_Util.Inl (st1,deps) ->
           ((let uu____5643 = FStar_Options.restore_cmd_line_options false
                in
             FStar_All.pipe_right uu____5643 (fun a241  -> ()));
            (let names1 =
               add_module_completions st1.repl_fname deps st1.repl_names  in
             run_push_without_deps
               (let uu___104_5646 = st1  in
                {
                  repl_line = (uu___104_5646.repl_line);
                  repl_column = (uu___104_5646.repl_column);
                  repl_fname = (uu___104_5646.repl_fname);
                  repl_deps_stack = (uu___104_5646.repl_deps_stack);
                  repl_curmod = (uu___104_5646.repl_curmod);
                  repl_env = (uu___104_5646.repl_env);
                  repl_stdin = (uu___104_5646.repl_stdin);
                  repl_names = names1
                }) query)))
  
let run_push :
  'Auu____5653 .
    repl_state ->
      push_query ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____5653) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____5676 = nothing_left_to_pop st  in
      if uu____5676
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
              let uu____5764 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".")
                 in
              FStar_Ident.lid_of_ids uu____5764  in
            let lid1 =
              let uu____5768 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid
                 in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____5768  in
            let uu____5773 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1
               in
            FStar_All.pipe_right uu____5773
              (FStar_Util.map_option
                 (fun uu____5828  ->
                    match uu____5828 with
                    | ((uu____5847,typ),r) -> ((FStar_Util.Inr lid1), typ, r)))
             in
          let docs_of_lid lid =
            let uu____5866 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid
               in
            FStar_All.pipe_right uu____5866
              (FStar_Util.map_option FStar_Pervasives_Native.fst)
             in
          let def_of_lid lid =
            let uu____5897 = FStar_TypeChecker_Env.lookup_qname tcenv lid  in
            FStar_Util.bind_opt uu____5897
              (fun uu___85_5941  ->
                 match uu___85_5941 with
                 | (FStar_Util.Inr (se,uu____5963),uu____5964) ->
                     let uu____5993 = sigelt_to_string se  in
                     FStar_Pervasives_Native.Some uu____5993
                 | uu____5994 -> FStar_Pervasives_Native.None)
             in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____6046  ->
                 match uu____6046 with
                 | (file,row,col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col)
             in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____6093 -> info_at_pos_opt
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
                    let uu____6221 = term_to_string tcenv typ  in
                    FStar_Pervasives_Native.Some uu____6221
                  else FStar_Pervasives_Native.None  in
                let doc_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "documentation" requested_info ->
                      docs_of_lid lid
                  | uu____6229 -> FStar_Pervasives_Native.None  in
                let def_str =
                  match name_or_lid with
                  | FStar_Util.Inr lid when
                      FStar_List.mem "definition" requested_info ->
                      def_of_lid lid
                  | uu____6240 -> FStar_Pervasives_Native.None  in
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
                let uu____6252 =
                  let uu____6263 = alist_of_symbol_lookup_result result  in
                  ("symbol", uu____6263)  in
                FStar_Pervasives_Native.Some uu____6252
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
    let uu____6370 = trim_option_name opt_name  in
    match uu____6370 with
    | (uu____6389,trimmed_name) ->
        let uu____6391 =
          FStar_Util.smap_try_find fstar_options_map_cache trimmed_name  in
        (match uu____6391 with
         | FStar_Pervasives_Native.None  ->
             FStar_Util.Inl (Prims.strcat "Unknown option:" opt_name)
         | FStar_Pervasives_Native.Some opt ->
             let uu____6419 =
               let uu____6430 =
                 let uu____6437 = update_option opt  in
                 alist_of_fstar_option uu____6437  in
               ("option", uu____6430)  in
             FStar_Util.Inr uu____6419)
  
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
      let uu____6481 =
        FStar_Interactive_CompletionTable.find_module_or_ns st.repl_names
          query
         in
      match uu____6481 with
      | FStar_Pervasives_Native.None  ->
          FStar_Util.Inl "No such module or namespace"
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Module mod_info) ->
          let uu____6509 =
            let uu____6520 =
              FStar_Interactive_CompletionTable.alist_of_mod_info mod_info
               in
            ("module", uu____6520)  in
          FStar_Util.Inr uu____6509
      | FStar_Pervasives_Native.Some
          (FStar_Interactive_CompletionTable.Namespace ns_info) ->
          let uu____6544 =
            let uu____6555 =
              FStar_Interactive_CompletionTable.alist_of_ns_info ns_info  in
            ("namespace", uu____6555)  in
          FStar_Util.Inr uu____6544
  
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
          let uu____6632 = run_symbol_lookup st symbol pos_opt requested_info
             in
          match uu____6632 with
          | FStar_Util.Inr alist -> FStar_Util.Inr alist
          | FStar_Util.Inl uu____6692 ->
              let uu____6703 = run_module_lookup st symbol  in
              (match uu____6703 with
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
  'Auu____6869 .
    repl_state ->
      Prims.string ->
        lookup_context ->
          (Prims.string,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
            FStar_Pervasives_Native.option ->
            Prims.string Prims.list ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____6869) FStar_Util.either)
                FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun symbol  ->
      fun context  ->
        fun pos_opt  ->
          fun requested_info  ->
            let uu____6927 =
              run_lookup' st symbol context pos_opt requested_info  in
            match uu____6927 with
            | FStar_Util.Inl err_msg ->
                ((QueryNOK, (FStar_Util.JsonStr err_msg)),
                  (FStar_Util.Inl st))
            | FStar_Util.Inr (kind,info) ->
                ((QueryOK,
                   (FStar_Util.JsonAssoc (("kind", (FStar_Util.JsonStr kind))
                      :: info))), (FStar_Util.Inl st))
  
let code_autocomplete_mod_filter :
  'Auu____7013 .
    ('Auu____7013,FStar_Interactive_CompletionTable.mod_symbol)
      FStar_Pervasives_Native.tuple2 ->
      ('Auu____7013,FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option
  =
  fun uu___86_7028  ->
    match uu___86_7028 with
    | (uu____7033,FStar_Interactive_CompletionTable.Namespace uu____7034) ->
        FStar_Pervasives_Native.None
    | (uu____7039,FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____7040;
         FStar_Interactive_CompletionTable.mod_path = uu____7041;
         FStar_Interactive_CompletionTable.mod_loaded = true ;_})
        -> FStar_Pervasives_Native.None
    | (pth,FStar_Interactive_CompletionTable.Module md) ->
        let uu____7048 =
          let uu____7053 =
            let uu____7054 =
              let uu___105_7055 = md  in
              let uu____7056 =
                let uu____7057 =
                  FStar_Interactive_CompletionTable.mod_name md  in
                Prims.strcat uu____7057 "."  in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____7056;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___105_7055.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___105_7055.FStar_Interactive_CompletionTable.mod_loaded)
              }  in
            FStar_Interactive_CompletionTable.Module uu____7054  in
          (pth, uu____7053)  in
        FStar_Pervasives_Native.Some uu____7048
  
let run_code_autocomplete :
  'Auu____7068 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____7068) FStar_Util.either)
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
  'Auu____7125 'Auu____7126 'Auu____7127 .
    repl_state ->
      Prims.string ->
        'Auu____7125 ->
          'Auu____7126 ->
            ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
              (repl_state,'Auu____7127) FStar_Util.either)
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
              (fun _0_30  -> FStar_Pervasives_Native.Some _0_30)
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
        let uu____7198 =
          match opt.opt_permission_level with
          | OptSet  -> (true, "")
          | OptReset  -> (is_reset, "#reset-only")
          | OptReadOnly  -> (false, "read-only")  in
        match uu____7198 with
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
  'Auu____7230 'Auu____7231 .
    'Auu____7230 ->
      Prims.string ->
        Prims.bool ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            ('Auu____7230,'Auu____7231) FStar_Util.either)
            FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun search_term  ->
      fun is_reset  ->
        let uu____7259 = trim_option_name search_term  in
        match uu____7259 with
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
        | (uu____7314,uu____7315) ->
            ((QueryNOK,
               (FStar_Util.JsonStr "Options should start with '--'")),
              (FStar_Util.Inl st))
  
let run_autocomplete :
  'Auu____7332 .
    repl_state ->
      Prims.string ->
        completion_context ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7332) FStar_Util.either)
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
  'Auu____7371 'Auu____7372 .
    repl_state ->
      (repl_state -> 'Auu____7371) ->
        ('Auu____7371,(repl_state,'Auu____7372) FStar_Util.either)
          FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun task  ->
      let env' = push st.repl_env "#compute"  in
      let results =
        try
          let uu____7413 = task st  in
          FStar_All.pipe_left (fun _0_31  -> FStar_Util.Inl _0_31) uu____7413
        with | e -> FStar_Util.Inr e  in
      pop env' "#compute";
      (match results with
       | FStar_Util.Inl results1 ->
           (results1,
             (FStar_Util.Inl
                (let uu___108_7441 = st  in
                 {
                   repl_line = (uu___108_7441.repl_line);
                   repl_column = (uu___108_7441.repl_column);
                   repl_fname = (uu___108_7441.repl_fname);
                   repl_deps_stack = (uu___108_7441.repl_deps_stack);
                   repl_curmod = (uu___108_7441.repl_curmod);
                   repl_env = env';
                   repl_stdin = (uu___108_7441.repl_stdin);
                   repl_names = (uu___108_7441.repl_names)
                 })))
       | FStar_Util.Inr e -> FStar_Exn.raise e)
  
let run_with_parsed_and_tc_term :
  'Auu____7467 'Auu____7468 'Auu____7469 .
    repl_state ->
      Prims.string ->
        'Auu____7467 ->
          'Auu____7468 ->
            (FStar_TypeChecker_Env.env ->
               FStar_Syntax_Syntax.term ->
                 (query_status,FStar_Util.json)
                   FStar_Pervasives_Native.tuple2)
              ->
              ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
                (repl_state,'Auu____7469) FStar_Util.either)
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
                FStar_Parser_ParseIt.frag_line = (Prims.lift_native_int (0));
                FStar_Parser_ParseIt.frag_col = (Prims.lift_native_int (0))
              }  in
            let find_let_body ses =
              match ses with
              | {
                  FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                    ((uu____7562,{ FStar_Syntax_Syntax.lbname = uu____7563;
                                   FStar_Syntax_Syntax.lbunivs = univs1;
                                   FStar_Syntax_Syntax.lbtyp = uu____7565;
                                   FStar_Syntax_Syntax.lbeff = uu____7566;
                                   FStar_Syntax_Syntax.lbdef = def;
                                   FStar_Syntax_Syntax.lbattrs = uu____7568;
                                   FStar_Syntax_Syntax.lbpos = uu____7569;_}::[]),uu____7570);
                  FStar_Syntax_Syntax.sigrng = uu____7571;
                  FStar_Syntax_Syntax.sigquals = uu____7572;
                  FStar_Syntax_Syntax.sigmeta = uu____7573;
                  FStar_Syntax_Syntax.sigattrs = uu____7574;_}::[] ->
                  FStar_Pervasives_Native.Some (univs1, def)
              | uu____7617 -> FStar_Pervasives_Native.None  in
            let parse1 frag =
              let uu____7638 =
                FStar_Parser_ParseIt.parse
                  (FStar_Parser_ParseIt.Toplevel frag)
                 in
              match uu____7638 with
              | FStar_Parser_ParseIt.ASTFragment
                  (FStar_Util.Inr decls,uu____7644) ->
                  FStar_Pervasives_Native.Some decls
              | uu____7669 -> FStar_Pervasives_Native.None  in
            let desugar env decls =
              let uu____7687 =
                let uu____7692 =
                  FStar_ToSyntax_ToSyntax.decls_to_sigelts decls  in
                uu____7692 env.FStar_TypeChecker_Env.dsenv  in
              FStar_Pervasives_Native.fst uu____7687  in
            let typecheck tcenv decls =
              let uu____7716 = FStar_TypeChecker_Tc.tc_decls tcenv decls  in
              match uu____7716 with | (ses,uu____7730,uu____7731) -> ses  in
            run_and_rewind st
              (fun st1  ->
                 let tcenv = st1.repl_env  in
                 let frag = dummy_let_fragment term  in
                 match st1.repl_curmod with
                 | FStar_Pervasives_Native.None  ->
                     (QueryNOK, (FStar_Util.JsonStr "Current module unset"))
                 | uu____7754 ->
                     let uu____7755 = parse1 frag  in
                     (match uu____7755 with
                      | FStar_Pervasives_Native.None  ->
                          (QueryNOK,
                            (FStar_Util.JsonStr "Could not parse this term"))
                      | FStar_Pervasives_Native.Some decls ->
                          let aux uu____7780 =
                            let decls1 = desugar tcenv decls  in
                            let ses = typecheck tcenv decls1  in
                            match find_let_body ses with
                            | FStar_Pervasives_Native.None  ->
                                (QueryNOK,
                                  (FStar_Util.JsonStr
                                     "Typechecking yielded an unexpected term"))
                            | FStar_Pervasives_Native.Some (univs1,def) ->
                                let uu____7815 =
                                  FStar_Syntax_Subst.open_univ_vars univs1
                                    def
                                   in
                                (match uu____7815 with
                                 | (univs2,def1) ->
                                     let tcenv1 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         tcenv univs2
                                        in
                                     continuation tcenv1 def1)
                             in
                          let uu____7827 = FStar_Options.trace_error ()  in
                          if uu____7827
                          then aux ()
                          else
                            (try aux ()
                             with
                             | e ->
                                 let uu____7852 =
                                   let uu____7853 =
                                     FStar_Errors.issue_of_exn e  in
                                   match uu____7853 with
                                   | FStar_Pervasives_Native.Some issue ->
                                       let uu____7857 =
                                         FStar_Errors.format_issue issue  in
                                       FStar_Util.JsonStr uu____7857
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Exn.raise e
                                    in
                                 (QueryNOK, uu____7852))))
  
let run_compute :
  'Auu____7866 .
    repl_state ->
      Prims.string ->
        FStar_TypeChecker_Normalize.step Prims.list
          FStar_Pervasives_Native.option ->
          ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
            (repl_state,'Auu____7866) FStar_Util.either)
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
        run_with_parsed_and_tc_term st term (Prims.lift_native_int (0))
          (Prims.lift_native_int (0))
          (fun tcenv  ->
             fun def  ->
               let normalized = normalize_term1 tcenv rules1 def  in
               let uu____7938 =
                 let uu____7939 = term_to_string tcenv normalized  in
                 FStar_Util.JsonStr uu____7939  in
               (QueryOK, uu____7938))
  
type search_term' =
  | NameContainsStr of Prims.string 
  | TypeContainsLid of FStar_Ident.lid [@@deriving show]
and search_term = {
  st_negate: Prims.bool ;
  st_term: search_term' }[@@deriving show]
let uu___is_NameContainsStr : search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | NameContainsStr _0 -> true | uu____7966 -> false
  
let __proj__NameContainsStr__item___0 : search_term' -> Prims.string =
  fun projectee  -> match projectee with | NameContainsStr _0 -> _0 
let uu___is_TypeContainsLid : search_term' -> Prims.bool =
  fun projectee  ->
    match projectee with | TypeContainsLid _0 -> true | uu____7980 -> false
  
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
  fun uu___87_8006  ->
    match uu___87_8006 with
    | NameContainsStr str -> - (FStar_String.length str)
    | TypeContainsLid lid -> (Prims.lift_native_int (1))
  
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
    let uu____8221 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    let uu____8228 = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
    { sc_lid = lid; sc_typ = uu____8221; sc_fvars = uu____8228 }
  
let sc_typ :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Syntax_Syntax.typ =
  fun tcenv  ->
    fun sc  ->
      let uu____8295 = FStar_ST.op_Bang sc.sc_typ  in
      match uu____8295 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let typ =
            let uu____8329 =
              FStar_TypeChecker_Env.try_lookup_lid tcenv sc.sc_lid  in
            match uu____8329 with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                  FStar_Pervasives_Native.None FStar_Range.dummyRange
            | FStar_Pervasives_Native.Some ((uu____8350,typ),uu____8352) ->
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
      let uu____8407 = FStar_ST.op_Bang sc.sc_fvars  in
      match uu____8407 with
      | FStar_Pervasives_Native.Some fv -> fv
      | FStar_Pervasives_Native.None  ->
          let fv =
            let uu____8455 = sc_typ tcenv sc  in
            FStar_Syntax_Free.fvars uu____8455  in
          (FStar_ST.op_Colon_Equals sc.sc_fvars
             (FStar_Pervasives_Native.Some fv);
           fv)
  
let json_of_search_result :
  FStar_TypeChecker_Env.env -> search_candidate -> FStar_Util.json =
  fun tcenv  ->
    fun sc  ->
      let typ_str =
        let uu____8501 = sc_typ tcenv sc  in term_to_string tcenv uu____8501
         in
      let uu____8502 =
        let uu____8509 =
          let uu____8514 =
            let uu____8515 =
              let uu____8516 =
                FStar_Syntax_DsEnv.shorten_lid
                  tcenv.FStar_TypeChecker_Env.dsenv sc.sc_lid
                 in
              uu____8516.FStar_Ident.str  in
            FStar_Util.JsonStr uu____8515  in
          ("lid", uu____8514)  in
        [uu____8509; ("type", (FStar_Util.JsonStr typ_str))]  in
      FStar_Util.JsonAssoc uu____8502
  
exception InvalidSearch of Prims.string 
let uu___is_InvalidSearch : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | InvalidSearch uu____8538 -> true
    | uu____8539 -> false
  
let __proj__InvalidSearch__item__uu___ : Prims.exn -> Prims.string =
  fun projectee  ->
    match projectee with | InvalidSearch uu____8546 -> uu____8546
  
let run_search :
  'Auu____8553 .
    repl_state ->
      Prims.string ->
        ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
          (repl_state,'Auu____8553) FStar_Util.either)
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
              let uu____8594 = sc_fvars tcenv candidate  in
              FStar_Util.set_mem lid uu____8594
           in
        found <> term.st_negate  in
      let parse1 search_str1 =
        let parse_one term =
          let negate = FStar_Util.starts_with term "-"  in
          let term1 =
            if negate
            then FStar_Util.substring_from term (Prims.lift_native_int (1))
            else term  in
          let beg_quote = FStar_Util.starts_with term1 "\""  in
          let end_quote = FStar_Util.ends_with term1 "\""  in
          let strip_quotes str =
            if (FStar_String.length str) < (Prims.lift_native_int (2))
            then FStar_Exn.raise (InvalidSearch "Empty search term")
            else
              FStar_Util.substring str (Prims.lift_native_int (1))
                ((FStar_String.length term1) - (Prims.lift_native_int (2)))
             in
          let parsed =
            if beg_quote <> end_quote
            then
              let uu____8624 =
                let uu____8625 =
                  FStar_Util.format1 "Improperly quoted search term: %s"
                    term1
                   in
                InvalidSearch uu____8625  in
              FStar_Exn.raise uu____8624
            else
              if beg_quote
              then
                (let uu____8627 = strip_quotes term1  in
                 NameContainsStr uu____8627)
              else
                (let lid = FStar_Ident.lid_of_str term1  in
                 let uu____8630 =
                   FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                     tcenv.FStar_TypeChecker_Env.dsenv lid
                    in
                 match uu____8630 with
                 | FStar_Pervasives_Native.None  ->
                     let uu____8633 =
                       let uu____8634 =
                         FStar_Util.format1 "Unknown identifier: %s" term1
                          in
                       InvalidSearch uu____8634  in
                     FStar_Exn.raise uu____8633
                 | FStar_Pervasives_Native.Some lid1 -> TypeContainsLid lid1)
             in
          { st_negate = negate; st_term = parsed }  in
        let terms =
          FStar_List.map parse_one (FStar_Util.split search_str1 " ")  in
        let cmp x y = (st_cost x.st_term) - (st_cost y.st_term)  in
        FStar_Util.sort_with cmp terms  in
      let pprint_one term =
        let uu____8656 =
          match term.st_term with
          | NameContainsStr s -> FStar_Util.format1 "\"%s\"" s
          | TypeContainsLid l -> FStar_Util.format1 "%s" l.FStar_Ident.str
           in
        Prims.strcat (if term.st_negate then "-" else "") uu____8656  in
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
                let uu____8725 = FStar_List.map pprint_one terms  in
                FStar_Util.concat_l " " uu____8725  in
              let uu____8728 =
                let uu____8729 =
                  FStar_Util.format1 "No results found for query [%s]" kwds
                   in
                InvalidSearch uu____8729  in
              FStar_Exn.raise uu____8728
          | uu____8734 -> (QueryOK, (FStar_Util.JsonList js))
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
          { push_kind = SyntaxCheck ; push_code = uu____8832;
            push_line = uu____8833; push_column = uu____8834;
            push_peek_only = false ;_}
          ->
          {
            qq =
              (ProtocolViolation
                 "Cannot use 'kind': 'syntax' with 'query': 'push'");
            qid = (q.qid)
          }
      | uu____8835 ->
          (match st.repl_curmod with
           | FStar_Pervasives_Native.None  when
               query_needs_current_module q.qq ->
               { qq = (GenericError "Current module unset"); qid = (q.qid) }
           | uu____8836 -> q)
  
let validate_and_run_query :
  repl_state ->
    query ->
      ((query_status,FStar_Util.json) FStar_Pervasives_Native.tuple2,
        (repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let query1 = validate_query st query  in
      FStar_ST.op_Colon_Equals repl_current_qid
        (FStar_Pervasives_Native.Some (query1.qid));
      run_query st query1.qq
  
let js_repl_eval :
  repl_state ->
    query ->
      (FStar_Util.json,(repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query  ->
      let uu____8906 = validate_and_run_query st query  in
      match uu____8906 with
      | ((status,response),st_opt) ->
          let js_response = json_of_response query.qid status response  in
          (js_response, st_opt)
  
let js_repl_eval_js :
  repl_state ->
    FStar_Util.json ->
      (FStar_Util.json,(repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query_js  ->
      let uu____8965 = deserialize_interactive_query query_js  in
      js_repl_eval st uu____8965
  
let js_repl_eval_str :
  repl_state ->
    Prims.string ->
      (Prims.string,(repl_state,Prims.int) FStar_Util.either)
        FStar_Pervasives_Native.tuple2
  =
  fun st  ->
    fun query_str  ->
      let uu____8984 =
        let uu____8993 = parse_interactive_query query_str  in
        js_repl_eval st uu____8993  in
      match uu____8984 with
      | (js_response,st_opt) ->
          let uu____9012 = FStar_Util.string_of_json js_response  in
          (uu____9012, st_opt)
  
let js_repl_init_opts : unit -> unit =
  fun uu____9021  ->
    let uu____9022 = FStar_Options.parse_cmd_line ()  in
    match uu____9022 with
    | (res,fnames) ->
        (match res with
         | FStar_Getopt.Error msg ->
             failwith (Prims.strcat "repl_init: " msg)
         | FStar_Getopt.Help  -> failwith "repl_init: --help unexpected"
         | FStar_Getopt.Success  ->
             (match fnames with
              | [] ->
                  failwith
                    "repl_init: No file name given in --ide invocation"
              | h::uu____9037::uu____9038 ->
                  failwith
                    "repl_init: Too many file names given in --ide invocation"
              | uu____9041 -> ()))
  
let rec go : repl_state -> Prims.int =
  fun st  ->
    let query = read_interactive_query st.repl_stdin  in
    let uu____9050 = validate_and_run_query st query  in
    match uu____9050 with
    | ((status,response),state_opt) ->
        (write_response query.qid status response;
         (match state_opt with
          | FStar_Util.Inl st' -> go st'
          | FStar_Util.Inr exitcode -> exitcode))
  
let interactive_error_handler : FStar_Errors.error_handler =
  let issues = FStar_Util.mk_ref []  in
  let add_one1 e =
    let uu____9094 =
      let uu____9097 = FStar_ST.op_Bang issues  in e :: uu____9097  in
    FStar_ST.op_Colon_Equals issues uu____9094  in
  let count_errors uu____9203 =
    let uu____9204 =
      let uu____9207 = FStar_ST.op_Bang issues  in
      FStar_List.filter
        (fun e  -> e.FStar_Errors.issue_level = FStar_Errors.EError)
        uu____9207
       in
    FStar_List.length uu____9204  in
  let report uu____9268 =
    let uu____9269 = FStar_ST.op_Bang issues  in
    FStar_List.sortWith FStar_Errors.compare_issues uu____9269  in
  let clear1 uu____9326 = FStar_ST.op_Colon_Equals issues []  in
  {
    FStar_Errors.eh_add_one = add_one1;
    FStar_Errors.eh_count_errors = count_errors;
    FStar_Errors.eh_report = report;
    FStar_Errors.eh_clear = clear1
  } 
let interactive_printer : (FStar_Util.json -> unit) -> FStar_Util.printer =
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
               let uu____9408 = get_json ()  in
               forward_message printer label uu____9408)
    }
  
let install_ide_mode_hooks : (FStar_Util.json -> unit) -> unit =
  fun printer  ->
    FStar_Util.set_printer (interactive_printer printer);
    FStar_Errors.set_handler interactive_error_handler
  
let initial_range : FStar_Range.range =
  let uu____9420 =
    FStar_Range.mk_pos (Prims.lift_native_int (1))
      (Prims.lift_native_int (0))
     in
  let uu____9421 =
    FStar_Range.mk_pos (Prims.lift_native_int (1))
      (Prims.lift_native_int (0))
     in
  FStar_Range.mk_range "<input>" uu____9420 uu____9421 
let build_initial_repl_state : Prims.string -> repl_state =
  fun filename  ->
    let env = FStar_Universal.init_env FStar_Parser_Dep.empty_deps  in
    let env1 = FStar_TypeChecker_Env.set_range env initial_range  in
    let uu____9429 = FStar_Util.open_stdin ()  in
    {
      repl_line = (Prims.lift_native_int (1));
      repl_column = (Prims.lift_native_int (0));
      repl_fname = filename;
      repl_deps_stack = [];
      repl_curmod = FStar_Pervasives_Native.None;
      repl_env = env1;
      repl_stdin = uu____9429;
      repl_names = FStar_Interactive_CompletionTable.empty
    }
  
let interactive_mode' : 'Auu____9438 . repl_state -> 'Auu____9438 =
  fun init_st  ->
    write_hello ();
    (let exit_code =
       let uu____9446 =
         (FStar_Options.record_hints ()) || (FStar_Options.use_hints ())  in
       if uu____9446
       then
         let uu____9447 =
           let uu____9448 = FStar_Options.file_list ()  in
           FStar_List.hd uu____9448  in
         FStar_SMTEncoding_Solver.with_hints_db uu____9447
           (fun uu____9452  -> go init_st)
       else go init_st  in
     FStar_All.exit exit_code)
  
let interactive_mode : Prims.string -> unit =
  fun filename  ->
    install_ide_mode_hooks write_json;
    (let uu____9461 =
       let uu____9462 = FStar_Options.codegen ()  in
       FStar_Option.isSome uu____9462  in
     if uu____9461
     then
       FStar_Errors.log_issue FStar_Range.dummyRange
         (FStar_Errors.Warning_IDEIgnoreCodeGen, "--ide: ignoring --codegen")
     else ());
    (let init1 = build_initial_repl_state filename  in
     let uu____9467 = FStar_Options.trace_error ()  in
     if uu____9467
     then interactive_mode' init1
     else
       (try interactive_mode' init1
        with
        | e ->
            (FStar_Errors.set_handler FStar_Errors.default_handler;
             FStar_Exn.raise e)))
  
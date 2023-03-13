open Prims
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type timed_fname =
  {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Compiler_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Compiler_Util.time) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of (FStar_Parser_ParseIt.input_frag, FStar_Parser_AST.decl)
  FStar_Pervasives.either 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDInterleaved _0 -> true | uu___ -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu___ -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu___ -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu___ -> false
let (__proj__PushFragment__item___0 :
  repl_task ->
    (FStar_Parser_ParseIt.input_frag, FStar_Parser_AST.decl)
      FStar_Pervasives.either)
  = fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu___ -> false
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: FStar_TypeChecker_Env.env ;
  repl_stdin: FStar_Compiler_Util.stream_reader ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_column
let (__proj__Mkrepl_state__item__repl_fname : repl_state -> Prims.string) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_fname
let (__proj__Mkrepl_state__item__repl_deps_stack :
  repl_state -> (repl_depth_t * (repl_task * repl_state)) Prims.list) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_deps_stack
let (__proj__Mkrepl_state__item__repl_curmod : repl_state -> optmod_t) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_curmod
let (__proj__Mkrepl_state__item__repl_env :
  repl_state -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_env
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Compiler_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_stdin
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_fname; repl_deps_stack; repl_curmod;
        repl_env; repl_stdin; repl_names;_} -> repl_names
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
type grepl_state =
  {
  grepl_repls: repl_state FStar_Compiler_Util.psmap ;
  grepl_stdin: FStar_Compiler_Util.stream_reader }
let (__proj__Mkgrepl_state__item__grepl_repls :
  grepl_state -> repl_state FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_repls
let (__proj__Mkgrepl_state__item__grepl_stdin :
  grepl_state -> FStar_Compiler_Util.stream_reader) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_stdin
let (t0 : FStar_Compiler_Util.time) = FStar_Compiler_Util.now ()
let (dummy_tf_of_fname : Prims.string -> timed_fname) =
  fun fname -> { tf_fname = fname; tf_modtime = t0 }
let (string_of_timed_fname : timed_fname -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | { tf_fname = fname; tf_modtime = modtime;_} ->
        if modtime = t0
        then FStar_Compiler_Util.format1 "{ %s }" fname
        else
          (let uu___2 = FStar_Compiler_Util.string_of_time modtime in
           FStar_Compiler_Util.format2 "{ %s; %s }" fname uu___2)
let (string_of_repl_task : repl_task -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | LDInterleaved (intf, impl) ->
        let uu___1 = string_of_timed_fname intf in
        let uu___2 = string_of_timed_fname impl in
        FStar_Compiler_Util.format2 "LDInterleaved (%s, %s)" uu___1 uu___2
    | LDSingle intf_or_impl ->
        let uu___1 = string_of_timed_fname intf_or_impl in
        FStar_Compiler_Util.format1 "LDSingle %s" uu___1
    | LDInterfaceOfCurrentFile intf ->
        let uu___1 = string_of_timed_fname intf in
        FStar_Compiler_Util.format1 "LDInterfaceOfCurrentFile %s" uu___1
    | PushFragment (FStar_Pervasives.Inl frag) ->
        FStar_Compiler_Util.format1 "PushFragment { code = %s }"
          frag.FStar_Parser_ParseIt.frag_text
    | PushFragment (FStar_Pervasives.Inr d) ->
        let uu___1 = FStar_Parser_AST.decl_to_string d in
        FStar_Compiler_Util.format1 "PushFragment { decl = %s }" uu___1
    | Noop -> "Noop {}"
let (string_of_repl_stack_entry : repl_stack_entry_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ((depth, i), (task, state)) ->
        let uu___1 =
          let uu___2 = FStar_Compiler_Util.string_of_int i in
          let uu___3 = let uu___4 = string_of_repl_task task in [uu___4] in
          uu___2 :: uu___3 in
        FStar_Compiler_Util.format "{depth=%s; task=%s}" uu___1
let (string_of_repl_stack : repl_stack_entry_t Prims.list -> Prims.string) =
  fun s ->
    let uu___ = FStar_Compiler_List.map string_of_repl_stack_entry s in
    FStar_String.concat ";\n\t\t" uu___
let (repl_state_to_string : repl_state -> Prims.string) =
  fun r ->
    let uu___ =
      let uu___1 = FStar_Compiler_Util.string_of_int r.repl_line in
      let uu___2 =
        let uu___3 = FStar_Compiler_Util.string_of_int r.repl_column in
        let uu___4 =
          let uu___5 =
            let uu___6 =
              match r.repl_curmod with
              | FStar_Pervasives_Native.None -> "None"
              | FStar_Pervasives_Native.Some m ->
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
            let uu___7 =
              let uu___8 = string_of_repl_stack r.repl_deps_stack in [uu___8] in
            uu___6 :: uu___7 in
          (r.repl_fname) :: uu___5 in
        uu___3 :: uu___4 in
      uu___1 :: uu___2 in
    FStar_Compiler_Util.format
      "{\n\trepl_line=%s;\n\trepl_column=%s;\n\trepl_fname=%s;\n\trepl_cur_mod=%s;\n\t\\      \n      repl_deps_stack={%s}\n}"
      uu___
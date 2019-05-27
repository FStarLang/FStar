open Prims
let (try_assoc :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list ->
      FStar_Util.json FStar_Pervasives_Native.option)
  =
  fun key ->
    fun d ->
      let uu____53 =
        FStar_Util.try_find
          (fun uu____69 -> match uu____69 with | (k, uu____77) -> k = key) d in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____53
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu____100 -> true | uu____103 -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu____113 -> uu____113
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____128 -> true
    | uu____131 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu____141 -> uu____141
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____160 -> true
    | uu____167 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____185 -> uu____185
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu____200 -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu____211 -> false
let (assoc :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun key ->
    fun a ->
      let uu____240 = try_assoc key a in
      match uu____240 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____244 =
            let uu____245 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____245 in
          FStar_Exn.raise uu____244
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____255 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____255);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____268 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____268
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_302 ->
    match uu___0_302 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_319 ->
    match uu___1_319 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_348 ->
      match uu___2_348 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___3_380 ->
    match uu___3_380 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_415 ->
    match uu___4_415 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun k ->
    fun r ->
      let uu____451 =
        let uu____459 = assoc "params" r in
        FStar_All.pipe_right uu____459 js_assoc in
      assoc k uu____451
let (uri_to_path : Prims.string -> Prims.string) =
  fun u ->
    if FStar_Util.starts_with u "file://"
    then FStar_Util.substring_from u (Prims.parse_int "7")
    else u
type completion_context =
  {
  trigger_kind: Prims.int ;
  trigger_char: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkcompletion_context__item__trigger_kind :
  completion_context -> Prims.int) =
  fun projectee ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_kind
let (__proj__Mkcompletion_context__item__trigger_char :
  completion_context -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_char
let (js_compl_context : FStar_Util.json -> completion_context) =
  fun uu___5_537 ->
    match uu___5_537 with
    | FStar_Util.JsonAssoc a ->
        let uu____546 =
          let uu____548 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____548 js_int in
        let uu____551 =
          let uu____555 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____555 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____546; trigger_char = uu____551 }
    | other -> js_fail "dictionary" other
type txdoc_item =
  {
  fname: Prims.string ;
  langId: Prims.string ;
  version: Prims.int ;
  text: Prims.string }
let (__proj__Mktxdoc_item__item__fname : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> fname
let (__proj__Mktxdoc_item__item__langId : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> langId
let (__proj__Mktxdoc_item__item__version : txdoc_item -> Prims.int) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> version
let (__proj__Mktxdoc_item__item__text : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { fname; langId; version; text;_} -> text
let (js_txdoc_item : FStar_Util.json -> txdoc_item) =
  fun uu___6_663 ->
    match uu___6_663 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____680 =
          let uu____682 = arg1 "uri" in FStar_All.pipe_right uu____682 js_str in
        let uu____685 =
          let uu____687 = arg1 "languageId" in
          FStar_All.pipe_right uu____687 js_str in
        let uu____690 =
          let uu____692 = arg1 "version" in
          FStar_All.pipe_right uu____692 js_int in
        let uu____695 =
          let uu____697 = arg1 "text" in
          FStar_All.pipe_right uu____697 js_str in
        {
          fname = uu____680;
          langId = uu____685;
          version = uu____690;
          text = uu____695
        }
    | other -> js_fail "dictionary" other
type txdoc_pos = {
  uri: Prims.string ;
  line: Prims.int ;
  col: Prims.int }
let (__proj__Mktxdoc_pos__item__uri : txdoc_pos -> Prims.string) =
  fun projectee -> match projectee with | { uri; line; col;_} -> uri
let (__proj__Mktxdoc_pos__item__line : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { uri; line; col;_} -> line
let (__proj__Mktxdoc_pos__item__col : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { uri; line; col;_} -> col
let (js_txdoc_id :
  (Prims.string * FStar_Util.json) Prims.list -> Prims.string) =
  fun r ->
    let uu____784 =
      let uu____785 =
        let uu____793 = arg "textDocument" r in
        FStar_All.pipe_right uu____793 js_assoc in
      assoc "uri" uu____785 in
    FStar_All.pipe_right uu____784 js_str
let (js_txdoc_pos : (Prims.string * FStar_Util.json) Prims.list -> txdoc_pos)
  =
  fun r ->
    let pos =
      let uu____832 = arg "position" r in
      FStar_All.pipe_right uu____832 js_assoc in
    let uu____841 = js_txdoc_id r in
    let uu____843 =
      let uu____845 = assoc "line" pos in
      FStar_All.pipe_right uu____845 js_int in
    let uu____848 =
      let uu____850 = assoc "character" pos in
      FStar_All.pipe_right uu____850 js_int in
    { uri = uu____841; line = uu____843; col = uu____848 }
type workspace_folder = {
  wk_uri: Prims.string ;
  wk_name: Prims.string }
let (__proj__Mkworkspace_folder__item__wk_uri :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { wk_uri; wk_name;_} -> wk_uri
let (__proj__Mkworkspace_folder__item__wk_name :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { wk_uri; wk_name;_} -> wk_name
type wsch_event = {
  added: workspace_folder ;
  removed: workspace_folder }
let (__proj__Mkwsch_event__item__added : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> added
let (__proj__Mkwsch_event__item__removed : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> removed
let (js_wsch_event : FStar_Util.json -> wsch_event) =
  fun uu___7_923 ->
    match uu___7_923 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____940 = assoc "added" a in
          FStar_All.pipe_right uu____940 js_assoc in
        let removed' =
          let uu____957 = assoc "removed" a in
          FStar_All.pipe_right uu____957 js_assoc in
        let uu____966 =
          let uu____967 =
            let uu____969 = assoc "uri" added' in
            FStar_All.pipe_right uu____969 js_str in
          let uu____972 =
            let uu____974 = assoc "name" added' in
            FStar_All.pipe_right uu____974 js_str in
          { wk_uri = uu____967; wk_name = uu____972 } in
        let uu____977 =
          let uu____978 =
            let uu____980 = assoc "uri" removed' in
            FStar_All.pipe_right uu____980 js_str in
          let uu____983 =
            let uu____985 = assoc "name" removed' in
            FStar_All.pipe_right uu____985 js_str in
          { wk_uri = uu____978; wk_name = uu____983 } in
        { added = uu____966; removed = uu____977 }
    | other -> js_fail "dictionary" other
type lquery =
  | Initialize of (Prims.int * Prims.string) 
  | Initialized 
  | Shutdown 
  | Exit 
  | Cancel of Prims.string 
  | FolderChange of wsch_event 
  | ChangeConfig 
  | ChangeWatch 
  | Symbol of Prims.string 
  | ExecCommand of Prims.string 
  | DidOpen of txdoc_item 
  | DidChange 
  | WillSave of Prims.string 
  | WillSaveWait of Prims.string 
  | DidSave of Prims.string 
  | DidClose of Prims.string 
  | Completion of completion_context 
  | Resolve 
  | Hover of txdoc_pos 
  | SignatureHelp of txdoc_pos 
  | Declaration of txdoc_pos 
  | Definition of txdoc_pos 
  | TypeDefinition of txdoc_pos 
  | Implementation of txdoc_pos 
  | References 
  | DocumentHighlight of txdoc_pos 
  | DocumentSymbol 
  | CodeAction 
  | CodeLens 
  | CodeLensResolve 
  | DocumentLink 
  | DocumentLinkResolve 
  | DocumentColor 
  | ColorPresentation 
  | Formatting 
  | RangeFormatting 
  | TypeFormatting 
  | Rename 
  | PrepareRename of txdoc_pos 
  | FoldingRange 
  | BadProtocolMsg of Prims.string 
let (uu___is_Initialize : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialize _0 -> true | uu____1120 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____1156 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____1167 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1178 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____1191 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____1213 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____1231 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____1242 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____1255 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____1278 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____1300 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange -> true | uu____1318 -> false
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1331 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1354 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1377 -> false
let (__proj__DidSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1400 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1422 -> false
let (__proj__Completion__item___0 : lquery -> completion_context) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1440 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1452 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1471 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1490 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1509 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1528 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1547 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1565 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1577 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1595 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1606 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1617 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____1628 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____1639 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____1650 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____1661 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____1672 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____1683 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____1694 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____1705 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____1716 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____1728 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____1746 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1759 -> false
let (__proj__BadProtocolMsg__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | BadProtocolMsg _0 -> _0
type lsp_query =
  {
  query_id: Prims.int FStar_Pervasives_Native.option ;
  q: lquery }
let (__proj__Mklsp_query__item__query_id :
  lsp_query -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | { query_id; q;_} -> query_id
let (__proj__Mklsp_query__item__q : lsp_query -> lquery) =
  fun projectee -> match projectee with | { query_id; q;_} -> q
type repl_depth_t = (FStar_TypeChecker_Env.tcenv_depth_t * Prims.int)
type optmod_t = FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option
type timed_fname = {
  tf_fname: Prims.string ;
  tf_modtime: FStar_Util.time }
let (__proj__Mktimed_fname__item__tf_fname : timed_fname -> Prims.string) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_fname
let (__proj__Mktimed_fname__item__tf_modtime :
  timed_fname -> FStar_Util.time) =
  fun projectee ->
    match projectee with | { tf_fname; tf_modtime;_} -> tf_modtime
type repl_task =
  | LDInterleaved of (timed_fname * timed_fname) 
  | LDSingle of timed_fname 
  | LDInterfaceOfCurrentFile of timed_fname 
  | PushFragment of FStar_Parser_ParseIt.input_frag 
  | Noop 
let (uu___is_LDInterleaved : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDInterleaved _0 -> true | uu____1888 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____1919 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____1938 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____1957 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____1975 -> false
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_fname: Prims.string ;
  repl_deps_stack: (repl_depth_t * (repl_task * repl_state)) Prims.list ;
  repl_curmod: optmod_t ;
  repl_env: FStar_TypeChecker_Env.env ;
  repl_stdin: FStar_Util.stream_reader ;
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
  repl_state -> FStar_Util.stream_reader) =
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
type grepl_state = repl_state FStar_Util.smap
type optresponse =
  (FStar_Util.json, FStar_Util.json) FStar_Util.either
    FStar_Pervasives_Native.option
type either_st_exit = (repl_state, Prims.int) FStar_Util.either
type error_code =
  | ParseError 
  | InvalidRequest 
  | MethodNotFound 
  | InvalidParams 
  | InternalError 
  | ServerErrorStart 
  | ServerErrorEnd 
  | ServerNotInitialized 
  | UnknownErrorCode 
  | RequestCancelled 
  | ContentModified 
let (uu___is_ParseError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ParseError -> true | uu____2312 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____2323 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____2334 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____2345 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____2356 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____2367 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____2378 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____2389 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____2400 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____2411 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____2422 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___8_2434 ->
    match uu___8_2434 with
    | ParseError -> ~- (Prims.parse_int "32700")
    | InvalidRequest -> ~- (Prims.parse_int "32600")
    | MethodNotFound -> ~- (Prims.parse_int "32601")
    | InvalidParams -> ~- (Prims.parse_int "32602")
    | InternalError -> ~- (Prims.parse_int "32603")
    | ServerErrorStart -> ~- (Prims.parse_int "32099")
    | ServerErrorEnd -> ~- (Prims.parse_int "32000")
    | ServerNotInitialized -> ~- (Prims.parse_int "32002")
    | UnknownErrorCode -> ~- (Prims.parse_int "32001")
    | RequestCancelled -> ~- (Prims.parse_int "32800")
    | ContentModified -> ~- (Prims.parse_int "32801")
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___9_2453 ->
    match uu___9_2453 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2467 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2467
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2473 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2477 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2510 =
          let uu____2511 =
            let uu____2513 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2513 in
          BadProtocolMsg uu____2511 in
        { query_id = qid; q = uu____2510 }
let (json_of_response :
  Prims.int FStar_Pervasives_Native.option ->
    (FStar_Util.json, FStar_Util.json) FStar_Util.either -> FStar_Util.json)
  =
  fun qid ->
    fun response ->
      let qid1 =
        match qid with
        | FStar_Pervasives_Native.Some i -> FStar_Util.JsonInt i
        | FStar_Pervasives_Native.None -> FStar_Util.JsonNull in
      match response with
      | FStar_Util.Inl result ->
          FStar_Util.JsonAssoc
            [("jsonrpc", (FStar_Util.JsonStr "2.0"));
            ("id", qid1);
            ("result", result)]
      | FStar_Util.Inr err ->
          FStar_Util.JsonAssoc
            [("jsonrpc", (FStar_Util.JsonStr "2.0"));
            ("id", qid1);
            ("error", err)]
let (js_resperr : error_code -> Prims.string -> FStar_Util.json) =
  fun err ->
    fun msg ->
      let uu____2615 =
        let uu____2623 =
          let uu____2629 =
            let uu____2630 = errorcode_to_int err in
            FStar_Util.JsonInt uu____2630 in
          ("code", uu____2629) in
        [uu____2623; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____2615
let (wrap_content_szerr : Prims.string -> lsp_query) =
  fun m ->
    { query_id = FStar_Pervasives_Native.None; q = (BadProtocolMsg m) }
let (js_servcap : FStar_Util.json) =
  FStar_Util.JsonAssoc
    [("capabilities",
       (FStar_Util.JsonAssoc
          [("textDocumentSync",
             (FStar_Util.JsonAssoc
                [("openClose", (FStar_Util.JsonBool true));
                ("change", (FStar_Util.JsonInt (Prims.parse_int "1")));
                ("willSave", (FStar_Util.JsonBool true));
                ("willSaveWaitUntil", (FStar_Util.JsonBool false))]));
          ("hoverProvider", (FStar_Util.JsonBool false));
          ("completionProvider",
            (FStar_Util.JsonAssoc
               [("resolveProvider", (FStar_Util.JsonBool false))]));
          ("signatureHelpProvider", (FStar_Util.JsonAssoc []));
          ("definitionProvider", (FStar_Util.JsonBool true));
          ("typeDefinitionProvider", (FStar_Util.JsonBool false));
          ("implementationProvider", (FStar_Util.JsonBool false));
          ("referencesProvider", (FStar_Util.JsonBool false));
          ("documentSymbolProvider", (FStar_Util.JsonBool false));
          ("workspaceSymbolProvider", (FStar_Util.JsonBool false));
          ("codeActionProvider", (FStar_Util.JsonBool false))]))]
let (js_pos : FStar_Range.pos -> FStar_Util.json) =
  fun p ->
    let uu____2824 =
      let uu____2832 =
        let uu____2838 =
          let uu____2839 = FStar_Range.line_of_pos p in
          FStar_Util.JsonInt uu____2839 in
        ("line", uu____2838) in
      let uu____2843 =
        let uu____2851 =
          let uu____2857 =
            let uu____2858 = FStar_Range.col_of_pos p in
            FStar_Util.JsonInt uu____2858 in
          ("column", uu____2857) in
        [uu____2851] in
      uu____2832 :: uu____2843 in
    FStar_Util.JsonAssoc uu____2824
let (js_range : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let uu____2883 =
      let uu____2891 =
        let uu____2897 =
          let uu____2898 = FStar_Range.file_of_range r in
          FStar_Util.JsonStr uu____2898 in
        ("uri", uu____2897) in
      let uu____2902 =
        let uu____2910 =
          let uu____2916 =
            let uu____2917 =
              let uu____2925 =
                let uu____2931 =
                  let uu____2932 = FStar_Range.start_of_range r in
                  js_pos uu____2932 in
                ("start", uu____2931) in
              let uu____2935 =
                let uu____2943 =
                  let uu____2949 =
                    let uu____2950 = FStar_Range.end_of_range r in
                    js_pos uu____2950 in
                  ("end", uu____2949) in
                [uu____2943] in
              uu____2925 :: uu____2935 in
            FStar_Util.JsonAssoc uu____2917 in
          ("range", uu____2916) in
        [uu____2910] in
      uu____2891 :: uu____2902 in
    FStar_Util.JsonAssoc uu____2883
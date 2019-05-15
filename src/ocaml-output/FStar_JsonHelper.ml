open Prims
let try_assoc :
  'a .
    Prims.string ->
      (Prims.string * 'a) Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun a1 ->
    fun a2 ->
      (fun key ->
         fun d ->
           let d = Obj.magic d in
           let uu____53 =
             FStar_Util.try_find
               (fun uu____69 ->
                  match uu____69 with | (k, uu____77) -> k = key)
               (Obj.magic d) in
           Obj.magic
             (FStar_Util.map_option FStar_Pervasives_Native.snd uu____53)) a1
        a2
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
let assoc : 'a . Prims.string -> (Prims.string * 'a) Prims.list -> 'a =
  fun key ->
    fun a ->
      let uu____247 = try_assoc key a in
      match uu____247 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____251 =
            let uu____252 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____252 in
          FStar_Exn.raise uu____251
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____262 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____262);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____275 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____275
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_309 ->
    match uu___0_309 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_326 ->
    match uu___1_326 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_355 ->
      match uu___2_355 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___3_387 ->
    match uu___3_387 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_422 ->
    match uu___4_422 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun k ->
    fun r ->
      let uu____458 =
        let uu____466 = assoc "params" r in
        FStar_All.pipe_right uu____466 js_assoc in
      assoc k uu____458
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
  fun uu___5_529 ->
    match uu___5_529 with
    | FStar_Util.JsonAssoc a ->
        let uu____538 =
          let uu____540 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____540 js_int in
        let uu____543 =
          let uu____547 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____547 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____538; trigger_char = uu____543 }
    | other -> js_fail "dictionary" other
type txdoc_item =
  {
  uri: Prims.string ;
  langId: Prims.string ;
  version: Prims.int ;
  text: Prims.string }
let (__proj__Mktxdoc_item__item__uri : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { uri; langId; version; text;_} -> uri
let (__proj__Mktxdoc_item__item__langId : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { uri; langId; version; text;_} -> langId
let (__proj__Mktxdoc_item__item__version : txdoc_item -> Prims.int) =
  fun projectee ->
    match projectee with | { uri; langId; version; text;_} -> version
let (__proj__Mktxdoc_item__item__text : txdoc_item -> Prims.string) =
  fun projectee ->
    match projectee with | { uri; langId; version; text;_} -> text
let (js_txdoc_item : FStar_Util.json -> txdoc_item) =
  fun uu___6_655 ->
    match uu___6_655 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____672 =
          let uu____674 = arg1 "uri" in FStar_All.pipe_right uu____674 js_str in
        let uu____677 =
          let uu____679 = arg1 "languageId" in
          FStar_All.pipe_right uu____679 js_str in
        let uu____682 =
          let uu____684 = arg1 "version" in
          FStar_All.pipe_right uu____684 js_int in
        let uu____687 =
          let uu____689 = arg1 "text" in
          FStar_All.pipe_right uu____689 js_str in
        {
          uri = uu____672;
          langId = uu____677;
          version = uu____682;
          text = uu____687
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
    let uu____776 =
      let uu____777 =
        let uu____785 = arg "textDocument" r in
        FStar_All.pipe_right uu____785 js_assoc in
      assoc "uri" uu____777 in
    FStar_All.pipe_right uu____776 js_str
let (js_txdoc_pos : (Prims.string * FStar_Util.json) Prims.list -> txdoc_pos)
  =
  fun r ->
    let pos =
      let uu____824 = arg "position" r in
      FStar_All.pipe_right uu____824 js_assoc in
    let uu____833 = js_txdoc_id r in
    let uu____835 =
      let uu____837 = assoc "line" pos in
      FStar_All.pipe_right uu____837 js_int in
    let uu____840 =
      let uu____842 = assoc "character" pos in
      FStar_All.pipe_right uu____842 js_int in
    { uri = uu____833; line = uu____835; col = uu____840 }
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
  fun uu___7_915 ->
    match uu___7_915 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____932 = assoc "added" a in
          FStar_All.pipe_right uu____932 js_assoc in
        let removed' =
          let uu____949 = assoc "removed" a in
          FStar_All.pipe_right uu____949 js_assoc in
        let uu____958 =
          let uu____959 =
            let uu____961 = assoc "uri" added' in
            FStar_All.pipe_right uu____961 js_str in
          let uu____964 =
            let uu____966 = assoc "name" added' in
            FStar_All.pipe_right uu____966 js_str in
          { wk_uri = uu____959; wk_name = uu____964 } in
        let uu____969 =
          let uu____970 =
            let uu____972 = assoc "uri" removed' in
            FStar_All.pipe_right uu____972 js_str in
          let uu____975 =
            let uu____977 = assoc "name" removed' in
            FStar_All.pipe_right uu____977 js_str in
          { wk_uri = uu____970; wk_name = uu____975 } in
        { added = uu____958; removed = uu____969 }
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
    match projectee with | Initialize _0 -> true | uu____1112 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____1148 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____1159 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1170 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____1183 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____1205 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____1223 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____1234 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____1247 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____1270 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____1292 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange -> true | uu____1310 -> false
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1323 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1346 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1369 -> false
let (__proj__DidSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1392 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1414 -> false
let (__proj__Completion__item___0 : lquery -> completion_context) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1432 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1444 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1463 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1482 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1501 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1520 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1539 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1557 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1569 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1587 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1598 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1609 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____1620 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____1631 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____1642 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____1653 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____1664 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____1675 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____1686 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____1697 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____1708 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____1720 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____1738 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1751 -> false
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
    match projectee with | LDInterleaved _0 -> true | uu____1880 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____1911 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____1930 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____1949 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____1967 -> false
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
    match projectee with | ParseError -> true | uu____2302 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____2313 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____2324 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____2335 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____2346 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____2357 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____2368 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____2379 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____2390 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____2401 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____2412 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___8_2424 ->
    match uu___8_2424 with
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
  fun uu___9_2443 ->
    match uu___9_2443 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2457 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2457
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2463 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2467 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2500 =
          let uu____2501 =
            let uu____2503 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2503 in
          BadProtocolMsg uu____2501 in
        { query_id = qid; q = uu____2500 }
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
      let uu____2605 =
        let uu____2613 =
          let uu____2619 =
            let uu____2620 = errorcode_to_int err in
            FStar_Util.JsonInt uu____2620 in
          ("code", uu____2619) in
        [uu____2613; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____2605
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
    let uu____2814 =
      let uu____2822 =
        let uu____2828 =
          let uu____2829 = FStar_Range.line_of_pos p in
          FStar_Util.JsonInt uu____2829 in
        ("line", uu____2828) in
      let uu____2833 =
        let uu____2841 =
          let uu____2847 =
            let uu____2848 = FStar_Range.col_of_pos p in
            FStar_Util.JsonInt uu____2848 in
          ("column", uu____2847) in
        [uu____2841] in
      uu____2822 :: uu____2833 in
    FStar_Util.JsonAssoc uu____2814
let (js_range : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let uu____2873 =
      let uu____2881 =
        let uu____2887 =
          let uu____2888 = FStar_Range.file_of_range r in
          FStar_Util.JsonStr uu____2888 in
        ("uri", uu____2887) in
      let uu____2892 =
        let uu____2900 =
          let uu____2906 =
            let uu____2907 =
              let uu____2915 =
                let uu____2921 =
                  let uu____2922 = FStar_Range.start_of_range r in
                  js_pos uu____2922 in
                ("start", uu____2921) in
              let uu____2925 =
                let uu____2933 =
                  let uu____2939 =
                    let uu____2940 = FStar_Range.end_of_range r in
                    js_pos uu____2940 in
                  ("end", uu____2939) in
                [uu____2933] in
              uu____2915 :: uu____2925 in
            FStar_Util.JsonAssoc uu____2907 in
          ("range", uu____2906) in
        [uu____2900] in
      uu____2881 :: uu____2892 in
    FStar_Util.JsonAssoc uu____2873
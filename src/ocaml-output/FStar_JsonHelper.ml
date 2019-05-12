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
           let uu____48 =
             FStar_Util.try_find
               (fun uu____64 ->
                  match uu____64 with | (k, uu____72) -> k = key)
               (Obj.magic d) in
           Obj.magic
             (FStar_Util.map_option FStar_Pervasives_Native.snd uu____48)) a1
        a2
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu____95 -> true | uu____98 -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu____108 -> uu____108
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____123 -> true
    | uu____126 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu____136 -> uu____136
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____155 -> true
    | uu____162 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____180 -> uu____180
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu____195 -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu____206 -> false
let assoc : 'a . Prims.string -> (Prims.string * 'a) Prims.list -> 'a =
  fun key ->
    fun a ->
      let uu____242 = try_assoc key a in
      match uu____242 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____246 =
            let uu____247 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____247 in
          FStar_Exn.raise uu____246
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____257 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____257);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____270 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____270
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_304 ->
    match uu___0_304 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_321 ->
    match uu___1_321 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_350 ->
      match uu___2_350 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___3_382 ->
    match uu___3_382 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_417 ->
    match uu___4_417 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let arg : 'a . Prims.string -> (Prims.string * 'a) Prims.list -> 'a =
  fun a3 ->
    fun a4 ->
      (fun k ->
         fun r ->
           let uu____460 =
             let uu____468 = Obj.magic (assoc "params" r) in
             FStar_All.pipe_right uu____468 js_assoc in
           Obj.magic (assoc k uu____460)) a3 a4
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
  fun uu___5_531 ->
    match uu___5_531 with
    | FStar_Util.JsonAssoc a ->
        let uu____540 =
          let uu____542 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____542 js_int in
        let uu____545 =
          let uu____549 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____549 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____540; trigger_char = uu____545 }
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
  fun uu___6_657 ->
    match uu___6_657 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____674 =
          let uu____676 = arg1 "uri" in FStar_All.pipe_right uu____676 js_str in
        let uu____679 =
          let uu____681 = arg1 "languageId" in
          FStar_All.pipe_right uu____681 js_str in
        let uu____684 =
          let uu____686 = arg1 "version" in
          FStar_All.pipe_right uu____686 js_int in
        let uu____689 =
          let uu____691 = arg1 "text" in
          FStar_All.pipe_right uu____691 js_str in
        {
          uri = uu____674;
          langId = uu____679;
          version = uu____684;
          text = uu____689
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
let js_txdoc_id : 'a . (Prims.string * 'a) Prims.list -> Prims.string =
  fun r ->
    let uu____782 =
      let uu____783 =
        let uu____791 = Obj.magic (arg "textDocument" r) in
        FStar_All.pipe_right uu____791 js_assoc in
      assoc "uri" uu____783 in
    FStar_All.pipe_right uu____782 js_str
let js_txdoc_pos : 'a . (Prims.string * 'a) Prims.list -> txdoc_pos =
  fun r ->
    let pos =
      let uu____835 = Obj.magic (arg "position" r) in
      FStar_All.pipe_right uu____835 js_assoc in
    let uu____844 = js_txdoc_id r in
    let uu____846 =
      let uu____848 = assoc "line" pos in
      FStar_All.pipe_right uu____848 js_int in
    let uu____851 =
      let uu____853 = assoc "character" pos in
      FStar_All.pipe_right uu____853 js_int in
    { uri = uu____844; line = uu____846; col = uu____851 }
type workspace_folder = {
  uri: Prims.string ;
  name: Prims.string }
let (__proj__Mkworkspace_folder__item__uri :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { uri; name;_} -> uri
let (__proj__Mkworkspace_folder__item__name :
  workspace_folder -> Prims.string) =
  fun projectee -> match projectee with | { uri; name;_} -> name
type wsch_event = {
  added: workspace_folder ;
  removed: workspace_folder }
let (__proj__Mkwsch_event__item__added : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> added
let (__proj__Mkwsch_event__item__removed : wsch_event -> workspace_folder) =
  fun projectee -> match projectee with | { added; removed;_} -> removed
let (js_wsch_event : FStar_Util.json -> wsch_event) =
  fun uu___7_926 ->
    match uu___7_926 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____943 = assoc "added" a in
          FStar_All.pipe_right uu____943 js_assoc in
        let removed' =
          let uu____960 = assoc "removed" a in
          FStar_All.pipe_right uu____960 js_assoc in
        let uu____969 =
          let uu____970 =
            let uu____972 = assoc "uri" added' in
            FStar_All.pipe_right uu____972 js_str in
          let uu____975 =
            let uu____977 = assoc "name" added' in
            FStar_All.pipe_right uu____977 js_str in
          { uri = uu____970; name = uu____975 } in
        let uu____980 =
          let uu____981 =
            let uu____983 = assoc "uri" removed' in
            FStar_All.pipe_right uu____983 js_str in
          let uu____986 =
            let uu____988 = assoc "name" removed' in
            FStar_All.pipe_right uu____988 js_str in
          { uri = uu____981; name = uu____986 } in
        { added = uu____969; removed = uu____980 }
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
    match projectee with | Initialize _0 -> true | uu____1123 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____1159 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____1170 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1181 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____1194 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____1216 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____1234 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____1245 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____1258 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____1281 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____1303 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange -> true | uu____1321 -> false
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1334 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1357 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1380 -> false
let (__proj__DidSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1403 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1425 -> false
let (__proj__Completion__item___0 : lquery -> completion_context) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1443 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1455 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1474 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1493 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1512 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1531 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1550 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1568 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1580 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1598 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1609 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1620 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____1631 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____1642 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____1653 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____1664 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____1675 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____1686 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____1697 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____1708 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____1719 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____1731 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____1749 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1762 -> false
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
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_last: lquery ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_line
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_column
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_stdin
let (__proj__Mkrepl_state__item__repl_last : repl_state -> lquery) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_last
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_names
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
    match projectee with | ParseError -> true | uu____1931 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____1942 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____1953 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____1964 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____1975 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____1986 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____1997 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____2008 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____2019 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____2030 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____2041 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___8_2053 ->
    match uu___8_2053 with
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
  fun uu___9_2072 ->
    match uu___9_2072 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2086 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2086
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2092 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2096 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2129 =
          let uu____2130 =
            let uu____2132 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2132 in
          BadProtocolMsg uu____2130 in
        { query_id = qid; q = uu____2129 }
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
      let uu____2234 =
        let uu____2242 =
          let uu____2248 =
            let uu____2249 = errorcode_to_int err in
            FStar_Util.JsonInt uu____2249 in
          ("code", uu____2248) in
        [uu____2242; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____2234
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
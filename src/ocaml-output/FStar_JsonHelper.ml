open Prims
let try_assoc :
  'a .
    Prims.string ->
      (Prims.string * 'a) Prims.list -> 'a FStar_Pervasives_Native.option
  =
  fun key  ->
    fun d  ->
      let uu____52 =
        FStar_Util.try_find
          (fun uu____68  -> match uu____68 with | (k,uu____76) -> k = key) d
         in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____52
  
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | MissingKey uu____99 -> true | uu____102 -> false
  
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  -> match projectee with | MissingKey uu____112 -> uu____112 
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | InvalidQuery uu____127 -> true
    | uu____130 -> false
  
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee  ->
    match projectee with | InvalidQuery uu____140 -> uu____140
  
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | UnexpectedJsonType uu____159 -> true
    | uu____166 -> false
  
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee  ->
    match projectee with | UnexpectedJsonType uu____184 -> uu____184
  
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | MalformedHeader  -> true | uu____199 -> false
  
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | InputExhausted  -> true | uu____210 -> false
  
let assoc : 'b . Prims.string -> (Prims.string * 'b) Prims.list -> 'b =
  fun key  ->
    fun a  ->
      let uu____246 = try_assoc key a  in
      match uu____246 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None  ->
          let uu____250 =
            let uu____251 = FStar_Util.format1 "Missing key [%s]" key  in
            MissingKey uu____251  in
          FStar_Exn.raise uu____250
  
let (write_json : FStar_Util.json -> unit) =
  fun js  ->
    (let uu____261 = FStar_Util.string_of_json js  in
     FStar_Util.print_raw uu____261);
    FStar_Util.print_raw "\n"
  
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js  ->
    let js_str = FStar_Util.string_of_json js  in
    let len = FStar_Util.string_of_int (FStar_String.length js_str)  in
    let uu____274 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str  in
    FStar_Util.print_raw uu____274
  
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected  ->
    fun got  -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
  
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_308  ->
    match uu___0_308 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
  
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_325  ->
    match uu___1_325 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
  
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k  ->
    fun uu___2_354  ->
      match uu___2_354 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
  
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___3_386  ->
    match uu___3_386 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
  
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_421  ->
    match uu___4_421 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
  
type completion_context =
  {
  trigger_kind: Prims.int ;
  trigger_char: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkcompletion_context__item__trigger_kind :
  completion_context -> Prims.int) =
  fun projectee  ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_kind
  
let (__proj__Mkcompletion_context__item__trigger_char :
  completion_context -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with | { trigger_kind; trigger_char;_} -> trigger_char
  
let (js_compl_context : FStar_Util.json -> completion_context) =
  fun uu___5_484  ->
    match uu___5_484 with
    | FStar_Util.JsonAssoc a ->
        let uu____493 =
          let uu____495 = assoc "triggerKind" a  in
          FStar_All.pipe_right uu____495 js_int  in
        let uu____498 =
          let uu____502 = try_assoc "triggerChar" a  in
          FStar_All.pipe_right uu____502 (FStar_Util.map_option js_str)  in
        { trigger_kind = uu____493; trigger_char = uu____498 }
    | other -> js_fail "dictionary" other
  
type txdoc_item =
  {
  uri: Prims.string ;
  langId: Prims.string ;
  version: Prims.int ;
  text: Prims.string }
let (__proj__Mktxdoc_item__item__uri : txdoc_item -> Prims.string) =
  fun projectee  ->
    match projectee with | { uri; langId; version; text;_} -> uri
  
let (__proj__Mktxdoc_item__item__langId : txdoc_item -> Prims.string) =
  fun projectee  ->
    match projectee with | { uri; langId; version; text;_} -> langId
  
let (__proj__Mktxdoc_item__item__version : txdoc_item -> Prims.int) =
  fun projectee  ->
    match projectee with | { uri; langId; version; text;_} -> version
  
let (__proj__Mktxdoc_item__item__text : txdoc_item -> Prims.string) =
  fun projectee  ->
    match projectee with | { uri; langId; version; text;_} -> text
  
let (js_txdoc_item : FStar_Util.json -> txdoc_item) =
  fun uu___6_610  ->
    match uu___6_610 with
    | FStar_Util.JsonAssoc a ->
        let arg k = assoc k a  in
        let uu____627 =
          let uu____629 = arg "uri"  in FStar_All.pipe_right uu____629 js_str
           in
        let uu____632 =
          let uu____634 = arg "languageId"  in
          FStar_All.pipe_right uu____634 js_str  in
        let uu____637 =
          let uu____639 = arg "version"  in
          FStar_All.pipe_right uu____639 js_int  in
        let uu____642 =
          let uu____644 = arg "text"  in
          FStar_All.pipe_right uu____644 js_str  in
        {
          uri = uu____627;
          langId = uu____632;
          version = uu____637;
          text = uu____642
        }
    | other -> js_fail "dictionary" other
  
type workspace_folder = {
  uri: Prims.string ;
  name: Prims.string }
let (__proj__Mkworkspace_folder__item__uri :
  workspace_folder -> Prims.string) =
  fun projectee  -> match projectee with | { uri; name;_} -> uri 
let (__proj__Mkworkspace_folder__item__name :
  workspace_folder -> Prims.string) =
  fun projectee  -> match projectee with | { uri; name;_} -> name 
type wsch_event = {
  added: workspace_folder ;
  removed: workspace_folder }
let (__proj__Mkwsch_event__item__added : wsch_event -> workspace_folder) =
  fun projectee  -> match projectee with | { added; removed;_} -> added 
let (__proj__Mkwsch_event__item__removed : wsch_event -> workspace_folder) =
  fun projectee  -> match projectee with | { added; removed;_} -> removed 
let (js_wsch_event : FStar_Util.json -> wsch_event) =
  fun uu___7_719  ->
    match uu___7_719 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____736 = assoc "added" a  in
          FStar_All.pipe_right uu____736 js_assoc  in
        let removed' =
          let uu____753 = assoc "removed" a  in
          FStar_All.pipe_right uu____753 js_assoc  in
        let uu____762 =
          let uu____763 =
            let uu____765 = assoc "uri" added'  in
            FStar_All.pipe_right uu____765 js_str  in
          let uu____768 =
            let uu____770 = assoc "name" added'  in
            FStar_All.pipe_right uu____770 js_str  in
          { uri = uu____763; name = uu____768 }  in
        let uu____773 =
          let uu____774 =
            let uu____776 = assoc "uri" removed'  in
            FStar_All.pipe_right uu____776 js_str  in
          let uu____779 =
            let uu____781 = assoc "name" removed'  in
            FStar_All.pipe_right uu____781 js_str  in
          { uri = uu____774; name = uu____779 }  in
        { added = uu____762; removed = uu____773 }
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
  | WillSaveWait of (Prims.string * Prims.int) 
  | DidSave of Prims.string 
  | DidClose of Prims.string 
  | Completion of completion_context 
  | Resolve 
  | Hover 
  | SignatureHelp 
  | Declaration 
  | Definition 
  | Implementation 
  | References 
  | DocumentHighlight 
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
  | PrepareRename 
  | FoldingRange 
  | BadProtocolMsg of Prims.string 
let (uu___is_Initialize : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Initialize _0 -> true | uu____881 -> false
  
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee  -> match projectee with | Initialize _0 -> _0 
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Initialized  -> true | uu____917 -> false
  
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Shutdown  -> true | uu____928 -> false
  
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee  -> match projectee with | Exit  -> true | uu____939 -> false 
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Cancel _0 -> true | uu____952 -> false
  
let (__proj__Cancel__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | Cancel _0 -> _0 
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | FolderChange _0 -> true | uu____974 -> false
  
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee  -> match projectee with | FolderChange _0 -> _0 
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | ChangeConfig  -> true | uu____992 -> false
  
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | ChangeWatch  -> true | uu____1003 -> false
  
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Symbol _0 -> true | uu____1016 -> false
  
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | Symbol _0 -> _0 
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | ExecCommand _0 -> true | uu____1039 -> false
  
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | ExecCommand _0 -> _0 
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DidOpen _0 -> true | uu____1061 -> false
  
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee  -> match projectee with | DidOpen _0 -> _0 
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DidChange  -> true | uu____1079 -> false
  
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | WillSave _0 -> true | uu____1092 -> false
  
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | WillSave _0 -> _0 
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | WillSaveWait _0 -> true | uu____1120 -> false
  
let (__proj__WillSaveWait__item___0 : lquery -> (Prims.string * Prims.int)) =
  fun projectee  -> match projectee with | WillSaveWait _0 -> _0 
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DidSave _0 -> true | uu____1158 -> false
  
let (__proj__DidSave__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | DidSave _0 -> _0 
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DidClose _0 -> true | uu____1181 -> false
  
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | DidClose _0 -> _0 
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Completion _0 -> true | uu____1203 -> false
  
let (__proj__Completion__item___0 : lquery -> completion_context) =
  fun projectee  -> match projectee with | Completion _0 -> _0 
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Resolve  -> true | uu____1221 -> false
  
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Hover  -> true | uu____1232 -> false
  
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | SignatureHelp  -> true | uu____1243 -> false
  
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Declaration  -> true | uu____1254 -> false
  
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Definition  -> true | uu____1265 -> false
  
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Implementation  -> true | uu____1276 -> false
  
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | References  -> true | uu____1287 -> false
  
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DocumentHighlight  -> true | uu____1298 -> false
  
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DocumentSymbol  -> true | uu____1309 -> false
  
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | CodeAction  -> true | uu____1320 -> false
  
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | CodeLens  -> true | uu____1331 -> false
  
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | CodeLensResolve  -> true | uu____1342 -> false
  
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DocumentLink  -> true | uu____1353 -> false
  
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DocumentLinkResolve  -> true | uu____1364 -> false
  
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | DocumentColor  -> true | uu____1375 -> false
  
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | ColorPresentation  -> true | uu____1386 -> false
  
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Formatting  -> true | uu____1397 -> false
  
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | RangeFormatting  -> true | uu____1408 -> false
  
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | TypeFormatting  -> true | uu____1419 -> false
  
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rename  -> true | uu____1430 -> false
  
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | PrepareRename  -> true | uu____1441 -> false
  
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | FoldingRange  -> true | uu____1452 -> false
  
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee  ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1465 -> false
  
let (__proj__BadProtocolMsg__item___0 : lquery -> Prims.string) =
  fun projectee  -> match projectee with | BadProtocolMsg _0 -> _0 
type lsp_query =
  {
  query_id: Prims.int FStar_Pervasives_Native.option ;
  q: lquery }
let (__proj__Mklsp_query__item__query_id :
  lsp_query -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee  -> match projectee with | { query_id; q;_} -> query_id 
let (__proj__Mklsp_query__item__q : lsp_query -> lquery) =
  fun projectee  -> match projectee with | { query_id; q;_} -> q 
type repl_state =
  {
  repl_line: Prims.int ;
  repl_column: Prims.int ;
  repl_stdin: FStar_Util.stream_reader ;
  repl_last: lquery ;
  repl_names: FStar_Interactive_CompletionTable.table }
let (__proj__Mkrepl_state__item__repl_line : repl_state -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_line
  
let (__proj__Mkrepl_state__item__repl_column : repl_state -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_column
  
let (__proj__Mkrepl_state__item__repl_stdin :
  repl_state -> FStar_Util.stream_reader) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_stdin
  
let (__proj__Mkrepl_state__item__repl_last : repl_state -> lquery) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_last
  
let (__proj__Mkrepl_state__item__repl_names :
  repl_state -> FStar_Interactive_CompletionTable.table) =
  fun projectee  ->
    match projectee with
    | { repl_line; repl_column; repl_stdin; repl_last; repl_names;_} ->
        repl_names
  
type optresponse =
  (FStar_Util.json,FStar_Util.json) FStar_Util.either
    FStar_Pervasives_Native.option
type either_st_exit = (repl_state,Prims.int) FStar_Util.either
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
  fun projectee  ->
    match projectee with | ParseError  -> true | uu____1634 -> false
  
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | InvalidRequest  -> true | uu____1645 -> false
  
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | MethodNotFound  -> true | uu____1656 -> false
  
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | InvalidParams  -> true | uu____1667 -> false
  
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | InternalError  -> true | uu____1678 -> false
  
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | ServerErrorStart  -> true | uu____1689 -> false
  
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | ServerErrorEnd  -> true | uu____1700 -> false
  
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | ServerNotInitialized  -> true
    | uu____1711 -> false
  
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnknownErrorCode  -> true | uu____1722 -> false
  
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | RequestCancelled  -> true | uu____1733 -> false
  
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee  ->
    match projectee with | ContentModified  -> true | uu____1744 -> false
  
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___8_1756  ->
    match uu___8_1756 with
    | ParseError  -> ~- (Prims.of_int (32700))
    | InvalidRequest  -> ~- (Prims.of_int (32600))
    | MethodNotFound  -> ~- (Prims.of_int (32601))
    | InvalidParams  -> ~- (Prims.of_int (32602))
    | InternalError  -> ~- (Prims.of_int (32603))
    | ServerErrorStart  -> ~- (Prims.of_int (32099))
    | ServerErrorEnd  -> ~- (Prims.of_int (32000))
    | ServerNotInitialized  -> ~- (Prims.of_int (32002))
    | UnknownErrorCode  -> ~- (Prims.of_int (32001))
    | RequestCancelled  -> ~- (Prims.of_int (32800))
    | ContentModified  -> ~- (Prims.of_int (32801))
  
let (json_debug : FStar_Util.json -> Prims.string) =
  fun uu___9_1775  ->
    match uu___9_1775 with
    | FStar_Util.JsonNull  -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____1789 = FStar_Util.string_of_int i  in
        FStar_Util.format1 "int (%s)" uu____1789
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____1795 -> "list (...)"
    | FStar_Util.JsonAssoc uu____1799 -> "dictionary (...)"
  
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid  ->
    fun expected  ->
      fun got  ->
        let uu____1832 =
          let uu____1833 =
            let uu____1835 = json_debug got  in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____1835
             in
          BadProtocolMsg uu____1833  in
        { query_id = qid; q = uu____1832 }
  
let (json_of_response :
  Prims.int FStar_Pervasives_Native.option ->
    (FStar_Util.json,FStar_Util.json) FStar_Util.either -> FStar_Util.json)
  =
  fun qid  ->
    fun response  ->
      let qid1 =
        match qid with
        | FStar_Pervasives_Native.Some i -> FStar_Util.JsonInt i
        | FStar_Pervasives_Native.None  -> FStar_Util.JsonNull  in
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
  fun err  ->
    fun msg  ->
      let uu____1937 =
        let uu____1945 =
          let uu____1951 =
            let uu____1952 = errorcode_to_int err  in
            FStar_Util.JsonInt uu____1952  in
          ("code", uu____1951)  in
        [uu____1945; ("message", (FStar_Util.JsonStr msg))]  in
      FStar_Util.JsonAssoc uu____1937
  
let (wrap_content_szerr : Prims.string -> lsp_query) =
  fun m  ->
    { query_id = FStar_Pervasives_Native.None; q = (BadProtocolMsg m) }
  
let (js_servcap : FStar_Util.json) =
  FStar_Util.JsonAssoc
    [("capabilities",
       (FStar_Util.JsonAssoc
          [("hoverProvider", (FStar_Util.JsonBool false));
          ("definitionProvider", (FStar_Util.JsonBool false));
          ("typeDefinitionProvider", (FStar_Util.JsonBool false));
          ("implementationProvider", (FStar_Util.JsonBool false));
          ("referencesProvider", (FStar_Util.JsonBool false));
          ("documentSymbolProvider", (FStar_Util.JsonBool false));
          ("workspaceSymbolProvider", (FStar_Util.JsonBool false));
          ("codeActionProvider", (FStar_Util.JsonBool false))]))]
  
open Prims
type assoct = (Prims.string * FStarC_Json.json) Prims.list
let (try_assoc :
  Prims.string -> assoct -> FStarC_Json.json FStar_Pervasives_Native.option)
  =
  fun key ->
    fun d ->
      let uu___ =
        FStarC_Compiler_Util.try_find
          (fun uu___1 -> match uu___1 with | (k, uu___2) -> k = key) d in
      FStarC_Compiler_Util.map_option FStar_Pervasives_Native.snd uu___
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu___ -> true | uu___ -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu___ -> uu___
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidQuery uu___ -> true | uu___ -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu___ -> uu___
exception UnexpectedJsonType of (Prims.string * FStarC_Json.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu___ -> true | uu___ -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStarC_Json.json)) =
  fun projectee -> match projectee with | UnexpectedJsonType uu___ -> uu___
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu___ -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu___ -> false
let (assoc : Prims.string -> assoct -> FStarC_Json.json) =
  fun key ->
    fun a ->
      let uu___ = try_assoc key a in
      match uu___ with
      | FStar_Pervasives_Native.Some v -> v
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 = FStarC_Compiler_Util.format1 "Missing key [%s]" key in
            MissingKey uu___2 in
          FStarC_Compiler_Effect.raise uu___1
let (write_json : FStarC_Json.json -> unit) =
  fun js ->
    (let uu___1 = FStarC_Json.string_of_json js in
     FStarC_Compiler_Util.print_raw uu___1);
    FStarC_Compiler_Util.print_raw "\n"
let (write_jsonrpc : FStarC_Json.json -> unit) =
  fun js ->
    let js_str = FStarC_Json.string_of_json js in
    let len =
      FStarC_Compiler_Util.string_of_int
        (FStarC_Compiler_String.length js_str) in
    let uu___ =
      FStarC_Compiler_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStarC_Compiler_Util.print_raw uu___
let js_fail : 'a . Prims.string -> FStarC_Json.json -> 'a =
  fun expected ->
    fun got ->
      FStarC_Compiler_Effect.raise (UnexpectedJsonType (expected, got))
let (js_int : FStarC_Json.json -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonInt i -> i
    | other -> js_fail "int" other
let (js_bool : FStarC_Json.json -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonBool b -> b
    | other -> js_fail "int" other
let (js_str : FStarC_Json.json -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStarC_Json.json -> 'a) -> FStarC_Json.json -> 'a Prims.list =
  fun k ->
    fun uu___ ->
      match uu___ with
      | FStarC_Json.JsonList l -> FStarC_Compiler_List.map k l
      | other -> js_fail "list" other
let (js_assoc : FStarC_Json.json -> assoct) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStarC_Json.json -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonInt i -> i
    | FStarC_Json.JsonStr s -> FStarC_Compiler_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg : Prims.string -> assoct -> FStarC_Json.json) =
  fun k ->
    fun r ->
      let uu___ = let uu___1 = assoc "params" r in js_assoc uu___1 in
      assoc k uu___
let (uri_to_path : Prims.string -> Prims.string) =
  fun u ->
    let uu___ =
      let uu___1 =
        FStarC_Compiler_Util.substring u (Prims.of_int (9))
          (Prims.of_int (3)) in
      uu___1 = "%3A" in
    if uu___
    then
      let uu___1 =
        FStarC_Compiler_Util.substring u (Prims.of_int (8)) Prims.int_one in
      let uu___2 = FStarC_Compiler_Util.substring_from u (Prims.of_int (12)) in
      FStarC_Compiler_Util.format2 "%s:%s" uu___1 uu___2
    else FStarC_Compiler_Util.substring_from u (Prims.of_int (7))
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
let (path_to_uri : Prims.string -> Prims.string) =
  fun u ->
    let uu___ =
      let uu___1 = FStarC_Compiler_Util.char_at u Prims.int_one in
      uu___1 = 58 in
    if uu___
    then
      let rest =
        let uu___1 = FStarC_Compiler_Util.substring_from u (Prims.of_int (2)) in
        FStarC_Compiler_Util.replace_char uu___1 92 47 in
      let uu___1 =
        FStarC_Compiler_Util.substring u Prims.int_zero Prims.int_one in
      FStarC_Compiler_Util.format2 "file:///%s%3A%s" uu___1 rest
    else FStarC_Compiler_Util.format1 "file://%s" u
let (js_compl_context : FStarC_Json.json -> completion_context) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonAssoc a ->
        let uu___1 = let uu___2 = assoc "triggerKind" a in js_int uu___2 in
        let uu___2 =
          let uu___3 = try_assoc "triggerChar" a in
          FStarC_Compiler_Util.map_option js_str uu___3 in
        { trigger_kind = uu___1; trigger_char = uu___2 }
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
let (js_txdoc_item : FStarC_Json.json -> txdoc_item) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu___1 =
          let uu___2 = let uu___3 = arg1 "uri" in js_str uu___3 in
          uri_to_path uu___2 in
        let uu___2 = let uu___3 = arg1 "languageId" in js_str uu___3 in
        let uu___3 = let uu___4 = arg1 "version" in js_int uu___4 in
        let uu___4 = let uu___5 = arg1 "text" in js_str uu___5 in
        { fname = uu___1; langId = uu___2; version = uu___3; text = uu___4 }
    | other -> js_fail "dictionary" other
type txdoc_pos = {
  path: Prims.string ;
  line: Prims.int ;
  col: Prims.int }
let (__proj__Mktxdoc_pos__item__path : txdoc_pos -> Prims.string) =
  fun projectee -> match projectee with | { path; line; col;_} -> path
let (__proj__Mktxdoc_pos__item__line : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { path; line; col;_} -> line
let (__proj__Mktxdoc_pos__item__col : txdoc_pos -> Prims.int) =
  fun projectee -> match projectee with | { path; line; col;_} -> col
let (js_txdoc_id : assoct -> Prims.string) =
  fun r ->
    let uu___ =
      let uu___1 =
        let uu___2 = let uu___3 = arg "textDocument" r in js_assoc uu___3 in
        assoc "uri" uu___2 in
      js_str uu___1 in
    uri_to_path uu___
let (js_txdoc_pos : assoct -> txdoc_pos) =
  fun r ->
    let pos = let uu___ = arg "position" r in js_assoc uu___ in
    let uu___ = js_txdoc_id r in
    let uu___1 = let uu___2 = assoc "line" pos in js_int uu___2 in
    let uu___2 = let uu___3 = assoc "character" pos in js_int uu___3 in
    { path = uu___; line = uu___1; col = uu___2 }
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
let (js_wsch_event : FStarC_Json.json -> wsch_event) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonAssoc a ->
        let added' = let uu___1 = assoc "added" a in js_assoc uu___1 in
        let removed' = let uu___1 = assoc "removed" a in js_assoc uu___1 in
        let uu___1 =
          let uu___2 = let uu___3 = assoc "uri" added' in js_str uu___3 in
          let uu___3 = let uu___4 = assoc "name" added' in js_str uu___4 in
          { wk_uri = uu___2; wk_name = uu___3 } in
        let uu___2 =
          let uu___3 = let uu___4 = assoc "uri" removed' in js_str uu___4 in
          let uu___4 = let uu___5 = assoc "name" removed' in js_str uu___5 in
          { wk_uri = uu___3; wk_name = uu___4 } in
        { added = uu___1; removed = uu___2 }
    | other -> js_fail "dictionary" other
let (js_contentch : FStarC_Json.json -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonList l ->
        let uu___1 =
          FStarC_Compiler_List.map
            (fun uu___2 ->
               match uu___2 with
               | FStarC_Json.JsonAssoc a ->
                   let uu___3 = assoc "text" a in js_str uu___3) l in
        FStarC_Compiler_List.hd uu___1
    | other -> js_fail "dictionary" other
type lquery =
  | Initialize of (Prims.int * Prims.string) 
  | Initialized 
  | Shutdown 
  | Exit 
  | Cancel of Prims.int 
  | FolderChange of wsch_event 
  | ChangeConfig 
  | ChangeWatch 
  | Symbol of Prims.string 
  | ExecCommand of Prims.string 
  | DidOpen of txdoc_item 
  | DidChange of (Prims.string * Prims.string) 
  | WillSave of Prims.string 
  | WillSaveWait of Prims.string 
  | DidSave of (Prims.string * Prims.string) 
  | DidClose of Prims.string 
  | Completion of (txdoc_pos * completion_context) 
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
    match projectee with | Initialize _0 -> true | uu___ -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu___ -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Shutdown -> true | uu___ -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu___ -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Cancel _0 -> true | uu___ -> false
let (__proj__Cancel__item___0 : lquery -> Prims.int) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu___ -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu___ -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu___ -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Symbol _0 -> true | uu___ -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu___ -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee -> match projectee with | DidOpen _0 -> true | uu___ -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange _0 -> true | uu___ -> false
let (__proj__DidChange__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidChange _0 -> _0
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu___ -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu___ -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee -> match projectee with | DidSave _0 -> true | uu___ -> false
let (__proj__DidSave__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu___ -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu___ -> false
let (__proj__Completion__item___0 :
  lquery -> (txdoc_pos * completion_context)) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Resolve -> true | uu___ -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Hover _0 -> true | uu___ -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu___ -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu___ -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu___ -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu___ -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu___ -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee -> match projectee with | References -> true | uu___ -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu___ -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu___ -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee -> match projectee with | CodeAction -> true | uu___ -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee -> match projectee with | CodeLens -> true | uu___ -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu___ -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu___ -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu___ -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu___ -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu___ -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Formatting -> true | uu___ -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu___ -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu___ -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Rename -> true | uu___ -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu___ -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu___ -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu___ -> false
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
  fun projectee -> match projectee with | ParseError -> true | uu___ -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu___ -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu___ -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu___ -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu___ -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu___ -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu___ -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu___ -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu___ -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu___ -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu___ -> false
type rng =
  {
  rng_start: (Prims.int * Prims.int) ;
  rng_end: (Prims.int * Prims.int) }
let (__proj__Mkrng__item__rng_start : rng -> (Prims.int * Prims.int)) =
  fun projectee ->
    match projectee with | { rng_start; rng_end;_} -> rng_start
let (__proj__Mkrng__item__rng_end : rng -> (Prims.int * Prims.int)) =
  fun projectee -> match projectee with | { rng_start; rng_end;_} -> rng_end
let (js_rng : FStarC_Json.json -> rng) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonAssoc a ->
        let st = assoc "start" a in
        let fin = assoc "end" a in
        let l = assoc "line" in
        let c = assoc "character" in
        let uu___1 =
          let uu___2 =
            let uu___3 = let uu___4 = js_assoc st in l uu___4 in
            js_int uu___3 in
          let uu___3 =
            let uu___4 = let uu___5 = js_assoc st in c uu___5 in
            js_int uu___4 in
          (uu___2, uu___3) in
        let uu___2 =
          let uu___3 =
            let uu___4 = let uu___5 = js_assoc fin in l uu___5 in
            js_int uu___4 in
          let uu___4 =
            let uu___5 = let uu___6 = js_assoc st in c uu___6 in
            js_int uu___5 in
          (uu___3, uu___4) in
        { rng_start = uu___1; rng_end = uu___2 }
    | other -> js_fail "dictionary" other
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___ ->
    match uu___ with
    | ParseError -> (Prims.of_int (-32700))
    | InvalidRequest -> (Prims.of_int (-32600))
    | MethodNotFound -> (Prims.of_int (-32601))
    | InvalidParams -> (Prims.of_int (-32602))
    | InternalError -> (Prims.of_int (-32603))
    | ServerErrorStart -> (Prims.of_int (-32099))
    | ServerErrorEnd -> (Prims.of_int (-32000))
    | ServerNotInitialized -> (Prims.of_int (-32002))
    | UnknownErrorCode -> (Prims.of_int (-32001))
    | RequestCancelled -> (Prims.of_int (-32800))
    | ContentModified -> (Prims.of_int (-32801))
let (json_debug : FStarC_Json.json -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | FStarC_Json.JsonNull -> "null"
    | FStarC_Json.JsonBool b ->
        FStarC_Compiler_Util.format1 "bool (%s)"
          (if b then "true" else "false")
    | FStarC_Json.JsonInt i ->
        let uu___1 = FStarC_Compiler_Util.string_of_int i in
        FStarC_Compiler_Util.format1 "int (%s)" uu___1
    | FStarC_Json.JsonStr s -> FStarC_Compiler_Util.format1 "string (%s)" s
    | FStarC_Json.JsonList uu___1 -> "list (...)"
    | FStarC_Json.JsonAssoc uu___1 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStarC_Json.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu___ =
          let uu___1 =
            let uu___2 = json_debug got in
            FStarC_Compiler_Util.format2
              "JSON decoding failed: expected %s, got %s" expected uu___2 in
          BadProtocolMsg uu___1 in
        { query_id = qid; q = uu___ }
let (resultResponse :
  FStarC_Json.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("result", r)]
let (errorResponse :
  FStarC_Json.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("error", r)]
let (nullResponse : assoct FStar_Pervasives_Native.option) =
  resultResponse FStarC_Json.JsonNull
let (json_of_response :
  Prims.int FStar_Pervasives_Native.option -> assoct -> FStarC_Json.json) =
  fun qid ->
    fun response ->
      match qid with
      | FStar_Pervasives_Native.Some i ->
          FStarC_Json.JsonAssoc
            (FStarC_Compiler_List.op_At
               [("jsonrpc", (FStarC_Json.JsonStr "2.0"));
               ("id", (FStarC_Json.JsonInt i))] response)
      | FStar_Pervasives_Native.None ->
          FStarC_Json.JsonAssoc
            (FStarC_Compiler_List.op_At
               [("jsonrpc", (FStarC_Json.JsonStr "2.0"))] response)
let (js_resperr : error_code -> Prims.string -> FStarC_Json.json) =
  fun err ->
    fun msg ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = errorcode_to_int err in FStarC_Json.JsonInt uu___3 in
          ("code", uu___2) in
        [uu___1; ("message", (FStarC_Json.JsonStr msg))] in
      FStarC_Json.JsonAssoc uu___
let (wrap_content_szerr : Prims.string -> lsp_query) =
  fun m ->
    { query_id = FStar_Pervasives_Native.None; q = (BadProtocolMsg m) }
let (js_servcap : FStarC_Json.json) =
  FStarC_Json.JsonAssoc
    [("capabilities",
       (FStarC_Json.JsonAssoc
          [("textDocumentSync",
             (FStarC_Json.JsonAssoc
                [("openClose", (FStarC_Json.JsonBool true));
                ("change", (FStarC_Json.JsonInt Prims.int_one));
                ("willSave", (FStarC_Json.JsonBool false));
                ("willSaveWaitUntil", (FStarC_Json.JsonBool false));
                ("save",
                  (FStarC_Json.JsonAssoc
                     [("includeText", (FStarC_Json.JsonBool true))]))]));
          ("hoverProvider", (FStarC_Json.JsonBool true));
          ("completionProvider", (FStarC_Json.JsonAssoc []));
          ("signatureHelpProvider", (FStarC_Json.JsonAssoc []));
          ("definitionProvider", (FStarC_Json.JsonBool true));
          ("typeDefinitionProvider", (FStarC_Json.JsonBool false));
          ("implementationProvider", (FStarC_Json.JsonBool false));
          ("referencesProvider", (FStarC_Json.JsonBool false));
          ("documentSymbolProvider", (FStarC_Json.JsonBool false));
          ("workspaceSymbolProvider", (FStarC_Json.JsonBool false));
          ("codeActionProvider", (FStarC_Json.JsonBool false))]))]
let (js_pos : FStarC_Compiler_Range_Type.pos -> FStarC_Json.json) =
  fun p ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Compiler_Range_Ops.line_of_pos p in
            uu___4 - Prims.int_one in
          FStarC_Json.JsonInt uu___3 in
        ("line", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Compiler_Range_Ops.col_of_pos p in
            FStarC_Json.JsonInt uu___5 in
          ("character", uu___4) in
        [uu___3] in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___
let (js_range : FStarC_Compiler_Range_Type.range -> FStarC_Json.json) =
  fun r ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Compiler_Range_Ops.start_of_range r in
          js_pos uu___3 in
        ("start", uu___2) in
      let uu___2 =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Compiler_Range_Ops.end_of_range r in
            js_pos uu___5 in
          ("end", uu___4) in
        [uu___3] in
      uu___1 :: uu___2 in
    FStarC_Json.JsonAssoc uu___
let (js_dummyrange : FStarC_Json.json) =
  FStarC_Json.JsonAssoc
    [("start",
       (FStarC_Json.JsonAssoc
          [("line", (FStarC_Json.JsonInt Prims.int_zero));
          ("character", (FStarC_Json.JsonInt Prims.int_zero));
          ("end",
            (FStarC_Json.JsonAssoc
               [("line", (FStarC_Json.JsonInt Prims.int_zero));
               ("character", (FStarC_Json.JsonInt Prims.int_zero))]))]))]
let (js_loclink : FStarC_Compiler_Range_Type.range -> FStarC_Json.json) =
  fun r ->
    let s = js_range r in
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = FStarC_Compiler_Range_Ops.file_of_range r in
                path_to_uri uu___6 in
              FStarC_Json.JsonStr uu___5 in
            ("targetUri", uu___4) in
          [uu___3; ("targetRange", s); ("targetSelectionRange", s)] in
        FStarC_Json.JsonAssoc uu___2 in
      [uu___1] in
    FStarC_Json.JsonList uu___
let (pos_munge : txdoc_pos -> (Prims.string * Prims.int * Prims.int)) =
  fun pos -> ((pos.path), (pos.line + Prims.int_one), (pos.col))
let (js_diag :
  Prims.string ->
    Prims.string ->
      FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ->
        assoct)
  =
  fun fname ->
    fun msg ->
      fun r ->
        let r' =
          match r with
          | FStar_Pervasives_Native.Some r1 -> js_range r1
          | FStar_Pervasives_Native.None -> js_dummyrange in
        let ds =
          ("diagnostics",
            (FStarC_Json.JsonList
               [FStarC_Json.JsonAssoc
                  [("range", r'); ("message", (FStarC_Json.JsonStr msg))]])) in
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    let uu___6 = path_to_uri fname in
                    FStarC_Json.JsonStr uu___6 in
                  ("uri", uu___5) in
                [uu___4; ds] in
              FStarC_Json.JsonAssoc uu___3 in
            ("params", uu___2) in
          [uu___1] in
        ("method", (FStarC_Json.JsonStr "textDocument/publishDiagnostics"))
          :: uu___
let (js_diag_clear : Prims.string -> assoct) =
  fun fname ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 =
                let uu___6 = path_to_uri fname in FStarC_Json.JsonStr uu___6 in
              ("uri", uu___5) in
            [uu___4; ("diagnostics", (FStarC_Json.JsonList []))] in
          FStarC_Json.JsonAssoc uu___3 in
        ("params", uu___2) in
      [uu___1] in
    ("method", (FStarC_Json.JsonStr "textDocument/publishDiagnostics")) ::
      uu___
open Prims
type assoct = (Prims.string * FStar_Util.json) Prims.list
let (try_assoc :
  Prims.string -> assoct -> FStar_Util.json FStar_Pervasives_Native.option) =
  fun key ->
    fun d ->
      let uu____50 =
        FStar_Util.try_find
          (fun uu____66 -> match uu____66 with | (k, uu____74) -> k = key) d in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____50
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu____97 -> true | uu____100 -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu____110 -> uu____110
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____125 -> true
    | uu____128 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu____138 -> uu____138
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____157 -> true
    | uu____164 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____182 -> uu____182
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu____197 -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu____208 -> false
let (assoc : Prims.string -> assoct -> FStar_Util.json) =
  fun key ->
    fun a ->
      let uu____223 = try_assoc key a in
      match uu____223 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____227 =
            let uu____228 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____228 in
          FStar_Exn.raise uu____227
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____238 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____238);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____251 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____251
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_285 ->
    match uu___0_285 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_302 ->
    match uu___1_302 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_331 ->
      match uu___2_331 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc : FStar_Util.json -> assoct) =
  fun uu___3_349 ->
    match uu___3_349 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_370 ->
    match uu___4_370 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg : Prims.string -> assoct -> FStar_Util.json) =
  fun k ->
    fun r ->
      let uu____392 =
        let uu____393 = assoc "params" r in
        FStar_All.pipe_right uu____393 js_assoc in
      assoc k uu____392
let (uri_to_path : Prims.string -> Prims.string) =
  fun u ->
    let uu____404 =
      let uu____406 =
        FStar_Util.substring u (Prims.parse_int "9") (Prims.parse_int "3") in
      uu____406 = "%3A" in
    if uu____404
    then
      let uu____414 =
        FStar_Util.substring u (Prims.parse_int "8") (Prims.parse_int "1") in
      let uu____418 = FStar_Util.substring_from u (Prims.parse_int "12") in
      FStar_Util.format2 "%s:%s" uu____414 uu____418
    else FStar_Util.substring_from u (Prims.parse_int "7")
let (path_to_uri : Prims.string -> Prims.string) =
  fun u -> FStar_Util.format1 "file://%s" u
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
  fun uu___5_489 ->
    match uu___5_489 with
    | FStar_Util.JsonAssoc a ->
        let uu____498 =
          let uu____500 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____500 js_int in
        let uu____503 =
          let uu____507 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____507 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____498; trigger_char = uu____503 }
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
  fun uu___6_615 ->
    match uu___6_615 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____632 =
          let uu____634 =
            let uu____636 = arg1 "uri" in
            FStar_All.pipe_right uu____636 js_str in
          uri_to_path uu____634 in
        let uu____639 =
          let uu____641 = arg1 "languageId" in
          FStar_All.pipe_right uu____641 js_str in
        let uu____644 =
          let uu____646 = arg1 "version" in
          FStar_All.pipe_right uu____646 js_int in
        let uu____649 =
          let uu____651 = arg1 "text" in
          FStar_All.pipe_right uu____651 js_str in
        {
          fname = uu____632;
          langId = uu____639;
          version = uu____644;
          text = uu____649
        }
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
    let uu____731 =
      let uu____733 =
        let uu____734 =
          let uu____735 = arg "textDocument" r in
          FStar_All.pipe_right uu____735 js_assoc in
        assoc "uri" uu____734 in
      FStar_All.pipe_right uu____733 js_str in
    uri_to_path uu____731
let (js_txdoc_pos : assoct -> txdoc_pos) =
  fun r ->
    let pos =
      let uu____753 = arg "position" r in
      FStar_All.pipe_right uu____753 js_assoc in
    let uu____755 = js_txdoc_id r in
    let uu____757 =
      let uu____759 = assoc "line" pos in
      FStar_All.pipe_right uu____759 js_int in
    let uu____762 =
      let uu____764 = assoc "character" pos in
      FStar_All.pipe_right uu____764 js_int in
    { path = uu____755; line = uu____757; col = uu____762 }
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
  fun uu___7_837 ->
    match uu___7_837 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____847 = assoc "added" a in
          FStar_All.pipe_right uu____847 js_assoc in
        let removed' =
          let uu____850 = assoc "removed" a in
          FStar_All.pipe_right uu____850 js_assoc in
        let uu____852 =
          let uu____853 =
            let uu____855 = assoc "uri" added' in
            FStar_All.pipe_right uu____855 js_str in
          let uu____858 =
            let uu____860 = assoc "name" added' in
            FStar_All.pipe_right uu____860 js_str in
          { wk_uri = uu____853; wk_name = uu____858 } in
        let uu____863 =
          let uu____864 =
            let uu____866 = assoc "uri" removed' in
            FStar_All.pipe_right uu____866 js_str in
          let uu____869 =
            let uu____871 = assoc "name" removed' in
            FStar_All.pipe_right uu____871 js_str in
          { wk_uri = uu____864; wk_name = uu____869 } in
        { added = uu____852; removed = uu____863 }
    | other -> js_fail "dictionary" other
let (js_contentch : FStar_Util.json -> Prims.string) =
  fun uu___8_886 ->
    match uu___8_886 with
    | FStar_Util.JsonList l ->
        let uu____891 =
          FStar_List.map
            (fun uu____899 ->
               match uu____899 with
               | FStar_Util.JsonAssoc a ->
                   let uu____909 = assoc "text" a in
                   FStar_All.pipe_right uu____909 js_str) l in
        FStar_List.hd uu____891
    | other -> js_fail "dictionary" other
type rng =
  {
  rng_start: (Prims.int * Prims.int) ;
  rng_end: (Prims.int * Prims.int) }
let (__proj__Mkrng__item__rng_start : rng -> (Prims.int * Prims.int)) =
  fun projectee ->
    match projectee with | { rng_start; rng_end;_} -> rng_start
let (__proj__Mkrng__item__rng_end : rng -> (Prims.int * Prims.int)) =
  fun projectee -> match projectee with | { rng_start; rng_end;_} -> rng_end
let (js_rng : FStar_Util.json -> rng) =
  fun uu___9_1007 ->
    match uu___9_1007 with
    | FStar_Util.JsonAssoc a ->
        let st = assoc "start" a in
        let fin = assoc "end" a in
        let l = assoc "line" in
        let c = assoc "character" in
        let uu____1032 =
          let uu____1039 =
            let uu____1041 =
              let uu____1042 = FStar_All.pipe_right st js_assoc in
              l uu____1042 in
            FStar_All.pipe_right uu____1041 js_int in
          let uu____1044 =
            let uu____1046 =
              let uu____1047 = FStar_All.pipe_right st js_assoc in
              c uu____1047 in
            FStar_All.pipe_right uu____1046 js_int in
          (uu____1039, uu____1044) in
        let uu____1051 =
          let uu____1058 =
            let uu____1060 =
              let uu____1061 = FStar_All.pipe_right fin js_assoc in
              l uu____1061 in
            FStar_All.pipe_right uu____1060 js_int in
          let uu____1063 =
            let uu____1065 =
              let uu____1066 = FStar_All.pipe_right st js_assoc in
              c uu____1066 in
            FStar_All.pipe_right uu____1065 js_int in
          (uu____1058, uu____1063) in
        { rng_start = uu____1032; rng_end = uu____1051 }
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
    match projectee with | Initialize _0 -> true | uu____1222 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____1258 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____1269 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1280 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____1293 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.int) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____1315 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____1333 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____1344 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____1357 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____1380 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____1402 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange _0 -> true | uu____1427 -> false
let (__proj__DidChange__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidChange _0 -> _0
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1465 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1488 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1516 -> false
let (__proj__DidSave__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1554 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1580 -> false
let (__proj__Completion__item___0 :
  lquery -> (txdoc_pos * completion_context)) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1610 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1622 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1641 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1660 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1679 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1698 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1717 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1735 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1747 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1765 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1776 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1787 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____1798 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____1809 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____1820 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____1831 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____1842 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____1853 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____1864 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____1875 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____1886 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____1898 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____1916 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____1929 -> false
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
    match projectee with | LDInterleaved _0 -> true | uu____2058 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____2089 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____2108 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____2127 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____2145 -> false
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
and grepl_state =
  {
  grepl_repls: repl_state FStar_Util.psmap ;
  grepl_stdin: FStar_Util.stream_reader }
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
let (__proj__Mkgrepl_state__item__grepl_repls :
  grepl_state -> repl_state FStar_Util.psmap) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_repls
let (__proj__Mkgrepl_state__item__grepl_stdin :
  grepl_state -> FStar_Util.stream_reader) =
  fun projectee ->
    match projectee with | { grepl_repls; grepl_stdin;_} -> grepl_stdin
type repl_stack_entry_t = (repl_depth_t * (repl_task * repl_state))
type repl_stack_t = (repl_depth_t * (repl_task * repl_state)) Prims.list
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
    match projectee with | ParseError -> true | uu____2505 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____2516 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____2527 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____2538 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____2549 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____2560 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____2571 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____2582 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____2593 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____2604 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____2615 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___10_2627 ->
    match uu___10_2627 with
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
  fun uu___11_2646 ->
    match uu___11_2646 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2660 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2660
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2666 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2670 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2703 =
          let uu____2704 =
            let uu____2706 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2706 in
          BadProtocolMsg uu____2704 in
        { query_id = qid; q = uu____2703 }
let (resultResponse :
  FStar_Util.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("result", r)]
let (errorResponse :
  FStar_Util.json -> assoct FStar_Pervasives_Native.option) =
  fun r -> FStar_Pervasives_Native.Some [("error", r)]
let (nullResponse : assoct FStar_Pervasives_Native.option) =
  resultResponse FStar_Util.JsonNull
let (json_of_response :
  Prims.int FStar_Pervasives_Native.option -> assoct -> FStar_Util.json) =
  fun qid ->
    fun response ->
      match qid with
      | FStar_Pervasives_Native.Some i ->
          FStar_Util.JsonAssoc
            (FStar_List.append
               [("jsonrpc", (FStar_Util.JsonStr "2.0"));
               ("id", (FStar_Util.JsonInt i))] response)
      | FStar_Pervasives_Native.None ->
          FStar_Util.JsonAssoc
            (FStar_List.append [("jsonrpc", (FStar_Util.JsonStr "2.0"))]
               response)
let (js_resperr : error_code -> Prims.string -> FStar_Util.json) =
  fun err ->
    fun msg ->
      let uu____2835 =
        let uu____2843 =
          let uu____2849 =
            let uu____2850 = errorcode_to_int err in
            FStar_Util.JsonInt uu____2850 in
          ("code", uu____2849) in
        [uu____2843; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____2835
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
                ("willSave", (FStar_Util.JsonBool false));
                ("willSaveWaitUntil", (FStar_Util.JsonBool false));
                ("save",
                  (FStar_Util.JsonAssoc
                     [("includeText", (FStar_Util.JsonBool true))]))]));
          ("hoverProvider", (FStar_Util.JsonBool true));
          ("completionProvider", (FStar_Util.JsonAssoc []));
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
    let uu____3056 =
      let uu____3064 =
        let uu____3070 =
          let uu____3071 =
            let uu____3073 = FStar_Range.line_of_pos p in
            uu____3073 - (Prims.parse_int "1") in
          FStar_Util.JsonInt uu____3071 in
        ("line", uu____3070) in
      let uu____3078 =
        let uu____3086 =
          let uu____3092 =
            let uu____3093 = FStar_Range.col_of_pos p in
            FStar_Util.JsonInt uu____3093 in
          ("character", uu____3092) in
        [uu____3086] in
      uu____3064 :: uu____3078 in
    FStar_Util.JsonAssoc uu____3056
let (js_range : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let uu____3118 =
      let uu____3126 =
        let uu____3132 =
          let uu____3133 = FStar_Range.start_of_range r in js_pos uu____3133 in
        ("start", uu____3132) in
      let uu____3136 =
        let uu____3144 =
          let uu____3150 =
            let uu____3151 = FStar_Range.end_of_range r in js_pos uu____3151 in
          ("end", uu____3150) in
        [uu____3144] in
      uu____3126 :: uu____3136 in
    FStar_Util.JsonAssoc uu____3118
let (js_dummyrange : FStar_Util.json) =
  FStar_Util.JsonAssoc
    [("start",
       (FStar_Util.JsonAssoc
          [("line", (FStar_Util.JsonInt (Prims.parse_int "0")));
          ("character", (FStar_Util.JsonInt (Prims.parse_int "0")));
          ("end",
            (FStar_Util.JsonAssoc
               [("line", (FStar_Util.JsonInt (Prims.parse_int "0")));
               ("character", (FStar_Util.JsonInt (Prims.parse_int "0")))]))]))]
let (js_loclink : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let s = js_range r in
    let uu____3238 =
      let uu____3241 =
        let uu____3242 =
          let uu____3250 =
            let uu____3256 =
              let uu____3257 =
                let uu____3259 = FStar_Range.file_of_range r in
                path_to_uri uu____3259 in
              FStar_Util.JsonStr uu____3257 in
            ("targetUri", uu____3256) in
          [uu____3250; ("targetRange", s); ("targetSelectionRange", s)] in
        FStar_Util.JsonAssoc uu____3242 in
      [uu____3241] in
    FStar_Util.JsonList uu____3238
let (pos_munge : txdoc_pos -> (Prims.string * Prims.int * Prims.int)) =
  fun pos -> ((pos.path), (pos.line + (Prims.parse_int "1")), (pos.col))
let (js_diag :
  Prims.string ->
    Prims.string ->
      FStar_Range.range FStar_Pervasives_Native.option -> assoct)
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
            (FStar_Util.JsonList
               [FStar_Util.JsonAssoc
                  [("range", r'); ("message", (FStar_Util.JsonStr msg))]])) in
        let uu____3359 =
          let uu____3367 =
            let uu____3373 =
              let uu____3374 =
                let uu____3382 =
                  let uu____3388 =
                    let uu____3389 = path_to_uri fname in
                    FStar_Util.JsonStr uu____3389 in
                  ("uri", uu____3388) in
                [uu____3382; ds] in
              FStar_Util.JsonAssoc uu____3374 in
            ("params", uu____3373) in
          [uu____3367] in
        ("method", (FStar_Util.JsonStr "textDocument/publishDiagnostics")) ::
          uu____3359
let (js_diag_clear : Prims.string -> assoct) =
  fun fname ->
    let uu____3436 =
      let uu____3444 =
        let uu____3450 =
          let uu____3451 =
            let uu____3459 =
              let uu____3465 =
                let uu____3466 = path_to_uri fname in
                FStar_Util.JsonStr uu____3466 in
              ("uri", uu____3465) in
            [uu____3459; ("diagnostics", (FStar_Util.JsonList []))] in
          FStar_Util.JsonAssoc uu____3451 in
        ("params", uu____3450) in
      [uu____3444] in
    ("method", (FStar_Util.JsonStr "textDocument/publishDiagnostics")) ::
      uu____3436
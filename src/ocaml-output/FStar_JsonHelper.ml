open Prims
let (try_assoc :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list ->
      FStar_Util.json FStar_Pervasives_Native.option)
  =
  fun key ->
    fun d ->
      let uu____57 =
        FStar_Util.try_find
          (fun uu____73 -> match uu____73 with | (k, uu____81) -> k = key) d in
      FStar_Util.map_option FStar_Pervasives_Native.snd uu____57
exception MissingKey of Prims.string 
let (uu___is_MissingKey : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MissingKey uu____104 -> true | uu____107 -> false
let (__proj__MissingKey__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | MissingKey uu____117 -> uu____117
exception InvalidQuery of Prims.string 
let (uu___is_InvalidQuery : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | InvalidQuery uu____132 -> true
    | uu____135 -> false
let (__proj__InvalidQuery__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidQuery uu____145 -> uu____145
exception UnexpectedJsonType of (Prims.string * FStar_Util.json) 
let (uu___is_UnexpectedJsonType : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnexpectedJsonType uu____164 -> true
    | uu____171 -> false
let (__proj__UnexpectedJsonType__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Util.json)) =
  fun projectee ->
    match projectee with | UnexpectedJsonType uu____189 -> uu____189
exception MalformedHeader 
let (uu___is_MalformedHeader : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | MalformedHeader -> true | uu____204 -> false
exception InputExhausted 
let (uu___is_InputExhausted : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InputExhausted -> true | uu____215 -> false
let (assoc :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun key ->
    fun a ->
      let uu____244 = try_assoc key a in
      match uu____244 with
      | FStar_Pervasives_Native.Some v1 -> v1
      | FStar_Pervasives_Native.None ->
          let uu____248 =
            let uu____249 = FStar_Util.format1 "Missing key [%s]" key in
            MissingKey uu____249 in
          FStar_Exn.raise uu____248
let (write_json : FStar_Util.json -> unit) =
  fun js ->
    (let uu____259 = FStar_Util.string_of_json js in
     FStar_Util.print_raw uu____259);
    FStar_Util.print_raw "\n"
let (write_jsonrpc : FStar_Util.json -> unit) =
  fun js ->
    let js_str = FStar_Util.string_of_json js in
    let len = FStar_Util.string_of_int (FStar_String.length js_str) in
    let uu____272 =
      FStar_Util.format2 "Content-Length: %s\r\n\r\n%s" len js_str in
    FStar_Util.print_raw uu____272
let js_fail : 'a . Prims.string -> FStar_Util.json -> 'a =
  fun expected ->
    fun got -> FStar_Exn.raise (UnexpectedJsonType (expected, got))
let (js_int : FStar_Util.json -> Prims.int) =
  fun uu___0_306 ->
    match uu___0_306 with
    | FStar_Util.JsonInt i -> i
    | other -> js_fail "int" other
let (js_str : FStar_Util.json -> Prims.string) =
  fun uu___1_323 ->
    match uu___1_323 with
    | FStar_Util.JsonStr s -> s
    | other -> js_fail "string" other
let js_list :
  'a . (FStar_Util.json -> 'a) -> FStar_Util.json -> 'a Prims.list =
  fun k ->
    fun uu___2_352 ->
      match uu___2_352 with
      | FStar_Util.JsonList l -> FStar_List.map k l
      | other -> js_fail "list" other
let (js_assoc :
  FStar_Util.json -> (Prims.string * FStar_Util.json) Prims.list) =
  fun uu___3_384 ->
    match uu___3_384 with
    | FStar_Util.JsonAssoc a -> a
    | other -> js_fail "dictionary" other
let (js_str_int : FStar_Util.json -> Prims.int) =
  fun uu___4_419 ->
    match uu___4_419 with
    | FStar_Util.JsonInt i -> i
    | FStar_Util.JsonStr s -> FStar_Util.int_of_string s
    | other -> js_fail "string or int" other
let (arg :
  Prims.string ->
    (Prims.string * FStar_Util.json) Prims.list -> FStar_Util.json)
  =
  fun k ->
    fun r ->
      let uu____455 =
        let uu____463 = assoc "params" r in
        FStar_All.pipe_right uu____463 js_assoc in
      assoc k uu____455
let (uri_to_path : Prims.string -> Prims.string) =
  fun u ->
    if FStar_Util.starts_with u "file://"
    then FStar_Util.substring_from u (Prims.parse_int "7")
    else u
let (path_to_uri : Prims.string -> Prims.string) =
  fun u ->
    if FStar_Util.starts_with u "file://"
    then u
    else FStar_Util.format1 "file://%s" u
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
  fun uu___5_556 ->
    match uu___5_556 with
    | FStar_Util.JsonAssoc a ->
        let uu____565 =
          let uu____567 = assoc "triggerKind" a in
          FStar_All.pipe_right uu____567 js_int in
        let uu____570 =
          let uu____574 = try_assoc "triggerChar" a in
          FStar_All.pipe_right uu____574 (FStar_Util.map_option js_str) in
        { trigger_kind = uu____565; trigger_char = uu____570 }
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
  fun uu___6_682 ->
    match uu___6_682 with
    | FStar_Util.JsonAssoc a ->
        let arg1 k = assoc k a in
        let uu____699 =
          let uu____701 = arg1 "uri" in FStar_All.pipe_right uu____701 js_str in
        let uu____704 =
          let uu____706 = arg1 "languageId" in
          FStar_All.pipe_right uu____706 js_str in
        let uu____709 =
          let uu____711 = arg1 "version" in
          FStar_All.pipe_right uu____711 js_int in
        let uu____714 =
          let uu____716 = arg1 "text" in
          FStar_All.pipe_right uu____716 js_str in
        {
          fname = uu____699;
          langId = uu____704;
          version = uu____709;
          text = uu____714
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
    let uu____803 =
      let uu____804 =
        let uu____812 = arg "textDocument" r in
        FStar_All.pipe_right uu____812 js_assoc in
      assoc "uri" uu____804 in
    FStar_All.pipe_right uu____803 js_str
let (js_txdoc_pos : (Prims.string * FStar_Util.json) Prims.list -> txdoc_pos)
  =
  fun r ->
    let pos =
      let uu____851 = arg "position" r in
      FStar_All.pipe_right uu____851 js_assoc in
    let uu____860 = js_txdoc_id r in
    let uu____862 =
      let uu____864 = assoc "line" pos in
      FStar_All.pipe_right uu____864 js_int in
    let uu____867 =
      let uu____869 = assoc "character" pos in
      FStar_All.pipe_right uu____869 js_int in
    { uri = uu____860; line = uu____862; col = uu____867 }
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
  fun uu___7_942 ->
    match uu___7_942 with
    | FStar_Util.JsonAssoc a ->
        let added' =
          let uu____959 = assoc "added" a in
          FStar_All.pipe_right uu____959 js_assoc in
        let removed' =
          let uu____976 = assoc "removed" a in
          FStar_All.pipe_right uu____976 js_assoc in
        let uu____985 =
          let uu____986 =
            let uu____988 = assoc "uri" added' in
            FStar_All.pipe_right uu____988 js_str in
          let uu____991 =
            let uu____993 = assoc "name" added' in
            FStar_All.pipe_right uu____993 js_str in
          { wk_uri = uu____986; wk_name = uu____991 } in
        let uu____996 =
          let uu____997 =
            let uu____999 = assoc "uri" removed' in
            FStar_All.pipe_right uu____999 js_str in
          let uu____1002 =
            let uu____1004 = assoc "name" removed' in
            FStar_All.pipe_right uu____1004 js_str in
          { wk_uri = uu____997; wk_name = uu____1002 } in
        { added = uu____985; removed = uu____996 }
    | other -> js_fail "dictionary" other
let (js_contentch : FStar_Util.json -> Prims.string) =
  fun uu___8_1019 ->
    match uu___8_1019 with
    | FStar_Util.JsonList l ->
        let uu____1024 =
          FStar_List.map
            (fun uu____1032 ->
               match uu____1032 with
               | FStar_Util.JsonAssoc a ->
                   let uu____1042 = assoc "text" a in
                   FStar_All.pipe_right uu____1042 js_str) l in
        FStar_List.hd uu____1024
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
  fun uu___9_1140 ->
    match uu___9_1140 with
    | FStar_Util.JsonAssoc a ->
        let st = assoc "start" a in
        let fin = assoc "end" a in
        let l = assoc "line" in
        let c = assoc "character" in
        let uu____1179 =
          let uu____1186 =
            let uu____1188 =
              let uu____1189 = FStar_All.pipe_right st js_assoc in
              l uu____1189 in
            FStar_All.pipe_right uu____1188 js_int in
          let uu____1205 =
            let uu____1207 =
              let uu____1208 = FStar_All.pipe_right st js_assoc in
              c uu____1208 in
            FStar_All.pipe_right uu____1207 js_int in
          (uu____1186, uu____1205) in
        let uu____1226 =
          let uu____1233 =
            let uu____1235 =
              let uu____1236 = FStar_All.pipe_right fin js_assoc in
              l uu____1236 in
            FStar_All.pipe_right uu____1235 js_int in
          let uu____1252 =
            let uu____1254 =
              let uu____1255 = FStar_All.pipe_right st js_assoc in
              c uu____1255 in
            FStar_All.pipe_right uu____1254 js_int in
          (uu____1233, uu____1252) in
        { rng_start = uu____1179; rng_end = uu____1226 }
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
    match projectee with | Initialize _0 -> true | uu____1425 -> false
let (__proj__Initialize__item___0 : lquery -> (Prims.int * Prims.string)) =
  fun projectee -> match projectee with | Initialize _0 -> _0
let (uu___is_Initialized : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Initialized -> true | uu____1461 -> false
let (uu___is_Shutdown : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Shutdown -> true | uu____1472 -> false
let (uu___is_Exit : lquery -> Prims.bool) =
  fun projectee -> match projectee with | Exit -> true | uu____1483 -> false
let (uu___is_Cancel : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Cancel _0 -> true | uu____1496 -> false
let (__proj__Cancel__item___0 : lquery -> Prims.int) =
  fun projectee -> match projectee with | Cancel _0 -> _0
let (uu___is_FolderChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FolderChange _0 -> true | uu____1518 -> false
let (__proj__FolderChange__item___0 : lquery -> wsch_event) =
  fun projectee -> match projectee with | FolderChange _0 -> _0
let (uu___is_ChangeConfig : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeConfig -> true | uu____1536 -> false
let (uu___is_ChangeWatch : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ChangeWatch -> true | uu____1547 -> false
let (uu___is_Symbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Symbol _0 -> true | uu____1560 -> false
let (__proj__Symbol__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | Symbol _0 -> _0
let (uu___is_ExecCommand : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ExecCommand _0 -> true | uu____1583 -> false
let (__proj__ExecCommand__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | ExecCommand _0 -> _0
let (uu___is_DidOpen : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidOpen _0 -> true | uu____1605 -> false
let (__proj__DidOpen__item___0 : lquery -> txdoc_item) =
  fun projectee -> match projectee with | DidOpen _0 -> _0
let (uu___is_DidChange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidChange _0 -> true | uu____1630 -> false
let (__proj__DidChange__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidChange _0 -> _0
let (uu___is_WillSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSave _0 -> true | uu____1668 -> false
let (__proj__WillSave__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSave _0 -> _0
let (uu___is_WillSaveWait : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | WillSaveWait _0 -> true | uu____1691 -> false
let (__proj__WillSaveWait__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | WillSaveWait _0 -> _0
let (uu___is_DidSave : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidSave _0 -> true | uu____1719 -> false
let (__proj__DidSave__item___0 : lquery -> (Prims.string * Prims.string)) =
  fun projectee -> match projectee with | DidSave _0 -> _0
let (uu___is_DidClose : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DidClose _0 -> true | uu____1757 -> false
let (__proj__DidClose__item___0 : lquery -> Prims.string) =
  fun projectee -> match projectee with | DidClose _0 -> _0
let (uu___is_Completion : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Completion _0 -> true | uu____1783 -> false
let (__proj__Completion__item___0 :
  lquery -> (txdoc_pos * completion_context)) =
  fun projectee -> match projectee with | Completion _0 -> _0
let (uu___is_Resolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Resolve -> true | uu____1813 -> false
let (uu___is_Hover : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Hover _0 -> true | uu____1825 -> false
let (__proj__Hover__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Hover _0 -> _0
let (uu___is_SignatureHelp : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | SignatureHelp _0 -> true | uu____1844 -> false
let (__proj__SignatureHelp__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | SignatureHelp _0 -> _0
let (uu___is_Declaration : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Declaration _0 -> true | uu____1863 -> false
let (__proj__Declaration__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Declaration _0 -> _0
let (uu___is_Definition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Definition _0 -> true | uu____1882 -> false
let (__proj__Definition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Definition _0 -> _0
let (uu___is_TypeDefinition : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeDefinition _0 -> true | uu____1901 -> false
let (__proj__TypeDefinition__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | TypeDefinition _0 -> _0
let (uu___is_Implementation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Implementation _0 -> true | uu____1920 -> false
let (__proj__Implementation__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | Implementation _0 -> _0
let (uu___is_References : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | References -> true | uu____1938 -> false
let (uu___is_DocumentHighlight : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentHighlight _0 -> true | uu____1950 -> false
let (__proj__DocumentHighlight__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | DocumentHighlight _0 -> _0
let (uu___is_DocumentSymbol : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentSymbol -> true | uu____1968 -> false
let (uu___is_CodeAction : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeAction -> true | uu____1979 -> false
let (uu___is_CodeLens : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLens -> true | uu____1990 -> false
let (uu___is_CodeLensResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | CodeLensResolve -> true | uu____2001 -> false
let (uu___is_DocumentLink : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLink -> true | uu____2012 -> false
let (uu___is_DocumentLinkResolve : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentLinkResolve -> true | uu____2023 -> false
let (uu___is_DocumentColor : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | DocumentColor -> true | uu____2034 -> false
let (uu___is_ColorPresentation : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | ColorPresentation -> true | uu____2045 -> false
let (uu___is_Formatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Formatting -> true | uu____2056 -> false
let (uu___is_RangeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | RangeFormatting -> true | uu____2067 -> false
let (uu___is_TypeFormatting : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | TypeFormatting -> true | uu____2078 -> false
let (uu___is_Rename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | Rename -> true | uu____2089 -> false
let (uu___is_PrepareRename : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | PrepareRename _0 -> true | uu____2101 -> false
let (__proj__PrepareRename__item___0 : lquery -> txdoc_pos) =
  fun projectee -> match projectee with | PrepareRename _0 -> _0
let (uu___is_FoldingRange : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | FoldingRange -> true | uu____2119 -> false
let (uu___is_BadProtocolMsg : lquery -> Prims.bool) =
  fun projectee ->
    match projectee with | BadProtocolMsg _0 -> true | uu____2132 -> false
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
    match projectee with | LDInterleaved _0 -> true | uu____2261 -> false
let (__proj__LDInterleaved__item___0 :
  repl_task -> (timed_fname * timed_fname)) =
  fun projectee -> match projectee with | LDInterleaved _0 -> _0
let (uu___is_LDSingle : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | LDSingle _0 -> true | uu____2292 -> false
let (__proj__LDSingle__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDSingle _0 -> _0
let (uu___is_LDInterfaceOfCurrentFile : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with
    | LDInterfaceOfCurrentFile _0 -> true
    | uu____2311 -> false
let (__proj__LDInterfaceOfCurrentFile__item___0 : repl_task -> timed_fname) =
  fun projectee -> match projectee with | LDInterfaceOfCurrentFile _0 -> _0
let (uu___is_PushFragment : repl_task -> Prims.bool) =
  fun projectee ->
    match projectee with | PushFragment _0 -> true | uu____2330 -> false
let (__proj__PushFragment__item___0 :
  repl_task -> FStar_Parser_ParseIt.input_frag) =
  fun projectee -> match projectee with | PushFragment _0 -> _0
let (uu___is_Noop : repl_task -> Prims.bool) =
  fun projectee -> match projectee with | Noop -> true | uu____2348 -> false
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
type optresponse =
  (FStar_Util.json, FStar_Util.json) FStar_Util.either
    FStar_Pervasives_Native.option
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
    match projectee with | ParseError -> true | uu____2714 -> false
let (uu___is_InvalidRequest : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidRequest -> true | uu____2725 -> false
let (uu___is_MethodNotFound : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | MethodNotFound -> true | uu____2736 -> false
let (uu___is_InvalidParams : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidParams -> true | uu____2747 -> false
let (uu___is_InternalError : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalError -> true | uu____2758 -> false
let (uu___is_ServerErrorStart : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorStart -> true | uu____2769 -> false
let (uu___is_ServerErrorEnd : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerErrorEnd -> true | uu____2780 -> false
let (uu___is_ServerNotInitialized : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ServerNotInitialized -> true | uu____2791 -> false
let (uu___is_UnknownErrorCode : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | UnknownErrorCode -> true | uu____2802 -> false
let (uu___is_RequestCancelled : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | RequestCancelled -> true | uu____2813 -> false
let (uu___is_ContentModified : error_code -> Prims.bool) =
  fun projectee ->
    match projectee with | ContentModified -> true | uu____2824 -> false
let (errorcode_to_int : error_code -> Prims.int) =
  fun uu___10_2836 ->
    match uu___10_2836 with
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
  fun uu___11_2855 ->
    match uu___11_2855 with
    | FStar_Util.JsonNull -> "null"
    | FStar_Util.JsonBool b ->
        FStar_Util.format1 "bool (%s)" (if b then "true" else "false")
    | FStar_Util.JsonInt i ->
        let uu____2869 = FStar_Util.string_of_int i in
        FStar_Util.format1 "int (%s)" uu____2869
    | FStar_Util.JsonStr s -> FStar_Util.format1 "string (%s)" s
    | FStar_Util.JsonList uu____2875 -> "list (...)"
    | FStar_Util.JsonAssoc uu____2879 -> "dictionary (...)"
let (wrap_jsfail :
  Prims.int FStar_Pervasives_Native.option ->
    Prims.string -> FStar_Util.json -> lsp_query)
  =
  fun qid ->
    fun expected ->
      fun got ->
        let uu____2912 =
          let uu____2913 =
            let uu____2915 = json_debug got in
            FStar_Util.format2 "JSON decoding failed: expected %s, got %s"
              expected uu____2915 in
          BadProtocolMsg uu____2913 in
        { query_id = qid; q = uu____2912 }
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
      let uu____3017 =
        let uu____3025 =
          let uu____3031 =
            let uu____3032 = errorcode_to_int err in
            FStar_Util.JsonInt uu____3032 in
          ("code", uu____3031) in
        [uu____3025; ("message", (FStar_Util.JsonStr msg))] in
      FStar_Util.JsonAssoc uu____3017
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
    let uu____3238 =
      let uu____3246 =
        let uu____3252 =
          let uu____3253 =
            let uu____3255 = FStar_Range.line_of_pos p in
            uu____3255 - (Prims.parse_int "1") in
          FStar_Util.JsonInt uu____3253 in
        ("line", uu____3252) in
      let uu____3260 =
        let uu____3268 =
          let uu____3274 =
            let uu____3275 = FStar_Range.col_of_pos p in
            FStar_Util.JsonInt uu____3275 in
          ("character", uu____3274) in
        [uu____3268] in
      uu____3246 :: uu____3260 in
    FStar_Util.JsonAssoc uu____3238
let (js_loclink : FStar_Range.range -> FStar_Util.json) =
  fun r ->
    let s =
      let uu____3301 =
        let uu____3309 =
          let uu____3315 =
            let uu____3316 = FStar_Range.start_of_range r in
            js_pos uu____3316 in
          ("start", uu____3315) in
        let uu____3319 =
          let uu____3327 =
            let uu____3333 =
              let uu____3334 = FStar_Range.end_of_range r in
              js_pos uu____3334 in
            ("end", uu____3333) in
          [uu____3327] in
        uu____3309 :: uu____3319 in
      FStar_Util.JsonAssoc uu____3301 in
    let uu____3352 =
      let uu____3355 =
        let uu____3356 =
          let uu____3364 =
            let uu____3370 =
              let uu____3371 =
                let uu____3373 = FStar_Range.file_of_range r in
                path_to_uri uu____3373 in
              FStar_Util.JsonStr uu____3371 in
            ("targetUri", uu____3370) in
          [uu____3364; ("targetRange", s); ("targetSelectionRange", s)] in
        FStar_Util.JsonAssoc uu____3356 in
      [uu____3355] in
    FStar_Util.JsonList uu____3352
let (pos_munge : txdoc_pos -> (Prims.string * Prims.int * Prims.int)) =
  fun pos ->
    let uu____3416 = uri_to_path pos.uri in
    (uu____3416, (pos.line + (Prims.parse_int "1")), (pos.col))
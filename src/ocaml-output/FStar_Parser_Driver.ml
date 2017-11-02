open Prims
let is_cache_file: Prims.string -> Prims.bool =
  fun fn  ->
    let uu____4 = FStar_Util.get_file_extension fn in uu____4 = ".cache"
type fragment =
  | Empty
  | Modul of FStar_Parser_AST.modul
  | Decls of FStar_Parser_AST.decl Prims.list[@@deriving show]
let uu___is_Empty: fragment -> Prims.bool =
  fun projectee  -> match projectee with | Empty  -> true | uu____18 -> false
let uu___is_Modul: fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Modul _0 -> true | uu____23 -> false
let __proj__Modul__item___0: fragment -> FStar_Parser_AST.modul =
  fun projectee  -> match projectee with | Modul _0 -> _0
let uu___is_Decls: fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Decls _0 -> true | uu____37 -> false
let __proj__Decls__item___0: fragment -> FStar_Parser_AST.decl Prims.list =
  fun projectee  -> match projectee with | Decls _0 -> _0
let parse_fragment: FStar_Parser_ParseIt.input_frag -> fragment =
  fun frag  ->
    let uu____54 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag) in
    match uu____54 with
    | FStar_Util.Inl (FStar_Util.Inl modul,uu____74) -> Modul modul
    | FStar_Util.Inl (FStar_Util.Inr [],uu____115) -> Empty
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____157) -> Decls decls
    | FStar_Util.Inr (msg,r) -> FStar_Exn.raise (FStar_Errors.Error (msg, r))
let parse_file:
  FStar_Parser_ParseIt.filename ->
    (FStar_Parser_AST.file,(Prims.string,FStar_Range.range)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun fn  ->
    let uu____229 = FStar_Parser_ParseIt.parse (FStar_Util.Inl fn) in
    match uu____229 with
    | FStar_Util.Inl (FStar_Util.Inl ast,comments) -> (ast, comments)
    | FStar_Util.Inl (FStar_Util.Inr uu____306,uu____307) ->
        let msg = FStar_Util.format1 "%s: expected a module\n" fn in
        let r = FStar_Range.dummyRange in
        FStar_Exn.raise (FStar_Errors.Error (msg, r))
    | FStar_Util.Inr (msg,r) -> FStar_Exn.raise (FStar_Errors.Error (msg, r))
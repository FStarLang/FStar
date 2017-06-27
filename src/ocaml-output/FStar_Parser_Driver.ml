open Prims
let is_cache_file : Prims.string -> Prims.bool =
  fun fn  ->
    let uu____4 = FStar_Util.get_file_extension fn  in uu____4 = ".cache"
  
type fragment =
  | Empty 
  | Modul of FStar_Parser_AST.modul 
  | Decls of FStar_Parser_AST.decl Prims.list 
let uu___is_Empty : fragment -> Prims.bool =
  fun projectee  -> match projectee with | Empty  -> true | uu____17 -> false 
let uu___is_Modul : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Modul _0 -> true | uu____22 -> false
  
let __proj__Modul__item___0 : fragment -> FStar_Parser_AST.modul =
  fun projectee  -> match projectee with | Modul _0 -> _0 
let uu___is_Decls : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Decls _0 -> true | uu____35 -> false
  
let __proj__Decls__item___0 : fragment -> FStar_Parser_AST.decl Prims.list =
  fun projectee  -> match projectee with | Decls _0 -> _0 
let parse_fragment : FStar_Parser_ParseIt.input_frag -> fragment =
  fun frag  ->
    let uu____49 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag)  in
    match uu____49 with
    | FStar_Util.Inl (FStar_Util.Inl [],uu____59) -> Empty
    | FStar_Util.Inl (FStar_Util.Inl (modul::[]),uu____84) -> Modul modul
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____109) -> Decls decls
    | FStar_Util.Inl (FStar_Util.Inl uu____131,uu____132) ->
        raise
          (FStar_Errors.Err
             "Refusing to check more than one module at a time incrementally")
    | FStar_Util.Inr (msg,r) -> raise (FStar_Errors.Error (msg, r))
  
let parse_file :
  FStar_Parser_ParseIt.filename ->
    (FStar_Parser_AST.file,(Prims.string,FStar_Range.range)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun fn  ->
    let uu____170 = FStar_Parser_ParseIt.parse (FStar_Util.Inl fn)  in
    match uu____170 with
    | FStar_Util.Inl (FStar_Util.Inl ast,comments) -> (ast, comments)
    | FStar_Util.Inl (FStar_Util.Inr uu____210,uu____211) ->
        let msg = FStar_Util.format1 "%s: expected a module\n" fn  in
        let r = FStar_Range.dummyRange  in
        raise (FStar_Errors.Error (msg, r))
    | FStar_Util.Inr (msg,r) -> raise (FStar_Errors.Error (msg, r))
  
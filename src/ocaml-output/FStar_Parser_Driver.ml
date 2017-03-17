open Prims
let is_cache_file : Prims.string -> Prims.bool =
  fun fn  ->
    let _0_285 = FStar_Util.get_file_extension fn  in _0_285 = ".cache"
  
type fragment =
  | Empty 
  | Modul of FStar_Parser_AST.modul 
  | Decls of FStar_Parser_AST.decl Prims.list 
let uu___is_Empty : fragment -> Prims.bool =
  fun projectee  -> match projectee with | Empty  -> true | uu____14 -> false 
let uu___is_Modul : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Modul _0 -> true | uu____19 -> false
  
let __proj__Modul__item___0 : fragment -> FStar_Parser_AST.modul =
  fun projectee  -> match projectee with | Modul _0 -> _0 
let uu___is_Decls : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Decls _0 -> true | uu____32 -> false
  
let __proj__Decls__item___0 : fragment -> FStar_Parser_AST.decl Prims.list =
  fun projectee  -> match projectee with | Decls _0 -> _0 
let parse_fragment : FStar_Parser_ParseIt.input_frag -> fragment =
  fun frag  ->
    let uu____46 = FStar_Parser_ParseIt.parse (FStar_Util.Inr frag)  in
    match uu____46 with
    | FStar_Util.Inl (FStar_Util.Inl [],uu____56) -> Empty
    | FStar_Util.Inl (FStar_Util.Inl (modul::[]),uu____81) -> Modul modul
    | FStar_Util.Inl (FStar_Util.Inr decls,uu____106) -> Decls decls
    | FStar_Util.Inl (FStar_Util.Inl uu____128,uu____129) ->
        Prims.raise
          (FStar_Errors.Err
             "Refusing to check more than one module at a time incrementally")
    | FStar_Util.Inr (msg,r) -> Prims.raise (FStar_Errors.Error (msg, r))
  
let parse_file :
  FStar_Parser_ParseIt.filename ->
    (FStar_Parser_AST.file * (Prims.string * FStar_Range.range) Prims.list)
  =
  fun fn  ->
    let uu____167 = FStar_Parser_ParseIt.parse (FStar_Util.Inl fn)  in
    match uu____167 with
    | FStar_Util.Inl (FStar_Util.Inl ast,comments) -> (ast, comments)
    | FStar_Util.Inl (FStar_Util.Inr uu____207,uu____208) ->
        let msg = FStar_Util.format1 "%s: expected a module\n" fn  in
        let r = FStar_Range.dummyRange  in
        Prims.raise (FStar_Errors.Error (msg, r))
    | FStar_Util.Inr (msg,r) -> Prims.raise (FStar_Errors.Error (msg, r))
  
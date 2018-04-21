open Prims
let is_cache_file : Prims.string -> Prims.bool =
  fun fn  ->
    let uu____6 = FStar_Util.get_file_extension fn  in uu____6 = ".cache"
  
type fragment =
  | Empty 
  | Modul of FStar_Parser_AST.modul 
  | Decls of FStar_Parser_AST.decl Prims.list [@@deriving show]
let uu___is_Empty : fragment -> Prims.bool =
  fun projectee  -> match projectee with | Empty  -> true | uu____24 -> false 
let uu___is_Modul : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Modul _0 -> true | uu____31 -> false
  
let __proj__Modul__item___0 : fragment -> FStar_Parser_AST.modul =
  fun projectee  -> match projectee with | Modul _0 -> _0 
let uu___is_Decls : fragment -> Prims.bool =
  fun projectee  ->
    match projectee with | Decls _0 -> true | uu____47 -> false
  
let __proj__Decls__item___0 : fragment -> FStar_Parser_AST.decl Prims.list =
  fun projectee  -> match projectee with | Decls _0 -> _0 
let parse_fragment : FStar_Parser_ParseIt.input_frag -> fragment =
  fun frag  ->
    let uu____66 =
      FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Toplevel frag)  in
    match uu____66 with
    | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl modul,uu____68) ->
        Modul modul
    | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr [],uu____89) -> Empty
    | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr decls,uu____111) ->
        Decls decls
    | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
        FStar_Errors.raise_error (e, msg) r
    | FStar_Parser_ParseIt.Term uu____137 ->
        failwith
          "Impossible: parsing a Toplevel always results in an ASTFragment"
  
let parse_file :
  FStar_Parser_ParseIt.filename ->
    (FStar_Parser_AST.file,(Prims.string,FStar_Range.range)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun fn  ->
    let uu____153 =
      FStar_Parser_ParseIt.parse (FStar_Parser_ParseIt.Filename fn)  in
    match uu____153 with
    | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inl ast,comments) ->
        (ast, comments)
    | FStar_Parser_ParseIt.ASTFragment (FStar_Util.Inr uu____192,uu____193)
        ->
        let msg = FStar_Util.format1 "%s: expected a module\n" fn  in
        let r = FStar_Range.dummyRange  in
        FStar_Errors.raise_error (FStar_Errors.Fatal_ModuleExpected, msg) r
    | FStar_Parser_ParseIt.ParseError (e,msg,r) ->
        FStar_Errors.raise_error (e, msg) r
    | FStar_Parser_ParseIt.Term uu____241 ->
        failwith
          "Impossible: parsing a Filename always results in an ASTFragment"
  
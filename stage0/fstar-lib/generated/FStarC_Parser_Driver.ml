open Prims
let (is_cache_file : Prims.string -> Prims.bool) =
  fun fn ->
    let uu___ = FStarC_Compiler_Util.get_file_extension fn in
    uu___ = ".cache"
type fragment =
  | Empty 
  | Modul of FStarC_Parser_AST.modul 
  | Decls of FStarC_Parser_AST.decl Prims.list 
  | DeclsWithContent of (FStarC_Parser_AST.decl *
  FStarC_Parser_ParseIt.code_fragment) Prims.list 
let (uu___is_Empty : fragment -> Prims.bool) =
  fun projectee -> match projectee with | Empty -> true | uu___ -> false
let (uu___is_Modul : fragment -> Prims.bool) =
  fun projectee -> match projectee with | Modul _0 -> true | uu___ -> false
let (__proj__Modul__item___0 : fragment -> FStarC_Parser_AST.modul) =
  fun projectee -> match projectee with | Modul _0 -> _0
let (uu___is_Decls : fragment -> Prims.bool) =
  fun projectee -> match projectee with | Decls _0 -> true | uu___ -> false
let (__proj__Decls__item___0 : fragment -> FStarC_Parser_AST.decl Prims.list)
  = fun projectee -> match projectee with | Decls _0 -> _0
let (uu___is_DeclsWithContent : fragment -> Prims.bool) =
  fun projectee ->
    match projectee with | DeclsWithContent _0 -> true | uu___ -> false
let (__proj__DeclsWithContent__item___0 :
  fragment ->
    (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment) Prims.list)
  = fun projectee -> match projectee with | DeclsWithContent _0 -> _0
let (parse_fragment :
  FStarC_Parser_ParseIt.lang_opts ->
    FStarC_Parser_ParseIt.input_frag -> fragment)
  =
  fun lang_opt ->
    fun frag ->
      let uu___ =
        FStarC_Parser_ParseIt.parse lang_opt
          (FStarC_Parser_ParseIt.Toplevel frag) in
      match uu___ with
      | FStarC_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inl modul, uu___1) -> Modul modul
      | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inr [], uu___1)
          -> Empty
      | FStarC_Parser_ParseIt.ASTFragment
          (FStar_Pervasives.Inr decls, uu___1) -> Decls decls
      | FStarC_Parser_ParseIt.IncrementalFragment (decls, uu___1, uu___2) ->
          DeclsWithContent decls
      | FStarC_Parser_ParseIt.ParseError (e, msg, r) ->
          FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r e
            () (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
            (Obj.magic msg)
      | FStarC_Parser_ParseIt.Term uu___1 ->
          failwith
            "Impossible: parsing a Toplevel always results in an ASTFragment"
let (maybe_dump_module : FStarC_Parser_AST.modul -> unit) =
  fun m ->
    match m with
    | FStarC_Parser_AST.Module (l, ds) ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_lid l in
          FStarC_Options.dump_module uu___1 in
        if uu___
        then
          let uu___1 = FStarC_Ident.string_of_lid l in
          let uu___2 =
            let uu___3 =
              FStarC_Compiler_List.map
                (FStarC_Class_Show.show FStarC_Parser_AST.showable_decl) ds in
            FStarC_Compiler_String.concat "\n" uu___3 in
          FStarC_Compiler_Util.print2 "Parsed module %s\n%s\n" uu___1 uu___2
        else ()
    | FStarC_Parser_AST.Interface (l, ds, uu___) ->
        let uu___1 =
          let uu___2 = FStarC_Ident.string_of_lid l in
          FStarC_Options.dump_module uu___2 in
        if uu___1
        then
          let uu___2 = FStarC_Ident.string_of_lid l in
          let uu___3 =
            let uu___4 =
              FStarC_Compiler_List.map
                (FStarC_Class_Show.show FStarC_Parser_AST.showable_decl) ds in
            FStarC_Compiler_String.concat "\n" uu___4 in
          FStarC_Compiler_Util.print2 "Parsed module %s\n%s\n" uu___2 uu___3
        else ()
let (parse_file :
  Prims.string ->
    (FStarC_Parser_AST.file * (Prims.string *
      FStarC_Compiler_Range_Type.range) Prims.list))
  =
  fun fn ->
    let uu___ =
      FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
        (FStarC_Parser_ParseIt.Filename fn) in
    match uu___ with
    | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inl ast, comments)
        -> (ast, comments)
    | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inr uu___1, uu___2)
        ->
        let msg = FStarC_Compiler_Util.format1 "%s: expected a module\n" fn in
        let r = FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
          FStarC_Errors_Codes.Fatal_ModuleExpected ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic msg)
    | FStarC_Parser_ParseIt.ParseError (e, msg, r) ->
        FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r e ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic msg)
    | FStarC_Parser_ParseIt.Term uu___1 ->
        failwith
          "Impossible: parsing a Filename always results in an ASTFragment"
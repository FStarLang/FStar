open Prims
let is_cache_file (fn : Prims.string) : Prims.bool=
  let uu___ = FStarC_Filepath.get_file_extension fn in uu___ = ".cache"
type fragment =
  | Empty 
  | Modul of FStarC_Parser_AST.modul 
  | Decls of FStarC_Parser_AST.decl Prims.list 
  | DeclsWithContent of (FStarC_Parser_AST.decl *
  FStarC_Parser_ParseIt.code_fragment) Prims.list 
let uu___is_Empty (projectee : fragment) : Prims.bool=
  match projectee with | Empty -> true | uu___ -> false
let uu___is_Modul (projectee : fragment) : Prims.bool=
  match projectee with | Modul _0 -> true | uu___ -> false
let __proj__Modul__item___0 (projectee : fragment) : FStarC_Parser_AST.modul=
  match projectee with | Modul _0 -> _0
let uu___is_Decls (projectee : fragment) : Prims.bool=
  match projectee with | Decls _0 -> true | uu___ -> false
let __proj__Decls__item___0 (projectee : fragment) :
  FStarC_Parser_AST.decl Prims.list= match projectee with | Decls _0 -> _0
let uu___is_DeclsWithContent (projectee : fragment) : Prims.bool=
  match projectee with | DeclsWithContent _0 -> true | uu___ -> false
let __proj__DeclsWithContent__item___0 (projectee : fragment) :
  (FStarC_Parser_AST.decl * FStarC_Parser_ParseIt.code_fragment) Prims.list=
  match projectee with | DeclsWithContent _0 -> _0
let parse_fragment (lang_opt : FStarC_Parser_ParseIt.lang_opts)
  (frag : FStarC_Parser_ParseIt.input_frag) : fragment=
  let uu___ =
    FStarC_Parser_ParseIt.parse lang_opt
      (FStarC_Parser_ParseIt.Toplevel frag) in
  match uu___ with
  | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inl modul, uu___1) ->
      Modul modul
  | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inr [], uu___1) ->
      Empty
  | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inr decls, uu___1) ->
      Decls decls
  | FStarC_Parser_ParseIt.IncrementalFragment (decls, uu___1, uu___2) ->
      DeclsWithContent decls
  | FStarC_Parser_ParseIt.ParseError (e, msg, r) ->
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r e ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic msg)
  | FStarC_Parser_ParseIt.Term uu___1 ->
      failwith
        "Impossible: parsing a Toplevel always results in an ASTFragment"
let maybe_dump_module (m : FStarC_Parser_AST.modul) : unit=
  match m with
  | FStarC_Parser_AST.Module
      { FStarC_Parser_AST.no_prelude = uu___;
        FStarC_Parser_AST.mname = mname; FStarC_Parser_AST.decls = decls;_}
      ->
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid mname in
        FStarC_Options.dump_module uu___2 in
      if uu___1
      then
        let uu___2 =
          FStarC_Class_Show.show FStarC_Ident.showable_lident mname in
        let uu___3 =
          let uu___4 =
            FStarC_List.map
              (FStarC_Class_Show.show FStarC_Parser_AST.showable_decl) decls in
          FStarC_String.concat "\n" uu___4 in
        FStarC_Format.print2 "Parsed module %s\n%s\n" uu___2 uu___3
      else ()
  | FStarC_Parser_AST.Interface
      { FStarC_Parser_AST.no_prelude1 = uu___;
        FStarC_Parser_AST.mname1 = mname; FStarC_Parser_AST.decls1 = decls;
        FStarC_Parser_AST.admitted = uu___1;_}
      ->
      let uu___2 =
        let uu___3 = FStarC_Ident.string_of_lid mname in
        FStarC_Options.dump_module uu___3 in
      if uu___2
      then
        let uu___3 =
          FStarC_Class_Show.show FStarC_Ident.showable_lident mname in
        let uu___4 =
          let uu___5 =
            FStarC_List.map
              (FStarC_Class_Show.show FStarC_Parser_AST.showable_decl) decls in
          FStarC_String.concat "\n" uu___5 in
        FStarC_Format.print2 "Parsed module %s\n%s\n" uu___3 uu___4
      else ()
let parse_file (fn : Prims.string) :
  (FStarC_Parser_AST.file * (Prims.string * FStarC_Range_Type.t) Prims.list)=
  let uu___ =
    FStarC_Parser_ParseIt.parse FStar_Pervasives_Native.None
      (FStarC_Parser_ParseIt.Filename fn) in
  match uu___ with
  | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inl ast, comments) ->
      (ast, comments)
  | FStarC_Parser_ParseIt.ASTFragment (FStar_Pervasives.Inr uu___1, uu___2)
      ->
      let msg = FStarC_Format.fmt1 "%s: expected a module\n" fn in
      let r = FStarC_Range_Type.dummyRange in
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Fatal_ModuleExpected ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string) (Obj.magic msg)
  | FStarC_Parser_ParseIt.ParseError (e, msg, r) ->
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r e ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic msg)
  | FStarC_Parser_ParseIt.Term uu___1 ->
      failwith
        "Impossible: parsing a Filename always results in an ASTFragment"

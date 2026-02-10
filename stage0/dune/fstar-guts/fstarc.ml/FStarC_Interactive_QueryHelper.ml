open Prims
type position = (Prims.string * Prims.int * Prims.int)
type sl_reponse =
  {
  slr_name: Prims.string ;
  slr_def_range: FStarC_Range_Type.t FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }
let __proj__Mksl_reponse__item__slr_name (projectee : sl_reponse) :
  Prims.string=
  match projectee with
  | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_name
let __proj__Mksl_reponse__item__slr_def_range (projectee : sl_reponse) :
  FStarC_Range_Type.t FStar_Pervasives_Native.option=
  match projectee with
  | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_def_range
let __proj__Mksl_reponse__item__slr_typ (projectee : sl_reponse) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_typ
let __proj__Mksl_reponse__item__slr_doc (projectee : sl_reponse) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_doc
let __proj__Mksl_reponse__item__slr_def (projectee : sl_reponse) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_def
let with_printed_effect_args (k : unit -> 'uuuuu) : 'uuuuu=
  FStarC_Options.with_saved_options
    (fun uu___ ->
       FStarC_Options.set_option "print_effect_args"
         (FStarC_Options.Bool true);
       k ())
let term_to_string (tcenv : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : Prims.string=
  with_printed_effect_args
    (fun uu___ -> FStarC_TypeChecker_Normalize.term_to_string tcenv t)
let sigelt_to_string (tcenv : FStarC_TypeChecker_Env.env)
  (se : FStarC_Syntax_Syntax.sigelt) : Prims.string=
  with_printed_effect_args
    (fun uu___ ->
       let uu___1 =
         FStarC_Syntax_DsEnv.set_current_module
           tcenv.FStarC_TypeChecker_Env.dsenv
           tcenv.FStarC_TypeChecker_Env.curmodule in
       FStarC_Syntax_Print.sigelt_to_string' uu___1 se)
let symlookup (tcenv : FStarC_TypeChecker_Env.env) (symbol : Prims.string)
  (pos_opt : position FStar_Pervasives_Native.option)
  (requested_info : Prims.string Prims.list) :
  sl_reponse FStar_Pervasives_Native.option=
  let info_of_lid_str lid_str =
    let lid =
      let uu___ =
        FStarC_List.map FStarC_Ident.id_of_text
          (FStarC_Util.split lid_str ".") in
      FStarC_Ident.lid_of_ids uu___ in
    let lid1 =
      let uu___ =
        FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
          tcenv.FStarC_TypeChecker_Env.dsenv lid in
      FStarC_Option.dflt lid uu___ in
    let uu___ = FStarC_TypeChecker_Env.try_lookup_lid tcenv lid1 in
    FStarC_Option.map
      (fun uu___1 ->
         match uu___1 with
         | ((uu___2, typ), r) -> ((FStar_Pervasives.Inr lid1), typ, r)) uu___ in
  let docs_of_lid lid = FStar_Pervasives_Native.None in
  let def_of_lid lid =
    let uu___ = FStarC_TypeChecker_Env.lookup_qname tcenv lid in
    FStarC_Option.bind uu___
      (fun uu___1 ->
         match uu___1 with
         | (FStar_Pervasives.Inr (se, uu___2), uu___3) ->
             let uu___4 = sigelt_to_string tcenv se in
             FStar_Pervasives_Native.Some uu___4
         | uu___2 -> FStar_Pervasives_Native.None) in
  let info_at_pos_opt =
    FStarC_Option.bind pos_opt
      (fun uu___ ->
         match uu___ with
         | (file, row, col) ->
             FStarC_TypeChecker_Err.info_at_pos tcenv file row col) in
  let info_opt =
    match info_at_pos_opt with
    | FStar_Pervasives_Native.Some uu___ -> info_at_pos_opt
    | FStar_Pervasives_Native.None ->
        if symbol = ""
        then FStar_Pervasives_Native.None
        else info_of_lid_str symbol in
  match info_opt with
  | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
  | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
      let name =
        match name_or_lid with
        | FStar_Pervasives.Inl name1 -> name1
        | FStar_Pervasives.Inr lid -> FStarC_Ident.string_of_lid lid in
      let str_of_opt uu___ =
        match uu___ with
        | FStar_Pervasives_Native.None -> "<none>"
        | FStar_Pervasives_Native.Some s -> s in
      let typ_str =
        if FStarC_List.mem "type" requested_info
        then
          let uu___ = term_to_string tcenv typ in
          FStar_Pervasives_Native.Some uu___
        else FStar_Pervasives_Native.None in
      let doc_str =
        match name_or_lid with
        | FStar_Pervasives.Inr lid when
            FStarC_List.mem "documentation" requested_info -> docs_of_lid lid
        | uu___ -> FStar_Pervasives_Native.None in
      let def_str =
        match name_or_lid with
        | FStar_Pervasives.Inr lid when
            FStarC_List.mem "definition" requested_info -> def_of_lid lid
        | uu___ -> FStar_Pervasives_Native.None in
      let def_range =
        if FStarC_List.mem "defined-at" requested_info
        then FStar_Pervasives_Native.Some rng
        else FStar_Pervasives_Native.None in
      FStar_Pervasives_Native.Some
        {
          slr_name = name;
          slr_def_range = def_range;
          slr_typ = typ_str;
          slr_doc = doc_str;
          slr_def = def_str
        }
let mod_filter
  (uu___ : ('uuuuu * FStarC_Interactive_CompletionTable.mod_symbol)) :
  ('uuuuu * FStarC_Interactive_CompletionTable.mod_symbol)
    FStar_Pervasives_Native.option=
  match uu___ with
  | (uu___1, FStarC_Interactive_CompletionTable.Namespace uu___2) ->
      FStar_Pervasives_Native.None
  | (uu___1, FStarC_Interactive_CompletionTable.Module
     { FStarC_Interactive_CompletionTable.mod_name = uu___2;
       FStarC_Interactive_CompletionTable.mod_path = uu___3;
       FStarC_Interactive_CompletionTable.mod_loaded = true;_})
      -> FStar_Pervasives_Native.None
  | (pth, FStarC_Interactive_CompletionTable.Module md) ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              let uu___5 = FStarC_Interactive_CompletionTable.mod_name md in
              Prims.strcat uu___5 "." in
            {
              FStarC_Interactive_CompletionTable.mod_name = uu___4;
              FStarC_Interactive_CompletionTable.mod_path =
                (md.FStarC_Interactive_CompletionTable.mod_path);
              FStarC_Interactive_CompletionTable.mod_loaded =
                (md.FStarC_Interactive_CompletionTable.mod_loaded)
            } in
          FStarC_Interactive_CompletionTable.Module uu___3 in
        (pth, uu___2) in
      FStar_Pervasives_Native.Some uu___1
let ck_completion (st : FStarC_Interactive_Ide_Types.repl_state)
  (search_term : Prims.string) :
  FStarC_Interactive_CompletionTable.completion_result Prims.list=
  let needle = FStarC_Util.split search_term "." in
  let mods_and_nss =
    FStarC_Interactive_CompletionTable.autocomplete_mod_or_ns
      st.FStarC_Interactive_Ide_Types.repl_names needle mod_filter in
  let lids =
    FStarC_Interactive_CompletionTable.autocomplete_lid
      st.FStarC_Interactive_Ide_Types.repl_names needle in
  FStarC_List.op_At lids mods_and_nss

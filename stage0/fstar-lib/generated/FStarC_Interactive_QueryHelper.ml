open Prims
type position = (Prims.string * Prims.int * Prims.int)
type sl_reponse =
  {
  slr_name: Prims.string ;
  slr_def_range:
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mksl_reponse__item__slr_name : sl_reponse -> Prims.string) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_name
let (__proj__Mksl_reponse__item__slr_def_range :
  sl_reponse ->
    FStarC_Compiler_Range_Type.range FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} ->
        slr_def_range
let (__proj__Mksl_reponse__item__slr_typ :
  sl_reponse -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_typ
let (__proj__Mksl_reponse__item__slr_doc :
  sl_reponse -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_doc
let (__proj__Mksl_reponse__item__slr_def :
  sl_reponse -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_def
let with_printed_effect_args : 'uuuuu . (unit -> 'uuuuu) -> 'uuuuu =
  fun k ->
    FStarC_Options.with_saved_options
      (fun uu___ ->
         FStarC_Options.set_option "print_effect_args"
           (FStarC_Options.Bool true);
         k ())
let (term_to_string :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.term -> Prims.string) =
  fun tcenv ->
    fun t ->
      with_printed_effect_args
        (fun uu___ -> FStarC_TypeChecker_Normalize.term_to_string tcenv t)
let (sigelt_to_string :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.sigelt -> Prims.string)
  =
  fun tcenv ->
    fun se ->
      with_printed_effect_args
        (fun uu___ ->
           let uu___1 =
             FStarC_Syntax_DsEnv.set_current_module
               tcenv.FStarC_TypeChecker_Env.dsenv
               tcenv.FStarC_TypeChecker_Env.curmodule in
           FStarC_Syntax_Print.sigelt_to_string' uu___1 se)
let (symlookup :
  FStarC_TypeChecker_Env.env ->
    Prims.string ->
      position FStar_Pervasives_Native.option ->
        Prims.string Prims.list -> sl_reponse FStar_Pervasives_Native.option)
  =
  fun tcenv ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let info_of_lid_str lid_str =
            let lid =
              let uu___ =
                FStarC_Compiler_List.map FStarC_Ident.id_of_text
                  (FStarC_Compiler_Util.split lid_str ".") in
              FStarC_Ident.lid_of_ids uu___ in
            let lid1 =
              let uu___ =
                FStarC_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStarC_TypeChecker_Env.dsenv lid in
              FStarC_Compiler_Util.dflt lid uu___ in
            let uu___ = FStarC_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStarC_Compiler_Util.map_option
              (fun uu___1 ->
                 match uu___1 with
                 | ((uu___2, typ), r) ->
                     ((FStar_Pervasives.Inr lid1), typ, r)) uu___ in
          let docs_of_lid lid = FStar_Pervasives_Native.None in
          let def_of_lid lid =
            let uu___ = FStarC_TypeChecker_Env.lookup_qname tcenv lid in
            FStarC_Compiler_Util.bind_opt uu___
              (fun uu___1 ->
                 match uu___1 with
                 | (FStar_Pervasives.Inr (se, uu___2), uu___3) ->
                     let uu___4 = sigelt_to_string tcenv se in
                     FStar_Pervasives_Native.Some uu___4
                 | uu___2 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStarC_Compiler_Util.bind_opt pos_opt
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
                if FStarC_Compiler_List.mem "type" requested_info
                then
                  let uu___ = term_to_string tcenv typ in
                  FStar_Pervasives_Native.Some uu___
                else FStar_Pervasives_Native.None in
              let doc_str =
                match name_or_lid with
                | FStar_Pervasives.Inr lid when
                    FStarC_Compiler_List.mem "documentation" requested_info
                    -> docs_of_lid lid
                | uu___ -> FStar_Pervasives_Native.None in
              let def_str =
                match name_or_lid with
                | FStar_Pervasives.Inr lid when
                    FStarC_Compiler_List.mem "definition" requested_info ->
                    def_of_lid lid
                | uu___ -> FStar_Pervasives_Native.None in
              let def_range =
                if FStarC_Compiler_List.mem "defined-at" requested_info
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
let mod_filter :
  'uuuuu .
    ('uuuuu * FStarC_Interactive_CompletionTable.mod_symbol) ->
      ('uuuuu * FStarC_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___ ->
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
let (ck_completion :
  FStarC_Interactive_Ide_Types.repl_state ->
    Prims.string ->
      FStarC_Interactive_CompletionTable.completion_result Prims.list)
  =
  fun st ->
    fun search_term ->
      let needle = FStarC_Compiler_Util.split search_term "." in
      let mods_and_nss =
        FStarC_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.FStarC_Interactive_Ide_Types.repl_names needle mod_filter in
      let lids =
        FStarC_Interactive_CompletionTable.autocomplete_lid
          st.FStarC_Interactive_Ide_Types.repl_names needle in
      FStarC_Compiler_List.op_At lids mods_and_nss
let (deflookup :
  FStarC_TypeChecker_Env.env ->
    FStarC_Interactive_JsonHelper.txdoc_pos ->
      FStarC_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun env ->
    fun pos ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Interactive_JsonHelper.pos_munge pos in
          FStar_Pervasives_Native.Some uu___2 in
        symlookup env "" uu___1 ["defined-at"] in
      match uu___ with
      | FStar_Pervasives_Native.Some
          { slr_name = uu___1;
            slr_def_range = FStar_Pervasives_Native.Some r; slr_typ = uu___2;
            slr_doc = uu___3; slr_def = uu___4;_}
          ->
          let uu___5 = FStarC_Interactive_JsonHelper.js_loclink r in
          FStarC_Interactive_JsonHelper.resultResponse uu___5
      | uu___1 -> FStarC_Interactive_JsonHelper.nullResponse
let (hoverlookup :
  FStarC_TypeChecker_Env.env ->
    FStarC_Interactive_JsonHelper.txdoc_pos ->
      FStarC_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun env ->
    fun pos ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Interactive_JsonHelper.pos_munge pos in
          FStar_Pervasives_Native.Some uu___2 in
        symlookup env "" uu___1 ["type"; "definition"] in
      match uu___ with
      | FStar_Pervasives_Native.Some
          { slr_name = n; slr_def_range = uu___1;
            slr_typ = FStar_Pervasives_Native.Some t; slr_doc = uu___2;
            slr_def = FStar_Pervasives_Native.Some d;_}
          ->
          let hovertxt =
            FStarC_Compiler_Util.format2
              "```fstar\n%s\n````\n---\n```fstar\n%s\n```" t d in
          FStarC_Interactive_JsonHelper.resultResponse
            (FStarC_Json.JsonAssoc
               [("contents",
                  (FStarC_Json.JsonAssoc
                     [("kind", (FStarC_Json.JsonStr "markdown"));
                     ("value", (FStarC_Json.JsonStr hovertxt))]))])
      | uu___1 -> FStarC_Interactive_JsonHelper.nullResponse
let (complookup :
  FStarC_Interactive_Ide_Types.repl_state ->
    FStarC_Interactive_JsonHelper.txdoc_pos ->
      FStarC_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun st ->
    fun pos ->
      let uu___ = FStarC_Interactive_JsonHelper.pos_munge pos in
      match uu___ with
      | (file, row, current_col) ->
          let uu___1 = FStarC_Parser_ParseIt.read_vfs_entry file in
          (match uu___1 with
           | FStar_Pervasives_Native.Some (uu___2, text) ->
               let rec find_col l =
                 match l with
                 | [] -> Prims.int_zero
                 | h::t ->
                     if
                       (h = 32) &&
                         ((FStarC_Compiler_List.length t) < current_col)
                     then (FStarC_Compiler_List.length t) + Prims.int_one
                     else find_col t in
               let str =
                 FStarC_Compiler_List.nth
                   (FStarC_Compiler_Util.splitlines text)
                   (row - Prims.int_one) in
               let explode s =
                 let rec exp i l =
                   if i < Prims.int_zero
                   then l
                   else
                     (let uu___4 =
                        let uu___5 = FStarC_Compiler_String.get s i in uu___5
                          :: l in
                      exp (i - Prims.int_one) uu___4) in
                 exp ((FStarC_Compiler_String.length s) - Prims.int_one) [] in
               let begin_col =
                 let uu___3 =
                   let uu___4 = explode str in
                   FStarC_Compiler_List.rev uu___4 in
                 find_col uu___3 in
               let term =
                 FStarC_Compiler_Util.substring str begin_col
                   (current_col - begin_col) in
               let items = ck_completion st term in
               let l =
                 FStarC_Compiler_List.map
                   (fun r ->
                      FStarC_Json.JsonAssoc
                        [("label",
                           (FStarC_Json.JsonStr
                              (r.FStarC_Interactive_CompletionTable.completion_candidate)))])
                   items in
               FStarC_Interactive_JsonHelper.resultResponse
                 (FStarC_Json.JsonList l))
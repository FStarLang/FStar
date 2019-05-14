open Prims
type loc = (Prims.string * Prims.int * Prims.int)
type env_t = FStar_TypeChecker_Env.env
type sl_reponse =
  {
  slr_name: Prims.string ;
  slr_def_range: FStar_Range.range FStar_Pervasives_Native.option ;
  slr_typ: Prims.string FStar_Pervasives_Native.option ;
  slr_doc: Prims.string FStar_Pervasives_Native.option ;
  slr_def: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mksl_reponse__item__slr_name : sl_reponse -> Prims.string) =
  fun projectee ->
    match projectee with
    | { slr_name; slr_def_range; slr_typ; slr_doc; slr_def;_} -> slr_name
let (__proj__Mksl_reponse__item__slr_def_range :
  sl_reponse -> FStar_Range.range FStar_Pervasives_Native.option) =
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
let with_printed_effect_args :
  'Auu____194 . (unit -> 'Auu____194) -> 'Auu____194 =
  fun k ->
    FStar_Options.with_saved_options
      (fun uu____207 ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv ->
    fun t ->
      with_printed_effect_args
        (fun uu____225 -> FStar_TypeChecker_Normalize.term_to_string tcenv t)
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    with_printed_effect_args
      (fun uu____235 -> FStar_Syntax_Print.sigelt_to_string se)
let (run_symbol_lookup :
  FStar_JsonHelper.repl_state ->
    Prims.string ->
      loc FStar_Pervasives_Native.option ->
        Prims.string Prims.list -> sl_reponse FStar_Pervasives_Native.option)
  =
  fun st ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let tcenv = st.FStar_JsonHelper.repl_env in
          let info_of_lid_str lid_str =
            let lid =
              let uu____294 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____294 in
            let lid1 =
              let uu____300 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____300 in
            let uu____305 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____305
              (FStar_Util.map_option
                 (fun uu____362 ->
                    match uu____362 with
                    | ((uu____382, typ), r) ->
                        ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid =
            let uu____404 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid in
            FStar_All.pipe_right uu____404
              (FStar_Util.map_option FStar_Pervasives_Native.fst) in
          let def_of_lid lid =
            let uu____470 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____470
              (fun uu___0_515 ->
                 match uu___0_515 with
                 | (FStar_Util.Inr (se, uu____538), uu____539) ->
                     let uu____568 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____568
                 | uu____571 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____620 ->
                 match uu____620 with
                 | (file, row, col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____670 -> info_at_pos_opt
            | FStar_Pervasives_Native.None ->
                if symbol = ""
                then FStar_Pervasives_Native.None
                else info_of_lid_str symbol in
          match info_opt with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
              let name =
                match name_or_lid with
                | FStar_Util.Inl name -> name
                | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
              let typ_str =
                if FStar_List.mem "type" requested_info
                then
                  let uu____788 = term_to_string tcenv typ in
                  FStar_Pervasives_Native.Some uu____788
                else FStar_Pervasives_Native.None in
              let doc_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "documentation" requested_info ->
                    docs_of_lid lid
                | uu____805 -> FStar_Pervasives_Native.None in
              let def_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "definition" requested_info ->
                    def_of_lid lid
                | uu____823 -> FStar_Pervasives_Native.None in
              let def_range1 =
                if FStar_List.mem "defined-at" requested_info
                then FStar_Pervasives_Native.Some rng
                else FStar_Pervasives_Native.None in
              FStar_Pervasives_Native.Some
                {
                  slr_name = name;
                  slr_def_range = def_range1;
                  slr_typ = typ_str;
                  slr_doc = doc_str;
                  slr_def = def_str
                }
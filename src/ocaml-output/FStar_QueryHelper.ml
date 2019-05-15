open Prims
type loc = (Prims.string * Prims.int * Prims.int)
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
let (symlookup :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      loc FStar_Pervasives_Native.option ->
        Prims.string Prims.list -> sl_reponse FStar_Pervasives_Native.option)
  =
  fun tcenv ->
    fun symbol ->
      fun pos_opt ->
        fun requested_info ->
          let info_of_lid_str lid_str =
            let lid =
              let uu____293 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____293 in
            let lid1 =
              let uu____299 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____299 in
            let uu____304 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____304
              (FStar_Util.map_option
                 (fun uu____361 ->
                    match uu____361 with
                    | ((uu____381, typ), r) ->
                        ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid =
            let uu____403 =
              FStar_Syntax_DsEnv.try_lookup_doc
                tcenv.FStar_TypeChecker_Env.dsenv lid in
            FStar_All.pipe_right uu____403
              (FStar_Util.map_option FStar_Pervasives_Native.fst) in
          let def_of_lid lid =
            let uu____469 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____469
              (fun uu___0_514 ->
                 match uu___0_514 with
                 | (FStar_Util.Inr (se, uu____537), uu____538) ->
                     let uu____567 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____567
                 | uu____570 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____620 ->
                 match uu____620 with
                 | (file, row, col) ->
                     let uu____643 =
                       FStar_Util.substring_from file (Prims.parse_int "7") in
                     FStar_TypeChecker_Err.info_at_pos tcenv uu____643 row
                       col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____673 -> info_at_pos_opt
            | FStar_Pervasives_Native.None ->
                if symbol = ""
                then FStar_Pervasives_Native.None
                else info_of_lid_str symbol in
          match info_opt with
          | FStar_Pervasives_Native.None ->
              (FStar_Util.print_error "[E] Blank info_opt\n";
               FStar_Pervasives_Native.None)
          | FStar_Pervasives_Native.Some (name_or_lid, typ, rng) ->
              let name =
                match name_or_lid with
                | FStar_Util.Inl name -> name
                | FStar_Util.Inr lid -> FStar_Ident.string_of_lid lid in
              let typ_str =
                if FStar_List.mem "type" requested_info
                then
                  let uu____793 = term_to_string tcenv typ in
                  FStar_Pervasives_Native.Some uu____793
                else FStar_Pervasives_Native.None in
              let doc_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "documentation" requested_info ->
                    docs_of_lid lid
                | uu____810 -> FStar_Pervasives_Native.None in
              let def_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "definition" requested_info ->
                    def_of_lid lid
                | uu____828 -> FStar_Pervasives_Native.None in
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
let (deflookup :
  FStar_TypeChecker_Env.env ->
    FStar_JsonHelper.txdoc_pos ->
      (FStar_Util.json, FStar_Util.json) FStar_Util.either)
  =
  fun st ->
    fun pos ->
      let uu____864 =
        symlookup st ""
          (FStar_Pervasives_Native.Some
             ((pos.FStar_JsonHelper.uri), (pos.FStar_JsonHelper.line),
               (pos.FStar_JsonHelper.col))) ["definition"] in
      match uu____864 with
      | FStar_Pervasives_Native.Some
          { slr_name = uu____878;
            slr_def_range = FStar_Pervasives_Native.Some r;
            slr_typ = uu____880; slr_doc = uu____881; slr_def = uu____882;_}
          ->
          let uu____893 =
            let uu____894 =
              let uu____902 =
                let uu____908 = FStar_JsonHelper.js_range r in
                ("result", uu____908) in
              [uu____902] in
            FStar_Util.JsonAssoc uu____894 in
          FStar_Util.Inl uu____893
      | FStar_Pervasives_Native.None ->
          let uu____921 =
            FStar_JsonHelper.js_resperr FStar_JsonHelper.InternalError
              "symlookup failed" in
          FStar_Util.Inr uu____921
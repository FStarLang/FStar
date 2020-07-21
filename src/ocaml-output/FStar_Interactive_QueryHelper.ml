open Prims
type position = (Prims.string * Prims.int * Prims.int)
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
  'uuuuuu154 . (unit -> 'uuuuuu154) -> 'uuuuuu154 =
  fun k ->
    FStar_Options.with_saved_options
      (fun uu____167 ->
         FStar_Options.set_option "print_effect_args"
           (FStar_Options.Bool true);
         k ())
let (term_to_string :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  fun tcenv ->
    fun t ->
      with_printed_effect_args
        (fun uu____180 -> FStar_TypeChecker_Normalize.term_to_string tcenv t)
let (sigelt_to_string : FStar_Syntax_Syntax.sigelt -> Prims.string) =
  fun se ->
    with_printed_effect_args
      (fun uu____187 -> FStar_Syntax_Print.sigelt_to_string se)
let (symlookup :
  FStar_TypeChecker_Env.env ->
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
              let uu____237 =
                FStar_List.map FStar_Ident.id_of_text
                  (FStar_Util.split lid_str ".") in
              FStar_Ident.lid_of_ids uu____237 in
            let lid1 =
              let uu____239 =
                FStar_Syntax_DsEnv.resolve_to_fully_qualified_name
                  tcenv.FStar_TypeChecker_Env.dsenv lid in
              FStar_All.pipe_left (FStar_Util.dflt lid) uu____239 in
            let uu____244 = FStar_TypeChecker_Env.try_lookup_lid tcenv lid1 in
            FStar_All.pipe_right uu____244
              (FStar_Util.map_option
                 (fun uu____299 ->
                    match uu____299 with
                    | ((uu____318, typ), r) ->
                        ((FStar_Util.Inr lid1), typ, r))) in
          let docs_of_lid lid = FStar_Pervasives_Native.None in
          let def_of_lid lid =
            let uu____345 = FStar_TypeChecker_Env.lookup_qname tcenv lid in
            FStar_Util.bind_opt uu____345
              (fun uu___0_389 ->
                 match uu___0_389 with
                 | (FStar_Util.Inr (se, uu____411), uu____412) ->
                     let uu____441 = sigelt_to_string se in
                     FStar_Pervasives_Native.Some uu____441
                 | uu____442 -> FStar_Pervasives_Native.None) in
          let info_at_pos_opt =
            FStar_Util.bind_opt pos_opt
              (fun uu____488 ->
                 match uu____488 with
                 | (file, row, col) ->
                     FStar_TypeChecker_Err.info_at_pos tcenv file row col) in
          let info_opt =
            match info_at_pos_opt with
            | FStar_Pervasives_Native.Some uu____529 -> info_at_pos_opt
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
                  let uu____624 = term_to_string tcenv typ in
                  FStar_Pervasives_Native.Some uu____624
                else FStar_Pervasives_Native.None in
              let doc_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "documentation" requested_info ->
                    docs_of_lid lid
                | uu____632 -> FStar_Pervasives_Native.None in
              let def_str =
                match name_or_lid with
                | FStar_Util.Inr lid when
                    FStar_List.mem "definition" requested_info ->
                    def_of_lid lid
                | uu____643 -> FStar_Pervasives_Native.None in
              let def_range =
                if FStar_List.mem "defined-at" requested_info
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
  'uuuuuu658 .
    ('uuuuuu658 * FStar_Interactive_CompletionTable.mod_symbol) ->
      ('uuuuuu658 * FStar_Interactive_CompletionTable.mod_symbol)
        FStar_Pervasives_Native.option
  =
  fun uu___1_673 ->
    match uu___1_673 with
    | (uu____678, FStar_Interactive_CompletionTable.Namespace uu____679) ->
        FStar_Pervasives_Native.None
    | (uu____684, FStar_Interactive_CompletionTable.Module
       { FStar_Interactive_CompletionTable.mod_name = uu____685;
         FStar_Interactive_CompletionTable.mod_path = uu____686;
         FStar_Interactive_CompletionTable.mod_loaded = true;_})
        -> FStar_Pervasives_Native.None
    | (pth, FStar_Interactive_CompletionTable.Module md) ->
        let uu____693 =
          let uu____698 =
            let uu____699 =
              let uu___99_700 = md in
              let uu____701 =
                let uu____702 = FStar_Interactive_CompletionTable.mod_name md in
                Prims.op_Hat uu____702 "." in
              {
                FStar_Interactive_CompletionTable.mod_name = uu____701;
                FStar_Interactive_CompletionTable.mod_path =
                  (uu___99_700.FStar_Interactive_CompletionTable.mod_path);
                FStar_Interactive_CompletionTable.mod_loaded =
                  (uu___99_700.FStar_Interactive_CompletionTable.mod_loaded)
              } in
            FStar_Interactive_CompletionTable.Module uu____699 in
          (pth, uu____698) in
        FStar_Pervasives_Native.Some uu____693
let (ck_completion :
  FStar_Interactive_JsonHelper.repl_state ->
    Prims.string ->
      FStar_Interactive_CompletionTable.completion_result Prims.list)
  =
  fun st ->
    fun search_term ->
      let needle = FStar_Util.split search_term "." in
      let mods_and_nss =
        FStar_Interactive_CompletionTable.autocomplete_mod_or_ns
          st.FStar_Interactive_JsonHelper.repl_names needle mod_filter in
      let lids =
        FStar_Interactive_CompletionTable.autocomplete_lid
          st.FStar_Interactive_JsonHelper.repl_names needle in
      FStar_List.append lids mods_and_nss
let (deflookup :
  FStar_TypeChecker_Env.env ->
    FStar_Interactive_JsonHelper.txdoc_pos ->
      FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun env ->
    fun pos ->
      let uu____744 =
        let uu____747 =
          let uu____750 = FStar_Interactive_JsonHelper.pos_munge pos in
          FStar_Pervasives_Native.Some uu____750 in
        symlookup env "" uu____747 ["defined-at"] in
      match uu____744 with
      | FStar_Pervasives_Native.Some
          { slr_name = uu____753;
            slr_def_range = FStar_Pervasives_Native.Some r;
            slr_typ = uu____755; slr_doc = uu____756; slr_def = uu____757;_}
          ->
          let uu____764 = FStar_Interactive_JsonHelper.js_loclink r in
          FStar_Interactive_JsonHelper.resultResponse uu____764
      | uu____765 -> FStar_Interactive_JsonHelper.nullResponse
let (hoverlookup :
  FStar_TypeChecker_Env.env ->
    FStar_Interactive_JsonHelper.txdoc_pos ->
      FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun env ->
    fun pos ->
      let uu____782 =
        let uu____785 =
          let uu____788 = FStar_Interactive_JsonHelper.pos_munge pos in
          FStar_Pervasives_Native.Some uu____788 in
        symlookup env "" uu____785 ["type"; "definition"] in
      match uu____782 with
      | FStar_Pervasives_Native.Some
          { slr_name = n; slr_def_range = uu____792;
            slr_typ = FStar_Pervasives_Native.Some t; slr_doc = uu____794;
            slr_def = FStar_Pervasives_Native.Some d;_}
          ->
          let hovertxt =
            FStar_Util.format2 "```fstar\n%s\n````\n---\n```fstar\n%s\n```" t
              d in
          FStar_Interactive_JsonHelper.resultResponse
            (FStar_Util.JsonAssoc
               [("contents",
                  (FStar_Util.JsonAssoc
                     [("kind", (FStar_Util.JsonStr "markdown"));
                     ("value", (FStar_Util.JsonStr hovertxt))]))])
      | uu____821 -> FStar_Interactive_JsonHelper.nullResponse
let (complookup :
  FStar_Interactive_JsonHelper.repl_state ->
    FStar_Interactive_JsonHelper.txdoc_pos ->
      FStar_Interactive_JsonHelper.assoct FStar_Pervasives_Native.option)
  =
  fun st ->
    fun pos ->
      let uu____838 = FStar_Interactive_JsonHelper.pos_munge pos in
      match uu____838 with
      | (file, row, current_col) ->
          let uu____850 = FStar_Parser_ParseIt.read_vfs_entry file in
          (match uu____850 with
           | FStar_Pervasives_Native.Some (uu____859, text) ->
               let rec find_col l =
                 match l with
                 | [] -> Prims.int_zero
                 | h::t ->
                     if (h = 32) && ((FStar_List.length t) < current_col)
                     then (FStar_List.length t) + Prims.int_one
                     else find_col t in
               let str =
                 FStar_List.nth (FStar_Util.splitlines text)
                   (row - Prims.int_one) in
               let explode s =
                 let rec exp i l =
                   if i < Prims.int_zero
                   then l
                   else
                     (let uu____909 =
                        let uu____912 = FStar_String.get s i in uu____912 ::
                          l in
                      exp (i - Prims.int_one) uu____909) in
                 exp ((FStar_String.length s) - Prims.int_one) [] in
               let begin_col =
                 let uu____914 =
                   let uu____917 = explode str in FStar_List.rev uu____917 in
                 find_col uu____914 in
               let term =
                 FStar_Util.substring str begin_col (current_col - begin_col) in
               let items = ck_completion st term in
               let l =
                 FStar_List.map
                   (fun r ->
                      FStar_Util.JsonAssoc
                        [("label",
                           (FStar_Util.JsonStr
                              (r.FStar_Interactive_CompletionTable.completion_candidate)))])
                   items in
               FStar_Interactive_JsonHelper.resultResponse
                 (FStar_Util.JsonList l))
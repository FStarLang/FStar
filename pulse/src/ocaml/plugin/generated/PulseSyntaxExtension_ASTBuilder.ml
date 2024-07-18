open Prims
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (pulse_checker_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
let (pulse_checker_after_parse_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse_after_parse"] r_
let (tm :
  FStar_Parser_AST.term' ->
    FStar_Compiler_Range_Type.range -> FStar_Parser_AST.term)
  =
  fun t ->
    fun r ->
      {
        FStar_Parser_AST.tm = t;
        FStar_Parser_AST.range = r;
        FStar_Parser_AST.level = FStar_Parser_AST.Un
      }
let (parse_decl_name :
  Prims.string ->
    FStar_Compiler_Range_Type.range ->
      (FStar_Parser_AST_Util.error_message, FStar_Ident.ident)
        FStar_Pervasives.either)
  =
  fun contents ->
    fun r ->
      let uu___ = PulseSyntaxExtension_Parser.parse_peek_id contents r in
      match uu___ with
      | FStar_Pervasives.Inl s ->
          let uu___1 = FStar_Ident.id_of_text s in
          FStar_Pervasives.Inr uu___1
      | FStar_Pervasives.Inr (msg, r1) ->
          FStar_Pervasives.Inl
            {
              FStar_Parser_AST_Util.message = msg;
              FStar_Parser_AST_Util.range = r1
            }
let (i :
  Prims.int -> FStar_Compiler_Range_Type.range -> FStar_Parser_AST.term) =
  fun s ->
    fun r ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Compiler_Util.string_of_int s in
            (uu___3, FStar_Pervasives_Native.None) in
          FStar_Const.Const_int uu___2 in
        FStar_Parser_AST.Const uu___1 in
      tm uu___ r
let (str :
  Prims.string -> FStar_Compiler_Range_Type.range -> FStar_Parser_AST.term) =
  fun s ->
    fun r -> tm (FStar_Parser_AST.Const (FStar_Const.Const_string (s, r))) r
let (lid_as_term :
  FStar_Ident.lident ->
    FStar_Compiler_Range_Type.range -> FStar_Parser_AST.term)
  =
  fun ns -> fun r -> let uu___ = FStar_Ident.string_of_lid ns in str uu___ r
let (encode_open_namespaces_and_abbreviations :
  FStar_Parser_AST_Util.open_namespaces_and_abbreviations ->
    FStar_Compiler_Range_Type.range ->
      (FStar_Parser_AST.term * FStar_Parser_AST.term))
  =
  fun ctx ->
    fun r ->
      let tm1 t = tm t r in
      let str1 s = str s r in
      let lid_as_term1 ns = lid_as_term ns r in
      let namespaces =
        let uu___ =
          FStar_Compiler_List.map lid_as_term1
            ctx.FStar_Parser_AST_Util.open_namespaces in
        FStar_Parser_AST.mkConsList r uu___ in
      let abbrevs =
        let uu___ =
          FStar_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (a, m) ->
                   let a1 =
                     let uu___2 = FStar_Ident.string_of_id a in str1 uu___2 in
                   let m1 = lid_as_term1 m in
                   FStar_Parser_AST.mkTuple [a1; m1] r)
            ctx.FStar_Parser_AST_Util.module_abbreviations in
        FStar_Parser_AST.mkConsList r uu___ in
      (namespaces, abbrevs)
let (encode_range :
  FStar_Compiler_Range_Type.range ->
    (FStar_Parser_AST.term * FStar_Parser_AST.term * FStar_Parser_AST.term))
  =
  fun r ->
    let line =
      let uu___ = FStar_Compiler_Range_Ops.start_of_range r in
      FStar_Compiler_Range_Ops.line_of_pos uu___ in
    let col =
      let uu___ = FStar_Compiler_Range_Ops.start_of_range r in
      FStar_Compiler_Range_Ops.col_of_pos uu___ in
    let uu___ =
      let uu___1 = FStar_Compiler_Range_Ops.file_of_range r in str uu___1 r in
    let uu___1 = i line r in let uu___2 = i col r in (uu___, uu___1, uu___2)
let (parse_decl :
  FStar_Parser_AST_Util.open_namespaces_and_abbreviations ->
    Prims.string ->
      FStar_Compiler_Range_Type.range ->
        (FStar_Parser_AST_Util.error_message, FStar_Parser_AST.decl)
          FStar_Pervasives.either)
  =
  fun ctx ->
    fun contents ->
      fun r ->
        let tm1 t = tm t r in
        let str1 s = str s r in
        let i1 s =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Compiler_Util.string_of_int s in
                (uu___3, FStar_Pervasives_Native.None) in
              FStar_Const.Const_int uu___2 in
            FStar_Parser_AST.Const uu___1 in
          tm1 uu___ in
        let uu___ = PulseSyntaxExtension_Parser.parse_peek_id contents r in
        match uu___ with
        | FStar_Pervasives.Inr (err, r1) ->
            FStar_Pervasives.Inl
              {
                FStar_Parser_AST_Util.message = err;
                FStar_Parser_AST_Util.range = r1
              }
        | FStar_Pervasives.Inl id ->
            let splicer =
              let head = tm1 (FStar_Parser_AST.Var pulse_checker_tac) in
              let lid_as_term1 ns = lid_as_term ns r in
              let uu___1 = encode_open_namespaces_and_abbreviations ctx r in
              match uu___1 with
              | (namespaces, abbrevs) ->
                  let uu___2 = encode_range r in
                  (match uu___2 with
                   | (file_name, line, col) ->
                       FStar_Parser_AST.mkApp head
                         [(namespaces, FStar_Parser_AST.Nothing);
                         (abbrevs, FStar_Parser_AST.Nothing);
                         ((str1 contents), FStar_Parser_AST.Nothing);
                         (file_name, FStar_Parser_AST.Nothing);
                         (line, FStar_Parser_AST.Nothing);
                         (col, FStar_Parser_AST.Nothing);
                         ((str1 id), FStar_Parser_AST.Nothing)] r) in
            let d =
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStar_Ident.id_of_text id in [uu___3] in
                (true, uu___2, splicer) in
              FStar_Parser_AST.Splice uu___1 in
            let d1 =
              {
                FStar_Parser_AST.d = d;
                FStar_Parser_AST.drange = r;
                FStar_Parser_AST.quals = [FStar_Parser_AST.Irreducible];
                FStar_Parser_AST.attrs = [str1 "uninterpreted_by_smt"];
                FStar_Parser_AST.interleaved = false
              } in
            FStar_Pervasives.Inr d1
let maybe_report_error :
  'uuuuu .
    ('uuuuu * FStar_Errors_Msg.error_message *
      FStar_Compiler_Range_Type.range) FStar_Pervasives_Native.option ->
      FStar_Parser_AST_Util.error_message FStar_Pervasives_Native.option
  =
  fun first_error ->
    match first_error with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some (raw_error, msg, r) ->
        let should_fail_on_error =
          let file = FStar_Compiler_Range_Ops.file_of_range r in
          let uu___ = FStar_Parser_Dep.maybe_module_name_of_file file in
          match uu___ with
          | FStar_Pervasives_Native.None -> false
          | FStar_Pervasives_Native.Some uu___1 ->
              let uu___2 = FStar_Options.ide_filename () in
              (match uu___2 with
               | FStar_Pervasives_Native.None -> true
               | FStar_Pervasives_Native.Some fn ->
                   ((let uu___4 = FStar_Compiler_Util.basename file in
                     let uu___5 = FStar_Compiler_Util.basename fn in
                     FStar_Compiler_Util.print2
                       "Hard error?: filename=%s; ide filename=%s\n" uu___4
                       uu___5);
                    (let uu___4 = FStar_Compiler_Util.basename fn in
                     let uu___5 = FStar_Compiler_Util.basename file in
                     uu___4 <> uu___5))) in
        if should_fail_on_error
        then
          let uu___ =
            let uu___1 = FStar_Errors_Msg.rendermsg msg in
            {
              FStar_Parser_AST_Util.message = uu___1;
              FStar_Parser_AST_Util.range = r
            } in
          FStar_Pervasives_Native.Some uu___
        else
          (let msg1 =
             FStar_Errors_Msg.text
               "Tolerating syntax error when opening file interactively" in
           let issue =
             {
               FStar_Errors.issue_msg = [msg1];
               FStar_Errors.issue_level = FStar_Errors.EWarning;
               FStar_Errors.issue_range = (FStar_Pervasives_Native.Some r);
               FStar_Errors.issue_number = FStar_Pervasives_Native.None;
               FStar_Errors.issue_ctx = []
             } in
           FStar_Errors.add_issues [issue]; FStar_Pervasives_Native.None)
let (parse_extension_lang :
  Prims.string ->
    FStar_Compiler_Range_Type.range ->
      (FStar_Parser_AST_Util.error_message, FStar_Parser_AST.decl Prims.list)
        FStar_Pervasives.either)
  =
  fun contents ->
    fun r ->
      let uu___ = PulseSyntaxExtension_Parser.parse_lang contents r in
      match uu___ with
      | FStar_Pervasives.Inr (FStar_Pervasives_Native.None) ->
          FStar_Pervasives.Inl
            {
              FStar_Parser_AST_Util.message = "#lang-pulse: Parsing failed";
              FStar_Parser_AST_Util.range = r
            }
      | FStar_Pervasives.Inr (FStar_Pervasives_Native.Some (err, r1)) ->
          FStar_Pervasives.Inl
            {
              FStar_Parser_AST_Util.message = err;
              FStar_Parser_AST_Util.range = r1
            }
      | FStar_Pervasives.Inl (decls, first_error) ->
          let uu___1 = maybe_report_error first_error in
          (match uu___1 with
           | FStar_Pervasives_Native.Some err -> FStar_Pervasives.Inl err
           | uu___2 ->
               let id_and_range_of_decl d =
                 match d with
                 | PulseSyntaxExtension_Sugar.FnDefn
                     { PulseSyntaxExtension_Sugar.id2 = id;
                       PulseSyntaxExtension_Sugar.is_rec = uu___3;
                       PulseSyntaxExtension_Sugar.binders2 = uu___4;
                       PulseSyntaxExtension_Sugar.ascription1 = uu___5;
                       PulseSyntaxExtension_Sugar.measure = uu___6;
                       PulseSyntaxExtension_Sugar.body3 = uu___7;
                       PulseSyntaxExtension_Sugar.range3 = range;_}
                     -> (id, range)
                 | PulseSyntaxExtension_Sugar.FnDecl
                     { PulseSyntaxExtension_Sugar.id3 = id;
                       PulseSyntaxExtension_Sugar.binders3 = uu___3;
                       PulseSyntaxExtension_Sugar.ascription2 = uu___4;
                       PulseSyntaxExtension_Sugar.range4 = range;_}
                     -> (id, range) in
               let splice_decl ctx d =
                 let uu___3 = id_and_range_of_decl d in
                 match uu___3 with
                 | (id, r1) ->
                     let id_txt = FStar_Ident.string_of_id id in
                     let decl_as_term =
                       let uu___4 =
                         let uu___5 =
                           FStar_Syntax_Util.mk_lazy d
                             FStar_Syntax_Syntax.t_bool
                             (FStar_Syntax_Syntax.Lazy_extension
                                "pulse_sugar_decl")
                             (FStar_Pervasives_Native.Some r1) in
                         FStar_Parser_AST.DesugaredBlob uu___5 in
                       tm uu___4 r1 in
                     let splicer =
                       let head =
                         tm
                           (FStar_Parser_AST.Var
                              pulse_checker_after_parse_tac) r1 in
                       let uu___4 =
                         encode_open_namespaces_and_abbreviations ctx r1 in
                       match uu___4 with
                       | (namespaces, abbrevs) ->
                           FStar_Parser_AST.mkApp head
                             [(namespaces, FStar_Parser_AST.Nothing);
                             (abbrevs, FStar_Parser_AST.Nothing);
                             (decl_as_term, FStar_Parser_AST.Nothing);
                             ((str id_txt r1), FStar_Parser_AST.Nothing)] r1 in
                     let d1 = FStar_Parser_AST.Splice (true, [id], splicer) in
                     let d2 =
                       {
                         FStar_Parser_AST.d = d1;
                         FStar_Parser_AST.drange = r1;
                         FStar_Parser_AST.quals =
                           [FStar_Parser_AST.Irreducible];
                         FStar_Parser_AST.attrs =
                           [str "uninterpreted_by_smt" r1];
                         FStar_Parser_AST.interleaved = false
                       } in
                     d2 in
               let maybe_extend_ctx ctx d =
                 match d.FStar_Parser_AST.d with
                 | FStar_Parser_AST.Open lid ->
                     {
                       FStar_Parser_AST_Util.open_namespaces = (lid ::
                         (ctx.FStar_Parser_AST_Util.open_namespaces));
                       FStar_Parser_AST_Util.module_abbreviations =
                         (ctx.FStar_Parser_AST_Util.module_abbreviations)
                     }
                 | FStar_Parser_AST.ModuleAbbrev (i1, l) ->
                     {
                       FStar_Parser_AST_Util.open_namespaces =
                         (ctx.FStar_Parser_AST_Util.open_namespaces);
                       FStar_Parser_AST_Util.module_abbreviations = (
                         (i1, l) ::
                         (ctx.FStar_Parser_AST_Util.module_abbreviations))
                     }
                 | uu___3 -> ctx in
               let default_opens =
                 [FStar_Parser_Const.pervasives_lid;
                 FStar_Parser_Const.prims_lid;
                 FStar_Parser_Const.fstar_ns_lid] in
               let uu___3 =
                 FStar_Compiler_List.fold_left
                   (fun uu___4 ->
                      fun d ->
                        match uu___4 with
                        | (ctx, out) ->
                            (match d with
                             | FStar_Pervasives.Inr d1 ->
                                 ((maybe_extend_ctx ctx d1), (d1 :: out))
                             | FStar_Pervasives.Inl d1 ->
                                 let uu___5 =
                                   let uu___6 = splice_decl ctx d1 in uu___6
                                     :: out in
                                 (ctx, uu___5)))
                   ({
                      FStar_Parser_AST_Util.open_namespaces = default_opens;
                      FStar_Parser_AST_Util.module_abbreviations = []
                    }, []) decls in
               (match uu___3 with
                | (uu___4, decls1) ->
                    FStar_Pervasives.Inr (FStar_Compiler_List.rev decls1)))
let (uu___148 : unit) =
  FStar_Parser_AST_Util.register_extension_parser "pulse"
    {
      FStar_Parser_AST_Util.parse_decl_name = parse_decl_name;
      FStar_Parser_AST_Util.parse_decl = parse_decl
    }
let (uu___149 : unit) =
  FStar_Parser_AST_Util.register_extension_lang_parser "pulse"
    { FStar_Parser_AST_Util.parse_decls = parse_extension_lang }
type sugar_decl = PulseSyntaxExtension_Sugar.decl
let (desugar_pulse :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      (Prims.string * Prims.string) Prims.list ->
        sugar_decl ->
          (PulseSyntaxExtension_SyntaxWrapper.decl,
            (Prims.string * FStar_Compiler_Range_Type.range)
              FStar_Pervasives_Native.option)
            FStar_Pervasives.either)
  =
  fun env ->
    fun namespaces ->
      fun module_abbrevs ->
        fun sugar ->
          let namespaces1 =
            FStar_Compiler_List.map FStar_Ident.path_of_text namespaces in
          let module_abbrevs1 =
            FStar_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (x, l) ->
                     let uu___1 = FStar_Ident.path_of_text l in (x, uu___1))
              module_abbrevs in
          let env1 =
            PulseSyntaxExtension_Desugar.initialize_env env namespaces1
              module_abbrevs1 in
          let uu___ =
            let uu___1 = PulseSyntaxExtension_Desugar.desugar_decl env1 sugar in
            uu___1 Prims.int_zero in
          FStar_Pervasives_Native.fst uu___
let (parse_pulse :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      (Prims.string * Prims.string) Prims.list ->
        Prims.string ->
          Prims.string ->
            Prims.int ->
              Prims.int ->
                (PulseSyntaxExtension_SyntaxWrapper.decl,
                  (Prims.string * FStar_Compiler_Range_Type.range)
                    FStar_Pervasives_Native.option)
                  FStar_Pervasives.either)
  =
  fun env ->
    fun namespaces ->
      fun module_abbrevs ->
        fun content ->
          fun file_name ->
            fun line ->
              fun col ->
                let range =
                  let p = FStar_Compiler_Range_Type.mk_pos line col in
                  FStar_Compiler_Range_Type.mk_range file_name p p in
                let uu___ =
                  PulseSyntaxExtension_Parser.parse_decl content range in
                match uu___ with
                | FStar_Pervasives.Inl d ->
                    desugar_pulse env namespaces module_abbrevs d
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
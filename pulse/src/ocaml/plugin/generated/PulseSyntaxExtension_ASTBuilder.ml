open Prims
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (pulse_checker_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
let (pulse_checker_after_desugar_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse_after_desugar"] r_
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
  'uuuuu 'uuuuu1 .
    ('uuuuu * FStar_Errors_Msg.error_message *
      FStar_Compiler_Range_Type.range) FStar_Pervasives_Native.option ->
      ('uuuuu1, FStar_Parser_AST.decl) FStar_Pervasives.either Prims.list ->
        (FStar_Parser_AST_Util.error_message,
          ('uuuuu1, FStar_Parser_AST.decl) FStar_Pervasives.either Prims.list)
          FStar_Pervasives.either
  =
  fun first_error ->
    fun decls ->
      match first_error with
      | FStar_Pervasives_Native.None -> FStar_Pervasives.Inr decls
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
                     let uu___3 = FStar_Compiler_Util.basename fn in
                     let uu___4 = FStar_Compiler_Util.basename file in
                     uu___3 <> uu___4) in
          if should_fail_on_error
          then
            let uu___ =
              let uu___1 = FStar_Errors_Msg.rendermsg msg in
              {
                FStar_Parser_AST_Util.message = uu___1;
                FStar_Parser_AST_Util.range = r
              } in
            FStar_Pervasives.Inl uu___
          else
            (let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Parser_AST.mk_decl FStar_Parser_AST.Unparseable r
                       [] in
                   FStar_Pervasives.Inr uu___4 in
                 [uu___3] in
               FStar_List_Tot_Base.op_At decls uu___2 in
             FStar_Pervasives.Inr uu___1)
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
          let uu___1 = maybe_report_error first_error decls in
          (match uu___1 with
           | FStar_Pervasives.Inl err -> FStar_Pervasives.Inl err
           | FStar_Pervasives.Inr decls1 ->
               let id_and_range_of_decl d =
                 match d with
                 | PulseSyntaxExtension_Sugar.FnDefn
                     { PulseSyntaxExtension_Sugar.id2 = id;
                       PulseSyntaxExtension_Sugar.is_rec = uu___2;
                       PulseSyntaxExtension_Sugar.binders2 = uu___3;
                       PulseSyntaxExtension_Sugar.ascription1 = uu___4;
                       PulseSyntaxExtension_Sugar.measure = uu___5;
                       PulseSyntaxExtension_Sugar.body3 = uu___6;
                       PulseSyntaxExtension_Sugar.decorations = uu___7;
                       PulseSyntaxExtension_Sugar.range3 = range;_}
                     -> (id, range)
                 | PulseSyntaxExtension_Sugar.FnDecl
                     { PulseSyntaxExtension_Sugar.id3 = id;
                       PulseSyntaxExtension_Sugar.binders3 = uu___2;
                       PulseSyntaxExtension_Sugar.ascription2 = uu___3;
                       PulseSyntaxExtension_Sugar.decorations1 = uu___4;
                       PulseSyntaxExtension_Sugar.range4 = range;_}
                     -> (id, range) in
               let splice_decl d =
                 let uu___2 = id_and_range_of_decl d in
                 match uu___2 with
                 | (id, r1) ->
                     let id_txt = FStar_Ident.string_of_id id in
                     let decors =
                       match d with
                       | PulseSyntaxExtension_Sugar.FnDefn
                           { PulseSyntaxExtension_Sugar.id2 = uu___3;
                             PulseSyntaxExtension_Sugar.is_rec = uu___4;
                             PulseSyntaxExtension_Sugar.binders2 = uu___5;
                             PulseSyntaxExtension_Sugar.ascription1 = uu___6;
                             PulseSyntaxExtension_Sugar.measure = uu___7;
                             PulseSyntaxExtension_Sugar.body3 = uu___8;
                             PulseSyntaxExtension_Sugar.decorations =
                               decorations;
                             PulseSyntaxExtension_Sugar.range3 = uu___9;_}
                           -> decorations
                       | PulseSyntaxExtension_Sugar.FnDecl
                           { PulseSyntaxExtension_Sugar.id3 = uu___3;
                             PulseSyntaxExtension_Sugar.binders3 = uu___4;
                             PulseSyntaxExtension_Sugar.ascription2 = uu___5;
                             PulseSyntaxExtension_Sugar.decorations1 =
                               decorations;
                             PulseSyntaxExtension_Sugar.range4 = uu___6;_}
                           -> decorations in
                     let d1 =
                       let uu___3 =
                         let uu___4 = FStar_Compiler_Dyn.mkdyn d in
                         {
                           FStar_Parser_AST.lang_name = "pulse";
                           FStar_Parser_AST.blob = uu___4;
                           FStar_Parser_AST.idents = [id];
                           FStar_Parser_AST.to_string = (fun d2 -> "<TBD>");
                           FStar_Parser_AST.eq =
                             (fun d11 ->
                                fun d2 ->
                                  let uu___5 = FStar_Compiler_Dyn.undyn d11 in
                                  let uu___6 = FStar_Compiler_Dyn.undyn d2 in
                                  PulseSyntaxExtension_Sugar.eq_decl uu___5
                                    uu___6);
                           FStar_Parser_AST.dep_scan =
                             (fun cbs ->
                                fun d2 ->
                                  let uu___5 = FStar_Compiler_Dyn.undyn d2 in
                                  PulseSyntaxExtension_Sugar.scan_decl cbs
                                    uu___5)
                         } in
                       FStar_Parser_AST.DeclToBeDesugared uu___3 in
                     let d2 =
                       let uu___3 =
                         FStar_Compiler_List.partition
                           FStar_Parser_AST.uu___is_DeclAttributes decors in
                       match uu___3 with
                       | (attrs, quals) ->
                           let attrs1 =
                             match attrs with
                             | [] ->
                                 [FStar_Parser_AST.DeclAttributes
                                    [str "uninterpreted_by_smt" r1]]
                             | (FStar_Parser_AST.DeclAttributes attrs2)::tl
                                 ->
                                 (FStar_Parser_AST.DeclAttributes
                                    ((str "uninterpreted_by_smt" r1) ::
                                    attrs2))
                                 :: tl in
                           let decors1 =
                             FStar_List_Tot_Base.op_At
                               ((FStar_Parser_AST.Qualifier
                                   FStar_Parser_AST.Irreducible) :: quals)
                               attrs1 in
                           FStar_Parser_AST.mk_decl d1 r1 decors1 in
                     d2 in
               let uu___2 =
                 FStar_Compiler_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | FStar_Pervasives.Inl d -> splice_decl d
                      | FStar_Pervasives.Inr d -> d) decls1 in
               FStar_Pervasives.Inr uu___2)
let (uu___144 : unit) =
  FStar_Parser_AST_Util.register_extension_parser "pulse"
    {
      FStar_Parser_AST_Util.parse_decl_name = parse_decl_name;
      FStar_Parser_AST_Util.parse_decl = parse_decl
    }
let (uu___145 : unit) =
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
            let uu___ = FStar_TypeChecker_Env.current_module env in
            PulseSyntaxExtension_Desugar.reinitialize_env
              env.FStar_TypeChecker_Env.dsenv uu___ namespaces1
              module_abbrevs1 in
          let uu___ =
            let uu___1 = PulseSyntaxExtension_Desugar.desugar_decl env1 sugar in
            uu___1 Prims.int_zero in
          FStar_Pervasives_Native.fst uu___
let (desugar_pulse_decl_callback :
  FStar_Syntax_DsEnv.env ->
    FStar_Compiler_Dyn.dyn ->
      FStar_Ident.lident Prims.list ->
        FStar_Compiler_Range_Type.range ->
          FStar_Syntax_Syntax.sigelt' Prims.list)
  =
  fun env ->
    fun blob ->
      fun lids ->
        fun rng ->
          let d =
            let uu___ =
              let uu___1 = PulseSyntaxExtension_Desugar.mk_env env in
              let uu___2 = FStar_Compiler_Dyn.undyn blob in
              PulseSyntaxExtension_Desugar.desugar_decl uu___1 uu___2 in
            uu___ Prims.int_zero in
          match FStar_Pervasives_Native.fst d with
          | FStar_Pervasives.Inr (FStar_Pervasives_Native.None) ->
              FStar_Errors.raise_error
                (FStar_Errors_Codes.Fatal_SyntaxError,
                  "Failed to desugar pulse extension text") rng
          | FStar_Pervasives.Inr (FStar_Pervasives_Native.Some (msg, rng1))
              ->
              FStar_Errors.raise_error
                (FStar_Errors_Codes.Fatal_SyntaxError, msg) rng1
          | FStar_Pervasives.Inl d1 ->
              let blob1 =
                FStar_Syntax_Util.mk_lazy d1 FStar_Syntax_Syntax.t_bool
                  (FStar_Syntax_Syntax.Lazy_extension "pulse_decl")
                  (FStar_Pervasives_Native.Some rng) in
              let splicer =
                let head =
                  let uu___ =
                    FStar_Syntax_Syntax.lid_as_fv
                      pulse_checker_after_desugar_tac
                      FStar_Pervasives_Native.None in
                  FStar_Syntax_Syntax.fv_to_tm uu___ in
                FStar_Syntax_Syntax.mk_Tm_app head
                  [(blob1, FStar_Pervasives_Native.None)] rng in
              [FStar_Syntax_Syntax.Sig_splice
                 {
                   FStar_Syntax_Syntax.is_typed = true;
                   FStar_Syntax_Syntax.lids2 = lids;
                   FStar_Syntax_Syntax.tac = splicer
                 }]
let (uu___173 : unit) =
  FStar_ToSyntax_ToSyntax.register_extension_tosyntax "pulse"
    desugar_pulse_decl_callback
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
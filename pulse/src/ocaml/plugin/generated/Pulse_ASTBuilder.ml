open Prims
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (pulse_checker_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
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
let (extension_parser : FStar_Parser_AST_Util.extension_parser) =
  fun ctx ->
    fun contents ->
      fun r ->
        let tm1 t = tm t r in
        let str s =
          tm1 (FStar_Parser_AST.Const (FStar_Const.Const_string (s, r))) in
        let i s =
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = FStar_Compiler_Util.string_of_int s in
                (uu___3, FStar_Pervasives_Native.None) in
              FStar_Const.Const_int uu___2 in
            FStar_Parser_AST.Const uu___1 in
          tm1 uu___ in
        let uu___ = Pulse_Parser.parse_peek_id contents r in
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
              let lid_as_term ns =
                let uu___1 = FStar_Ident.string_of_lid ns in str uu___1 in
              let namespaces =
                let uu___1 =
                  FStar_Compiler_List.map lid_as_term
                    ctx.FStar_Parser_AST_Util.open_namespaces in
                FStar_Parser_AST.mkConsList r uu___1 in
              let abbrevs =
                let uu___1 =
                  FStar_Compiler_List.map
                    (fun uu___2 ->
                       match uu___2 with
                       | (a, m) ->
                           let a1 =
                             let uu___3 = FStar_Ident.string_of_id a in
                             str uu___3 in
                           let m1 = lid_as_term m in
                           FStar_Parser_AST.mkTuple [a1; m1] r)
                    ctx.FStar_Parser_AST_Util.module_abbreviations in
                FStar_Parser_AST.mkConsList r uu___1 in
              let uu___1 =
                let line =
                  let uu___2 = FStar_Compiler_Range_Ops.start_of_range r in
                  FStar_Compiler_Range_Ops.line_of_pos uu___2 in
                let col =
                  let uu___2 = FStar_Compiler_Range_Ops.start_of_range r in
                  FStar_Compiler_Range_Ops.col_of_pos uu___2 in
                let uu___2 = FStar_Compiler_Range_Ops.file_of_range r in
                (uu___2, line, col) in
              match uu___1 with
              | (file_name, line, col) ->
                  let uu___2 =
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = i line in
                              (uu___8, FStar_Parser_AST.Nothing) in
                            let uu___8 =
                              let uu___9 =
                                let uu___10 = i col in
                                (uu___10, FStar_Parser_AST.Nothing) in
                              [uu___9] in
                            uu___7 :: uu___8 in
                          ((str file_name), FStar_Parser_AST.Nothing) ::
                            uu___6 in
                        ((str contents), FStar_Parser_AST.Nothing) :: uu___5 in
                      (abbrevs, FStar_Parser_AST.Nothing) :: uu___4 in
                    (namespaces, FStar_Parser_AST.Nothing) :: uu___3 in
                  FStar_Parser_AST.mkApp head uu___2 r in
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
                FStar_Parser_AST.attrs = [str "uninterpreted_by_smt"]
              } in
            FStar_Pervasives.Inr d1
let (uu___36 : unit) =
  FStar_Parser_AST_Util.register_extension_parser "pulse" extension_parser
let (parse_pulse :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      (Prims.string * Prims.string) Prims.list ->
        Prims.string ->
          Prims.string ->
            Prims.int ->
              Prims.int ->
                (PulseSyntaxWrapper.st_term,
                  (Prims.string * FStar_Compiler_Range_Type.range))
                  FStar_Pervasives.either)
  =
  fun env ->
    fun namespaces ->
      fun module_abbrevs ->
        fun content ->
          fun file_name ->
            fun line ->
              fun col ->
                let namespaces1 =
                  FStar_Compiler_List.map FStar_Ident.path_of_text namespaces in
                let module_abbrevs1 =
                  FStar_Compiler_List.map
                    (fun uu___ ->
                       match uu___ with
                       | (x, l) ->
                           let uu___1 = FStar_Ident.path_of_text l in
                           (x, uu___1)) module_abbrevs in
                let env1 =
                  PulseDesugar.initialize_env env namespaces1 module_abbrevs1 in
                let range =
                  let p = FStar_Compiler_Range_Type.mk_pos line col in
                  FStar_Compiler_Range_Type.mk_range file_name p p in
                let uu___ = Pulse_Parser.parse_decl content range in
                match uu___ with
                | FStar_Pervasives.Inl d ->
                    let uu___1 =
                      let uu___2 = PulseDesugar.desugar_decl env1 d in
                      uu___2 Prims.int_zero in
                    FStar_Pervasives_Native.fst uu___1
                | FStar_Pervasives.Inr e -> FStar_Pervasives.Inr e
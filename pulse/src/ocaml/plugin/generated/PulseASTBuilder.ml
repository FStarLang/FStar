open Prims
let (r_ : FStar_Compiler_Range.range) = FStar_Compiler_Range.dummyRange
let (pulse_checker_tac : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Main"; "check_pulse"] r_
let (tm :
  FStar_Parser_AST.term' ->
    FStar_Compiler_Range.range -> FStar_Parser_AST.term)
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
      fun rng ->
        let tm1 t = tm t rng in
        let str s =
          tm1 (FStar_Parser_AST.Const (FStar_Const.Const_string (s, rng))) in
        let uu___ = Pulse_Parser.parse_peek_id contents rng in
        match uu___ with
        | FStar_Pervasives.Inr (err, r) ->
            FStar_Pervasives.Inl
              {
                FStar_Parser_AST_Util.message = err;
                FStar_Parser_AST_Util.range = r
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
                FStar_Parser_AST.mkConsList rng uu___1 in
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
                           FStar_Parser_AST.mkTuple [a1; m1] rng)
                    ctx.FStar_Parser_AST_Util.module_abbreviations in
                FStar_Parser_AST.mkConsList rng uu___1 in
              FStar_Parser_AST.mkApp head
                [(namespaces, FStar_Parser_AST.Nothing);
                (abbrevs, FStar_Parser_AST.Nothing);
                ((str contents), FStar_Parser_AST.Nothing)] rng in
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.id_of_text id in [uu___4] in
                (true, uu___3, splicer) in
              FStar_Parser_AST.Splice uu___2 in
            FStar_Pervasives.Inr uu___1
let (uu___26 : unit) =
  FStar_Parser_AST_Util.register_extension_parser "pulse" extension_parser
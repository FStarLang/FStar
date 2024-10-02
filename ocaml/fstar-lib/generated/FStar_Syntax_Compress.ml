open Prims
let (compress1_t :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun allow_uvars ->
    fun allow_names ->
      fun t ->
        let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_uvar (uv, s) when
            Prims.op_Negation allow_uvars ->
            let uu___ =
              let uu___1 =
                FStar_Class_Show.show FStar_Syntax_Print.showable_ctxu uv in
              FStar_Compiler_Util.format1
                "Internal error: unexpected unresolved uvar in deep_compress: %s"
                uu___1 in
            FStar_Errors.raise_error0
              FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar ()
              (Obj.magic FStar_Errors_Msg.is_error_message_string)
              (Obj.magic uu___)
        | FStar_Syntax_Syntax.Tm_name bv when Prims.op_Negation allow_names
            ->
            ((let uu___1 = FStar_Compiler_Debug.any () in
              if uu___1
              then
                let uu___2 =
                  let uu___3 =
                    FStar_Class_Show.show FStar_Syntax_Print.showable_bv bv in
                  FStar_Compiler_Util.format1 "Tm_name %s in deep compress"
                    uu___3 in
                FStar_Errors.log_issue
                  (FStar_Syntax_Syntax.has_range_syntax ()) t
                  FStar_Errors_Codes.Warning_NameEscape ()
                  (Obj.magic FStar_Errors_Msg.is_error_message_string)
                  (Obj.magic uu___2)
              else ());
             (let uu___1 =
                let uu___2 =
                  let uu___3 = mk FStar_Syntax_Syntax.Tm_unknown in
                  {
                    FStar_Syntax_Syntax.ppname =
                      (bv.FStar_Syntax_Syntax.ppname);
                    FStar_Syntax_Syntax.index =
                      (bv.FStar_Syntax_Syntax.index);
                    FStar_Syntax_Syntax.sort = uu___3
                  } in
                FStar_Syntax_Syntax.Tm_name uu___2 in
              mk uu___1))
        | FStar_Syntax_Syntax.Tm_bvar bv ->
            let uu___ =
              let uu___1 =
                let uu___2 = mk FStar_Syntax_Syntax.Tm_unknown in
                {
                  FStar_Syntax_Syntax.ppname =
                    (bv.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___2
                } in
              FStar_Syntax_Syntax.Tm_bvar uu___1 in
            mk uu___
        | FStar_Syntax_Syntax.Tm_name bv ->
            let uu___ =
              let uu___1 =
                let uu___2 = mk FStar_Syntax_Syntax.Tm_unknown in
                {
                  FStar_Syntax_Syntax.ppname =
                    (bv.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___2
                } in
              FStar_Syntax_Syntax.Tm_name uu___1 in
            mk uu___
        | uu___ -> t
let (compress1_u :
  Prims.bool ->
    Prims.bool ->
      FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun allow_uvars ->
    fun allow_names ->
      fun u ->
        match u with
        | FStar_Syntax_Syntax.U_name bv when Prims.op_Negation allow_names ->
            ((let uu___1 = FStar_Compiler_Debug.any () in
              if uu___1
              then
                let uu___2 =
                  let uu___3 =
                    FStar_Class_Show.show FStar_Ident.showable_ident bv in
                  FStar_Compiler_Util.format1 "U_name %s in deep compress"
                    uu___3 in
                FStar_Errors.log_issue0 FStar_Errors_Codes.Warning_NameEscape
                  () (Obj.magic FStar_Errors_Msg.is_error_message_string)
                  (Obj.magic uu___2)
              else ());
             u)
        | FStar_Syntax_Syntax.U_unif uv when Prims.op_Negation allow_uvars ->
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Unionfind.univ_uvar_id uv in
                FStar_Class_Show.show
                  (FStar_Class_Show.printableshow
                     FStar_Class_Printable.printable_int) uu___2 in
              FStar_Compiler_Util.format1
                "Internal error: unexpected unresolved (universe) uvar in deep_compress: %s"
                uu___1 in
            FStar_Errors.raise_error0
              FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar ()
              (Obj.magic FStar_Errors_Msg.is_error_message_string)
              (Obj.magic uu___)
        | uu___ -> u
let (deep_compress :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun allow_uvars ->
    fun allow_names ->
      fun tm ->
        FStar_Errors.with_ctx "While deep-compressing a term"
          (fun uu___ ->
             let uu___1 = compress1_t allow_uvars allow_names in
             let uu___2 = compress1_u allow_uvars allow_names in
             FStar_Syntax_Visit.visit_term_univs true uu___1 uu___2 tm)
let (deep_compress_uvars :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  deep_compress false true
let (deep_compress_if_no_uvars :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun tm ->
    FStar_Errors.with_ctx "While deep-compressing a term"
      (fun uu___ ->
         try
           (fun uu___1 ->
              match () with
              | () ->
                  let uu___2 =
                    let uu___3 = compress1_t false true in
                    let uu___4 = compress1_u false true in
                    FStar_Syntax_Visit.visit_term_univs true uu___3 uu___4 tm in
                  FStar_Pervasives_Native.Some uu___2) ()
         with
         | FStar_Errors.Error
             (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar, uu___2,
              uu___3, uu___4)
             -> FStar_Pervasives_Native.None)
let (deep_compress_se :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun allow_uvars ->
    fun allow_names ->
      fun se ->
        let uu___ =
          let uu___1 = FStar_Syntax_Print.sigelt_to_string_short se in
          FStar_Compiler_Util.format1 "While deep-compressing %s" uu___1 in
        FStar_Errors.with_ctx uu___
          (fun uu___1 ->
             let uu___2 = compress1_t allow_uvars allow_names in
             let uu___3 = compress1_u allow_uvars allow_names in
             FStar_Syntax_Visit.visit_sigelt true uu___2 uu___3 se)
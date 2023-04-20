open Prims
let (compress1_t :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun allow_uvars ->
    fun t ->
      let mk x = FStar_Syntax_Syntax.mk x t.FStar_Syntax_Syntax.pos in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_uvar (uv, s) when
          Prims.op_Negation allow_uvars ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Syntax_Unionfind.uvar_id
                    uv.FStar_Syntax_Syntax.ctx_uvar_head in
                FStar_Compiler_Util.string_of_int uu___3 in
              FStar_Compiler_Util.format1
                "Internal error: unexpected unresolved uvar in deep_compress: %s"
                uu___2 in
            (FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar, uu___1) in
          FStar_Errors.raise_err uu___
      | FStar_Syntax_Syntax.Tm_name bv when Prims.op_Negation allow_uvars ->
          ((let uu___1 = FStar_Options.debug_any () in
            if uu___1
            then
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Syntax_Print.bv_to_string bv in
                  FStar_Compiler_Util.format1 "Tm_name %s in deep compress"
                    uu___4 in
                (FStar_Errors_Codes.Warning_NameEscape, uu___3) in
              FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___2
            else ());
           (let uu___1 =
              let uu___2 =
                let uu___3 = mk FStar_Syntax_Syntax.Tm_unknown in
                {
                  FStar_Syntax_Syntax.ppname =
                    (bv.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___3
                } in
              FStar_Syntax_Syntax.Tm_name uu___2 in
            mk uu___1))
      | FStar_Syntax_Syntax.Tm_bvar bv ->
          let uu___ =
            let uu___1 =
              let uu___2 = mk FStar_Syntax_Syntax.Tm_unknown in
              {
                FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
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
                FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
                FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                FStar_Syntax_Syntax.sort = uu___2
              } in
            FStar_Syntax_Syntax.Tm_name uu___1 in
          mk uu___
      | uu___ -> t
let (compress1_u :
  Prims.bool -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun allow_uvars ->
    fun u ->
      match u with
      | FStar_Syntax_Syntax.U_unif uv when Prims.op_Negation allow_uvars ->
          FStar_Syntax_Syntax.U_zero
      | uu___ -> u
let (deep_compress :
  Prims.bool -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun allow_uvars ->
    fun tm ->
      FStar_Errors.with_ctx "While deep-compressing a term"
        (fun uu___ ->
           let uu___1 =
             let uu___2 = compress1_t allow_uvars in
             let uu___3 = compress1_u allow_uvars in
             FStar_Syntax_Visit.visit_term_univs uu___2 uu___3 in
           uu___1 tm)
let (deep_compress_se :
  Prims.bool -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun allow_uvars ->
    fun se ->
      let uu___ =
        let uu___1 = FStar_Syntax_Print.sigelt_to_string_short se in
        FStar_Compiler_Util.format1 "While deep-compressing %s" uu___1 in
      FStar_Errors.with_ctx uu___
        (fun uu___1 ->
           let uu___2 =
             let uu___3 = compress1_t allow_uvars in
             let uu___4 = compress1_u allow_uvars in
             FStar_Syntax_Visit.visit_sigelt uu___3 uu___4 in
           uu___2 se)
open Prims
let compress1_t (allow_uvars : Prims.bool) (allow_names : Prims.bool)
  (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let mk x = FStarC_Syntax_Syntax.mk x t.FStarC_Syntax_Syntax.pos in
  match t.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_uvar (uv, s) when Prims.op_Negation allow_uvars
      ->
      let uu___ =
        let uu___1 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_ctxu uv in
        FStarC_Format.fmt1
          "Internal error: unexpected unresolved uvar in deep_compress: %s"
          uu___1 in
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_UnexpectedUnresolvedUvar ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
  | FStarC_Syntax_Syntax.Tm_name bv when Prims.op_Negation allow_names ->
      ((let uu___1 = FStarC_Debug.any () in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv bv in
            FStarC_Format.fmt1 "Tm_name %s in deep compress" uu___3 in
          FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ())
            t FStarC_Errors_Codes.Warning_NameEscape ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2)
        else ());
       (let uu___1 =
          let uu___2 =
            let uu___3 = mk FStarC_Syntax_Syntax.Tm_unknown in
            {
              FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
              FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
              FStarC_Syntax_Syntax.sort = uu___3
            } in
          FStarC_Syntax_Syntax.Tm_name uu___2 in
        mk uu___1))
  | FStarC_Syntax_Syntax.Tm_bvar bv ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk FStarC_Syntax_Syntax.Tm_unknown in
          {
            FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_bvar uu___1 in
      mk uu___
  | FStarC_Syntax_Syntax.Tm_name bv ->
      let uu___ =
        let uu___1 =
          let uu___2 = mk FStarC_Syntax_Syntax.Tm_unknown in
          {
            FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = uu___2
          } in
        FStarC_Syntax_Syntax.Tm_name uu___1 in
      mk uu___
  | uu___ -> t
let compress1_u (allow_uvars : Prims.bool) (allow_names : Prims.bool)
  (u : FStarC_Syntax_Syntax.universe) : FStarC_Syntax_Syntax.universe=
  match u with
  | FStarC_Syntax_Syntax.U_name bv when Prims.op_Negation allow_names ->
      ((let uu___1 = FStarC_Debug.any () in
        if uu___1
        then
          let uu___2 =
            let uu___3 =
              FStarC_Class_Show.show FStarC_Ident.showable_ident bv in
            FStarC_Format.fmt1 "U_name %s in deep compress" uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NameEscape ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2)
        else ());
       u)
  | FStarC_Syntax_Syntax.U_unif uv when Prims.op_Negation allow_uvars ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Syntax_Unionfind.univ_uvar_id uv in
          FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___2 in
        FStarC_Format.fmt1
          "Internal error: unexpected unresolved (universe) uvar in deep_compress: %s"
          uu___1 in
      FStarC_Errors.raise_error0
        FStarC_Errors_Codes.Error_UnexpectedUnresolvedUvar ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___)
  | uu___ -> u
let deep_compress (allow_uvars : Prims.bool) (allow_names : Prims.bool)
  (tm : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_Stats.record "deep_compress"
    (fun uu___ ->
       FStarC_Errors.with_ctx "While deep-compressing a term"
         (fun uu___1 ->
            let uu___2 = compress1_t allow_uvars allow_names in
            let uu___3 = compress1_u allow_uvars allow_names in
            FStarC_Syntax_Visit.visit_term_univs true uu___2 uu___3 tm))
let deep_compress_uvars :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term=
  deep_compress false true
let deep_compress_if_no_uvars (tm : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  FStarC_Errors.with_ctx "While deep-compressing a term"
    (fun uu___ ->
       try
         (fun uu___1 ->
            match () with
            | () ->
                let uu___2 =
                  let uu___3 = compress1_t false true in
                  let uu___4 = compress1_u false true in
                  FStarC_Syntax_Visit.visit_term_univs true uu___3 uu___4 tm in
                FStar_Pervasives_Native.Some uu___2) ()
       with
       | FStarC_Errors.Error
           (FStarC_Errors_Codes.Error_UnexpectedUnresolvedUvar, uu___2,
            uu___3, uu___4)
           -> FStar_Pervasives_Native.None)
let deep_compress_se (allow_uvars : Prims.bool) (allow_names : Prims.bool)
  (se : FStarC_Syntax_Syntax.sigelt) : FStarC_Syntax_Syntax.sigelt=
  FStarC_Stats.record "deep_compress_se"
    (fun uu___ ->
       let uu___1 =
         let uu___2 = FStarC_Syntax_Print.sigelt_to_string_short se in
         FStarC_Format.fmt1 "While deep-compressing %s" uu___2 in
       FStarC_Errors.with_ctx uu___1
         (fun uu___2 ->
            let uu___3 = compress1_t allow_uvars allow_names in
            let uu___4 = compress1_u allow_uvars allow_names in
            FStarC_Syntax_Visit.visit_sigelt true uu___3 uu___4 se))

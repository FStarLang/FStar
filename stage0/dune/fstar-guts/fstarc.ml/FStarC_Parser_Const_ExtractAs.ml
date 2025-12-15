open Prims
let p2l (l : FStarC_Ident.path) : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path l FStarC_Range_Type.dummyRange
let extract_as_lid : FStarC_Ident.lid=
  p2l ["FStar"; "ExtractAs"; "extract_as"]
let is_extract_as_attr (attr : FStarC_Syntax_Syntax.attribute) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  let uu___ = FStarC_Syntax_Util.head_and_args attr in
  match uu___ with
  | (head, args) ->
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Subst.compress head in
          uu___3.FStarC_Syntax_Syntax.n in
        (uu___2, args) in
      (match uu___1 with
       | (FStarC_Syntax_Syntax.Tm_fvar fv, (t, uu___2)::[]) when
           FStarC_Syntax_Syntax.fv_eq_lid fv extract_as_lid ->
           let uu___3 =
             let uu___4 = FStarC_Syntax_Subst.compress t in
             uu___4.FStarC_Syntax_Syntax.n in
           (match uu___3 with
            | FStarC_Syntax_Syntax.Tm_quoted (impl, uu___4) ->
                FStar_Pervasives_Native.Some impl
            | uu___4 -> FStar_Pervasives_Native.None)
       | uu___2 -> FStar_Pervasives_Native.None)

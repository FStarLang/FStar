open Prims
type unsealedRange =
  | U of FStarC_Range_Type.t 
let uu___is_U (projectee : unsealedRange) : Prims.bool= true
let __proj__U__item___0 (projectee : unsealedRange) : FStarC_Range_Type.t=
  match projectee with | U _0 -> _0
let mk_range (fn : Prims.string) (from_l : Prims.int) (from_c : Prims.int)
  (to_l : Prims.int) (to_c : Prims.int) : FStarC_Range_Type.t=
  let uu___ = FStarC_Range_Type.mk_pos from_l from_c in
  let uu___1 = FStarC_Range_Type.mk_pos to_l to_c in
  FStarC_Range_Type.mk_range fn uu___ uu___1
let __mk_range (fn : Prims.string) (from_l : Prims.int) (from_c : Prims.int)
  (to_l : Prims.int) (to_c : Prims.int) : unsealedRange=
  let uu___ = mk_range fn from_l from_c to_l to_c in U uu___
let explode (r : unsealedRange) :
  (Prims.string * Prims.int * Prims.int * Prims.int * Prims.int)=
  match r with
  | U r1 ->
      let uu___ = FStarC_Range_Ops.file_of_range r1 in
      let uu___1 =
        let uu___2 = FStarC_Range_Ops.start_of_range r1 in
        FStarC_Range_Ops.line_of_pos uu___2 in
      let uu___2 =
        let uu___3 = FStarC_Range_Ops.start_of_range r1 in
        FStarC_Range_Ops.col_of_pos uu___3 in
      let uu___3 =
        let uu___4 = FStarC_Range_Ops.end_of_range r1 in
        FStarC_Range_Ops.line_of_pos uu___4 in
      let uu___4 =
        let uu___5 = FStarC_Range_Ops.end_of_range r1 in
        FStarC_Range_Ops.col_of_pos uu___5 in
      (uu___, uu___1, uu___2, uu___3, uu___4)
let e_unsealedRange : unsealedRange FStarC_Syntax_Embeddings_Base.embedding=
  FStarC_Syntax_Embeddings_Base.embed_as FStarC_Syntax_Embeddings.e___range
    (fun r -> U r) (fun uu___ -> match uu___ with | U r -> r)
    FStar_Pervasives_Native.None
let nbe_e_unsealedRange : unsealedRange FStarC_TypeChecker_NBETerm.embedding=
  FStarC_TypeChecker_NBETerm.embed_as FStarC_TypeChecker_NBETerm.e___range
    (fun r -> U r) (fun uu___ -> match uu___ with | U r -> r)
    FStar_Pervasives_Native.None
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk5 Prims.int_zero
      FStarC_Parser_Const.__mk_range_lid FStarC_Syntax_Embeddings.e_string
      FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int e_unsealedRange nbe_e_unsealedRange
      __mk_range in
  let uu___1 =
    let uu___2 =
      FStarC_TypeChecker_Primops_Base.mk5 Prims.int_zero
        FStarC_Parser_Const.mk_range_lid FStarC_Syntax_Embeddings.e_string
        FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
        FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
        FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
        FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
        FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_range
        FStarC_TypeChecker_NBETerm.e_range mk_range in
    let uu___3 =
      let uu___4 =
        FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
          FStarC_Parser_Const.__explode_range_lid e_unsealedRange
          nbe_e_unsealedRange
          (FStarC_Syntax_Embeddings.e_tuple5
             FStarC_Syntax_Embeddings.e_string FStarC_Syntax_Embeddings.e_int
             FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_int
             FStarC_Syntax_Embeddings.e_int)
          (FStarC_TypeChecker_NBETerm.e_tuple5
             FStarC_TypeChecker_NBETerm.e_string
             FStarC_TypeChecker_NBETerm.e_int
             FStarC_TypeChecker_NBETerm.e_int
             FStarC_TypeChecker_NBETerm.e_int
             FStarC_TypeChecker_NBETerm.e_int) explode in
      let uu___5 =
        let uu___6 =
          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
            FStarC_Parser_Const.join_range_lid
            FStarC_Syntax_Embeddings.e_range
            FStarC_TypeChecker_NBETerm.e_range
            FStarC_Syntax_Embeddings.e_range
            FStarC_TypeChecker_NBETerm.e_range
            FStarC_Syntax_Embeddings.e_range
            FStarC_TypeChecker_NBETerm.e_range FStarC_Range_Ops.union_ranges in
        [uu___6] in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1

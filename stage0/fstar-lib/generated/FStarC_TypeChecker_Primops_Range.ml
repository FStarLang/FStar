open Prims
type unsealedRange =
  | U of FStarC_Compiler_Range_Type.range 
let (uu___is_U : unsealedRange -> Prims.bool) = fun projectee -> true
let (__proj__U__item___0 : unsealedRange -> FStarC_Compiler_Range_Type.range)
  = fun projectee -> match projectee with | U _0 -> _0
let (mk_range :
  Prims.string ->
    FStarC_BigInt.t ->
      FStarC_BigInt.t ->
        FStarC_BigInt.t ->
          FStarC_BigInt.t -> FStarC_Compiler_Range_Type.range)
  =
  fun fn ->
    fun from_l ->
      fun from_c ->
        fun to_l ->
          fun to_c ->
            let uu___ =
              let uu___1 = FStarC_BigInt.to_int_fs from_l in
              let uu___2 = FStarC_BigInt.to_int_fs from_c in
              FStarC_Compiler_Range_Type.mk_pos uu___1 uu___2 in
            let uu___1 =
              let uu___2 = FStarC_BigInt.to_int_fs to_l in
              let uu___3 = FStarC_BigInt.to_int_fs to_c in
              FStarC_Compiler_Range_Type.mk_pos uu___2 uu___3 in
            FStarC_Compiler_Range_Type.mk_range fn uu___ uu___1
let (__mk_range :
  Prims.string ->
    FStarC_BigInt.t ->
      FStarC_BigInt.t -> FStarC_BigInt.t -> FStarC_BigInt.t -> unsealedRange)
  =
  fun fn ->
    fun from_l ->
      fun from_c ->
        fun to_l ->
          fun to_c ->
            let uu___ = mk_range fn from_l from_c to_l to_c in U uu___
let (explode :
  unsealedRange ->
    (Prims.string * FStarC_BigInt.t * FStarC_BigInt.t * FStarC_BigInt.t *
      FStarC_BigInt.t))
  =
  fun r ->
    match r with
    | U r1 ->
        let uu___ = FStarC_Compiler_Range_Ops.file_of_range r1 in
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Compiler_Range_Ops.start_of_range r1 in
            FStarC_Compiler_Range_Ops.line_of_pos uu___3 in
          FStarC_BigInt.of_int_fs uu___2 in
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Compiler_Range_Ops.start_of_range r1 in
            FStarC_Compiler_Range_Ops.col_of_pos uu___4 in
          FStarC_BigInt.of_int_fs uu___3 in
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Compiler_Range_Ops.end_of_range r1 in
            FStarC_Compiler_Range_Ops.line_of_pos uu___5 in
          FStarC_BigInt.of_int_fs uu___4 in
        let uu___4 =
          let uu___5 =
            let uu___6 = FStarC_Compiler_Range_Ops.end_of_range r1 in
            FStarC_Compiler_Range_Ops.col_of_pos uu___6 in
          FStarC_BigInt.of_int_fs uu___5 in
        (uu___, uu___1, uu___2, uu___3, uu___4)
let (e_unsealedRange : unsealedRange FStarC_Syntax_Embeddings_Base.embedding)
  =
  FStarC_Syntax_Embeddings_Base.embed_as FStarC_Syntax_Embeddings.e___range
    (fun r -> U r) (fun uu___ -> match uu___ with | U r -> r)
    FStar_Pervasives_Native.None
let (nbe_e_unsealedRange :
  unsealedRange FStarC_TypeChecker_NBETerm.embedding) =
  FStarC_TypeChecker_NBETerm.embed_as FStarC_TypeChecker_NBETerm.e___range
    (fun r -> U r) (fun uu___ -> match uu___ with | U r -> r)
    FStar_Pervasives_Native.None
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
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
            FStarC_TypeChecker_NBETerm.e_range
            FStarC_Compiler_Range_Ops.union_ranges in
        [uu___6] in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
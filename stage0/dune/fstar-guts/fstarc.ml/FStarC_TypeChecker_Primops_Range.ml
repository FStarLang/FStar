open Prims
let mk_range (fn : Prims.string) (from_l : Prims.int) (from_c : Prims.int)
  (to_l : Prims.int) (to_c : Prims.int) : FStarC_Range_Type.t=
  FStarC_Range_Type.mk_range fn (FStarC_Range_Type.mk_pos from_l from_c)
    (FStarC_Range_Type.mk_pos to_l to_c)
let explode (r : FStarC_Range_Type.t) :
  (Prims.string * Prims.int * Prims.int * Prims.int * Prims.int)=
  ((FStarC_Range_Ops.file_of_range r),
    (FStarC_Range_Ops.line_of_pos (FStarC_Range_Ops.start_of_range r)),
    (FStarC_Range_Ops.col_of_pos (FStarC_Range_Ops.start_of_range r)),
    (FStarC_Range_Ops.line_of_pos (FStarC_Range_Ops.end_of_range r)),
    (FStarC_Range_Ops.col_of_pos (FStarC_Range_Ops.end_of_range r)))
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  [FStarC_TypeChecker_Primops_Base.mk5 Prims.int_zero
     FStarC_Parser_Const.mk_range_lid FStarC_Syntax_Embeddings.e_string
     FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
     FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
     FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
     FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
     FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_range
     FStarC_TypeChecker_NBETerm.e_range mk_range;
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.__explode_range_lid FStarC_Syntax_Embeddings.e_range
    FStarC_TypeChecker_NBETerm.e_range
    (FStarC_Syntax_Embeddings.e_tuple5 FStarC_Syntax_Embeddings.e_string
       FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_int
       FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_int)
    (FStarC_TypeChecker_NBETerm.e_tuple5 FStarC_TypeChecker_NBETerm.e_string
       FStarC_TypeChecker_NBETerm.e_int FStarC_TypeChecker_NBETerm.e_int
       FStarC_TypeChecker_NBETerm.e_int FStarC_TypeChecker_NBETerm.e_int)
    explode;
  FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
    FStarC_Parser_Const.join_range_lid FStarC_Syntax_Embeddings.e_range
    FStarC_TypeChecker_NBETerm.e_range FStarC_Syntax_Embeddings.e_range
    FStarC_TypeChecker_NBETerm.e_range FStarC_Syntax_Embeddings.e_range
    FStarC_TypeChecker_NBETerm.e_range
    (fun r1 r2 ->
       let uu___ = FStarC_Range_Ops.union_ranges r1 r2 in
       FStar_Pervasives_Native.Some uu___)
    (fun r1 r2 ->
       let uu___ = FStarC_Range_Ops.union_ranges r1 r2 in
       FStar_Pervasives_Native.Some uu___)]

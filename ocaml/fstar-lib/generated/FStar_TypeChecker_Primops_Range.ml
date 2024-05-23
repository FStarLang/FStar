open Prims
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk5 Prims.int_zero
      FStar_Parser_Const.mk_range_lid FStar_Syntax_Embeddings.e_string
      FStar_TypeChecker_NBETerm.e_string FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_range
      FStar_TypeChecker_NBETerm.e_range
      (fun fn ->
         fun from_l ->
           fun from_c ->
             fun to_l ->
               fun to_c ->
                 let uu___1 =
                   let uu___2 = FStar_BigInt.to_int_fs from_l in
                   let uu___3 = FStar_BigInt.to_int_fs from_c in
                   FStar_Compiler_Range_Type.mk_pos uu___2 uu___3 in
                 let uu___2 =
                   let uu___3 = FStar_BigInt.to_int_fs to_l in
                   let uu___4 = FStar_BigInt.to_int_fs to_c in
                   FStar_Compiler_Range_Type.mk_pos uu___3 uu___4 in
                 FStar_Compiler_Range_Type.mk_range fn uu___1 uu___2) in
  let uu___1 =
    let uu___2 =
      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
        FStar_Parser_Const.join_range_lid FStar_Syntax_Embeddings.e_range
        FStar_TypeChecker_NBETerm.e_range FStar_Syntax_Embeddings.e_range
        FStar_TypeChecker_NBETerm.e_range FStar_Syntax_Embeddings.e_range
        FStar_TypeChecker_NBETerm.e_range
        FStar_Compiler_Range_Ops.union_ranges in
    [uu___2] in
  uu___ :: uu___1
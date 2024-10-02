open Prims
type tf =
  | T 
  | F 
let (uu___is_T : tf -> Prims.bool) =
  fun projectee -> match projectee with | T -> true | uu___ -> false
let (uu___is_F : tf -> Prims.bool) =
  fun projectee -> match projectee with | F -> true | uu___ -> false
let (e_tf : tf FStar_Syntax_Embeddings_Base.embedding) =
  let ty = FStar_Syntax_Util.fvar_const FStar_Parser_Const.prop_lid in
  let emb_t_prop =
    let uu___ =
      let uu___1 = FStar_Ident.string_of_lid FStar_Parser_Const.prop_lid in
      (uu___1, []) in
    FStar_Syntax_Syntax.ET_app uu___ in
  let em p rng _shadow _norm =
    match p with
    | T -> FStar_Syntax_Util.t_true
    | F -> FStar_Syntax_Util.t_false in
  let un t _norm =
    let uu___ =
      let uu___1 = FStar_Syntax_Embeddings_Base.unmeta_div_results t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
        FStar_Pervasives_Native.Some T
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
        FStar_Pervasives_Native.Some F
    | uu___1 -> FStar_Pervasives_Native.None in
  FStar_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___ -> ty)
    (fun uu___ -> match uu___ with | T -> "T" | F -> "F")
    (fun uu___ -> emb_t_prop)
let (nbe_e_tf : tf FStar_TypeChecker_NBETerm.embedding) =
  let lid_as_typ l us args =
    let uu___ = FStar_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
    FStar_TypeChecker_NBETerm.mkFV uu___ us args in
  let em _cb a =
    match a with
    | T -> lid_as_typ FStar_Parser_Const.true_lid [] []
    | F -> lid_as_typ FStar_Parser_Const.false_lid [] [] in
  let un _cb t =
    match t.FStar_TypeChecker_NBETerm.nbe_t with
    | FStar_TypeChecker_NBETerm.FV (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid ->
        FStar_Pervasives_Native.Some T
    | FStar_TypeChecker_NBETerm.FV (fv, [], []) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid ->
        FStar_Pervasives_Native.Some F
    | uu___ -> FStar_Pervasives_Native.None in
  FStar_TypeChecker_NBETerm.mk_emb em un
    (fun uu___ -> lid_as_typ FStar_Parser_Const.bool_lid [] [])
    (FStar_Syntax_Embeddings_Base.emb_typ_of e_tf)
let (cmp :
  FStar_Compiler_Real.real ->
    FStar_Compiler_Real.real ->
      FStar_Compiler_Order.order FStar_Pervasives_Native.option)
  =
  fun r1 ->
    fun r2 ->
      match ((FStar_Compiler_Real.__proj__Real__item___0 r1),
              (FStar_Compiler_Real.__proj__Real__item___0 r2))
      with
      | ("0.0", "0.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Eq
      | ("0.0", "0.5") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Lt
      | ("0.0", "1.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Lt
      | ("0.5", "0.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Gt
      | ("0.5", "0.5") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Eq
      | ("0.5", "1.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Lt
      | ("1.0", "0.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Gt
      | ("1.0", "0.5") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Gt
      | ("1.0", "1.0") ->
          FStar_Pervasives_Native.Some FStar_Compiler_Order.Eq
      | uu___ -> FStar_Pervasives_Native.None
let (lt :
  FStar_Compiler_Real.real ->
    FStar_Compiler_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = cmp r1 r2 in
           Obj.magic
             (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStar_Compiler_Order.Lt -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (le :
  FStar_Compiler_Real.real ->
    FStar_Compiler_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = cmp r1 r2 in
           Obj.magic
             (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStar_Compiler_Order.Lt -> Obj.magic T
                      | FStar_Compiler_Order.Eq -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (gt :
  FStar_Compiler_Real.real ->
    FStar_Compiler_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = cmp r1 r2 in
           Obj.magic
             (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStar_Compiler_Order.Gt -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (ge :
  FStar_Compiler_Real.real ->
    FStar_Compiler_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = cmp r1 r2 in
           Obj.magic
             (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStar_Compiler_Order.Gt -> Obj.magic T
                      | FStar_Compiler_Order.Eq -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (of_int : FStar_BigInt.t -> FStar_Compiler_Real.real) =
  fun i ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_BigInt.to_int_fs i in Prims.string_of_int uu___2 in
      Prims.strcat uu___1 ".0" in
    FStar_Compiler_Real.Real uu___
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
      FStar_Parser_Const.real_of_int FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_real
      FStar_TypeChecker_NBETerm.e_real of_int in
  [uu___]
let (simplify_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk2' Prims.int_zero
      FStar_Parser_Const.real_op_LT FStar_Syntax_Embeddings.e_real
      FStar_TypeChecker_NBETerm.e_real FStar_Syntax_Embeddings.e_real
      FStar_TypeChecker_NBETerm.e_real e_tf nbe_e_tf lt lt in
  let uu___1 =
    let uu___2 =
      FStar_TypeChecker_Primops_Base.mk2' Prims.int_zero
        FStar_Parser_Const.real_op_LTE FStar_Syntax_Embeddings.e_real
        FStar_TypeChecker_NBETerm.e_real FStar_Syntax_Embeddings.e_real
        FStar_TypeChecker_NBETerm.e_real e_tf nbe_e_tf le le in
    let uu___3 =
      let uu___4 =
        FStar_TypeChecker_Primops_Base.mk2' Prims.int_zero
          FStar_Parser_Const.real_op_GT FStar_Syntax_Embeddings.e_real
          FStar_TypeChecker_NBETerm.e_real FStar_Syntax_Embeddings.e_real
          FStar_TypeChecker_NBETerm.e_real e_tf nbe_e_tf gt gt in
      let uu___5 =
        let uu___6 =
          FStar_TypeChecker_Primops_Base.mk2' Prims.int_zero
            FStar_Parser_Const.real_op_GTE FStar_Syntax_Embeddings.e_real
            FStar_TypeChecker_NBETerm.e_real FStar_Syntax_Embeddings.e_real
            FStar_TypeChecker_NBETerm.e_real e_tf nbe_e_tf ge ge in
        [uu___6] in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
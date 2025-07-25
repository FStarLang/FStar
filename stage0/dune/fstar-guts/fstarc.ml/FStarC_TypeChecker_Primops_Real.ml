open Prims
type tf =
  | T 
  | F 
let (uu___is_T : tf -> Prims.bool) =
  fun projectee -> match projectee with | T -> true | uu___ -> false
let (uu___is_F : tf -> Prims.bool) =
  fun projectee -> match projectee with | F -> true | uu___ -> false
let (e_tf : tf FStarC_Syntax_Embeddings_Base.embedding) =
  let ty = FStarC_Syntax_Util.fvar_const FStarC_Parser_Const.prop_lid in
  let emb_t_prop =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid FStarC_Parser_Const.prop_lid in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let em p =
    fun rng ->
      fun _shadow ->
        fun _norm ->
          match p with
          | T -> FStarC_Syntax_Util.t_true
          | F -> FStarC_Syntax_Util.t_false in
  let un t =
    fun _norm ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Embeddings_Base.unmeta_div_results t in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid ->
          FStar_Pervasives_Native.Some T
      | FStarC_Syntax_Syntax.Tm_fvar fv when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.false_lid ->
          FStar_Pervasives_Native.Some F
      | uu___1 -> FStar_Pervasives_Native.None in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un (fun uu___ -> ty)
    (fun uu___ -> match uu___ with | T -> "T" | F -> "F")
    (fun uu___ -> emb_t_prop)
let (nbe_e_tf : tf FStarC_TypeChecker_NBETerm.embedding) =
  let lid_as_typ l =
    fun us ->
      fun args ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
        FStarC_TypeChecker_NBETerm.mkFV uu___ us args in
  let em _cb =
    fun a ->
      match a with
      | T -> lid_as_typ FStarC_Parser_Const.true_lid [] []
      | F -> lid_as_typ FStarC_Parser_Const.false_lid [] [] in
  let un _cb =
    fun t ->
      match t.FStarC_TypeChecker_NBETerm.nbe_t with
      | FStarC_TypeChecker_NBETerm.FV (fv, [], []) when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.true_lid ->
          FStar_Pervasives_Native.Some T
      | FStarC_TypeChecker_NBETerm.FV (fv, [], []) when
          FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.false_lid ->
          FStar_Pervasives_Native.Some F
      | uu___ -> FStar_Pervasives_Native.None in
  FStarC_TypeChecker_NBETerm.mk_emb em un
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.bool_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of e_tf)
let (lt :
  FStarC_Real.real -> FStarC_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = FStarC_Real.cmp r1 r2 in
           Obj.magic
             (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStarC_Order.Lt -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (le :
  FStarC_Real.real -> FStarC_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = FStarC_Real.cmp r1 r2 in
           Obj.magic
             (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStarC_Order.Lt -> Obj.magic T
                      | FStarC_Order.Eq -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (gt :
  FStarC_Real.real -> FStarC_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = FStarC_Real.cmp r1 r2 in
           Obj.magic
             (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStarC_Order.Gt -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (ge :
  FStarC_Real.real -> FStarC_Real.real -> tf FStar_Pervasives_Native.option)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun r1 ->
         fun r2 ->
           let uu___ = FStarC_Real.cmp r1 r2 in
           Obj.magic
             (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | FStarC_Order.Gt -> Obj.magic T
                      | FStarC_Order.Eq -> Obj.magic T
                      | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___)))
        uu___1 uu___
let (is_lit : Prims.string -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun s ->
    fun t ->
      let uu___ =
        FStarC_TypeChecker_Primops_Base.try_unembed_simple
          FStarC_Syntax_Embeddings.e_real t in
      match uu___ with
      | FStar_Pervasives_Native.Some r ->
          let uu___1 = FStarC_Real.cmp r (FStarC_Real.Real s) in
          uu___1 = (FStar_Pervasives_Native.Some FStarC_Order.Eq)
      | uu___1 -> false
let (bogus_cbs : FStarC_TypeChecker_NBETerm.nbe_cbs) =
  {
    FStarC_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
    FStarC_TypeChecker_NBETerm.translate =
      (fun uu___ -> failwith "bogus_cbs translate")
  }
let (is_nbe_lit : Prims.string -> FStarC_TypeChecker_NBETerm.t -> Prims.bool)
  =
  fun s ->
    fun t ->
      let uu___ =
        FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_real
          bogus_cbs t in
      match uu___ with
      | FStar_Pervasives_Native.Some r ->
          let uu___1 = FStarC_Real.cmp r (FStarC_Real.Real s) in
          uu___1 = (FStar_Pervasives_Native.Some FStarC_Order.Eq)
      | uu___1 -> false
let (is_zero : FStarC_Syntax_Syntax.term -> Prims.bool) = is_lit "0.0"
let (is_one : FStarC_Syntax_Syntax.term -> Prims.bool) = is_lit "1.0"
let (is_nbe_zero : FStarC_TypeChecker_NBETerm.t -> Prims.bool) =
  is_nbe_lit "0.0"
let (is_nbe_one : FStarC_TypeChecker_NBETerm.t -> Prims.bool) =
  is_nbe_lit "1.0"
let (add_op :
  FStarC_TypeChecker_Primops_Base.psc ->
    FStarC_Syntax_Embeddings_Base.norm_cb ->
      FStarC_Syntax_Syntax.universes ->
        FStarC_Syntax_Syntax.args ->
          FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ = is_zero a1 in
              if uu___
              then FStar_Pervasives_Native.Some a2
              else
                (let uu___2 = is_zero a2 in
                 if uu___2
                 then FStar_Pervasives_Native.Some a1
                 else FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
let (mul_op :
  FStarC_TypeChecker_Primops_Base.psc ->
    FStarC_Syntax_Embeddings_Base.norm_cb ->
      FStarC_Syntax_Syntax.universes ->
        FStarC_Syntax_Syntax.args ->
          FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ = is_one a1 in
              if uu___
              then FStar_Pervasives_Native.Some a2
              else
                (let uu___2 = is_one a2 in
                 if uu___2
                 then FStar_Pervasives_Native.Some a1
                 else FStar_Pervasives_Native.None)
          | uu___ -> FStar_Pervasives_Native.None
let add_op_nbe :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      (FStarC_TypeChecker_NBETerm.t * 'uuuuu1 FStar_Pervasives_Native.option)
        Prims.list ->
        FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun univs ->
    fun args ->
      match args with
      | (r, FStar_Pervasives_Native.None)::(l, FStar_Pervasives_Native.None)::[]
          ->
          let uu___ = is_nbe_zero l in
          if uu___
          then FStar_Pervasives_Native.Some r
          else
            (let uu___2 = is_nbe_zero r in
             if uu___2
             then FStar_Pervasives_Native.Some l
             else FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let mul_op_nbe :
  'uuuuu 'uuuuu1 .
    'uuuuu ->
      (FStarC_TypeChecker_NBETerm.t * 'uuuuu1 FStar_Pervasives_Native.option)
        Prims.list ->
        FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun univs ->
    fun args ->
      match args with
      | (r, FStar_Pervasives_Native.None)::(l, FStar_Pervasives_Native.None)::[]
          ->
          let uu___ = is_nbe_one l in
          if uu___
          then FStar_Pervasives_Native.Some r
          else
            (let uu___2 = is_nbe_one r in
             if uu___2
             then FStar_Pervasives_Native.Some l
             else FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (of_int : Prims.int -> FStarC_Real.real) =
  fun i -> FStarC_Real.Real (Prims.strcat (Prims.string_of_int i) ".0")
let (as_primitive_step :
  Prims.bool ->
    (FStarC_Ident.lident * Prims.int * Prims.int *
      FStarC_TypeChecker_Primops_Base.interp_t *
      (FStarC_Syntax_Syntax.universes ->
         FStarC_TypeChecker_NBETerm.args ->
           FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option))
      -> FStarC_TypeChecker_Primops_Base.primitive_step)
  =
  fun is_strong ->
    fun uu___ ->
      match uu___ with
      | (l, arity, u_arity, f, f_nbe) ->
          FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
            (l, arity, u_arity, f,
              (fun cb -> fun univs -> fun args -> f_nbe univs args))
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    let uu___1 =
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
        FStarC_Parser_Const.real_of_int FStarC_Syntax_Embeddings.e_int
        FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_real
        FStarC_TypeChecker_NBETerm.e_real of_int in
    [uu___1] in
  let uu___1 =
    FStarC_List.map (as_primitive_step true)
      [(FStarC_Parser_Const.real_op_Addition, (Prims.of_int (2)),
         Prims.int_zero, add_op, add_op_nbe);
      (FStarC_Parser_Const.real_op_Multiply, (Prims.of_int (2)),
        Prims.int_zero, mul_op, mul_op_nbe)] in
  FStarC_List.op_At uu___ uu___1
let (simplify_ops :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
      FStarC_Parser_Const.real_op_LT FStarC_Syntax_Embeddings.e_real
      FStarC_TypeChecker_NBETerm.e_real FStarC_Syntax_Embeddings.e_real
      FStarC_TypeChecker_NBETerm.e_real e_tf nbe_e_tf lt lt in
  let uu___1 =
    let uu___2 =
      FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
        FStarC_Parser_Const.real_op_LTE FStarC_Syntax_Embeddings.e_real
        FStarC_TypeChecker_NBETerm.e_real FStarC_Syntax_Embeddings.e_real
        FStarC_TypeChecker_NBETerm.e_real e_tf nbe_e_tf le le in
    let uu___3 =
      let uu___4 =
        FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
          FStarC_Parser_Const.real_op_GT FStarC_Syntax_Embeddings.e_real
          FStarC_TypeChecker_NBETerm.e_real FStarC_Syntax_Embeddings.e_real
          FStarC_TypeChecker_NBETerm.e_real e_tf nbe_e_tf gt gt in
      let uu___5 =
        let uu___6 =
          FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
            FStarC_Parser_Const.real_op_GTE FStarC_Syntax_Embeddings.e_real
            FStarC_TypeChecker_NBETerm.e_real FStarC_Syntax_Embeddings.e_real
            FStarC_TypeChecker_NBETerm.e_real e_tf nbe_e_tf ge ge in
        [uu___6] in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1

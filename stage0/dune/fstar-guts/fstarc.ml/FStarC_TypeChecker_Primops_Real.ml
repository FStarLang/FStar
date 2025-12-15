open Prims
type tf =
  | T 
  | F 
let uu___is_T (projectee : tf) : Prims.bool=
  match projectee with | T -> true | uu___ -> false
let uu___is_F (projectee : tf) : Prims.bool=
  match projectee with | F -> true | uu___ -> false
let e_tf : tf FStarC_Syntax_Embeddings_Base.embedding=
  let ty = FStarC_Syntax_Util.fvar_const FStarC_Parser_Const.prop_lid in
  let emb_t_prop =
    let uu___ =
      let uu___1 = FStarC_Ident.string_of_lid FStarC_Parser_Const.prop_lid in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let em p rng _shadow _norm =
    match p with
    | T -> FStarC_Syntax_Util.t_true
    | F -> FStarC_Syntax_Util.t_false in
  let un t _norm =
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
let nbe_e_tf : tf FStarC_TypeChecker_NBETerm.embedding=
  let lid_as_typ l us args =
    let uu___ = FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
    FStarC_TypeChecker_NBETerm.mkFV uu___ us args in
  let em _cb a =
    match a with
    | T -> lid_as_typ FStarC_Parser_Const.true_lid [] []
    | F -> lid_as_typ FStarC_Parser_Const.false_lid [] [] in
  let un _cb t =
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
let lt (uu___1 : FStarC_Real.real) (uu___ : FStarC_Real.real) :
  tf FStar_Pervasives_Native.option=
  (fun r1 r2 ->
     let uu___ = FStarC_Real.cmp r1 r2 in
     Obj.magic
       (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                match uu___1 with
                | FStarC_Order.Lt -> Obj.magic T
                | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___))) uu___1
    uu___
let le (uu___1 : FStarC_Real.real) (uu___ : FStarC_Real.real) :
  tf FStar_Pervasives_Native.option=
  (fun r1 r2 ->
     let uu___ = FStarC_Real.cmp r1 r2 in
     Obj.magic
       (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                match uu___1 with
                | FStarC_Order.Lt -> Obj.magic T
                | FStarC_Order.Eq -> Obj.magic T
                | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___))) uu___1
    uu___
let gt (uu___1 : FStarC_Real.real) (uu___ : FStarC_Real.real) :
  tf FStar_Pervasives_Native.option=
  (fun r1 r2 ->
     let uu___ = FStarC_Real.cmp r1 r2 in
     Obj.magic
       (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                match uu___1 with
                | FStarC_Order.Gt -> Obj.magic T
                | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___))) uu___1
    uu___
let ge (uu___1 : FStarC_Real.real) (uu___ : FStarC_Real.real) :
  tf FStar_Pervasives_Native.option=
  (fun r1 r2 ->
     let uu___ = FStarC_Real.cmp r1 r2 in
     Obj.magic
       (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___1 = Obj.magic uu___1 in
                match uu___1 with
                | FStarC_Order.Gt -> Obj.magic T
                | FStarC_Order.Eq -> Obj.magic T
                | uu___2 -> Obj.magic F) uu___1) (Obj.magic uu___))) uu___1
    uu___
let is_lit (s : Prims.string) (t : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ =
    FStarC_TypeChecker_Primops_Base.try_unembed_simple
      FStarC_Syntax_Embeddings.e_real t in
  match uu___ with
  | FStar_Pervasives_Native.Some r ->
      let uu___1 = FStarC_Real.cmp r (FStarC_Real.Real s) in
      uu___1 = (FStar_Pervasives_Native.Some FStarC_Order.Eq)
  | uu___1 -> false
let bogus_cbs : FStarC_TypeChecker_NBETerm.nbe_cbs=
  {
    FStarC_TypeChecker_NBETerm.iapp = (fun h _args -> h);
    FStarC_TypeChecker_NBETerm.translate =
      (fun uu___ -> failwith "bogus_cbs translate")
  }
let is_nbe_lit (s : Prims.string) (t : FStarC_TypeChecker_NBETerm.t) :
  Prims.bool=
  let uu___ =
    FStarC_TypeChecker_NBETerm.unembed FStarC_TypeChecker_NBETerm.e_real
      bogus_cbs t in
  match uu___ with
  | FStar_Pervasives_Native.Some r ->
      let uu___1 = FStarC_Real.cmp r (FStarC_Real.Real s) in
      uu___1 = (FStar_Pervasives_Native.Some FStarC_Order.Eq)
  | uu___1 -> false
let is_zero : FStarC_Syntax_Syntax.term -> Prims.bool= is_lit "0.0"
let is_one : FStarC_Syntax_Syntax.term -> Prims.bool= is_lit "1.0"
let is_nbe_zero : FStarC_TypeChecker_NBETerm.t -> Prims.bool=
  is_nbe_lit "0.0"
let is_nbe_one : FStarC_TypeChecker_NBETerm.t -> Prims.bool= is_nbe_lit "1.0"
let add_op (psc : FStarC_TypeChecker_Primops_Base.psc)
  (_norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (_us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
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
let mul_op (psc : FStarC_TypeChecker_Primops_Base.psc)
  (_norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (_us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
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
let add_op_nbe (univs : 'uuuuu)
  (args :
    (FStarC_TypeChecker_NBETerm.t * 'uuuuu1 FStar_Pervasives_Native.option)
      Prims.list)
  : FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
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
let mul_op_nbe (univs : 'uuuuu)
  (args :
    (FStarC_TypeChecker_NBETerm.t * 'uuuuu1 FStar_Pervasives_Native.option)
      Prims.list)
  : FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option=
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
let of_int (i : Prims.int) : FStarC_Real.real=
  FStarC_Real.Real (Prims.strcat (Prims.string_of_int i) ".0")
let as_primitive_step (is_strong : Prims.bool)
  (uu___ :
    (FStarC_Ident.lident * Prims.int * Prims.int *
      FStarC_TypeChecker_Primops_Base.interp_t *
      (FStarC_Syntax_Syntax.universes ->
         FStarC_TypeChecker_NBETerm.args ->
           FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)))
  : FStarC_TypeChecker_Primops_Base.primitive_step=
  match uu___ with
  | (l, arity, u_arity, f, f_nbe) ->
      FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
        (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
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
let simplify_ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
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

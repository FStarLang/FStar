open Prims
let (s_eq :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Embeddings.abstract_term ->
      FStarC_Syntax_Embeddings.abstract_term ->
        FStarC_Syntax_Embeddings.abstract_term ->
          Prims.bool FStar_Pervasives_Native.option)
  =
  fun env ->
    fun _typ ->
      fun x ->
        fun y ->
          let uu___ =
            FStarC_TypeChecker_TermEqAndSimplify.eq_tm env
              (FStarC_Syntax_Embeddings.__proj__Abstract__item__t x)
              (FStarC_Syntax_Embeddings.__proj__Abstract__item__t y) in
          match uu___ with
          | FStarC_TypeChecker_TermEqAndSimplify.Equal ->
              FStar_Pervasives_Native.Some true
          | FStarC_TypeChecker_TermEqAndSimplify.NotEqual ->
              FStar_Pervasives_Native.Some false
          | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
      FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
        FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
          Prims.bool FStar_Pervasives_Native.option)
  =
  fun env ->
    fun _typ ->
      fun x ->
        fun y ->
          let uu___ =
            FStarC_TypeChecker_NBETerm.eq_t env
              (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t x)
              (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t y) in
          match uu___ with
          | FStarC_TypeChecker_TermEqAndSimplify.Equal ->
              FStar_Pervasives_Native.Some true
          | FStarC_TypeChecker_TermEqAndSimplify.NotEqual ->
              FStar_Pervasives_Native.Some false
          | uu___1 -> FStar_Pervasives_Native.None
let push3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 .
    ('uuuuu -> 'uuuuu1) ->
      ('uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu) ->
        'uuuuu2 -> 'uuuuu3 -> 'uuuuu4 -> 'uuuuu1
  =
  fun f -> fun g -> fun x -> fun y -> fun z -> let uu___ = g x y z in f uu___
let negopt3 :
  'uuuuu 'uuuuu1 'uuuuu2 .
    unit ->
      ('uuuuu ->
         'uuuuu1 -> 'uuuuu2 -> Prims.bool FStar_Pervasives_Native.option)
        ->
        'uuuuu ->
          'uuuuu1 -> 'uuuuu2 -> Prims.bool FStar_Pervasives_Native.option
  =
  fun uu___ ->
    push3
      (fun uu___1 ->
         (Obj.magic
            (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option () ()
               (fun uu___1 -> (Obj.magic Prims.op_Negation) uu___1))) uu___1)
let (dec_eq_ops :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  fun env ->
    let uu___ =
      FStarC_TypeChecker_Primops_Base.mk3' Prims.int_zero
        FStarC_Parser_Const.op_Eq FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_bool FStarC_TypeChecker_NBETerm.e_bool
        (s_eq env) (nbe_eq env) in
    let uu___1 =
      let uu___2 =
        FStarC_TypeChecker_Primops_Base.mk3' Prims.int_zero
          FStarC_Parser_Const.op_notEq
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_bool FStarC_TypeChecker_NBETerm.e_bool
          ((negopt3 ()) (s_eq env)) ((negopt3 ()) (nbe_eq env)) in
      [uu___2] in
    uu___ :: uu___1
let (s_eq2 :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Embeddings.abstract_term ->
      FStarC_Syntax_Embeddings.abstract_term ->
        FStarC_Syntax_Embeddings.abstract_term ->
          FStarC_Syntax_Embeddings.abstract_term
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun _typ ->
      fun x ->
        fun y ->
          let uu___ =
            FStarC_TypeChecker_TermEqAndSimplify.eq_tm env
              (FStarC_Syntax_Embeddings.__proj__Abstract__item__t x)
              (FStarC_Syntax_Embeddings.__proj__Abstract__item__t y) in
          match uu___ with
          | FStarC_TypeChecker_TermEqAndSimplify.Equal ->
              FStar_Pervasives_Native.Some
                (FStarC_Syntax_Embeddings.Abstract FStarC_Syntax_Util.t_true)
          | FStarC_TypeChecker_TermEqAndSimplify.NotEqual ->
              FStar_Pervasives_Native.Some
                (FStarC_Syntax_Embeddings.Abstract FStarC_Syntax_Util.t_false)
          | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq2 :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
      FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
        FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
          FStarC_TypeChecker_NBETerm.abstract_nbe_term
            FStar_Pervasives_Native.option)
  =
  fun env ->
    fun _typ ->
      fun x ->
        fun y ->
          let uu___ =
            FStarC_TypeChecker_NBETerm.eq_t env
              (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t x)
              (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t y) in
          match uu___ with
          | FStarC_TypeChecker_TermEqAndSimplify.Equal ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_Syntax_Syntax.lid_as_fv
                      FStarC_Parser_Const.true_lid
                      FStar_Pervasives_Native.None in
                  FStarC_TypeChecker_NBETerm.mkFV uu___3 [] [] in
                FStarC_TypeChecker_NBETerm.AbstractNBE uu___2 in
              FStar_Pervasives_Native.Some uu___1
          | FStarC_TypeChecker_TermEqAndSimplify.NotEqual ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStarC_Syntax_Syntax.lid_as_fv
                      FStarC_Parser_Const.false_lid
                      FStar_Pervasives_Native.None in
                  FStarC_TypeChecker_NBETerm.mkFV uu___3 [] [] in
                FStarC_TypeChecker_NBETerm.AbstractNBE uu___2 in
              FStar_Pervasives_Native.Some uu___1
          | FStarC_TypeChecker_TermEqAndSimplify.Unknown ->
              FStar_Pervasives_Native.None
let (s_eq3 :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_Syntax_Embeddings.abstract_term ->
      FStarC_Syntax_Embeddings.abstract_term ->
        FStarC_Syntax_Embeddings.abstract_term ->
          FStarC_Syntax_Embeddings.abstract_term ->
            FStarC_Syntax_Embeddings.abstract_term
              FStar_Pervasives_Native.option)
  =
  fun env ->
    fun typ1 ->
      fun typ2 ->
        fun x ->
          fun y ->
            let uu___ =
              let uu___1 =
                FStarC_TypeChecker_TermEqAndSimplify.eq_tm env
                  (FStarC_Syntax_Embeddings.__proj__Abstract__item__t typ1)
                  (FStarC_Syntax_Embeddings.__proj__Abstract__item__t typ2) in
              let uu___2 =
                FStarC_TypeChecker_TermEqAndSimplify.eq_tm env
                  (FStarC_Syntax_Embeddings.__proj__Abstract__item__t x)
                  (FStarC_Syntax_Embeddings.__proj__Abstract__item__t y) in
              (uu___1, uu___2) in
            match uu___ with
            | (FStarC_TypeChecker_TermEqAndSimplify.Equal,
               FStarC_TypeChecker_TermEqAndSimplify.Equal) ->
                FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Embeddings.Abstract
                     FStarC_Syntax_Util.t_true)
            | (FStarC_TypeChecker_TermEqAndSimplify.NotEqual, uu___1) ->
                FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Embeddings.Abstract
                     FStarC_Syntax_Util.t_false)
            | (uu___1, FStarC_TypeChecker_TermEqAndSimplify.NotEqual) ->
                FStar_Pervasives_Native.Some
                  (FStarC_Syntax_Embeddings.Abstract
                     FStarC_Syntax_Util.t_false)
            | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq3 :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
      FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
        FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
          FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
            FStarC_TypeChecker_NBETerm.abstract_nbe_term
              FStar_Pervasives_Native.option)
  =
  fun env ->
    fun typ1 ->
      fun typ2 ->
        fun x ->
          fun y ->
            let uu___ =
              let uu___1 =
                FStarC_TypeChecker_NBETerm.eq_t env
                  (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t
                     typ1)
                  (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t
                     typ2) in
              let uu___2 =
                FStarC_TypeChecker_NBETerm.eq_t env
                  (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t x)
                  (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t y) in
              (uu___1, uu___2) in
            match uu___ with
            | (FStarC_TypeChecker_TermEqAndSimplify.Equal,
               FStarC_TypeChecker_TermEqAndSimplify.Equal) ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStarC_Syntax_Syntax.lid_as_fv
                        FStarC_Parser_Const.true_lid
                        FStar_Pervasives_Native.None in
                    FStarC_TypeChecker_NBETerm.mkFV uu___3 [] [] in
                  FStarC_TypeChecker_NBETerm.AbstractNBE uu___2 in
                FStar_Pervasives_Native.Some uu___1
            | (FStarC_TypeChecker_TermEqAndSimplify.NotEqual, uu___1) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStarC_Syntax_Syntax.lid_as_fv
                        FStarC_Parser_Const.false_lid
                        FStar_Pervasives_Native.None in
                    FStarC_TypeChecker_NBETerm.mkFV uu___4 [] [] in
                  FStarC_TypeChecker_NBETerm.AbstractNBE uu___3 in
                FStar_Pervasives_Native.Some uu___2
            | (uu___1, FStarC_TypeChecker_TermEqAndSimplify.NotEqual) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStarC_Syntax_Syntax.lid_as_fv
                        FStarC_Parser_Const.false_lid
                        FStar_Pervasives_Native.None in
                    FStarC_TypeChecker_NBETerm.mkFV uu___4 [] [] in
                  FStarC_TypeChecker_NBETerm.AbstractNBE uu___3 in
                FStar_Pervasives_Native.Some uu___2
            | uu___1 -> FStar_Pervasives_Native.None
let (prop_eq_ops :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  fun env ->
    let uu___ =
      FStarC_TypeChecker_Primops_Base.mk3' Prims.int_one
        FStarC_Parser_Const.eq2_lid FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
        FStarC_Syntax_Embeddings.e_abstract_term
        FStarC_TypeChecker_NBETerm.e_abstract_nbe_term (s_eq2 env)
        (nbe_eq2 env) in
    let uu___1 =
      let uu___2 =
        FStarC_TypeChecker_Primops_Base.mk4' (Prims.of_int (2))
          FStarC_Parser_Const.eq3_lid
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
          FStarC_Syntax_Embeddings.e_abstract_term
          FStarC_TypeChecker_NBETerm.e_abstract_nbe_term (s_eq3 env)
          (nbe_eq3 env) in
      [uu___2] in
    uu___ :: uu___1
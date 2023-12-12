open Prims
let (s_eq :
  FStar_Syntax_Embeddings.abstract_term ->
    FStar_Syntax_Embeddings.abstract_term ->
      FStar_Syntax_Embeddings.abstract_term ->
        Prims.bool FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_Syntax_Util.eq_tm
            (FStar_Syntax_Embeddings.__proj__Abstract__item__t x)
            (FStar_Syntax_Embeddings.__proj__Abstract__item__t y) in
        match uu___ with
        | FStar_Syntax_Util.Equal -> FStar_Pervasives_Native.Some true
        | FStar_Syntax_Util.NotEqual -> FStar_Pervasives_Native.Some false
        | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq :
  FStar_TypeChecker_NBETerm.abstract_nbe_term ->
    FStar_TypeChecker_NBETerm.abstract_nbe_term ->
      FStar_TypeChecker_NBETerm.abstract_nbe_term ->
        Prims.bool FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_TypeChecker_NBETerm.eq_t
            (FStar_TypeChecker_NBETerm.__proj__AbstractNBE__item__t x)
            (FStar_TypeChecker_NBETerm.__proj__AbstractNBE__item__t y) in
        match uu___ with
        | FStar_Syntax_Util.Equal -> FStar_Pervasives_Native.Some true
        | FStar_Syntax_Util.NotEqual -> FStar_Pervasives_Native.Some false
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
            (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
               (fun uu___1 -> (Obj.magic Prims.op_Negation) uu___1))) uu___1)
let (dec_eq_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk3' Prims.int_zero
      FStar_Parser_Const.op_Eq FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool s_eq
      nbe_eq in
  let uu___1 =
    let uu___2 =
      FStar_TypeChecker_Primops_Base.mk3' Prims.int_zero
        FStar_Parser_Const.op_notEq FStar_Syntax_Embeddings.e_abstract_term
        FStar_TypeChecker_NBETerm.e_abstract_nbe_term
        FStar_Syntax_Embeddings.e_abstract_term
        FStar_TypeChecker_NBETerm.e_abstract_nbe_term
        FStar_Syntax_Embeddings.e_abstract_term
        FStar_TypeChecker_NBETerm.e_abstract_nbe_term
        FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool
        ((negopt3 ()) s_eq) ((negopt3 ()) nbe_eq) in
    [uu___2] in
  uu___ :: uu___1
let (s_eq2 :
  FStar_Syntax_Embeddings.abstract_term ->
    FStar_Syntax_Embeddings.abstract_term ->
      FStar_Syntax_Embeddings.abstract_term ->
        FStar_Syntax_Embeddings.abstract_term FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_Syntax_Util.eq_tm
            (FStar_Syntax_Embeddings.__proj__Abstract__item__t x)
            (FStar_Syntax_Embeddings.__proj__Abstract__item__t y) in
        match uu___ with
        | FStar_Syntax_Util.Equal ->
            FStar_Pervasives_Native.Some
              (FStar_Syntax_Embeddings.Abstract FStar_Syntax_Util.t_true)
        | FStar_Syntax_Util.NotEqual ->
            FStar_Pervasives_Native.Some
              (FStar_Syntax_Embeddings.Abstract FStar_Syntax_Util.t_false)
        | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq2 :
  FStar_TypeChecker_NBETerm.abstract_nbe_term ->
    FStar_TypeChecker_NBETerm.abstract_nbe_term ->
      FStar_TypeChecker_NBETerm.abstract_nbe_term ->
        FStar_TypeChecker_NBETerm.abstract_nbe_term
          FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_TypeChecker_NBETerm.eq_t
            (FStar_TypeChecker_NBETerm.__proj__AbstractNBE__item__t x)
            (FStar_TypeChecker_NBETerm.__proj__AbstractNBE__item__t y) in
        match uu___ with
        | FStar_Syntax_Util.Equal ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.true_lid
                    FStar_Pervasives_Native.None in
                FStar_TypeChecker_NBETerm.mkFV uu___3 [] [] in
              FStar_TypeChecker_NBETerm.AbstractNBE uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | FStar_Syntax_Util.NotEqual ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.false_lid
                    FStar_Pervasives_Native.None in
                FStar_TypeChecker_NBETerm.mkFV uu___3 [] [] in
              FStar_TypeChecker_NBETerm.AbstractNBE uu___2 in
            FStar_Pervasives_Native.Some uu___1
        | FStar_Syntax_Util.Unknown -> FStar_Pervasives_Native.None
let (prop_eq_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk3' Prims.int_one
      FStar_Parser_Const.eq2_lid FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term s_eq2 nbe_eq2 in
  [uu___]
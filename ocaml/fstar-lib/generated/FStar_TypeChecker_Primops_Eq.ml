open Prims
type abstract_term =
  | Abstract of FStar_Syntax_Syntax.term 
let (uu___is_Abstract : abstract_term -> Prims.bool) = fun projectee -> true
let (__proj__Abstract__item__t : abstract_term -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Abstract t -> t
let (uu___4 : abstract_term FStar_Syntax_Embeddings_Base.embedding) =
  FStar_Syntax_Embeddings_Base.embed_as FStar_Syntax_Embeddings.e_any
    (fun x -> Abstract x) (fun x -> match x with | Abstract x1 -> x1)
    FStar_Pervasives_Native.None
type abstract_nbe_term =
  | AbstractNBE of FStar_TypeChecker_NBETerm.t 
let (uu___is_AbstractNBE : abstract_nbe_term -> Prims.bool) =
  fun projectee -> true
let (__proj__AbstractNBE__item__t :
  abstract_nbe_term -> FStar_TypeChecker_NBETerm.t) =
  fun projectee -> match projectee with | AbstractNBE t -> t
let (uu___13 : abstract_nbe_term FStar_TypeChecker_NBETerm.embedding) =
  FStar_TypeChecker_NBETerm.embed_as FStar_TypeChecker_NBETerm.e_any
    (fun x -> AbstractNBE x) (fun x -> match x with | AbstractNBE x1 -> x1)
    FStar_Pervasives_Native.None
let (s_eq :
  abstract_term ->
    abstract_term ->
      abstract_term -> Prims.bool FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_Syntax_Util.eq_tm (__proj__Abstract__item__t x)
            (__proj__Abstract__item__t y) in
        match uu___ with
        | FStar_Syntax_Util.Equal -> FStar_Pervasives_Native.Some true
        | FStar_Syntax_Util.NotEqual -> FStar_Pervasives_Native.Some false
        | uu___1 -> FStar_Pervasives_Native.None
let (nbe_eq :
  abstract_nbe_term ->
    abstract_nbe_term ->
      abstract_nbe_term -> Prims.bool FStar_Pervasives_Native.option)
  =
  fun _typ ->
    fun x ->
      fun y ->
        let uu___ =
          FStar_TypeChecker_NBETerm.eq_t (__proj__AbstractNBE__item__t x)
            (__proj__AbstractNBE__item__t y) in
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
      FStar_Parser_Const.op_Eq uu___4 uu___13 uu___4 uu___13 uu___4 uu___13
      FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool s_eq
      nbe_eq in
  let uu___1 =
    let uu___2 =
      FStar_TypeChecker_Primops_Base.mk3' Prims.int_zero
        FStar_Parser_Const.op_notEq uu___4 uu___13 uu___4 uu___13 uu___4
        uu___13 FStar_Syntax_Embeddings.e_bool
        FStar_TypeChecker_NBETerm.e_bool ((negopt3 ()) s_eq)
        ((negopt3 ()) nbe_eq) in
    [uu___2] in
  uu___ :: uu___1
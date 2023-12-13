open Prims
type 'a emb_erased =
  | Hide of 'a 
let uu___is_Hide : 'a . 'a emb_erased -> Prims.bool = fun projectee -> true
let __proj__Hide__item__x : 'a . 'a emb_erased -> 'a =
  fun projectee -> match projectee with | Hide x -> x
let e_erased :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      'a emb_erased FStar_Syntax_Embeddings_Base.embedding
  =
  fun d ->
    let em x rng shadow cbs =
      let uu___ = x in
      match uu___ with
      | Hide x1 ->
          let h =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.hide
              FStar_Pervasives_Native.None in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_Syntax_Embeddings_Base.type_of d in
              FStar_Syntax_Syntax.iarg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_Syntax_Embeddings_Base.embed d x1 in
                  uu___6 rng shadow cbs in
                FStar_Syntax_Syntax.as_arg uu___5 in
              [uu___4] in
            uu___2 :: uu___3 in
          FStar_Syntax_Util.mk_app h uu___1 in
    let un uu___1 uu___ =
      (fun t ->
         fun cbs ->
           let uu___ = FStar_Syntax_Util.head_and_args t in
           match uu___ with
           | (head, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStar_Syntax_Util.un_uinst head in
                   uu___3.FStar_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   _t::(a1, FStar_Pervasives_Native.None)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.hide
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            FStar_Syntax_Embeddings_Base.unembed d a1 cbs in
                          FStar_Class_Monad.op_let_Bang
                            FStar_Class_Monad.monad_option () ()
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun v ->
                                  let v = Obj.magic v in
                                  Obj.magic
                                    (FStar_Class_Monad.return
                                       FStar_Class_Monad.monad_option ()
                                       (Obj.magic (Hide v)))) uu___3)))
                | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
        uu___1 uu___ in
    FStar_Syntax_Embeddings_Base.mk_emb_full em un
      (fun uu___ ->
         let uu___1 = FStar_Syntax_Embeddings_Base.type_of d in
         FStar_Syntax_Syntax.t_erased_of uu___1)
      (fun uu___ ->
         match uu___ with
         | Hide x ->
             let uu___1 =
               let uu___2 = FStar_Syntax_Embeddings_Base.printer_of d in
               uu___2 x in
             Prims.strcat "Hide " uu___1)
      (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)
let nbe_e_erased :
  'a .
    'a FStar_TypeChecker_NBETerm.embedding ->
      'a emb_erased FStar_TypeChecker_NBETerm.embedding
  =
  fun d ->
    let em cbs x =
      let uu___ = x in
      match uu___ with
      | Hide x1 ->
          let fv =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.hide
              FStar_Pervasives_Native.None in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStar_TypeChecker_NBETerm.embed d cbs x1 in
              FStar_TypeChecker_NBETerm.as_arg uu___3 in
            [uu___2] in
          FStar_TypeChecker_NBETerm.mkFV fv [] uu___1 in
    let un uu___1 uu___ =
      (fun cbs ->
         fun t ->
           let uu___ = FStar_TypeChecker_NBETerm.nbe_t_of_t t in
           match uu___ with
           | FStar_TypeChecker_NBETerm.FV
               (fv, uu___1, (_t, uu___2)::(body, uu___3)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.hide ->
               Obj.magic
                 (Obj.repr
                    (let uu___4 =
                       FStar_TypeChecker_NBETerm.unembed d cbs body in
                     FStar_Class_Monad.op_let_Bang
                       FStar_Class_Monad.monad_option () ()
                       (Obj.magic uu___4)
                       (fun uu___5 ->
                          (fun v ->
                             let v = Obj.magic v in
                             Obj.magic
                               (FStar_Class_Monad.return
                                  FStar_Class_Monad.monad_option ()
                                  (Obj.magic (Hide v)))) uu___5)))
           | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
        uu___1 uu___ in
    FStar_TypeChecker_NBETerm.mk_emb em un (fun uu___ -> Prims.magic ())
      (fun uu___ -> FStar_Syntax_Syntax.ET_abstract)
let (s_reveal :
  FStar_Syntax_Embeddings.abstract_term ->
    FStar_Syntax_Embeddings.abstract_term emb_erased ->
      FStar_Syntax_Embeddings.abstract_term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun e ->
      let uu___ = e in
      match uu___ with | Hide x -> FStar_Pervasives_Native.Some x
let (nbe_reveal :
  FStar_TypeChecker_NBETerm.abstract_nbe_term ->
    FStar_TypeChecker_NBETerm.abstract_nbe_term emb_erased ->
      FStar_TypeChecker_NBETerm.abstract_nbe_term
        FStar_Pervasives_Native.option)
  =
  fun a ->
    fun e ->
      let uu___ = e in
      match uu___ with | Hide x -> FStar_Pervasives_Native.Some x
let (ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk2' Prims.int_one
      FStar_Parser_Const.reveal FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term
      (e_erased FStar_Syntax_Embeddings.e_abstract_term)
      (nbe_e_erased FStar_TypeChecker_NBETerm.e_abstract_nbe_term)
      FStar_Syntax_Embeddings.e_abstract_term
      FStar_TypeChecker_NBETerm.e_abstract_nbe_term s_reveal nbe_reveal in
  [uu___]
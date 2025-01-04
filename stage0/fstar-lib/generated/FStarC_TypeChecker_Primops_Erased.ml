open Prims
type 'a emb_erased =
  | Hide of 'a 
let uu___is_Hide : 'a . 'a emb_erased -> Prims.bool = fun projectee -> true
let __proj__Hide__item__x : 'a . 'a emb_erased -> 'a =
  fun projectee -> match projectee with | Hide x -> x
let e_erased :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'a emb_erased FStarC_Syntax_Embeddings_Base.embedding
  =
  fun d ->
    let em x rng shadow cbs =
      let uu___ = x in
      match uu___ with
      | Hide x1 ->
          let h =
            FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.hide
              FStar_Pervasives_Native.None in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_Syntax_Embeddings_Base.type_of d in
              FStarC_Syntax_Syntax.iarg uu___3 in
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 = FStarC_Syntax_Embeddings_Base.embed d x1 in
                  uu___6 rng shadow cbs in
                FStarC_Syntax_Syntax.as_arg uu___5 in
              [uu___4] in
            uu___2 :: uu___3 in
          FStarC_Syntax_Util.mk_app h uu___1 in
    let un uu___1 uu___ =
      (fun t ->
         fun cbs ->
           let uu___ = FStarC_Syntax_Util.head_and_args t in
           match uu___ with
           | (head, args) ->
               let uu___1 =
                 let uu___2 =
                   let uu___3 = FStarC_Syntax_Util.un_uinst head in
                   uu___3.FStarC_Syntax_Syntax.n in
                 (uu___2, args) in
               (match uu___1 with
                | (FStarC_Syntax_Syntax.Tm_fvar fv,
                   _t::(a1, FStar_Pervasives_Native.None)::[]) when
                    FStarC_Syntax_Syntax.fv_eq_lid fv
                      FStarC_Parser_Const.hide
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            FStarC_Syntax_Embeddings_Base.unembed d a1 cbs in
                          FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun v ->
                                  let v = Obj.magic v in
                                  Obj.magic
                                    (FStarC_Class_Monad.return
                                       FStarC_Class_Monad.monad_option ()
                                       (Obj.magic (Hide v)))) uu___3)))
                | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
        uu___1 uu___ in
    FStarC_Syntax_Embeddings_Base.mk_emb_full em un
      (fun uu___ ->
         let uu___1 = FStarC_Syntax_Embeddings_Base.type_of d in
         FStarC_Syntax_Syntax.t_erased_of uu___1)
      (fun uu___ ->
         match uu___ with
         | Hide x ->
             let uu___1 =
               let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of d in
               uu___2 x in
             Prims.strcat "Hide " uu___1)
      (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let nbe_e_erased :
  'a .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'a emb_erased FStarC_TypeChecker_NBETerm.embedding
  =
  fun d ->
    let em cbs x =
      let uu___ = x in
      match uu___ with
      | Hide x1 ->
          let fv =
            FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.hide
              FStar_Pervasives_Native.None in
          let uu___1 =
            let uu___2 =
              let uu___3 = FStarC_TypeChecker_NBETerm.embed d cbs x1 in
              FStarC_TypeChecker_NBETerm.as_arg uu___3 in
            [uu___2] in
          FStarC_TypeChecker_NBETerm.mkFV fv [] uu___1 in
    let un uu___1 uu___ =
      (fun cbs ->
         fun t ->
           let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
           match uu___ with
           | FStarC_TypeChecker_NBETerm.FV
               (fv, uu___1, (_t, uu___2)::(body, uu___3)::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.hide ->
               Obj.magic
                 (Obj.repr
                    (let uu___4 =
                       FStarC_TypeChecker_NBETerm.unembed d cbs body in
                     FStarC_Class_Monad.op_let_Bang
                       FStarC_Class_Monad.monad_option () ()
                       (Obj.magic uu___4)
                       (fun uu___5 ->
                          (fun v ->
                             let v = Obj.magic v in
                             Obj.magic
                               (FStarC_Class_Monad.return
                                  FStarC_Class_Monad.monad_option ()
                                  (Obj.magic (Hide v)))) uu___5)))
           | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
        uu___1 uu___ in
    FStarC_TypeChecker_NBETerm.mk_emb em un (fun uu___ -> Prims.magic ())
      (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let (s_reveal :
  FStarC_Syntax_Embeddings.abstract_term ->
    FStarC_Syntax_Embeddings.abstract_term emb_erased ->
      FStarC_Syntax_Embeddings.abstract_term FStar_Pervasives_Native.option)
  =
  fun a ->
    fun e ->
      let uu___ = e in
      match uu___ with | Hide x -> FStar_Pervasives_Native.Some x
let (nbe_reveal :
  FStarC_TypeChecker_NBETerm.abstract_nbe_term ->
    FStarC_TypeChecker_NBETerm.abstract_nbe_term emb_erased ->
      FStarC_TypeChecker_NBETerm.abstract_nbe_term
        FStar_Pervasives_Native.option)
  =
  fun a ->
    fun e ->
      let uu___ = e in
      match uu___ with | Hide x -> FStar_Pervasives_Native.Some x
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk2' Prims.int_one
      FStarC_Parser_Const.reveal FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
      (e_erased FStarC_Syntax_Embeddings.e_abstract_term)
      (nbe_e_erased FStarC_TypeChecker_NBETerm.e_abstract_nbe_term)
      FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term s_reveal nbe_reveal in
  [uu___]
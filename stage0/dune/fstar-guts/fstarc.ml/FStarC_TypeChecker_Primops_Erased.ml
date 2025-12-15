open Prims
type ('tmut, 'a) emb_erased =
  | Hide of 'tmut * 'a 
  | Reveal of 'tmut * 'a 
let uu___is_Hide (projectee : ('tmut, 'a) emb_erased) : Prims.bool=
  match projectee with | Hide (ty, x) -> true | uu___ -> false
let __proj__Hide__item__ty (projectee : ('tmut, 'a) emb_erased) : 'tmut=
  match projectee with | Hide (ty, x) -> ty
let __proj__Hide__item__x (projectee : ('tmut, 'a) emb_erased) : 'a=
  match projectee with | Hide (ty, x) -> x
let uu___is_Reveal (projectee : ('tmut, 'a) emb_erased) : Prims.bool=
  match projectee with | Reveal (ty, x) -> true | uu___ -> false
let __proj__Reveal__item__ty (projectee : ('tmut, 'a) emb_erased) : 'tmut=
  match projectee with | Reveal (ty, x) -> ty
let __proj__Reveal__item__x (projectee : ('tmut, 'a) emb_erased) : 'a=
  match projectee with | Reveal (ty, x) -> x
let e_erased (d : 'a FStarC_Syntax_Embeddings_Base.embedding) :
  (FStarC_Syntax_Syntax.term, 'a) emb_erased
    FStarC_Syntax_Embeddings_Base.embedding=
  let em x rng shadow cbs =
    match x with
    | Hide (_ty, x1) ->
        let h =
          FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.hide
            FStar_Pervasives_Native.None in
        let ty = FStarC_Syntax_Embeddings_Base.type_of d in
        let uu___ =
          let uu___1 = FStarC_Syntax_Syntax.iarg ty in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Syntax_Embeddings_Base.embed d x1 in
                uu___5 rng shadow cbs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Util.mk_app h uu___
    | Reveal (_ty, x1) ->
        let r =
          FStarC_Syntax_Syntax.fvar FStarC_Parser_Const.reveal
            FStar_Pervasives_Native.None in
        let ty = FStarC_Syntax_Embeddings_Base.type_of d in
        let uu___ =
          let uu___1 = FStarC_Syntax_Syntax.iarg ty in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 = FStarC_Syntax_Embeddings_Base.embed d x1 in
                uu___5 rng shadow cbs in
              FStarC_Syntax_Syntax.as_arg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_Syntax_Util.mk_app r uu___ in
  let un uu___1 uu___ =
    (fun t cbs ->
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
               (ty, FStar_Pervasives_Native.Some uu___2)::(a1,
                                                           FStar_Pervasives_Native.None)::[])
                when
                FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.hide ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        FStarC_Syntax_Embeddings_Base.unembed d a1 cbs in
                      FStarC_Class_Monad.op_let_Bang
                        FStarC_Class_Monad.monad_option () ()
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun v ->
                              let v = Obj.magic v in
                              Obj.magic
                                (FStarC_Class_Monad.return
                                   FStarC_Class_Monad.monad_option ()
                                   (Obj.magic (Hide (ty, v))))) uu___4)))
            | (FStarC_Syntax_Syntax.Tm_fvar fv,
               (ty, FStar_Pervasives_Native.Some uu___2)::(a1,
                                                           FStar_Pervasives_Native.None)::[])
                when
                FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.reveal
                ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 =
                        FStarC_Syntax_Embeddings_Base.unembed d a1 cbs in
                      FStarC_Class_Monad.op_let_Bang
                        FStarC_Class_Monad.monad_option () ()
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun v ->
                              let v = Obj.magic v in
                              Obj.magic
                                (FStarC_Class_Monad.return
                                   FStarC_Class_Monad.monad_option ()
                                   (Obj.magic (Reveal (ty, v))))) uu___4)))
            | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)))
      uu___1 uu___ in
  FStarC_Syntax_Embeddings_Base.mk_emb_full em un
    (fun uu___ ->
       let uu___1 = FStarC_Syntax_Embeddings_Base.type_of d in
       FStarC_Syntax_Syntax.t_erased_of uu___1)
    (fun uu___ ->
       match uu___ with
       | Hide (_ty, x) ->
           let uu___1 =
             let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of d in
             uu___2 x in
           Prims.strcat "Hide " uu___1
       | Reveal (_ty, x) ->
           let uu___1 =
             let uu___2 = FStarC_Syntax_Embeddings_Base.printer_of d in
             uu___2 x in
           Prims.strcat "Reveal " uu___1)
    (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let nbe_e_erased (d : 'a FStarC_TypeChecker_NBETerm.embedding) :
  (FStarC_TypeChecker_NBETerm.t, 'a) emb_erased
    FStarC_TypeChecker_NBETerm.embedding=
  let em cbs x =
    match x with
    | Hide (_ty, x1) ->
        let fv =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.hide
            FStar_Pervasives_Native.None in
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed d cbs x1 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.type_of d in
              FStarC_TypeChecker_NBETerm.as_iarg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_TypeChecker_NBETerm.mkFV fv [] uu___
    | Reveal (_ty, x1) ->
        let fv =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.reveal
            FStar_Pervasives_Native.None in
        let uu___ =
          let uu___1 =
            let uu___2 = FStarC_TypeChecker_NBETerm.embed d cbs x1 in
            FStarC_TypeChecker_NBETerm.as_arg uu___2 in
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_TypeChecker_NBETerm.type_of d in
              FStarC_TypeChecker_NBETerm.as_iarg uu___4 in
            [uu___3] in
          uu___1 :: uu___2 in
        FStarC_TypeChecker_NBETerm.mkFV fv [] uu___ in
  let un uu___1 uu___ =
    (fun cbs t ->
       let uu___ = FStarC_TypeChecker_NBETerm.nbe_t_of_t t in
       match uu___ with
       | FStarC_TypeChecker_NBETerm.FV
           (fv, uu___1, (body, uu___2)::(ty, uu___3)::[]) when
           FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.hide ->
           Obj.magic
             (Obj.repr
                (let uu___4 = FStarC_TypeChecker_NBETerm.unembed d cbs body in
                 FStarC_Class_Monad.op_let_Bang
                   FStarC_Class_Monad.monad_option () () (Obj.magic uu___4)
                   (fun uu___5 ->
                      (fun v ->
                         let v = Obj.magic v in
                         Obj.magic
                           (FStarC_Class_Monad.return
                              FStarC_Class_Monad.monad_option ()
                              (Obj.magic (Hide (ty, v))))) uu___5)))
       | FStarC_TypeChecker_NBETerm.FV
           (fv, uu___1, (body, uu___2)::(ty, uu___3)::[]) when
           FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.reveal ->
           Obj.magic
             (Obj.repr
                (let uu___4 = FStarC_TypeChecker_NBETerm.unembed d cbs body in
                 FStarC_Class_Monad.op_let_Bang
                   FStarC_Class_Monad.monad_option () () (Obj.magic uu___4)
                   (fun uu___5 ->
                      (fun v ->
                         let v = Obj.magic v in
                         Obj.magic
                           (FStarC_Class_Monad.return
                              FStarC_Class_Monad.monad_option ()
                              (Obj.magic (Reveal (ty, v))))) uu___5)))
       | uu___1 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___1
      uu___ in
  FStarC_TypeChecker_NBETerm.mk_emb em un (fun uu___ -> Prims.magic ())
    (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let s_reveal (a : FStarC_Syntax_Embeddings.abstract_term)
  (e :
    (FStarC_Syntax_Syntax.term, FStarC_Syntax_Embeddings.abstract_term)
      emb_erased)
  : FStarC_Syntax_Embeddings.abstract_term FStar_Pervasives_Native.option=
  match e with
  | Hide (uu___, x) -> FStar_Pervasives_Native.Some x
  | uu___ -> FStar_Pervasives_Native.None
let nbe_reveal (a : FStarC_TypeChecker_NBETerm.abstract_nbe_term)
  (e :
    (FStarC_TypeChecker_NBETerm.t,
      FStarC_TypeChecker_NBETerm.abstract_nbe_term) emb_erased)
  :
  FStarC_TypeChecker_NBETerm.abstract_nbe_term FStar_Pervasives_Native.option=
  match e with
  | Hide (uu___, x) -> FStar_Pervasives_Native.Some x
  | uu___ -> FStar_Pervasives_Native.None
let ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk2' Prims.int_one
      FStarC_Parser_Const.reveal FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
      (e_erased FStarC_Syntax_Embeddings.e_abstract_term)
      (nbe_e_erased FStarC_TypeChecker_NBETerm.e_abstract_nbe_term)
      FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term s_reveal nbe_reveal in
  [uu___]
let s_hide (a : FStarC_Syntax_Embeddings.abstract_term)
  (e :
    (FStarC_Syntax_Syntax.term, FStarC_Syntax_Embeddings.abstract_term)
      emb_erased)
  : FStarC_Syntax_Embeddings.abstract_term FStar_Pervasives_Native.option=
  match e with
  | Reveal (a', x) when
      FStarC_Syntax_Util.term_eq
        (FStarC_Syntax_Embeddings.__proj__Abstract__item__t a) a'
      -> FStar_Pervasives_Native.Some x
  | uu___ -> FStar_Pervasives_Native.None
let nbe_hide (a : FStarC_TypeChecker_NBETerm.abstract_nbe_term)
  (e :
    (FStarC_TypeChecker_NBETerm.t,
      FStarC_TypeChecker_NBETerm.abstract_nbe_term) emb_erased)
  :
  FStarC_TypeChecker_NBETerm.abstract_nbe_term FStar_Pervasives_Native.option=
  match e with
  | Reveal (a', x) when
      FStarC_TypeChecker_NBETerm.term_eq
        (FStarC_TypeChecker_NBETerm.__proj__AbstractNBE__item__t a) a'
      -> FStar_Pervasives_Native.Some x
  | uu___ -> FStar_Pervasives_Native.None
let simplify_ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk2' Prims.int_one
      FStarC_Parser_Const.hide FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term
      (e_erased FStarC_Syntax_Embeddings.e_abstract_term)
      (nbe_e_erased FStarC_TypeChecker_NBETerm.e_abstract_nbe_term)
      FStarC_Syntax_Embeddings.e_abstract_term
      FStarC_TypeChecker_NBETerm.e_abstract_nbe_term s_hide nbe_hide in
  [uu___]

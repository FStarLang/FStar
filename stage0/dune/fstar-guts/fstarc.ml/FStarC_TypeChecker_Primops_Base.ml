open Prims
type psc =
  {
  psc_range: FStarC_Range_Type.t ;
  psc_subst: unit -> FStarC_Syntax_Syntax.subst_t }
let __proj__Mkpsc__item__psc_range (projectee : psc) : FStarC_Range_Type.t=
  match projectee with | { psc_range; psc_subst;_} -> psc_range
let __proj__Mkpsc__item__psc_subst (projectee : psc) :
  unit -> FStarC_Syntax_Syntax.subst_t=
  match projectee with | { psc_range; psc_subst;_} -> psc_subst
let null_psc : psc=
  { psc_range = FStarC_Range_Type.dummyRange; psc_subst = (fun uu___ -> []) }
let psc_range (psc1 : psc) : FStarC_Range_Type.t= psc1.psc_range
let psc_subst (psc1 : psc) : FStarC_Syntax_Syntax.subst_t= psc1.psc_subst ()
type interp_t =
  psc ->
    FStarC_Syntax_Embeddings_Base.norm_cb ->
      FStarC_Syntax_Syntax.universes ->
        FStarC_Syntax_Syntax.args ->
          FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
type nbe_interp_t =
  FStarC_TypeChecker_NBETerm.nbe_cbs ->
    FStarC_Syntax_Syntax.universes ->
      FStarC_TypeChecker_NBETerm.args ->
        FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
type primitive_step =
  {
  name: FStarC_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  renorm_after: Prims.bool ;
  interpretation: interp_t ;
  interpretation_nbe: nbe_interp_t }
let __proj__Mkprimitive_step__item__name (projectee : primitive_step) :
  FStarC_Ident.lid=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> name
let __proj__Mkprimitive_step__item__arity (projectee : primitive_step) :
  Prims.int=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> arity
let __proj__Mkprimitive_step__item__univ_arity (projectee : primitive_step) :
  Prims.int=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> univ_arity
let __proj__Mkprimitive_step__item__auto_reflect (projectee : primitive_step)
  : Prims.int FStar_Pervasives_Native.option=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> auto_reflect
let __proj__Mkprimitive_step__item__strong_reduction_ok
  (projectee : primitive_step) : Prims.bool=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> strong_reduction_ok
let __proj__Mkprimitive_step__item__requires_binder_substitution
  (projectee : primitive_step) : Prims.bool=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> requires_binder_substitution
let __proj__Mkprimitive_step__item__renorm_after (projectee : primitive_step)
  : Prims.bool=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> renorm_after
let __proj__Mkprimitive_step__item__interpretation
  (projectee : primitive_step) : interp_t=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> interpretation
let __proj__Mkprimitive_step__item__interpretation_nbe
  (projectee : primitive_step) : nbe_interp_t=
  match projectee with
  | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
      requires_binder_substitution; renorm_after; interpretation;
      interpretation_nbe;_} -> interpretation_nbe
let solve (ev : 'a) : 'a= ev
let as_primitive_step_nbecbs (is_strong : Prims.bool)
  (uu___ :
    (FStarC_Ident.lident * Prims.int * Prims.int * interp_t * nbe_interp_t))
  : primitive_step=
  match uu___ with
  | (l, arity, u_arity, f, f_nbe) ->
      {
        name = l;
        arity;
        univ_arity = u_arity;
        auto_reflect = FStar_Pervasives_Native.None;
        strong_reduction_ok = is_strong;
        requires_binder_substitution = false;
        renorm_after = false;
        interpretation = f;
        interpretation_nbe = f_nbe
      }
let embed_simple (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (r : FStarC_Range_Type.t) (x : 'a) : FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Embeddings_Base.embed uu___ x r FStar_Pervasives_Native.None
    FStarC_Syntax_Embeddings_Base.id_norm_cb
let try_unembed_simple (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (x : FStarC_Syntax_Syntax.term) : 'a FStar_Pervasives_Native.option=
  FStarC_Syntax_Embeddings_Base.try_unembed uu___ x
    FStarC_Syntax_Embeddings_Base.id_norm_cb
let mk_interp1 (uu___2 : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'r FStarC_Syntax_Embeddings_Base.embedding) (uu___ : 'a -> 'r) :
  interp_t=
  (fun uu___ uu___1 f psc1 cb us args ->
     match args with
     | (a1, uu___2)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___3 = try_unembed_simple uu___ a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun a2 ->
                       let a2 = Obj.magic a2 in
                       let uu___4 =
                         let uu___5 = f a2 in
                         embed_simple uu___1 psc1.psc_range uu___5 in
                       Obj.magic
                         (FStarC_Class_Monad.return
                            FStarC_Class_Monad.monad_option ()
                            (Obj.magic uu___4))) uu___4)))
     | uu___2 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")))
    uu___2 uu___1 uu___
let mk_nbe_interp1 (uu___2 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___1 : 'r FStarC_TypeChecker_NBETerm.embedding) (uu___ : 'a -> 'r) :
  nbe_interp_t=
  (fun uu___ uu___1 f cbs us args ->
     match args with
     | (a1, uu___2)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___3 =
                 let uu___4 =
                   FStarC_TypeChecker_NBETerm.unembed (solve uu___) cbs a1 in
                 Obj.magic
                   (FStarC_Class_Monad.op_Less_Dollar_Greater
                      FStarC_Class_Monad.monad_option () ()
                      (fun uu___5 -> (Obj.magic f) uu___5) (Obj.magic uu___4)) in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun r1 ->
                       let r1 = Obj.magic r1 in
                       let uu___4 =
                         FStarC_TypeChecker_NBETerm.embed (solve uu___1) cbs
                           r1 in
                       Obj.magic
                         (FStarC_Class_Monad.return
                            FStarC_Class_Monad.monad_option ()
                            (Obj.magic uu___4))) uu___4)))
     | uu___2 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___2
    uu___1 uu___
let mk_interp2 (uu___3 : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___ : 'a -> 'b -> 'r) : interp_t=
  (fun uu___ uu___1 uu___2 f psc1 cb us args ->
     match args with
     | (a1, uu___3)::(b1, uu___4)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___5 = try_unembed_simple uu___ a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___5)
                 (fun uu___6 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___6 = try_unembed_simple uu___1 b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___6)
                            (fun uu___7 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let r1 = let uu___7 = f a' in uu___7 b' in
                                  let uu___7 =
                                    embed_simple uu___2 psc1.psc_range r1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.return
                                       FStarC_Class_Monad.monad_option ()
                                       (Obj.magic uu___7))) uu___7))) uu___6)))
     | uu___3 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")))
    uu___3 uu___2 uu___1 uu___
let mk_nbe_interp2 (uu___3 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___1 : 'r FStarC_TypeChecker_NBETerm.embedding) (uu___ : 'a -> 'b -> 'r)
  : nbe_interp_t=
  (fun uu___ uu___1 uu___2 f cbs us args ->
     match args with
     | (a1, uu___3)::(b1, uu___4)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___5 =
                 FStarC_TypeChecker_NBETerm.unembed (solve uu___) cbs a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___5)
                 (fun uu___6 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___6 =
                         FStarC_TypeChecker_NBETerm.unembed (solve uu___1)
                           cbs b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___6)
                            (fun uu___7 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let r1 = let uu___7 = f a' in uu___7 b' in
                                  let uu___7 =
                                    FStarC_TypeChecker_NBETerm.embed
                                      (solve uu___2) cbs r1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.return
                                       FStarC_Class_Monad.monad_option ()
                                       (Obj.magic uu___7))) uu___7))) uu___6)))
     | uu___3 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___3
    uu___2 uu___1 uu___
let mk_interp3 (uu___4 : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'r) : interp_t=
  (fun uu___ uu___1 uu___2 uu___3 f psc1 cb us args ->
     match args with
     | (a1, uu___4)::(b1, uu___5)::(c1, uu___6)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___7 = try_unembed_simple uu___ a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___7)
                 (fun uu___8 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___8 = try_unembed_simple uu___1 b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___8)
                            (fun uu___9 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___9 = try_unembed_simple uu___2 c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9)
                                       (fun uu___10 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let r1 =
                                               let uu___10 =
                                                 let uu___11 = f a' in
                                                 uu___11 b' in
                                               uu___10 c' in
                                             let uu___10 =
                                               embed_simple uu___3
                                                 psc1.psc_range r1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.return
                                                  FStarC_Class_Monad.monad_option
                                                  () (Obj.magic uu___10)))
                                            uu___10))) uu___9))) uu___8)))
     | uu___4 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")))
    uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp3 (uu___4 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___1 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'r) : nbe_interp_t=
  (fun uu___ uu___1 uu___2 uu___3 f cbs us args ->
     match args with
     | (a1, uu___4)::(b1, uu___5)::(c1, uu___6)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___7 =
                 FStarC_TypeChecker_NBETerm.unembed (solve uu___) cbs a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___7)
                 (fun uu___8 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___8 =
                         FStarC_TypeChecker_NBETerm.unembed (solve uu___1)
                           cbs b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___8)
                            (fun uu___9 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___9 =
                                    FStarC_TypeChecker_NBETerm.unembed
                                      (solve uu___2) cbs c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9)
                                       (fun uu___10 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let r1 =
                                               let uu___10 =
                                                 let uu___11 = f a' in
                                                 uu___11 b' in
                                               uu___10 c' in
                                             let uu___10 =
                                               FStarC_TypeChecker_NBETerm.embed
                                                 (solve uu___3) cbs r1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.return
                                                  FStarC_Class_Monad.monad_option
                                                  () (Obj.magic uu___10)))
                                            uu___10))) uu___9))) uu___8)))
     | uu___4 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___4
    uu___3 uu___2 uu___1 uu___
let mk_interp4 (uu___5 : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___4 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'd -> 'r) : interp_t=
  (fun uu___ uu___1 uu___2 uu___3 uu___4 f psc1 cb us args ->
     match args with
     | (a1, uu___5)::(b1, uu___6)::(c1, uu___7)::(d1, uu___8)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___9 = try_unembed_simple uu___ a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___9)
                 (fun uu___10 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___10 = try_unembed_simple uu___1 b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___10)
                            (fun uu___11 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___11 = try_unembed_simple uu___2 c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let uu___12 =
                                               try_unembed_simple uu___3 d1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___12)
                                                  (fun uu___13 ->
                                                     (fun d' ->
                                                        let d' = Obj.magic d' in
                                                        let r1 =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                f a' in
                                                              uu___15 b' in
                                                            uu___14 c' in
                                                          uu___13 d' in
                                                        let uu___13 =
                                                          embed_simple uu___4
                                                            psc1.psc_range r1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.return
                                                             FStarC_Class_Monad.monad_option
                                                             ()
                                                             (Obj.magic
                                                                uu___13)))
                                                       uu___13))) uu___12)))
                                 uu___11))) uu___10)))
     | uu___5 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")))
    uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp4 (uu___5 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'd FStarC_TypeChecker_NBETerm.embedding)
  (uu___1 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'd -> 'r) : nbe_interp_t=
  (fun uu___ uu___1 uu___2 uu___3 uu___4 f cbs us args ->
     match args with
     | (a1, uu___5)::(b1, uu___6)::(c1, uu___7)::(d1, uu___8)::[] ->
         Obj.magic
           (Obj.repr
              (let uu___9 =
                 FStarC_TypeChecker_NBETerm.unembed (solve uu___) cbs a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___9)
                 (fun uu___10 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___10 =
                         FStarC_TypeChecker_NBETerm.unembed (solve uu___1)
                           cbs b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___10)
                            (fun uu___11 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___11 =
                                    FStarC_TypeChecker_NBETerm.unembed
                                      (solve uu___2) cbs c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___11)
                                       (fun uu___12 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let uu___12 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 (solve uu___3) cbs d1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___12)
                                                  (fun uu___13 ->
                                                     (fun d' ->
                                                        let d' = Obj.magic d' in
                                                        let r1 =
                                                          let uu___13 =
                                                            let uu___14 =
                                                              let uu___15 =
                                                                f a' in
                                                              uu___15 b' in
                                                            uu___14 c' in
                                                          uu___13 d' in
                                                        let uu___13 =
                                                          FStarC_TypeChecker_NBETerm.embed
                                                            (solve uu___4)
                                                            cbs r1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.return
                                                             FStarC_Class_Monad.monad_option
                                                             ()
                                                             (Obj.magic
                                                                uu___13)))
                                                       uu___13))) uu___12)))
                                 uu___11))) uu___10)))
     | uu___5 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___5
    uu___4 uu___3 uu___2 uu___1 uu___
let mk_interp5 (uu___6 : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___2 : 'e FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'd -> 'e -> 'r) : interp_t=
  (fun uu___ uu___1 uu___2 uu___3 uu___4 uu___5 f psc1 cb us args ->
     match args with
     | (a1, uu___6)::(b1, uu___7)::(c1, uu___8)::(d1, uu___9)::(e1, uu___10)::[]
         ->
         Obj.magic
           (Obj.repr
              (let uu___11 = try_unembed_simple uu___ a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___11)
                 (fun uu___12 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___12 = try_unembed_simple uu___1 b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___12)
                            (fun uu___13 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___13 = try_unembed_simple uu___2 c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___13)
                                       (fun uu___14 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let uu___14 =
                                               try_unembed_simple uu___3 d1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___14)
                                                  (fun uu___15 ->
                                                     (fun d' ->
                                                        let d' = Obj.magic d' in
                                                        let uu___15 =
                                                          try_unembed_simple
                                                            uu___4 e1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (Obj.magic
                                                                uu___15)
                                                             (fun uu___16 ->
                                                                (fun e' ->
                                                                   let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                   let r1 =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    = f a' in
                                                                    uu___19
                                                                    b' in
                                                                    uu___18
                                                                    c' in
                                                                    uu___17
                                                                    d' in
                                                                    uu___16
                                                                    e' in
                                                                   let uu___16
                                                                    =
                                                                    embed_simple
                                                                    uu___5
                                                                    psc1.psc_range
                                                                    r1 in
                                                                   Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___16)))
                                                                  uu___16)))
                                                       uu___15))) uu___14)))
                                 uu___13))) uu___12)))
     | uu___6 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")))
    uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp5 (uu___6 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___5 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___3 : 'd FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'e FStarC_TypeChecker_NBETerm.embedding)
  (uu___1 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (uu___ : 'a -> 'b -> 'c -> 'd -> 'e -> 'r) : nbe_interp_t=
  (fun uu___ uu___1 uu___2 uu___3 uu___4 uu___5 f cbs us args ->
     match args with
     | (a1, uu___6)::(b1, uu___7)::(c1, uu___8)::(d1, uu___9)::(e1, uu___10)::[]
         ->
         Obj.magic
           (Obj.repr
              (let uu___11 =
                 FStarC_TypeChecker_NBETerm.unembed (solve uu___) cbs a1 in
               FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                 () () (Obj.magic uu___11)
                 (fun uu___12 ->
                    (fun a' ->
                       let a' = Obj.magic a' in
                       let uu___12 =
                         FStarC_TypeChecker_NBETerm.unembed (solve uu___1)
                           cbs b1 in
                       Obj.magic
                         (FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___12)
                            (fun uu___13 ->
                               (fun b' ->
                                  let b' = Obj.magic b' in
                                  let uu___13 =
                                    FStarC_TypeChecker_NBETerm.unembed
                                      (solve uu___2) cbs c1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___13)
                                       (fun uu___14 ->
                                          (fun c' ->
                                             let c' = Obj.magic c' in
                                             let uu___14 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 (solve uu___3) cbs d1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___14)
                                                  (fun uu___15 ->
                                                     (fun d' ->
                                                        let d' = Obj.magic d' in
                                                        let uu___15 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            (solve uu___4)
                                                            cbs e1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_let_Bang
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (Obj.magic
                                                                uu___15)
                                                             (fun uu___16 ->
                                                                (fun e' ->
                                                                   let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                   let r1 =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    = f a' in
                                                                    uu___19
                                                                    b' in
                                                                    uu___18
                                                                    c' in
                                                                    uu___17
                                                                    d' in
                                                                    uu___16
                                                                    e' in
                                                                   let uu___16
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___5)
                                                                    cbs r1 in
                                                                   Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___16)))
                                                                  uu___16)))
                                                       uu___15))) uu___14)))
                                 uu___13))) uu___12)))
     | uu___6 -> Obj.magic (Obj.repr FStar_Pervasives_Native.None)) uu___6
    uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk1 (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'r FStarC_TypeChecker_NBETerm.embedding) (f : 'a -> 'r) :
  primitive_step=
  let interp = mk_interp1 uu___ uu___2 f in
  let nbe_interp = mk_nbe_interp1 uu___1 uu___3 f in
  as_primitive_step_nbecbs true
    (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk2 (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'r FStarC_TypeChecker_NBETerm.embedding) (f : 'a -> 'b -> 'r) :
  primitive_step=
  let interp = mk_interp2 uu___ uu___2 uu___4 f in
  let nbe_interp = mk_nbe_interp2 uu___1 uu___3 uu___5 f in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (2)), u_arity, interp, nbe_interp)
let mk3 (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'r) : primitive_step=
  let interp = mk_interp3 uu___ uu___2 uu___4 uu___6 f in
  let nbe_interp = mk_nbe_interp3 uu___1 uu___3 uu___5 uu___7 f in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (3)), u_arity, interp, nbe_interp)
let mk4 (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'd FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___9 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'd -> 'r) : primitive_step=
  let interp = mk_interp4 uu___ uu___2 uu___4 uu___6 uu___8 f in
  let nbe_interp = mk_nbe_interp4 uu___1 uu___3 uu___5 uu___7 uu___9 f in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (4)), u_arity, interp, nbe_interp)
let mk5 (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'a FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'b FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'c FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'd FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'e FStarC_Syntax_Embeddings_Base.embedding)
  (uu___9 : 'e FStarC_TypeChecker_NBETerm.embedding)
  (uu___10 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___11 : 'r FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'd -> 'e -> 'r) : primitive_step=
  let interp = mk_interp5 uu___ uu___2 uu___4 uu___6 uu___8 uu___10 f in
  let nbe_interp =
    mk_nbe_interp5 uu___1 uu___3 uu___5 uu___7 uu___9 uu___11 f in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (5)), u_arity, interp, nbe_interp)
let mk1' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'r FStar_Pervasives_Native.option)
  (nbe_f : 'na -> 'nr FStar_Pervasives_Native.option) : primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___4)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___5 =
                let uu___6 = try_unembed_simple uu___ a1 in
                Obj.magic
                  (FStarC_Class_Monad.op_Less_Dollar_Greater
                     FStarC_Class_Monad.monad_option () ()
                     (fun uu___7 -> (Obj.magic f) uu___7) (Obj.magic uu___6)) in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___5)
                (fun uu___6 ->
                   (fun r1 ->
                      let r1 = Obj.magic r1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic r1)
                           (fun uu___6 ->
                              (fun r2 ->
                                 let r2 = Obj.magic r2 in
                                 let uu___6 =
                                   embed_simple uu___2 psc1.psc_range r2 in
                                 Obj.magic
                                   (FStarC_Class_Monad.return
                                      FStarC_Class_Monad.monad_option ()
                                      (Obj.magic uu___6))) uu___6))) uu___6)))
    | uu___4 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___4)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___5 =
                let uu___6 =
                  FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
                Obj.magic
                  (FStarC_Class_Monad.op_Less_Dollar_Greater
                     FStarC_Class_Monad.monad_option () ()
                     (fun uu___7 -> (Obj.magic nbe_f) uu___7)
                     (Obj.magic uu___6)) in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___5)
                (fun uu___6 ->
                   (fun r1 ->
                      let r1 = Obj.magic r1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic r1)
                           (fun uu___6 ->
                              (fun r2 ->
                                 let r2 = Obj.magic r2 in
                                 let uu___6 =
                                   FStarC_TypeChecker_NBETerm.embed
                                     (solve uu___3) cbs r2 in
                                 Obj.magic
                                   (FStarC_Class_Monad.return
                                      FStarC_Class_Monad.monad_option ()
                                      (Obj.magic uu___6))) uu___6))) uu___6)))
    | uu___4 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk1_psc' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : psc -> 'a -> 'r FStar_Pervasives_Native.option)
  (nbe_f : psc -> 'na -> 'nr FStar_Pervasives_Native.option) :
  primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___4)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___5 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___5)
                (fun uu___6 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___6 = let uu___7 = f psc1 in uu___7 a' in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___6)
                           (fun uu___7 ->
                              (fun r1 ->
                                 let r1 = Obj.magic r1 in
                                 let uu___7 =
                                   embed_simple uu___2 psc1.psc_range r1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.return
                                      FStarC_Class_Monad.monad_option ()
                                      (Obj.magic uu___7))) uu___7))) uu___6)))
    | uu___4 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___4)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___5 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___5)
                (fun uu___6 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___6 = let uu___7 = nbe_f null_psc in uu___7 a' in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___6)
                           (fun uu___7 ->
                              (fun r1 ->
                                 let r1 = Obj.magic r1 in
                                 let uu___7 =
                                   FStarC_TypeChecker_NBETerm.embed
                                     (solve uu___3) cbs r1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.return
                                      FStarC_Class_Monad.monad_option ()
                                      (Obj.magic uu___7))) uu___7))) uu___6)))
    | uu___4 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk2' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nb FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'r FStar_Pervasives_Native.option)
  (nbe_f : 'na -> 'nb -> 'nr FStar_Pervasives_Native.option) :
  primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___6)::(b1, uu___7)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___8 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___8)
                (fun uu___9 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___9 = try_unembed_simple uu___2 b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___9)
                           (fun uu___10 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___10 =
                                   let uu___11 = f a' in uu___11 b' in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___10)
                                      (fun uu___11 ->
                                         (fun r1 ->
                                            let r1 = Obj.magic r1 in
                                            let uu___11 =
                                              embed_simple uu___4
                                                psc1.psc_range r1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.return
                                                 FStarC_Class_Monad.monad_option
                                                 () (Obj.magic uu___11)))
                                           uu___11))) uu___10))) uu___9)))
    | uu___6 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___6)::(b1, uu___7)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___8 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___8)
                (fun uu___9 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___9 =
                        FStarC_TypeChecker_NBETerm.unembed (solve uu___3) cbs
                          b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___9)
                           (fun uu___10 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___10 =
                                   let uu___11 = nbe_f a' in uu___11 b' in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___10)
                                      (fun uu___11 ->
                                         (fun r1 ->
                                            let r1 = Obj.magic r1 in
                                            let uu___11 =
                                              FStarC_TypeChecker_NBETerm.embed
                                                (solve uu___5) cbs r1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.return
                                                 FStarC_Class_Monad.monad_option
                                                 () (Obj.magic uu___11)))
                                           uu___11))) uu___10))) uu___9)))
    | uu___6 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (2)), u_arity, interp, nbe_interp)
let mk3' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nb FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nc FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'r FStar_Pervasives_Native.option)
  (nbe_f : 'na -> 'nb -> 'nc -> 'nr FStar_Pervasives_Native.option) :
  primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___11 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___11)
                (fun uu___12 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___12 = try_unembed_simple uu___2 b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___12)
                           (fun uu___13 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___13 = try_unembed_simple uu___4 c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___13)
                                      (fun uu___14 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___14 =
                                              let uu___15 =
                                                let uu___16 = f a' in
                                                uu___16 b' in
                                              uu___15 c' in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    (fun r1 ->
                                                       let r1 = Obj.magic r1 in
                                                       let uu___15 =
                                                         embed_simple uu___6
                                                           psc1.psc_range r1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.return
                                                            FStarC_Class_Monad.monad_option
                                                            ()
                                                            (Obj.magic
                                                               uu___15)))
                                                      uu___15))) uu___14)))
                                uu___13))) uu___12)))
    | uu___8 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___11 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___11)
                (fun uu___12 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___12 =
                        FStarC_TypeChecker_NBETerm.unembed (solve uu___3) cbs
                          b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___12)
                           (fun uu___13 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___13 =
                                   FStarC_TypeChecker_NBETerm.unembed
                                     (solve uu___5) cbs c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___13)
                                      (fun uu___14 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___14 =
                                              let uu___15 =
                                                let uu___16 = nbe_f a' in
                                                uu___16 b' in
                                              uu___15 c' in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___14)
                                                 (fun uu___15 ->
                                                    (fun r1 ->
                                                       let r1 = Obj.magic r1 in
                                                       let uu___15 =
                                                         FStarC_TypeChecker_NBETerm.embed
                                                           (solve uu___7) cbs
                                                           r1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.return
                                                            FStarC_Class_Monad.monad_option
                                                            ()
                                                            (Obj.magic
                                                               uu___15)))
                                                      uu___15))) uu___14)))
                                uu___13))) uu___12)))
    | uu___8 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (3)), u_arity, interp, nbe_interp)
let mk4' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nb FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nc FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'nd FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___9 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'd -> 'r FStar_Pervasives_Native.option)
  (nbe_f : 'na -> 'nb -> 'nc -> 'nd -> 'nr FStar_Pervasives_Native.option) :
  primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___10)::(b1, uu___11)::(c1, uu___12)::(d1, uu___13)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___14 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___14)
                (fun uu___15 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___15 = try_unembed_simple uu___2 b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___15)
                           (fun uu___16 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___16 = try_unembed_simple uu___4 c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___16)
                                      (fun uu___17 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___17 =
                                              try_unembed_simple uu___6 d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___17)
                                                 (fun uu___18 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___18 =
                                                         let uu___19 =
                                                           let uu___20 =
                                                             let uu___21 =
                                                               f a' in
                                                             uu___21 b' in
                                                           uu___20 c' in
                                                         uu___19 d' in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___18)
                                                            (fun uu___19 ->
                                                               (fun r1 ->
                                                                  let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                  let uu___19
                                                                    =
                                                                    embed_simple
                                                                    uu___8
                                                                    psc1.psc_range
                                                                    r1 in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___19)))
                                                                 uu___19)))
                                                      uu___18))) uu___17)))
                                uu___16))) uu___15)))
    | uu___10 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___10)::(b1, uu___11)::(c1, uu___12)::(d1, uu___13)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___14 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___14)
                (fun uu___15 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___15 =
                        FStarC_TypeChecker_NBETerm.unembed (solve uu___3) cbs
                          b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___15)
                           (fun uu___16 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___16 =
                                   FStarC_TypeChecker_NBETerm.unembed
                                     (solve uu___5) cbs c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___16)
                                      (fun uu___17 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___17 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                (solve uu___7) cbs d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___17)
                                                 (fun uu___18 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___18 =
                                                         let uu___19 =
                                                           let uu___20 =
                                                             let uu___21 =
                                                               nbe_f a' in
                                                             uu___21 b' in
                                                           uu___20 c' in
                                                         uu___19 d' in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___18)
                                                            (fun uu___19 ->
                                                               (fun r1 ->
                                                                  let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                  let uu___19
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___9)
                                                                    cbs r1 in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___19)))
                                                                 uu___19)))
                                                      uu___18))) uu___17)))
                                uu___16))) uu___15)))
    | uu___10 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (4)), u_arity, interp, nbe_interp)
let mk5' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nb FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nc FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'nd FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'e FStarC_Syntax_Embeddings_Base.embedding)
  (uu___9 : 'ne FStarC_TypeChecker_NBETerm.embedding)
  (uu___10 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___11 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (f : 'a -> 'b -> 'c -> 'd -> 'e -> 'r FStar_Pervasives_Native.option)
  (nbe_f :
    'na -> 'nb -> 'nc -> 'nd -> 'ne -> 'nr FStar_Pervasives_Native.option)
  : primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___12)::(b1, uu___13)::(c1, uu___14)::(d1, uu___15)::(e1,
                                                                   uu___16)::[]
        ->
        Obj.magic
          (Obj.repr
             (let uu___17 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___17)
                (fun uu___18 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___18 = try_unembed_simple uu___2 b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___18)
                           (fun uu___19 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___19 = try_unembed_simple uu___4 c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___19)
                                      (fun uu___20 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___20 =
                                              try_unembed_simple uu___6 d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___20)
                                                 (fun uu___21 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___21 =
                                                         try_unembed_simple
                                                           uu___8 e1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___21)
                                                            (fun uu___22 ->
                                                               (fun e' ->
                                                                  let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                  let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    = f a' in
                                                                    uu___26
                                                                    b' in
                                                                    uu___25
                                                                    c' in
                                                                    uu___24
                                                                    d' in
                                                                    uu___23
                                                                    e' in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun r1
                                                                    ->
                                                                    let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                    let uu___23
                                                                    =
                                                                    embed_simple
                                                                    uu___10
                                                                    psc1.psc_range
                                                                    r1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___23)))
                                                                    uu___23)))
                                                                 uu___22)))
                                                      uu___21))) uu___20)))
                                uu___19))) uu___18)))
    | uu___12 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___12)::(b1, uu___13)::(c1, uu___14)::(d1, uu___15)::(e1,
                                                                   uu___16)::[]
        ->
        Obj.magic
          (Obj.repr
             (let uu___17 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___17)
                (fun uu___18 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___18 =
                        FStarC_TypeChecker_NBETerm.unembed (solve uu___3) cbs
                          b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___18)
                           (fun uu___19 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___19 =
                                   FStarC_TypeChecker_NBETerm.unembed
                                     (solve uu___5) cbs c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___19)
                                      (fun uu___20 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___20 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                (solve uu___7) cbs d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___20)
                                                 (fun uu___21 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___21 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           (solve uu___9) cbs
                                                           e1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___21)
                                                            (fun uu___22 ->
                                                               (fun e' ->
                                                                  let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                  let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    nbe_f a' in
                                                                    uu___26
                                                                    b' in
                                                                    uu___25
                                                                    c' in
                                                                    uu___24
                                                                    d' in
                                                                    uu___23
                                                                    e' in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    (fun r1
                                                                    ->
                                                                    let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                    let uu___23
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___11)
                                                                    cbs r1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___23)))
                                                                    uu___23)))
                                                                 uu___22)))
                                                      uu___21))) uu___20)))
                                uu___19))) uu___18)))
    | uu___12 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (5)), u_arity, interp, nbe_interp)
let mk6' (u_arity : Prims.int) (name : FStarC_Ident.lid)
  (uu___ : 'a FStarC_Syntax_Embeddings_Base.embedding)
  (uu___1 : 'na FStarC_TypeChecker_NBETerm.embedding)
  (uu___2 : 'b FStarC_Syntax_Embeddings_Base.embedding)
  (uu___3 : 'nb FStarC_TypeChecker_NBETerm.embedding)
  (uu___4 : 'c FStarC_Syntax_Embeddings_Base.embedding)
  (uu___5 : 'nc FStarC_TypeChecker_NBETerm.embedding)
  (uu___6 : 'd FStarC_Syntax_Embeddings_Base.embedding)
  (uu___7 : 'nd FStarC_TypeChecker_NBETerm.embedding)
  (uu___8 : 'e FStarC_Syntax_Embeddings_Base.embedding)
  (uu___9 : 'ne FStarC_TypeChecker_NBETerm.embedding)
  (uu___10 : 'f FStarC_Syntax_Embeddings_Base.embedding)
  (uu___11 : 'nf FStarC_TypeChecker_NBETerm.embedding)
  (uu___12 : 'r FStarC_Syntax_Embeddings_Base.embedding)
  (uu___13 : 'nr FStarC_TypeChecker_NBETerm.embedding)
  (ff :
    'a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'r FStar_Pervasives_Native.option)
  (nbe_ff :
    'na ->
      'nb -> 'nc -> 'nd -> 'ne -> 'nf -> 'nr FStar_Pervasives_Native.option)
  : primitive_step=
  let interp psc1 cb us args =
    match args with
    | (a1, uu___14)::(b1, uu___15)::(c1, uu___16)::(d1, uu___17)::(e1,
                                                                   uu___18)::
        (f1, uu___19)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___20 = try_unembed_simple uu___ a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___20)
                (fun uu___21 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___21 = try_unembed_simple uu___2 b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___21)
                           (fun uu___22 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___22 = try_unembed_simple uu___4 c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___22)
                                      (fun uu___23 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___23 =
                                              try_unembed_simple uu___6 d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___23)
                                                 (fun uu___24 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___24 =
                                                         try_unembed_simple
                                                           uu___8 e1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___24)
                                                            (fun uu___25 ->
                                                               (fun e' ->
                                                                  let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                  let uu___25
                                                                    =
                                                                    try_unembed_simple
                                                                    uu___10
                                                                    f1 in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun f'
                                                                    ->
                                                                    let f' =
                                                                    Obj.magic
                                                                    f' in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    = ff a' in
                                                                    uu___31
                                                                    b' in
                                                                    uu___30
                                                                    c' in
                                                                    uu___29
                                                                    d' in
                                                                    uu___28
                                                                    e' in
                                                                    uu___27
                                                                    f' in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun r1
                                                                    ->
                                                                    let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                    let uu___27
                                                                    =
                                                                    embed_simple
                                                                    uu___12
                                                                    psc1.psc_range
                                                                    r1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___27)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                 uu___25)))
                                                      uu___24))) uu___23)))
                                uu___22))) uu___21)))
    | uu___14 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  let nbe_interp cbs us args =
    match args with
    | (a1, uu___14)::(b1, uu___15)::(c1, uu___16)::(d1, uu___17)::(e1,
                                                                   uu___18)::
        (f1, uu___19)::[] ->
        Obj.magic
          (Obj.repr
             (let uu___20 =
                FStarC_TypeChecker_NBETerm.unembed (solve uu___1) cbs a1 in
              FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option
                () () (Obj.magic uu___20)
                (fun uu___21 ->
                   (fun a' ->
                      let a' = Obj.magic a' in
                      let uu___21 =
                        FStarC_TypeChecker_NBETerm.unembed (solve uu___3) cbs
                          b1 in
                      Obj.magic
                        (FStarC_Class_Monad.op_let_Bang
                           FStarC_Class_Monad.monad_option () ()
                           (Obj.magic uu___21)
                           (fun uu___22 ->
                              (fun b' ->
                                 let b' = Obj.magic b' in
                                 let uu___22 =
                                   FStarC_TypeChecker_NBETerm.unembed
                                     (solve uu___5) cbs c1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      FStarC_Class_Monad.monad_option () ()
                                      (Obj.magic uu___22)
                                      (fun uu___23 ->
                                         (fun c' ->
                                            let c' = Obj.magic c' in
                                            let uu___23 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                (solve uu___7) cbs d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___23)
                                                 (fun uu___24 ->
                                                    (fun d' ->
                                                       let d' = Obj.magic d' in
                                                       let uu___24 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           (solve uu___9) cbs
                                                           e1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_let_Bang
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___24)
                                                            (fun uu___25 ->
                                                               (fun e' ->
                                                                  let e' =
                                                                    Obj.magic
                                                                    e' in
                                                                  let uu___25
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.unembed
                                                                    (solve
                                                                    uu___11)
                                                                    cbs f1 in
                                                                  Obj.magic
                                                                    (
                                                                    FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    (fun f'
                                                                    ->
                                                                    let f' =
                                                                    Obj.magic
                                                                    f' in
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    let uu___29
                                                                    =
                                                                    let uu___30
                                                                    =
                                                                    let uu___31
                                                                    =
                                                                    nbe_ff a' in
                                                                    uu___31
                                                                    b' in
                                                                    uu___30
                                                                    c' in
                                                                    uu___29
                                                                    d' in
                                                                    uu___28
                                                                    e' in
                                                                    uu___27
                                                                    f' in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    (fun r1
                                                                    ->
                                                                    let r1 =
                                                                    Obj.magic
                                                                    r1 in
                                                                    let uu___27
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___13)
                                                                    cbs r1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___27)))
                                                                    uu___27)))
                                                                    uu___26)))
                                                                 uu___25)))
                                                      uu___24))) uu___23)))
                                uu___22))) uu___21)))
    | uu___14 -> Obj.magic (Obj.repr (FStarC_Effect.failwith "arity")) in
  as_primitive_step_nbecbs true
    (name, (Prims.of_int (6)), u_arity, interp, nbe_interp)

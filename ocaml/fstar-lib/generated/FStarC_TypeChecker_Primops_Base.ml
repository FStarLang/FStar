open Prims
type psc =
  {
  psc_range: FStarC_Compiler_Range_Type.range ;
  psc_subst: unit -> FStarC_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range :
  psc -> FStarC_Compiler_Range_Type.range) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStarC_Syntax_Syntax.subst_t) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
let (null_psc : psc) =
  {
    psc_range = FStarC_Compiler_Range_Type.dummyRange;
    psc_subst = (fun uu___ -> [])
  }
let (psc_range : psc -> FStarC_Compiler_Range_Type.range) =
  fun psc1 -> psc1.psc_range
let (psc_subst : psc -> FStarC_Syntax_Syntax.subst_t) =
  fun psc1 -> psc1.psc_subst ()
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
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStarC_Ident.lid) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> name
let (__proj__Mkprimitive_step__item__arity : primitive_step -> Prims.int) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> arity
let (__proj__Mkprimitive_step__item__univ_arity :
  primitive_step -> Prims.int) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> univ_arity
let (__proj__Mkprimitive_step__item__auto_reflect :
  primitive_step -> Prims.int FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> auto_reflect
let (__proj__Mkprimitive_step__item__strong_reduction_ok :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> strong_reduction_ok
let (__proj__Mkprimitive_step__item__requires_binder_substitution :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> requires_binder_substitution
let (__proj__Mkprimitive_step__item__renorm_after :
  primitive_step -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> renorm_after
let (__proj__Mkprimitive_step__item__interpretation :
  primitive_step -> interp_t) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> interpretation
let (__proj__Mkprimitive_step__item__interpretation_nbe :
  primitive_step -> nbe_interp_t) =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> interpretation_nbe
let embed_simple :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Compiler_Range_Type.range -> 'a -> FStarC_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        let uu___1 = FStarC_Syntax_Embeddings_Base.embed uu___ x in
        uu___1 r FStar_Pervasives_Native.None
          FStarC_Syntax_Embeddings_Base.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStarC_Syntax_Embeddings_Base.try_unembed uu___ x
        FStarC_Syntax_Embeddings_Base.id_norm_cb
let solve : 'a . 'a -> 'a = fun ev -> ev
let (as_primitive_step_nbecbs :
  Prims.bool ->
    (FStarC_Ident.lident * Prims.int * Prims.int * interp_t * nbe_interp_t)
      -> primitive_step)
  =
  fun is_strong ->
    fun uu___ ->
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
let mk_interp1 :
  'a 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'r FStarC_Syntax_Embeddings_Base.embedding -> ('a -> 'r) -> interp_t
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           fun uu___1 ->
             fun f ->
               fun psc1 ->
                 fun cb ->
                   fun us ->
                     fun args ->
                       match args with
                       | (a1, uu___2)::[] ->
                           Obj.magic
                             (Obj.repr
                                (let uu___3 = try_unembed_simple uu___ a1 in
                                 FStarC_Class_Monad.op_let_Bang
                                   FStarC_Class_Monad.monad_option () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun a2 ->
                                         let a2 = Obj.magic a2 in
                                         let uu___4 =
                                           let uu___5 = f a2 in
                                           embed_simple uu___1 psc1.psc_range
                                             uu___5 in
                                         Obj.magic
                                           (FStarC_Class_Monad.return
                                              FStarC_Class_Monad.monad_option
                                              () (Obj.magic uu___4))) uu___4)))
                       | uu___2 -> Obj.magic (Obj.repr (failwith "arity")))
          uu___2 uu___1 uu___
let mk_nbe_interp1 :
  'a 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'r FStarC_TypeChecker_NBETerm.embedding -> ('a -> 'r) -> nbe_interp_t
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun uu___ ->
           fun uu___1 ->
             fun f ->
               fun cbs ->
                 fun us ->
                   fun args ->
                     match args with
                     | (a1, uu___2)::[] ->
                         Obj.magic
                           (Obj.repr
                              (let uu___3 =
                                 let uu___4 =
                                   FStarC_TypeChecker_NBETerm.unembed
                                     (solve uu___) cbs a1 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_Less_Dollar_Greater
                                      FStarC_Class_Monad.monad_option () ()
                                      (fun uu___5 -> (Obj.magic f) uu___5)
                                      (Obj.magic uu___4)) in
                               FStarC_Class_Monad.op_let_Bang
                                 FStarC_Class_Monad.monad_option () ()
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun r1 ->
                                       let r1 = Obj.magic r1 in
                                       let uu___4 =
                                         FStarC_TypeChecker_NBETerm.embed
                                           (solve uu___1) cbs r1 in
                                       Obj.magic
                                         (FStarC_Class_Monad.return
                                            FStarC_Class_Monad.monad_option
                                            () (Obj.magic uu___4))) uu___4)))
                     | uu___2 ->
                         Obj.magic (Obj.repr FStar_Pervasives_Native.None))
          uu___2 uu___1 uu___
let mk_interp2 :
  'a 'b 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'r FStarC_Syntax_Embeddings_Base.embedding ->
          ('a -> 'b -> 'r) -> interp_t
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun uu___ ->
             fun uu___1 ->
               fun uu___2 ->
                 fun f ->
                   fun psc1 ->
                     fun cb ->
                       fun us ->
                         fun args ->
                           match args with
                           | (a1, uu___3)::(b1, uu___4)::[] ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 =
                                       let uu___6 =
                                         let uu___7 =
                                           try_unembed_simple uu___ a1 in
                                         Obj.magic
                                           (FStarC_Class_Monad.op_Less_Dollar_Greater
                                              FStarC_Class_Monad.monad_option
                                              () ()
                                              (fun uu___8 ->
                                                 (Obj.magic f) uu___8)
                                              (Obj.magic uu___7)) in
                                       let uu___7 =
                                         try_unembed_simple uu___1 b1 in
                                       Obj.magic
                                         (FStarC_Class_Monad.op_Less_Star_Greater
                                            FStarC_Class_Monad.monad_option
                                            () () (Obj.magic uu___6)
                                            (Obj.magic uu___7)) in
                                     FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun r1 ->
                                             let r1 = Obj.magic r1 in
                                             let uu___6 =
                                               embed_simple uu___2
                                                 psc1.psc_range r1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.return
                                                  FStarC_Class_Monad.monad_option
                                                  () (Obj.magic uu___6)))
                                            uu___6)))
                           | uu___3 ->
                               Obj.magic (Obj.repr (failwith "arity")))
            uu___3 uu___2 uu___1 uu___
let mk_nbe_interp2 :
  'a 'b 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'b FStarC_TypeChecker_NBETerm.embedding ->
        'r FStarC_TypeChecker_NBETerm.embedding ->
          ('a -> 'b -> 'r) -> nbe_interp_t
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun uu___ ->
             fun uu___1 ->
               fun uu___2 ->
                 fun f ->
                   fun cbs ->
                     fun us ->
                       fun args ->
                         match args with
                         | (a1, uu___3)::(b1, uu___4)::[] ->
                             Obj.magic
                               (Obj.repr
                                  (let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStarC_TypeChecker_NBETerm.unembed
                                           (solve uu___) cbs a1 in
                                       Obj.magic
                                         (FStarC_Class_Monad.op_Less_Dollar_Greater
                                            FStarC_Class_Monad.monad_option
                                            () ()
                                            (fun uu___8 ->
                                               (Obj.magic f) uu___8)
                                            (Obj.magic uu___7)) in
                                     let uu___7 =
                                       FStarC_TypeChecker_NBETerm.unembed
                                         (solve uu___1) cbs b1 in
                                     Obj.magic
                                       (FStarC_Class_Monad.op_Less_Star_Greater
                                          FStarC_Class_Monad.monad_option ()
                                          () (Obj.magic uu___6)
                                          (Obj.magic uu___7)) in
                                   FStarC_Class_Monad.op_let_Bang
                                     FStarC_Class_Monad.monad_option () ()
                                     (Obj.magic uu___5)
                                     (fun uu___6 ->
                                        (fun r1 ->
                                           let r1 = Obj.magic r1 in
                                           let uu___6 =
                                             FStarC_TypeChecker_NBETerm.embed
                                               (solve uu___2) cbs r1 in
                                           Obj.magic
                                             (FStarC_Class_Monad.return
                                                FStarC_Class_Monad.monad_option
                                                () (Obj.magic uu___6)))
                                          uu___6)))
                         | uu___3 ->
                             Obj.magic
                               (Obj.repr FStar_Pervasives_Native.None))
            uu___3 uu___2 uu___1 uu___
let mk_interp3 :
  'a 'b 'c 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'r FStarC_Syntax_Embeddings_Base.embedding ->
            ('a -> 'b -> 'c -> 'r) -> interp_t
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun uu___ ->
               fun uu___1 ->
                 fun uu___2 ->
                   fun uu___3 ->
                     fun f ->
                       fun psc1 ->
                         fun cb ->
                           fun us ->
                             fun args ->
                               match args with
                               | (a1, uu___4)::(b1, uu___5)::(c1, uu___6)::[]
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___7 =
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 try_unembed_simple uu___ a1 in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                    FStarC_Class_Monad.monad_option
                                                    () ()
                                                    (fun uu___11 ->
                                                       (Obj.magic f) uu___11)
                                                    (Obj.magic uu___10)) in
                                             let uu___10 =
                                               try_unembed_simple uu___1 b1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_Less_Star_Greater
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___9)
                                                  (Obj.magic uu___10)) in
                                           let uu___9 =
                                             try_unembed_simple uu___2 c1 in
                                           Obj.magic
                                             (FStarC_Class_Monad.op_Less_Star_Greater
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___8)
                                                (Obj.magic uu___9)) in
                                         FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic uu___7)
                                           (fun uu___8 ->
                                              (fun r1 ->
                                                 let r1 = Obj.magic r1 in
                                                 let uu___8 =
                                                   embed_simple uu___3
                                                     psc1.psc_range r1 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Class_Monad.monad_option
                                                      () (Obj.magic uu___8)))
                                                uu___8)))
                               | uu___4 ->
                                   Obj.magic (Obj.repr (failwith "arity")))
              uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp3 :
  'a 'b 'c 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'b FStarC_TypeChecker_NBETerm.embedding ->
        'c FStarC_TypeChecker_NBETerm.embedding ->
          'r FStarC_TypeChecker_NBETerm.embedding ->
            ('a -> 'b -> 'c -> 'r) -> nbe_interp_t
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun uu___ ->
               fun uu___1 ->
                 fun uu___2 ->
                   fun uu___3 ->
                     fun f ->
                       fun cbs ->
                         fun us ->
                           fun args ->
                             match args with
                             | (a1, uu___4)::(b1, uu___5)::(c1, uu___6)::[]
                                 ->
                                 Obj.magic
                                   (Obj.repr
                                      (let uu___7 =
                                         let uu___8 =
                                           let uu___9 =
                                             let uu___10 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 (solve uu___) cbs a1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                  FStarC_Class_Monad.monad_option
                                                  () ()
                                                  (fun uu___11 ->
                                                     (Obj.magic f) uu___11)
                                                  (Obj.magic uu___10)) in
                                           let uu___10 =
                                             FStarC_TypeChecker_NBETerm.unembed
                                               (solve uu___1) cbs b1 in
                                           Obj.magic
                                             (FStarC_Class_Monad.op_Less_Star_Greater
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___9)
                                                (Obj.magic uu___10)) in
                                         let uu___9 =
                                           FStarC_TypeChecker_NBETerm.unembed
                                             (solve uu___2) cbs c1 in
                                         Obj.magic
                                           (FStarC_Class_Monad.op_Less_Star_Greater
                                              FStarC_Class_Monad.monad_option
                                              () () (Obj.magic uu___8)
                                              (Obj.magic uu___9)) in
                                       FStarC_Class_Monad.op_let_Bang
                                         FStarC_Class_Monad.monad_option ()
                                         () (Obj.magic uu___7)
                                         (fun uu___8 ->
                                            (fun r1 ->
                                               let r1 = Obj.magic r1 in
                                               let uu___8 =
                                                 FStarC_TypeChecker_NBETerm.embed
                                                   (solve uu___3) cbs r1 in
                                               Obj.magic
                                                 (FStarC_Class_Monad.return
                                                    FStarC_Class_Monad.monad_option
                                                    () (Obj.magic uu___8)))
                                              uu___8)))
                             | uu___4 ->
                                 Obj.magic
                                   (Obj.repr FStar_Pervasives_Native.None))
              uu___4 uu___3 uu___2 uu___1 uu___
let mk_interp4 :
  'a 'b 'c 'd 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'd FStarC_Syntax_Embeddings_Base.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              ('a -> 'b -> 'c -> 'd -> 'r) -> interp_t
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun uu___ ->
                 fun uu___1 ->
                   fun uu___2 ->
                     fun uu___3 ->
                       fun uu___4 ->
                         fun f ->
                           fun psc1 ->
                             fun cb ->
                               fun us ->
                                 fun args ->
                                   match args with
                                   | (a1, uu___5)::(b1, uu___6)::(c1, uu___7)::
                                       (d1, uu___8)::[] ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       try_unembed_simple
                                                         uu___ a1 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                          FStarC_Class_Monad.monad_option
                                                          () ()
                                                          (fun uu___14 ->
                                                             (Obj.magic f)
                                                               uu___14)
                                                          (Obj.magic uu___13)) in
                                                   let uu___13 =
                                                     try_unembed_simple
                                                       uu___1 b1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_Less_Star_Greater
                                                        FStarC_Class_Monad.monad_option
                                                        () ()
                                                        (Obj.magic uu___12)
                                                        (Obj.magic uu___13)) in
                                                 let uu___12 =
                                                   try_unembed_simple uu___2
                                                     c1 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.op_Less_Star_Greater
                                                      FStarC_Class_Monad.monad_option
                                                      () ()
                                                      (Obj.magic uu___11)
                                                      (Obj.magic uu___12)) in
                                               let uu___11 =
                                                 try_unembed_simple uu___3 d1 in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_Less_Star_Greater
                                                    FStarC_Class_Monad.monad_option
                                                    () () (Obj.magic uu___10)
                                                    (Obj.magic uu___11)) in
                                             FStarC_Class_Monad.op_let_Bang
                                               FStarC_Class_Monad.monad_option
                                               () () (Obj.magic uu___9)
                                               (fun uu___10 ->
                                                  (fun r1 ->
                                                     let r1 = Obj.magic r1 in
                                                     let uu___10 =
                                                       embed_simple uu___4
                                                         psc1.psc_range r1 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.return
                                                          FStarC_Class_Monad.monad_option
                                                          ()
                                                          (Obj.magic uu___10)))
                                                    uu___10)))
                                   | uu___5 ->
                                       Obj.magic
                                         (Obj.repr (failwith "arity")))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp4 :
  'a 'b 'c 'd 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'b FStarC_TypeChecker_NBETerm.embedding ->
        'c FStarC_TypeChecker_NBETerm.embedding ->
          'd FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_TypeChecker_NBETerm.embedding ->
              ('a -> 'b -> 'c -> 'd -> 'r) -> nbe_interp_t
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun uu___ ->
                 fun uu___1 ->
                   fun uu___2 ->
                     fun uu___3 ->
                       fun uu___4 ->
                         fun f ->
                           fun cbs ->
                             fun us ->
                               fun args ->
                                 match args with
                                 | (a1, uu___5)::(b1, uu___6)::(c1, uu___7)::
                                     (d1, uu___8)::[] ->
                                     Obj.magic
                                       (Obj.repr
                                          (let uu___9 =
                                             let uu___10 =
                                               let uu___11 =
                                                 let uu___12 =
                                                   let uu___13 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       (solve uu___) cbs a1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                        FStarC_Class_Monad.monad_option
                                                        () ()
                                                        (fun uu___14 ->
                                                           (Obj.magic f)
                                                             uu___14)
                                                        (Obj.magic uu___13)) in
                                                 let uu___13 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     (solve uu___1) cbs b1 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.op_Less_Star_Greater
                                                      FStarC_Class_Monad.monad_option
                                                      () ()
                                                      (Obj.magic uu___12)
                                                      (Obj.magic uu___13)) in
                                               let uu___12 =
                                                 FStarC_TypeChecker_NBETerm.unembed
                                                   (solve uu___2) cbs c1 in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_Less_Star_Greater
                                                    FStarC_Class_Monad.monad_option
                                                    () () (Obj.magic uu___11)
                                                    (Obj.magic uu___12)) in
                                             let uu___11 =
                                               FStarC_TypeChecker_NBETerm.unembed
                                                 (solve uu___3) cbs d1 in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_Less_Star_Greater
                                                  FStarC_Class_Monad.monad_option
                                                  () () (Obj.magic uu___10)
                                                  (Obj.magic uu___11)) in
                                           FStarC_Class_Monad.op_let_Bang
                                             FStarC_Class_Monad.monad_option
                                             () () (Obj.magic uu___9)
                                             (fun uu___10 ->
                                                (fun r1 ->
                                                   let r1 = Obj.magic r1 in
                                                   let uu___10 =
                                                     FStarC_TypeChecker_NBETerm.embed
                                                       (solve uu___4) cbs r1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.return
                                                        FStarC_Class_Monad.monad_option
                                                        ()
                                                        (Obj.magic uu___10)))
                                                  uu___10)))
                                 | uu___5 ->
                                     Obj.magic
                                       (Obj.repr FStar_Pervasives_Native.None))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_interp5 :
  'a 'b 'c 'd 'e 'r .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      'b FStarC_Syntax_Embeddings_Base.embedding ->
        'c FStarC_Syntax_Embeddings_Base.embedding ->
          'd FStarC_Syntax_Embeddings_Base.embedding ->
            'e FStarC_Syntax_Embeddings_Base.embedding ->
              'r FStarC_Syntax_Embeddings_Base.embedding ->
                ('a -> 'b -> 'c -> 'd -> 'e -> 'r) -> interp_t
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun uu___ ->
                   fun uu___1 ->
                     fun uu___2 ->
                       fun uu___3 ->
                         fun uu___4 ->
                           fun uu___5 ->
                             fun f ->
                               fun psc1 ->
                                 fun cb ->
                                   fun us ->
                                     fun args ->
                                       match args with
                                       | (a1, uu___6)::(b1, uu___7)::
                                           (c1, uu___8)::(d1, uu___9)::
                                           (e1, uu___10)::[] ->
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___11 =
                                                   let uu___12 =
                                                     let uu___13 =
                                                       let uu___14 =
                                                         let uu___15 =
                                                           let uu___16 =
                                                             try_unembed_simple
                                                               uu___ a1 in
                                                           Obj.magic
                                                             (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                                FStarC_Class_Monad.monad_option
                                                                () ()
                                                                (fun uu___17
                                                                   ->
                                                                   (Obj.magic
                                                                    f)
                                                                    uu___17)
                                                                (Obj.magic
                                                                   uu___16)) in
                                                         let uu___16 =
                                                           try_unembed_simple
                                                             uu___1 b1 in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.op_Less_Star_Greater
                                                              FStarC_Class_Monad.monad_option
                                                              () ()
                                                              (Obj.magic
                                                                 uu___15)
                                                              (Obj.magic
                                                                 uu___16)) in
                                                       let uu___15 =
                                                         try_unembed_simple
                                                           uu___2 c1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_Less_Star_Greater
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___14)
                                                            (Obj.magic
                                                               uu___15)) in
                                                     let uu___14 =
                                                       try_unembed_simple
                                                         uu___3 d1 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.op_Less_Star_Greater
                                                          FStarC_Class_Monad.monad_option
                                                          () ()
                                                          (Obj.magic uu___13)
                                                          (Obj.magic uu___14)) in
                                                   let uu___13 =
                                                     try_unembed_simple
                                                       uu___4 e1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_Less_Star_Greater
                                                        FStarC_Class_Monad.monad_option
                                                        () ()
                                                        (Obj.magic uu___12)
                                                        (Obj.magic uu___13)) in
                                                 FStarC_Class_Monad.op_let_Bang
                                                   FStarC_Class_Monad.monad_option
                                                   () () (Obj.magic uu___11)
                                                   (fun uu___12 ->
                                                      (fun r1 ->
                                                         let r1 =
                                                           Obj.magic r1 in
                                                         let uu___12 =
                                                           embed_simple
                                                             uu___5
                                                             psc1.psc_range
                                                             r1 in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.return
                                                              FStarC_Class_Monad.monad_option
                                                              ()
                                                              (Obj.magic
                                                                 uu___12)))
                                                        uu___12)))
                                       | uu___6 ->
                                           Obj.magic
                                             (Obj.repr (failwith "arity")))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk_nbe_interp5 :
  'a 'b 'c 'd 'e 'r .
    'a FStarC_TypeChecker_NBETerm.embedding ->
      'b FStarC_TypeChecker_NBETerm.embedding ->
        'c FStarC_TypeChecker_NBETerm.embedding ->
          'd FStarC_TypeChecker_NBETerm.embedding ->
            'e FStarC_TypeChecker_NBETerm.embedding ->
              'r FStarC_TypeChecker_NBETerm.embedding ->
                ('a -> 'b -> 'c -> 'd -> 'e -> 'r) -> nbe_interp_t
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun uu___ ->
                   fun uu___1 ->
                     fun uu___2 ->
                       fun uu___3 ->
                         fun uu___4 ->
                           fun uu___5 ->
                             fun f ->
                               fun cbs ->
                                 fun us ->
                                   fun args ->
                                     match args with
                                     | (a1, uu___6)::(b1, uu___7)::(c1,
                                                                    uu___8)::
                                         (d1, uu___9)::(e1, uu___10)::[] ->
                                         Obj.magic
                                           (Obj.repr
                                              (let uu___11 =
                                                 let uu___12 =
                                                   let uu___13 =
                                                     let uu___14 =
                                                       let uu___15 =
                                                         let uu___16 =
                                                           FStarC_TypeChecker_NBETerm.unembed
                                                             (solve uu___)
                                                             cbs a1 in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                              FStarC_Class_Monad.monad_option
                                                              () ()
                                                              (fun uu___17 ->
                                                                 (Obj.magic f)
                                                                   uu___17)
                                                              (Obj.magic
                                                                 uu___16)) in
                                                       let uu___16 =
                                                         FStarC_TypeChecker_NBETerm.unembed
                                                           (solve uu___1) cbs
                                                           b1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.op_Less_Star_Greater
                                                            FStarC_Class_Monad.monad_option
                                                            () ()
                                                            (Obj.magic
                                                               uu___15)
                                                            (Obj.magic
                                                               uu___16)) in
                                                     let uu___15 =
                                                       FStarC_TypeChecker_NBETerm.unembed
                                                         (solve uu___2) cbs
                                                         c1 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.op_Less_Star_Greater
                                                          FStarC_Class_Monad.monad_option
                                                          () ()
                                                          (Obj.magic uu___14)
                                                          (Obj.magic uu___15)) in
                                                   let uu___14 =
                                                     FStarC_TypeChecker_NBETerm.unembed
                                                       (solve uu___3) cbs d1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_Less_Star_Greater
                                                        FStarC_Class_Monad.monad_option
                                                        () ()
                                                        (Obj.magic uu___13)
                                                        (Obj.magic uu___14)) in
                                                 let uu___13 =
                                                   FStarC_TypeChecker_NBETerm.unembed
                                                     (solve uu___4) cbs e1 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.op_Less_Star_Greater
                                                      FStarC_Class_Monad.monad_option
                                                      () ()
                                                      (Obj.magic uu___12)
                                                      (Obj.magic uu___13)) in
                                               FStarC_Class_Monad.op_let_Bang
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___11)
                                                 (fun uu___12 ->
                                                    (fun r1 ->
                                                       let r1 = Obj.magic r1 in
                                                       let uu___12 =
                                                         FStarC_TypeChecker_NBETerm.embed
                                                           (solve uu___5) cbs
                                                           r1 in
                                                       Obj.magic
                                                         (FStarC_Class_Monad.return
                                                            FStarC_Class_Monad.monad_option
                                                            ()
                                                            (Obj.magic
                                                               uu___12)))
                                                      uu___12)))
                                     | uu___6 ->
                                         Obj.magic
                                           (Obj.repr
                                              FStar_Pervasives_Native.None))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let mk1 :
  'a 'r .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'a FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              'r FStarC_TypeChecker_NBETerm.embedding ->
                ('a -> 'r) -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                let interp = mk_interp1 uu___ uu___2 f in
                let nbe_interp = mk_nbe_interp1 uu___1 uu___3 f in
                as_primitive_step_nbecbs true
                  (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk2 :
  'a 'b 'r .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'a FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'b FStarC_TypeChecker_NBETerm.embedding ->
                'r FStarC_Syntax_Embeddings_Base.embedding ->
                  'r FStarC_TypeChecker_NBETerm.embedding ->
                    ('a -> 'b -> 'r) -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun f ->
                    let interp = mk_interp2 uu___ uu___2 uu___4 f in
                    let nbe_interp = mk_nbe_interp2 uu___1 uu___3 uu___5 f in
                    as_primitive_step_nbecbs true
                      (name, (Prims.of_int (2)), u_arity, interp, nbe_interp)
let mk3 :
  'a 'b 'c 'r .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'a FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'b FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'c FStarC_TypeChecker_NBETerm.embedding ->
                    'r FStarC_Syntax_Embeddings_Base.embedding ->
                      'r FStarC_TypeChecker_NBETerm.embedding ->
                        ('a -> 'b -> 'c -> 'r) -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun f ->
                        let interp = mk_interp3 uu___ uu___2 uu___4 uu___6 f in
                        let nbe_interp =
                          mk_nbe_interp3 uu___1 uu___3 uu___5 uu___7 f in
                        as_primitive_step_nbecbs true
                          (name, (Prims.of_int (3)), u_arity, interp,
                            nbe_interp)
let mk4 :
  'a 'b 'c 'd 'r .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'a FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'b FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'c FStarC_TypeChecker_NBETerm.embedding ->
                    'd FStarC_Syntax_Embeddings_Base.embedding ->
                      'd FStarC_TypeChecker_NBETerm.embedding ->
                        'r FStarC_Syntax_Embeddings_Base.embedding ->
                          'r FStarC_TypeChecker_NBETerm.embedding ->
                            ('a -> 'b -> 'c -> 'd -> 'r) -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun f ->
                            let interp =
                              mk_interp4 uu___ uu___2 uu___4 uu___6 uu___8 f in
                            let nbe_interp =
                              mk_nbe_interp4 uu___1 uu___3 uu___5 uu___7
                                uu___9 f in
                            as_primitive_step_nbecbs true
                              (name, (Prims.of_int (4)), u_arity, interp,
                                nbe_interp)
let mk5 :
  'a 'b 'c 'd 'e 'r .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'a FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'b FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'c FStarC_TypeChecker_NBETerm.embedding ->
                    'd FStarC_Syntax_Embeddings_Base.embedding ->
                      'd FStarC_TypeChecker_NBETerm.embedding ->
                        'e FStarC_Syntax_Embeddings_Base.embedding ->
                          'e FStarC_TypeChecker_NBETerm.embedding ->
                            'r FStarC_Syntax_Embeddings_Base.embedding ->
                              'r FStarC_TypeChecker_NBETerm.embedding ->
                                ('a -> 'b -> 'c -> 'd -> 'e -> 'r) ->
                                  primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun uu___10 ->
                            fun uu___11 ->
                              fun f ->
                                let interp =
                                  mk_interp5 uu___ uu___2 uu___4 uu___6
                                    uu___8 uu___10 f in
                                let nbe_interp =
                                  mk_nbe_interp5 uu___1 uu___3 uu___5 uu___7
                                    uu___9 uu___11 f in
                                as_primitive_step_nbecbs true
                                  (name, (Prims.of_int (5)), u_arity, interp,
                                    nbe_interp)
let mk1' :
  'a 'r 'na 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              'nr FStarC_TypeChecker_NBETerm.embedding ->
                ('a -> 'r FStar_Pervasives_Native.option) ->
                  ('na -> 'nr FStar_Pervasives_Native.option) ->
                    primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                fun nbe_f ->
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
                                     (fun uu___7 -> (Obj.magic f) uu___7)
                                     (Obj.magic uu___6)) in
                              FStarC_Class_Monad.op_let_Bang
                                FStarC_Class_Monad.monad_option () ()
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun r1 ->
                                      let r1 = Obj.magic r1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic r1)
                                           (fun uu___6 ->
                                              (fun r2 ->
                                                 let r2 = Obj.magic r2 in
                                                 let uu___6 =
                                                   embed_simple uu___2
                                                     psc1.psc_range r2 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Class_Monad.monad_option
                                                      () (Obj.magic uu___6)))
                                                uu___6))) uu___6)))
                    | uu___4 -> Obj.magic (Obj.repr (failwith "arity")) in
                  let nbe_interp cbs us args =
                    match args with
                    | (a1, uu___4)::[] ->
                        Obj.magic
                          (Obj.repr
                             (let uu___5 =
                                let uu___6 =
                                  FStarC_TypeChecker_NBETerm.unembed
                                    (solve uu___1) cbs a1 in
                                Obj.magic
                                  (FStarC_Class_Monad.op_Less_Dollar_Greater
                                     FStarC_Class_Monad.monad_option () ()
                                     (fun uu___7 -> (Obj.magic nbe_f) uu___7)
                                     (Obj.magic uu___6)) in
                              FStarC_Class_Monad.op_let_Bang
                                FStarC_Class_Monad.monad_option () ()
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun r1 ->
                                      let r1 = Obj.magic r1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic r1)
                                           (fun uu___6 ->
                                              (fun r2 ->
                                                 let r2 = Obj.magic r2 in
                                                 let uu___6 =
                                                   FStarC_TypeChecker_NBETerm.embed
                                                     (solve uu___3) cbs r2 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Class_Monad.monad_option
                                                      () (Obj.magic uu___6)))
                                                uu___6))) uu___6)))
                    | uu___4 -> Obj.magic (Obj.repr (failwith "arity")) in
                  as_primitive_step_nbecbs true
                    (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk1_psc' :
  'a 'r 'na 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'r FStarC_Syntax_Embeddings_Base.embedding ->
              'nr FStarC_TypeChecker_NBETerm.embedding ->
                (psc -> 'a -> 'r FStar_Pervasives_Native.option) ->
                  (psc -> 'na -> 'nr FStar_Pervasives_Native.option) ->
                    primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                fun nbe_f ->
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
                                     (fun uu___7 ->
                                        (Obj.magic (f psc1)) uu___7)
                                     (Obj.magic uu___6)) in
                              FStarC_Class_Monad.op_let_Bang
                                FStarC_Class_Monad.monad_option () ()
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun r1 ->
                                      let r1 = Obj.magic r1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic r1)
                                           (fun uu___6 ->
                                              (fun r2 ->
                                                 let r2 = Obj.magic r2 in
                                                 let uu___6 =
                                                   embed_simple uu___2
                                                     psc1.psc_range r2 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Class_Monad.monad_option
                                                      () (Obj.magic uu___6)))
                                                uu___6))) uu___6)))
                    | uu___4 -> Obj.magic (Obj.repr (failwith "arity")) in
                  let nbe_interp cbs us args =
                    match args with
                    | (a1, uu___4)::[] ->
                        Obj.magic
                          (Obj.repr
                             (let uu___5 =
                                let uu___6 =
                                  FStarC_TypeChecker_NBETerm.unembed
                                    (solve uu___1) cbs a1 in
                                Obj.magic
                                  (FStarC_Class_Monad.op_Less_Dollar_Greater
                                     FStarC_Class_Monad.monad_option () ()
                                     (fun uu___7 ->
                                        (Obj.magic (nbe_f null_psc)) uu___7)
                                     (Obj.magic uu___6)) in
                              FStarC_Class_Monad.op_let_Bang
                                FStarC_Class_Monad.monad_option () ()
                                (Obj.magic uu___5)
                                (fun uu___6 ->
                                   (fun r1 ->
                                      let r1 = Obj.magic r1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic r1)
                                           (fun uu___6 ->
                                              (fun r2 ->
                                                 let r2 = Obj.magic r2 in
                                                 let uu___6 =
                                                   FStarC_TypeChecker_NBETerm.embed
                                                     (solve uu___3) cbs r2 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.return
                                                      FStarC_Class_Monad.monad_option
                                                      () (Obj.magic uu___6)))
                                                uu___6))) uu___6)))
                    | uu___4 -> Obj.magic (Obj.repr (failwith "arity")) in
                  as_primitive_step_nbecbs true
                    (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk2' :
  'a 'b 'r 'na 'nb 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'nb FStarC_TypeChecker_NBETerm.embedding ->
                'r FStarC_Syntax_Embeddings_Base.embedding ->
                  'nr FStarC_TypeChecker_NBETerm.embedding ->
                    ('a -> 'b -> 'r FStar_Pervasives_Native.option) ->
                      ('na -> 'nb -> 'nr FStar_Pervasives_Native.option) ->
                        primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun f ->
                    fun nbe_f ->
                      let interp psc1 cb us args =
                        match args with
                        | (a1, uu___6)::(b1, uu___7)::[] ->
                            Obj.magic
                              (Obj.repr
                                 (let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        try_unembed_simple uu___ a1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_Less_Dollar_Greater
                                           FStarC_Class_Monad.monad_option ()
                                           ()
                                           (fun uu___11 ->
                                              (Obj.magic f) uu___11)
                                           (Obj.magic uu___10)) in
                                    let uu___10 =
                                      try_unembed_simple uu___2 b1 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                         FStarC_Class_Monad.monad_option ()
                                         () (Obj.magic uu___9)
                                         (Obj.magic uu___10)) in
                                  FStarC_Class_Monad.op_let_Bang
                                    FStarC_Class_Monad.monad_option () ()
                                    (Obj.magic uu___8)
                                    (fun uu___9 ->
                                       (fun r1 ->
                                          let r1 = Obj.magic r1 in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_let_Bang
                                               FStarC_Class_Monad.monad_option
                                               () () (Obj.magic r1)
                                               (fun uu___9 ->
                                                  (fun r2 ->
                                                     let r2 = Obj.magic r2 in
                                                     let uu___9 =
                                                       embed_simple uu___4
                                                         psc1.psc_range r2 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.return
                                                          FStarC_Class_Monad.monad_option
                                                          ()
                                                          (Obj.magic uu___9)))
                                                    uu___9))) uu___9)))
                        | uu___6 -> Obj.magic (Obj.repr (failwith "arity")) in
                      let nbe_interp cbs us args =
                        match args with
                        | (a1, uu___6)::(b1, uu___7)::[] ->
                            Obj.magic
                              (Obj.repr
                                 (let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_TypeChecker_NBETerm.unembed
                                          (solve uu___1) cbs a1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_Less_Dollar_Greater
                                           FStarC_Class_Monad.monad_option ()
                                           ()
                                           (fun uu___11 ->
                                              (Obj.magic nbe_f) uu___11)
                                           (Obj.magic uu___10)) in
                                    let uu___10 =
                                      FStarC_TypeChecker_NBETerm.unembed
                                        (solve uu___3) cbs b1 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                         FStarC_Class_Monad.monad_option ()
                                         () (Obj.magic uu___9)
                                         (Obj.magic uu___10)) in
                                  FStarC_Class_Monad.op_let_Bang
                                    FStarC_Class_Monad.monad_option () ()
                                    (Obj.magic uu___8)
                                    (fun uu___9 ->
                                       (fun r1 ->
                                          let r1 = Obj.magic r1 in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_let_Bang
                                               FStarC_Class_Monad.monad_option
                                               () () (Obj.magic r1)
                                               (fun uu___9 ->
                                                  (fun r2 ->
                                                     let r2 = Obj.magic r2 in
                                                     let uu___9 =
                                                       FStarC_TypeChecker_NBETerm.embed
                                                         (solve uu___5) cbs
                                                         r2 in
                                                     Obj.magic
                                                       (FStarC_Class_Monad.return
                                                          FStarC_Class_Monad.monad_option
                                                          ()
                                                          (Obj.magic uu___9)))
                                                    uu___9))) uu___9)))
                        | uu___6 -> Obj.magic (Obj.repr (failwith "arity")) in
                      as_primitive_step_nbecbs true
                        (name, (Prims.of_int (2)), u_arity, interp,
                          nbe_interp)
let mk3' :
  'a 'b 'c 'r 'na 'nb 'nc 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'nb FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'nc FStarC_TypeChecker_NBETerm.embedding ->
                    'r FStarC_Syntax_Embeddings_Base.embedding ->
                      'nr FStarC_TypeChecker_NBETerm.embedding ->
                        ('a -> 'b -> 'c -> 'r FStar_Pervasives_Native.option)
                          ->
                          ('na ->
                             'nb -> 'nc -> 'nr FStar_Pervasives_Native.option)
                            -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun f ->
                        fun nbe_f ->
                          let interp psc1 cb us args =
                            match args with
                            | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[]
                                ->
                                Obj.magic
                                  (Obj.repr
                                     (let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              try_unembed_simple uu___ a1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                 FStarC_Class_Monad.monad_option
                                                 () ()
                                                 (fun uu___15 ->
                                                    (Obj.magic f) uu___15)
                                                 (Obj.magic uu___14)) in
                                          let uu___14 =
                                            try_unembed_simple uu___2 b1 in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_Less_Star_Greater
                                               FStarC_Class_Monad.monad_option
                                               () () (Obj.magic uu___13)
                                               (Obj.magic uu___14)) in
                                        let uu___13 =
                                          try_unembed_simple uu___4 c1 in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_Less_Star_Greater
                                             FStarC_Class_Monad.monad_option
                                             () () (Obj.magic uu___12)
                                             (Obj.magic uu___13)) in
                                      FStarC_Class_Monad.op_let_Bang
                                        FStarC_Class_Monad.monad_option () ()
                                        (Obj.magic uu___11)
                                        (fun uu___12 ->
                                           (fun r1 ->
                                              let r1 = Obj.magic r1 in
                                              Obj.magic
                                                (FStarC_Class_Monad.op_let_Bang
                                                   FStarC_Class_Monad.monad_option
                                                   () () (Obj.magic r1)
                                                   (fun uu___12 ->
                                                      (fun r2 ->
                                                         let r2 =
                                                           Obj.magic r2 in
                                                         let uu___12 =
                                                           embed_simple
                                                             uu___6
                                                             psc1.psc_range
                                                             r2 in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.return
                                                              FStarC_Class_Monad.monad_option
                                                              ()
                                                              (Obj.magic
                                                                 uu___12)))
                                                        uu___12))) uu___12)))
                            | uu___8 ->
                                Obj.magic (Obj.repr (failwith "arity")) in
                          let nbe_interp cbs us args =
                            match args with
                            | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[]
                                ->
                                Obj.magic
                                  (Obj.repr
                                     (let uu___11 =
                                        let uu___12 =
                                          let uu___13 =
                                            let uu___14 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                (solve uu___1) cbs a1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                 FStarC_Class_Monad.monad_option
                                                 () ()
                                                 (fun uu___15 ->
                                                    (Obj.magic nbe_f) uu___15)
                                                 (Obj.magic uu___14)) in
                                          let uu___14 =
                                            FStarC_TypeChecker_NBETerm.unembed
                                              (solve uu___3) cbs b1 in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_Less_Star_Greater
                                               FStarC_Class_Monad.monad_option
                                               () () (Obj.magic uu___13)
                                               (Obj.magic uu___14)) in
                                        let uu___13 =
                                          FStarC_TypeChecker_NBETerm.unembed
                                            (solve uu___5) cbs c1 in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_Less_Star_Greater
                                             FStarC_Class_Monad.monad_option
                                             () () (Obj.magic uu___12)
                                             (Obj.magic uu___13)) in
                                      FStarC_Class_Monad.op_let_Bang
                                        FStarC_Class_Monad.monad_option () ()
                                        (Obj.magic uu___11)
                                        (fun uu___12 ->
                                           (fun r1 ->
                                              let r1 = Obj.magic r1 in
                                              Obj.magic
                                                (FStarC_Class_Monad.op_let_Bang
                                                   FStarC_Class_Monad.monad_option
                                                   () () (Obj.magic r1)
                                                   (fun uu___12 ->
                                                      (fun r2 ->
                                                         let r2 =
                                                           Obj.magic r2 in
                                                         let uu___12 =
                                                           FStarC_TypeChecker_NBETerm.embed
                                                             (solve uu___7)
                                                             cbs r2 in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.return
                                                              FStarC_Class_Monad.monad_option
                                                              ()
                                                              (Obj.magic
                                                                 uu___12)))
                                                        uu___12))) uu___12)))
                            | uu___8 ->
                                Obj.magic (Obj.repr (failwith "arity")) in
                          as_primitive_step_nbecbs true
                            (name, (Prims.of_int (3)), u_arity, interp,
                              nbe_interp)
let mk4' :
  'a 'b 'c 'd 'r 'na 'nb 'nc 'nd 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'nb FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'nc FStarC_TypeChecker_NBETerm.embedding ->
                    'd FStarC_Syntax_Embeddings_Base.embedding ->
                      'nd FStarC_TypeChecker_NBETerm.embedding ->
                        'r FStarC_Syntax_Embeddings_Base.embedding ->
                          'nr FStarC_TypeChecker_NBETerm.embedding ->
                            ('a ->
                               'b ->
                                 'c ->
                                   'd -> 'r FStar_Pervasives_Native.option)
                              ->
                              ('na ->
                                 'nb ->
                                   'nc ->
                                     'nd ->
                                       'nr FStar_Pervasives_Native.option)
                                -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun f ->
                            fun nbe_f ->
                              let interp psc1 cb us args =
                                match args with
                                | (a1, uu___10)::(b1, uu___11)::(c1, uu___12)::
                                    (d1, uu___13)::[] ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___14 =
                                            let uu___15 =
                                              let uu___16 =
                                                let uu___17 =
                                                  let uu___18 =
                                                    try_unembed_simple uu___
                                                      a1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                       FStarC_Class_Monad.monad_option
                                                       () ()
                                                       (fun uu___19 ->
                                                          (Obj.magic f)
                                                            uu___19)
                                                       (Obj.magic uu___18)) in
                                                let uu___18 =
                                                  try_unembed_simple uu___2
                                                    b1 in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_Less_Star_Greater
                                                     FStarC_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___17)
                                                     (Obj.magic uu___18)) in
                                              let uu___17 =
                                                try_unembed_simple uu___4 c1 in
                                              Obj.magic
                                                (FStarC_Class_Monad.op_Less_Star_Greater
                                                   FStarC_Class_Monad.monad_option
                                                   () () (Obj.magic uu___16)
                                                   (Obj.magic uu___17)) in
                                            let uu___16 =
                                              try_unembed_simple uu___6 d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_Less_Star_Greater
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___15)
                                                 (Obj.magic uu___16)) in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Class_Monad.monad_option
                                            () () (Obj.magic uu___14)
                                            (fun uu___15 ->
                                               (fun r1 ->
                                                  let r1 = Obj.magic r1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_let_Bang
                                                       FStarC_Class_Monad.monad_option
                                                       () () (Obj.magic r1)
                                                       (fun uu___15 ->
                                                          (fun r2 ->
                                                             let r2 =
                                                               Obj.magic r2 in
                                                             let uu___15 =
                                                               embed_simple
                                                                 uu___8
                                                                 psc1.psc_range
                                                                 r2 in
                                                             Obj.magic
                                                               (FStarC_Class_Monad.return
                                                                  FStarC_Class_Monad.monad_option
                                                                  ()
                                                                  (Obj.magic
                                                                    uu___15)))
                                                            uu___15)))
                                                 uu___15)))
                                | uu___10 ->
                                    Obj.magic (Obj.repr (failwith "arity")) in
                              let nbe_interp cbs us args =
                                match args with
                                | (a1, uu___10)::(b1, uu___11)::(c1, uu___12)::
                                    (d1, uu___13)::[] ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___14 =
                                            let uu___15 =
                                              let uu___16 =
                                                let uu___17 =
                                                  let uu___18 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      (solve uu___1) cbs a1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                       FStarC_Class_Monad.monad_option
                                                       () ()
                                                       (fun uu___19 ->
                                                          (Obj.magic nbe_f)
                                                            uu___19)
                                                       (Obj.magic uu___18)) in
                                                let uu___18 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    (solve uu___3) cbs b1 in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_Less_Star_Greater
                                                     FStarC_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___17)
                                                     (Obj.magic uu___18)) in
                                              let uu___17 =
                                                FStarC_TypeChecker_NBETerm.unembed
                                                  (solve uu___5) cbs c1 in
                                              Obj.magic
                                                (FStarC_Class_Monad.op_Less_Star_Greater
                                                   FStarC_Class_Monad.monad_option
                                                   () () (Obj.magic uu___16)
                                                   (Obj.magic uu___17)) in
                                            let uu___16 =
                                              FStarC_TypeChecker_NBETerm.unembed
                                                (solve uu___7) cbs d1 in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_Less_Star_Greater
                                                 FStarC_Class_Monad.monad_option
                                                 () () (Obj.magic uu___15)
                                                 (Obj.magic uu___16)) in
                                          FStarC_Class_Monad.op_let_Bang
                                            FStarC_Class_Monad.monad_option
                                            () () (Obj.magic uu___14)
                                            (fun uu___15 ->
                                               (fun r1 ->
                                                  let r1 = Obj.magic r1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_let_Bang
                                                       FStarC_Class_Monad.monad_option
                                                       () () (Obj.magic r1)
                                                       (fun uu___15 ->
                                                          (fun r2 ->
                                                             let r2 =
                                                               Obj.magic r2 in
                                                             let uu___15 =
                                                               FStarC_TypeChecker_NBETerm.embed
                                                                 (solve
                                                                    uu___9)
                                                                 cbs r2 in
                                                             Obj.magic
                                                               (FStarC_Class_Monad.return
                                                                  FStarC_Class_Monad.monad_option
                                                                  ()
                                                                  (Obj.magic
                                                                    uu___15)))
                                                            uu___15)))
                                                 uu___15)))
                                | uu___10 ->
                                    Obj.magic (Obj.repr (failwith "arity")) in
                              as_primitive_step_nbecbs true
                                (name, (Prims.of_int (4)), u_arity, interp,
                                  nbe_interp)
let mk5' :
  'a 'b 'c 'd 'e 'r 'na 'nb 'nc 'nd 'ne 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'nb FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'nc FStarC_TypeChecker_NBETerm.embedding ->
                    'd FStarC_Syntax_Embeddings_Base.embedding ->
                      'nd FStarC_TypeChecker_NBETerm.embedding ->
                        'e FStarC_Syntax_Embeddings_Base.embedding ->
                          'ne FStarC_TypeChecker_NBETerm.embedding ->
                            'r FStarC_Syntax_Embeddings_Base.embedding ->
                              'nr FStarC_TypeChecker_NBETerm.embedding ->
                                ('a ->
                                   'b ->
                                     'c ->
                                       'd ->
                                         'e ->
                                           'r FStar_Pervasives_Native.option)
                                  ->
                                  ('na ->
                                     'nb ->
                                       'nc ->
                                         'nd ->
                                           'ne ->
                                             'nr
                                               FStar_Pervasives_Native.option)
                                    -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun uu___10 ->
                            fun uu___11 ->
                              fun f ->
                                fun nbe_f ->
                                  let interp psc1 cb us args =
                                    match args with
                                    | (a1, uu___12)::(b1, uu___13)::(c1,
                                                                    uu___14)::
                                        (d1, uu___15)::(e1, uu___16)::[] ->
                                        Obj.magic
                                          (Obj.repr
                                             (let uu___17 =
                                                let uu___18 =
                                                  let uu___19 =
                                                    let uu___20 =
                                                      let uu___21 =
                                                        let uu___22 =
                                                          try_unembed_simple
                                                            uu___ a1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (fun uu___23 ->
                                                                (Obj.magic f)
                                                                  uu___23)
                                                             (Obj.magic
                                                                uu___22)) in
                                                      let uu___22 =
                                                        try_unembed_simple
                                                          uu___2 b1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_Less_Star_Greater
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic uu___21)
                                                           (Obj.magic uu___22)) in
                                                    let uu___21 =
                                                      try_unembed_simple
                                                        uu___4 c1 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                                         FStarC_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___20)
                                                         (Obj.magic uu___21)) in
                                                  let uu___20 =
                                                    try_unembed_simple uu___6
                                                      d1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_Less_Star_Greater
                                                       FStarC_Class_Monad.monad_option
                                                       () ()
                                                       (Obj.magic uu___19)
                                                       (Obj.magic uu___20)) in
                                                let uu___19 =
                                                  try_unembed_simple uu___8
                                                    e1 in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_Less_Star_Greater
                                                     FStarC_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___18)
                                                     (Obj.magic uu___19)) in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___17)
                                                (fun uu___18 ->
                                                   (fun r1 ->
                                                      let r1 = Obj.magic r1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic r1)
                                                           (fun uu___18 ->
                                                              (fun r2 ->
                                                                 let r2 =
                                                                   Obj.magic
                                                                    r2 in
                                                                 let uu___18
                                                                   =
                                                                   embed_simple
                                                                    uu___10
                                                                    psc1.psc_range
                                                                    r2 in
                                                                 Obj.magic
                                                                   (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___18)))
                                                                uu___18)))
                                                     uu___18)))
                                    | uu___12 ->
                                        Obj.magic
                                          (Obj.repr (failwith "arity")) in
                                  let nbe_interp cbs us args =
                                    match args with
                                    | (a1, uu___12)::(b1, uu___13)::(c1,
                                                                    uu___14)::
                                        (d1, uu___15)::(e1, uu___16)::[] ->
                                        Obj.magic
                                          (Obj.repr
                                             (let uu___17 =
                                                let uu___18 =
                                                  let uu___19 =
                                                    let uu___20 =
                                                      let uu___21 =
                                                        let uu___22 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            (solve uu___1)
                                                            cbs a1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (fun uu___23 ->
                                                                (Obj.magic
                                                                   nbe_f)
                                                                  uu___23)
                                                             (Obj.magic
                                                                uu___22)) in
                                                      let uu___22 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          (solve uu___3) cbs
                                                          b1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_Less_Star_Greater
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic uu___21)
                                                           (Obj.magic uu___22)) in
                                                    let uu___21 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        (solve uu___5) cbs c1 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                                         FStarC_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___20)
                                                         (Obj.magic uu___21)) in
                                                  let uu___20 =
                                                    FStarC_TypeChecker_NBETerm.unembed
                                                      (solve uu___7) cbs d1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_Less_Star_Greater
                                                       FStarC_Class_Monad.monad_option
                                                       () ()
                                                       (Obj.magic uu___19)
                                                       (Obj.magic uu___20)) in
                                                let uu___19 =
                                                  FStarC_TypeChecker_NBETerm.unembed
                                                    (solve uu___9) cbs e1 in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_Less_Star_Greater
                                                     FStarC_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___18)
                                                     (Obj.magic uu___19)) in
                                              FStarC_Class_Monad.op_let_Bang
                                                FStarC_Class_Monad.monad_option
                                                () () (Obj.magic uu___17)
                                                (fun uu___18 ->
                                                   (fun r1 ->
                                                      let r1 = Obj.magic r1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic r1)
                                                           (fun uu___18 ->
                                                              (fun r2 ->
                                                                 let r2 =
                                                                   Obj.magic
                                                                    r2 in
                                                                 let uu___18
                                                                   =
                                                                   FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___11)
                                                                    cbs r2 in
                                                                 Obj.magic
                                                                   (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___18)))
                                                                uu___18)))
                                                     uu___18)))
                                    | uu___12 ->
                                        Obj.magic
                                          (Obj.repr (failwith "arity")) in
                                  as_primitive_step_nbecbs true
                                    (name, (Prims.of_int (5)), u_arity,
                                      interp, nbe_interp)
let mk6' :
  'a 'b 'c 'd 'e 'f 'r 'na 'nb 'nc 'nd 'ne 'nf 'nr .
    Prims.int ->
      FStarC_Ident.lid ->
        'a FStarC_Syntax_Embeddings_Base.embedding ->
          'na FStarC_TypeChecker_NBETerm.embedding ->
            'b FStarC_Syntax_Embeddings_Base.embedding ->
              'nb FStarC_TypeChecker_NBETerm.embedding ->
                'c FStarC_Syntax_Embeddings_Base.embedding ->
                  'nc FStarC_TypeChecker_NBETerm.embedding ->
                    'd FStarC_Syntax_Embeddings_Base.embedding ->
                      'nd FStarC_TypeChecker_NBETerm.embedding ->
                        'e FStarC_Syntax_Embeddings_Base.embedding ->
                          'ne FStarC_TypeChecker_NBETerm.embedding ->
                            'f FStarC_Syntax_Embeddings_Base.embedding ->
                              'nf FStarC_TypeChecker_NBETerm.embedding ->
                                'r FStarC_Syntax_Embeddings_Base.embedding ->
                                  'nr FStarC_TypeChecker_NBETerm.embedding ->
                                    ('a ->
                                       'b ->
                                         'c ->
                                           'd ->
                                             'e ->
                                               'f ->
                                                 'r
                                                   FStar_Pervasives_Native.option)
                                      ->
                                      ('na ->
                                         'nb ->
                                           'nc ->
                                             'nd ->
                                               'ne ->
                                                 'nf ->
                                                   'nr
                                                     FStar_Pervasives_Native.option)
                                        -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun uu___4 ->
                fun uu___5 ->
                  fun uu___6 ->
                    fun uu___7 ->
                      fun uu___8 ->
                        fun uu___9 ->
                          fun uu___10 ->
                            fun uu___11 ->
                              fun uu___12 ->
                                fun uu___13 ->
                                  fun ff ->
                                    fun nbe_ff ->
                                      let interp psc1 cb us args =
                                        match args with
                                        | (a1, uu___14)::(b1, uu___15)::
                                            (c1, uu___16)::(d1, uu___17)::
                                            (e1, uu___18)::(f1, uu___19)::[]
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (let uu___20 =
                                                    let uu___21 =
                                                      let uu___22 =
                                                        let uu___23 =
                                                          let uu___24 =
                                                            let uu___25 =
                                                              let uu___26 =
                                                                try_unembed_simple
                                                                  uu___ a1 in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                                   FStarC_Class_Monad.monad_option
                                                                   () ()
                                                                   (fun
                                                                    uu___27
                                                                    ->
                                                                    (Obj.magic
                                                                    ff)
                                                                    uu___27)
                                                                   (Obj.magic
                                                                    uu___26)) in
                                                            let uu___26 =
                                                              try_unembed_simple
                                                                uu___2 b1 in
                                                            Obj.magic
                                                              (FStarC_Class_Monad.op_Less_Star_Greater
                                                                 FStarC_Class_Monad.monad_option
                                                                 () ()
                                                                 (Obj.magic
                                                                    uu___25)
                                                                 (Obj.magic
                                                                    uu___26)) in
                                                          let uu___25 =
                                                            try_unembed_simple
                                                              uu___4 c1 in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_Less_Star_Greater
                                                               FStarC_Class_Monad.monad_option
                                                               () ()
                                                               (Obj.magic
                                                                  uu___24)
                                                               (Obj.magic
                                                                  uu___25)) in
                                                        let uu___24 =
                                                          try_unembed_simple
                                                            uu___6 d1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_Less_Star_Greater
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (Obj.magic
                                                                uu___23)
                                                             (Obj.magic
                                                                uu___24)) in
                                                      let uu___23 =
                                                        try_unembed_simple
                                                          uu___8 e1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_Less_Star_Greater
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic uu___22)
                                                           (Obj.magic uu___23)) in
                                                    let uu___22 =
                                                      try_unembed_simple
                                                        uu___10 f1 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                                         FStarC_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___21)
                                                         (Obj.magic uu___22)) in
                                                  FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Class_Monad.monad_option
                                                    () () (Obj.magic uu___20)
                                                    (fun uu___21 ->
                                                       (fun r1 ->
                                                          let r1 =
                                                            Obj.magic r1 in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_let_Bang
                                                               FStarC_Class_Monad.monad_option
                                                               () ()
                                                               (Obj.magic r1)
                                                               (fun uu___21
                                                                  ->
                                                                  (fun r2 ->
                                                                    let r2 =
                                                                    Obj.magic
                                                                    r2 in
                                                                    let uu___21
                                                                    =
                                                                    embed_simple
                                                                    uu___12
                                                                    psc1.psc_range
                                                                    r2 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___21)))
                                                                    uu___21)))
                                                         uu___21)))
                                        | uu___14 ->
                                            Obj.magic
                                              (Obj.repr (failwith "arity")) in
                                      let nbe_interp cbs us args =
                                        match args with
                                        | (a1, uu___14)::(b1, uu___15)::
                                            (c1, uu___16)::(d1, uu___17)::
                                            (e1, uu___18)::(f1, uu___19)::[]
                                            ->
                                            Obj.magic
                                              (Obj.repr
                                                 (let uu___20 =
                                                    let uu___21 =
                                                      let uu___22 =
                                                        let uu___23 =
                                                          let uu___24 =
                                                            let uu___25 =
                                                              let uu___26 =
                                                                FStarC_TypeChecker_NBETerm.unembed
                                                                  (solve
                                                                    uu___1)
                                                                  cbs a1 in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_Less_Dollar_Greater
                                                                   FStarC_Class_Monad.monad_option
                                                                   () ()
                                                                   (fun
                                                                    uu___27
                                                                    ->
                                                                    (Obj.magic
                                                                    nbe_ff)
                                                                    uu___27)
                                                                   (Obj.magic
                                                                    uu___26)) in
                                                            let uu___26 =
                                                              FStarC_TypeChecker_NBETerm.unembed
                                                                (solve uu___3)
                                                                cbs b1 in
                                                            Obj.magic
                                                              (FStarC_Class_Monad.op_Less_Star_Greater
                                                                 FStarC_Class_Monad.monad_option
                                                                 () ()
                                                                 (Obj.magic
                                                                    uu___25)
                                                                 (Obj.magic
                                                                    uu___26)) in
                                                          let uu___25 =
                                                            FStarC_TypeChecker_NBETerm.unembed
                                                              (solve uu___5)
                                                              cbs c1 in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_Less_Star_Greater
                                                               FStarC_Class_Monad.monad_option
                                                               () ()
                                                               (Obj.magic
                                                                  uu___24)
                                                               (Obj.magic
                                                                  uu___25)) in
                                                        let uu___24 =
                                                          FStarC_TypeChecker_NBETerm.unembed
                                                            (solve uu___7)
                                                            cbs d1 in
                                                        Obj.magic
                                                          (FStarC_Class_Monad.op_Less_Star_Greater
                                                             FStarC_Class_Monad.monad_option
                                                             () ()
                                                             (Obj.magic
                                                                uu___23)
                                                             (Obj.magic
                                                                uu___24)) in
                                                      let uu___23 =
                                                        FStarC_TypeChecker_NBETerm.unembed
                                                          (solve uu___9) cbs
                                                          e1 in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_Less_Star_Greater
                                                           FStarC_Class_Monad.monad_option
                                                           () ()
                                                           (Obj.magic uu___22)
                                                           (Obj.magic uu___23)) in
                                                    let uu___22 =
                                                      FStarC_TypeChecker_NBETerm.unembed
                                                        (solve uu___11) cbs
                                                        f1 in
                                                    Obj.magic
                                                      (FStarC_Class_Monad.op_Less_Star_Greater
                                                         FStarC_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___21)
                                                         (Obj.magic uu___22)) in
                                                  FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Class_Monad.monad_option
                                                    () () (Obj.magic uu___20)
                                                    (fun uu___21 ->
                                                       (fun r1 ->
                                                          let r1 =
                                                            Obj.magic r1 in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_let_Bang
                                                               FStarC_Class_Monad.monad_option
                                                               () ()
                                                               (Obj.magic r1)
                                                               (fun uu___21
                                                                  ->
                                                                  (fun r2 ->
                                                                    let r2 =
                                                                    Obj.magic
                                                                    r2 in
                                                                    let uu___21
                                                                    =
                                                                    FStarC_TypeChecker_NBETerm.embed
                                                                    (solve
                                                                    uu___13)
                                                                    cbs r2 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    FStarC_Class_Monad.monad_option
                                                                    ()
                                                                    (Obj.magic
                                                                    uu___21)))
                                                                    uu___21)))
                                                         uu___21)))
                                        | uu___14 ->
                                            Obj.magic
                                              (Obj.repr (failwith "arity")) in
                                      as_primitive_step_nbecbs true
                                        (name, (Prims.of_int (6)), u_arity,
                                          interp, nbe_interp)
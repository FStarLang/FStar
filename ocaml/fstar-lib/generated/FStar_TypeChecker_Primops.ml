open Prims
type psc =
  {
  psc_range: FStar_Compiler_Range_Type.range ;
  psc_subst: unit -> FStar_Syntax_Syntax.subst_t }
let (__proj__Mkpsc__item__psc_range : psc -> FStar_Compiler_Range_Type.range)
  =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_range
let (__proj__Mkpsc__item__psc_subst :
  psc -> unit -> FStar_Syntax_Syntax.subst_t) =
  fun projectee ->
    match projectee with | { psc_range; psc_subst;_} -> psc_subst
let (null_psc : psc) =
  {
    psc_range = FStar_Compiler_Range_Type.dummyRange;
    psc_subst = (fun uu___ -> [])
  }
let (psc_range : psc -> FStar_Compiler_Range_Type.range) =
  fun psc1 -> psc1.psc_range
let (psc_subst : psc -> FStar_Syntax_Syntax.subst_t) =
  fun psc1 -> psc1.psc_subst ()
type interp_t =
  psc ->
    FStar_Syntax_Embeddings_Base.norm_cb ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
type nbe_interp_t =
  FStar_TypeChecker_NBETerm.nbe_cbs ->
    FStar_Syntax_Syntax.universes ->
      FStar_TypeChecker_NBETerm.args ->
        FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  renorm_after: Prims.bool ;
  interpretation: interp_t ;
  interpretation_nbe: nbe_interp_t }
let (__proj__Mkprimitive_step__item__name :
  primitive_step -> FStar_Ident.lid) =
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
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range -> 'a -> FStar_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        let uu___1 = FStar_Syntax_Embeddings_Base.embed uu___ x in
        uu___1 r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings_Base.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      FStar_Syntax_Embeddings_Base.try_unembed uu___ x
        FStar_Syntax_Embeddings_Base.id_norm_cb
let (arg_as_int :
  FStar_Syntax_Syntax.arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a ->
    try_unembed_simple FStar_Syntax_Embeddings.e_int
      (FStar_Pervasives_Native.fst a)
let (arg_as_char :
  FStar_Syntax_Syntax.arg -> FStar_Char.char FStar_Pervasives_Native.option)
  =
  fun a ->
    try_unembed_simple FStar_Syntax_Embeddings.e_char
      (FStar_Pervasives_Native.fst a)
let arg_as_list :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.arg -> 'a Prims.list FStar_Pervasives_Native.option
  =
  fun e ->
    fun a1 ->
      try_unembed_simple (FStar_Syntax_Embeddings.e_list e)
        (FStar_Pervasives_Native.fst a1)
let (arg_as_bounded_int :
  FStar_Syntax_Syntax.arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t *
      FStar_Syntax_Syntax.meta_source_info FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.option)
  =
  fun uu___ ->
    match uu___ with
    | (a, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 = FStar_Syntax_Subst.compress a in
            uu___4.FStar_Syntax_Syntax.n in
          match uu___3 with
          | FStar_Syntax_Syntax.Tm_meta
              { FStar_Syntax_Syntax.tm2 = t;
                FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_desugared
                  m;_}
              -> (t, (FStar_Pervasives_Native.Some m))
          | uu___4 -> (a, FStar_Pervasives_Native.None) in
        (match uu___2 with
         | (a1, m) ->
             let a2 = FStar_Syntax_Util.unmeta_safe a1 in
             let uu___3 = FStar_Syntax_Util.head_and_args_full a2 in
             (match uu___3 with
              | (hd, args) ->
                  let a3 = FStar_Syntax_Util.unlazy_emb a2 in
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Subst.compress hd in
                      uu___6.FStar_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv1, (arg, uu___5)::[])
                       when
                       let uu___6 =
                         FStar_Ident.string_of_lid
                           (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                       FStar_Compiler_Util.ends_with uu___6 "int_to_t" ->
                       let arg1 = FStar_Syntax_Util.unlazy_emb arg in
                       let uu___6 =
                         let uu___7 = FStar_Syntax_Subst.compress arg1 in
                         uu___7.FStar_Syntax_Syntax.n in
                       (match uu___6 with
                        | FStar_Syntax_Syntax.Tm_constant
                            (FStar_Const.Const_int
                            (i, FStar_Pervasives_Native.None)) ->
                            let uu___7 =
                              let uu___8 = FStar_BigInt.big_int_of_string i in
                              (fv1, uu___8, m) in
                            FStar_Pervasives_Native.Some uu___7
                        | uu___7 -> FStar_Pervasives_Native.None)
                   | uu___5 -> FStar_Pervasives_Native.None)))
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu___ = f a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu___ = f a0 a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
let unary_op :
  'a .
    (FStar_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStar_Compiler_Range_Type.range -> 'a -> FStar_Syntax_Syntax.term) ->
        psc ->
          FStar_Syntax_Embeddings_Base.norm_cb ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun psc1 ->
        fun norm_cb ->
          fun _univs ->
            fun args ->
              let uu___ = FStar_Compiler_List.map as_a args in
              lift_unary (f psc1.psc_range) uu___
let binary_op :
  'a .
    (FStar_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStar_Compiler_Range_Type.range ->
         'a -> 'a -> FStar_Syntax_Syntax.term)
        ->
        psc ->
          FStar_Syntax_Embeddings_Base.norm_cb ->
            FStar_Syntax_Syntax.universes ->
              FStar_Syntax_Syntax.args ->
                FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun f ->
      fun psc1 ->
        fun norm_cb ->
          fun _univs ->
            fun args ->
              let uu___ = FStar_Compiler_List.map as_a args in
              lift_binary (f psc1.psc_range) uu___
let (as_primitive_step_nbecbs :
  Prims.bool ->
    (FStar_Ident.lid * Prims.int * Prims.int *
      (psc ->
         FStar_Syntax_Embeddings_Base.norm_cb ->
           FStar_Syntax_Syntax.universes ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      *
      (FStar_TypeChecker_NBETerm.nbe_cbs ->
         FStar_Syntax_Syntax.universes ->
           FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option))
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
            interpretation =
              ((fun psc1 ->
                  fun cb -> fun univs -> fun args -> f psc1 cb univs args));
            interpretation_nbe =
              ((fun cb -> fun univs -> fun args -> f_nbe cb univs args))
          }
let (as_primitive_step :
  Prims.bool ->
    (FStar_Ident.lid * Prims.int * Prims.int *
      (psc ->
         FStar_Syntax_Embeddings_Base.norm_cb ->
           FStar_Syntax_Syntax.universes ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
      *
      (FStar_Syntax_Syntax.universes ->
         FStar_TypeChecker_NBETerm.args ->
           FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option))
      -> primitive_step)
  =
  fun is_strong ->
    fun uu___ ->
      match uu___ with
      | (l, arity, u_arity, f, f_nbe) ->
          as_primitive_step_nbecbs is_strong
            (l, arity, u_arity, f,
              (fun cb -> fun univs -> fun args -> f_nbe univs args))
let solve : 'a . 'a -> 'a = fun ev -> ev
let mk1 :
  'a 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_Syntax_Embeddings_Base.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                ('a -> 'r) -> primitive_step
  =
  fun u_arity ->
    fun name ->
      fun uu___ ->
        fun uu___1 ->
          fun uu___2 ->
            fun uu___3 ->
              fun f ->
                let interp psc1 cb us args =
                  match args with
                  | (a1, uu___4)::[] ->
                      Obj.magic
                        (Obj.repr
                           (let uu___5 = try_unembed_simple uu___ a1 in
                            FStar_Class_Monad.op_let_Bang
                              FStar_Class_Monad.monad_option () ()
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 (fun a2 ->
                                    let a2 = Obj.magic a2 in
                                    let uu___6 =
                                      let uu___7 = f a2 in
                                      embed_simple uu___2 psc1.psc_range
                                        uu___7 in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         FStar_Class_Monad.monad_option ()
                                         (Obj.magic uu___6))) uu___6)))
                  | uu___4 ->
                      Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                let nbe_interp cbs us args =
                  match args with
                  | (a1, uu___4)::[] ->
                      Obj.magic
                        (Obj.repr
                           (let uu___5 =
                              let uu___6 =
                                FStar_TypeChecker_NBETerm.unembed
                                  (solve uu___1) cbs a1 in
                              Obj.magic
                                (FStar_Class_Monad.op_Less_Dollar_Greater
                                   FStar_Class_Monad.monad_option () ()
                                   (fun uu___7 -> (Obj.magic f) uu___7)
                                   (Obj.magic uu___6)) in
                            FStar_Class_Monad.op_let_Bang
                              FStar_Class_Monad.monad_option () ()
                              (Obj.magic uu___5)
                              (fun uu___6 ->
                                 (fun r1 ->
                                    let r1 = Obj.magic r1 in
                                    let uu___6 =
                                      FStar_TypeChecker_NBETerm.embed
                                        (solve uu___3) cbs r1 in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         FStar_Class_Monad.monad_option ()
                                         (Obj.magic uu___6))) uu___6)))
                  | uu___4 ->
                      Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                as_primitive_step_nbecbs true
                  (name, Prims.int_one, u_arity, interp, nbe_interp)
let mk2 :
  'a 'b 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'b FStar_Syntax_Embeddings_Base.embedding ->
              'b FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_Syntax_Embeddings_Base.embedding ->
                  'r FStar_TypeChecker_NBETerm.embedding ->
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
                    let interp psc1 cb us args =
                      match args with
                      | (a1, uu___6)::(b1, uu___7)::[] ->
                          Obj.magic
                            (Obj.repr
                               (let uu___8 =
                                  let uu___9 =
                                    let uu___10 = try_unembed_simple uu___ a1 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_Less_Dollar_Greater
                                         FStar_Class_Monad.monad_option () ()
                                         (fun uu___11 ->
                                            (Obj.magic f) uu___11)
                                         (Obj.magic uu___10)) in
                                  let uu___10 = try_unembed_simple uu___2 b1 in
                                  Obj.magic
                                    (FStar_Class_Monad.op_Less_Star_Greater
                                       FStar_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9) (Obj.magic uu___10)) in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Class_Monad.monad_option () ()
                                  (Obj.magic uu___8)
                                  (fun uu___9 ->
                                     (fun r1 ->
                                        let r1 = Obj.magic r1 in
                                        let uu___9 =
                                          embed_simple uu___4 psc1.psc_range
                                            r1 in
                                        Obj.magic
                                          (FStar_Class_Monad.return
                                             FStar_Class_Monad.monad_option
                                             () (Obj.magic uu___9))) uu___9)))
                      | uu___6 ->
                          Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                    let nbe_interp cbs us args =
                      match args with
                      | (a1, uu___6)::(b1, uu___7)::[] ->
                          Obj.magic
                            (Obj.repr
                               (let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_TypeChecker_NBETerm.unembed
                                        (solve uu___1) cbs a1 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_Less_Dollar_Greater
                                         FStar_Class_Monad.monad_option () ()
                                         (fun uu___11 ->
                                            (Obj.magic f) uu___11)
                                         (Obj.magic uu___10)) in
                                  let uu___10 =
                                    FStar_TypeChecker_NBETerm.unembed
                                      (solve uu___3) cbs b1 in
                                  Obj.magic
                                    (FStar_Class_Monad.op_Less_Star_Greater
                                       FStar_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9) (Obj.magic uu___10)) in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Class_Monad.monad_option () ()
                                  (Obj.magic uu___8)
                                  (fun uu___9 ->
                                     (fun r1 ->
                                        let r1 = Obj.magic r1 in
                                        let uu___9 =
                                          FStar_TypeChecker_NBETerm.embed
                                            (solve uu___5) cbs r1 in
                                        Obj.magic
                                          (FStar_Class_Monad.return
                                             FStar_Class_Monad.monad_option
                                             () (Obj.magic uu___9))) uu___9)))
                      | uu___6 ->
                          Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                    as_primitive_step_nbecbs true
                      (name, (Prims.of_int (2)), u_arity, interp, nbe_interp)
let mk2' :
  'a 'b 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'b FStar_Syntax_Embeddings_Base.embedding ->
              'b FStar_TypeChecker_NBETerm.embedding ->
                'r FStar_Syntax_Embeddings_Base.embedding ->
                  'r FStar_TypeChecker_NBETerm.embedding ->
                    ('a -> 'b -> 'r FStar_Pervasives_Native.option) ->
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
                    let interp psc1 cb us args =
                      match args with
                      | (a1, uu___6)::(b1, uu___7)::[] ->
                          Obj.magic
                            (Obj.repr
                               (let uu___8 =
                                  let uu___9 =
                                    let uu___10 = try_unembed_simple uu___ a1 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_Less_Dollar_Greater
                                         FStar_Class_Monad.monad_option () ()
                                         (fun uu___11 ->
                                            (Obj.magic f) uu___11)
                                         (Obj.magic uu___10)) in
                                  let uu___10 = try_unembed_simple uu___2 b1 in
                                  Obj.magic
                                    (FStar_Class_Monad.op_Less_Star_Greater
                                       FStar_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9) (Obj.magic uu___10)) in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Class_Monad.monad_option () ()
                                  (Obj.magic uu___8)
                                  (fun uu___9 ->
                                     (fun r1 ->
                                        let r1 = Obj.magic r1 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Class_Monad.monad_option
                                             () () (Obj.magic r1)
                                             (fun uu___9 ->
                                                (fun r2 ->
                                                   let r2 = Obj.magic r2 in
                                                   let uu___9 =
                                                     embed_simple uu___4
                                                       psc1.psc_range r2 in
                                                   Obj.magic
                                                     (FStar_Class_Monad.return
                                                        FStar_Class_Monad.monad_option
                                                        () (Obj.magic uu___9)))
                                                  uu___9))) uu___9)))
                      | uu___6 ->
                          Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                    let nbe_interp cbs us args =
                      match args with
                      | (a1, uu___6)::(b1, uu___7)::[] ->
                          Obj.magic
                            (Obj.repr
                               (let uu___8 =
                                  let uu___9 =
                                    let uu___10 =
                                      FStar_TypeChecker_NBETerm.unembed
                                        (solve uu___1) cbs a1 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_Less_Dollar_Greater
                                         FStar_Class_Monad.monad_option () ()
                                         (fun uu___11 ->
                                            (Obj.magic f) uu___11)
                                         (Obj.magic uu___10)) in
                                  let uu___10 =
                                    FStar_TypeChecker_NBETerm.unembed
                                      (solve uu___3) cbs b1 in
                                  Obj.magic
                                    (FStar_Class_Monad.op_Less_Star_Greater
                                       FStar_Class_Monad.monad_option () ()
                                       (Obj.magic uu___9) (Obj.magic uu___10)) in
                                FStar_Class_Monad.op_let_Bang
                                  FStar_Class_Monad.monad_option () ()
                                  (Obj.magic uu___8)
                                  (fun uu___9 ->
                                     (fun r1 ->
                                        let r1 = Obj.magic r1 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             FStar_Class_Monad.monad_option
                                             () () (Obj.magic r1)
                                             (fun uu___9 ->
                                                (fun r2 ->
                                                   let r2 = Obj.magic r2 in
                                                   let uu___9 =
                                                     FStar_TypeChecker_NBETerm.embed
                                                       (solve uu___5) cbs r2 in
                                                   Obj.magic
                                                     (FStar_Class_Monad.return
                                                        FStar_Class_Monad.monad_option
                                                        () (Obj.magic uu___9)))
                                                  uu___9))) uu___9)))
                      | uu___6 ->
                          Obj.magic (Obj.repr FStar_Pervasives_Native.None) in
                    as_primitive_step_nbecbs true
                      (name, (Prims.of_int (2)), u_arity, interp, nbe_interp)
let mk3 :
  'a 'b 'c 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'b FStar_Syntax_Embeddings_Base.embedding ->
              'b FStar_TypeChecker_NBETerm.embedding ->
                'c FStar_Syntax_Embeddings_Base.embedding ->
                  'c FStar_TypeChecker_NBETerm.embedding ->
                    'r FStar_Syntax_Embeddings_Base.embedding ->
                      'r FStar_TypeChecker_NBETerm.embedding ->
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
                        let interp psc1 cb us args =
                          match args with
                          | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[] ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___11 =
                                      let uu___12 =
                                        let uu___13 =
                                          let uu___14 =
                                            try_unembed_simple uu___ a1 in
                                          Obj.magic
                                            (FStar_Class_Monad.op_Less_Dollar_Greater
                                               FStar_Class_Monad.monad_option
                                               () ()
                                               (fun uu___15 ->
                                                  (Obj.magic f) uu___15)
                                               (Obj.magic uu___14)) in
                                        let uu___14 =
                                          try_unembed_simple uu___2 b1 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_Less_Star_Greater
                                             FStar_Class_Monad.monad_option
                                             () () (Obj.magic uu___13)
                                             (Obj.magic uu___14)) in
                                      let uu___13 =
                                        try_unembed_simple uu___4 c1 in
                                      Obj.magic
                                        (FStar_Class_Monad.op_Less_Star_Greater
                                           FStar_Class_Monad.monad_option ()
                                           () (Obj.magic uu___12)
                                           (Obj.magic uu___13)) in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Class_Monad.monad_option () ()
                                      (Obj.magic uu___11)
                                      (fun uu___12 ->
                                         (fun r1 ->
                                            let r1 = Obj.magic r1 in
                                            let uu___12 =
                                              embed_simple uu___6
                                                psc1.psc_range r1 in
                                            Obj.magic
                                              (FStar_Class_Monad.return
                                                 FStar_Class_Monad.monad_option
                                                 () (Obj.magic uu___12)))
                                           uu___12)))
                          | uu___8 ->
                              Obj.magic
                                (Obj.repr FStar_Pervasives_Native.None) in
                        let nbe_interp cbs us args =
                          match args with
                          | (a1, uu___8)::(b1, uu___9)::(c1, uu___10)::[] ->
                              Obj.magic
                                (Obj.repr
                                   (let uu___11 =
                                      let uu___12 =
                                        let uu___13 =
                                          let uu___14 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              (solve uu___1) cbs a1 in
                                          Obj.magic
                                            (FStar_Class_Monad.op_Less_Dollar_Greater
                                               FStar_Class_Monad.monad_option
                                               () ()
                                               (fun uu___15 ->
                                                  (Obj.magic f) uu___15)
                                               (Obj.magic uu___14)) in
                                        let uu___14 =
                                          FStar_TypeChecker_NBETerm.unembed
                                            (solve uu___3) cbs b1 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_Less_Star_Greater
                                             FStar_Class_Monad.monad_option
                                             () () (Obj.magic uu___13)
                                             (Obj.magic uu___14)) in
                                      let uu___13 =
                                        FStar_TypeChecker_NBETerm.unembed
                                          (solve uu___5) cbs c1 in
                                      Obj.magic
                                        (FStar_Class_Monad.op_Less_Star_Greater
                                           FStar_Class_Monad.monad_option ()
                                           () (Obj.magic uu___12)
                                           (Obj.magic uu___13)) in
                                    FStar_Class_Monad.op_let_Bang
                                      FStar_Class_Monad.monad_option () ()
                                      (Obj.magic uu___11)
                                      (fun uu___12 ->
                                         (fun r1 ->
                                            let r1 = Obj.magic r1 in
                                            let uu___12 =
                                              FStar_TypeChecker_NBETerm.embed
                                                (solve uu___7) cbs r1 in
                                            Obj.magic
                                              (FStar_Class_Monad.return
                                                 FStar_Class_Monad.monad_option
                                                 () (Obj.magic uu___12)))
                                           uu___12)))
                          | uu___8 ->
                              Obj.magic
                                (Obj.repr FStar_Pervasives_Native.None) in
                        as_primitive_step_nbecbs true
                          (name, (Prims.of_int (3)), u_arity, interp,
                            nbe_interp)
let mk4 :
  'a 'b 'c 'd 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'b FStar_Syntax_Embeddings_Base.embedding ->
              'b FStar_TypeChecker_NBETerm.embedding ->
                'c FStar_Syntax_Embeddings_Base.embedding ->
                  'c FStar_TypeChecker_NBETerm.embedding ->
                    'd FStar_Syntax_Embeddings_Base.embedding ->
                      'd FStar_TypeChecker_NBETerm.embedding ->
                        'r FStar_Syntax_Embeddings_Base.embedding ->
                          'r FStar_TypeChecker_NBETerm.embedding ->
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
                            let interp psc1 cb us args =
                              match args with
                              | (a1, uu___10)::(b1, uu___11)::(c1, uu___12)::
                                  (d1, uu___13)::(e, uu___14)::[] ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___15 =
                                          let uu___16 =
                                            let uu___17 =
                                              let uu___18 =
                                                let uu___19 =
                                                  try_unembed_simple uu___ a1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_Less_Dollar_Greater
                                                     FStar_Class_Monad.monad_option
                                                     () ()
                                                     (fun uu___20 ->
                                                        (Obj.magic f) uu___20)
                                                     (Obj.magic uu___19)) in
                                              let uu___19 =
                                                try_unembed_simple uu___2 b1 in
                                              Obj.magic
                                                (FStar_Class_Monad.op_Less_Star_Greater
                                                   FStar_Class_Monad.monad_option
                                                   () () (Obj.magic uu___18)
                                                   (Obj.magic uu___19)) in
                                            let uu___18 =
                                              try_unembed_simple uu___4 c1 in
                                            Obj.magic
                                              (FStar_Class_Monad.op_Less_Star_Greater
                                                 FStar_Class_Monad.monad_option
                                                 () () (Obj.magic uu___17)
                                                 (Obj.magic uu___18)) in
                                          let uu___17 =
                                            try_unembed_simple uu___6 d1 in
                                          Obj.magic
                                            (FStar_Class_Monad.op_Less_Star_Greater
                                               FStar_Class_Monad.monad_option
                                               () () (Obj.magic uu___16)
                                               (Obj.magic uu___17)) in
                                        FStar_Class_Monad.op_let_Bang
                                          FStar_Class_Monad.monad_option ()
                                          () (Obj.magic uu___15)
                                          (fun uu___16 ->
                                             (fun r1 ->
                                                let r1 = Obj.magic r1 in
                                                let uu___16 =
                                                  embed_simple uu___8
                                                    psc1.psc_range r1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.return
                                                     FStar_Class_Monad.monad_option
                                                     () (Obj.magic uu___16)))
                                               uu___16)))
                              | uu___10 ->
                                  Obj.magic
                                    (Obj.repr FStar_Pervasives_Native.None) in
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
                                                  FStar_TypeChecker_NBETerm.unembed
                                                    (solve uu___1) cbs a1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_Less_Dollar_Greater
                                                     FStar_Class_Monad.monad_option
                                                     () ()
                                                     (fun uu___19 ->
                                                        (Obj.magic f) uu___19)
                                                     (Obj.magic uu___18)) in
                                              let uu___18 =
                                                FStar_TypeChecker_NBETerm.unembed
                                                  (solve uu___3) cbs b1 in
                                              Obj.magic
                                                (FStar_Class_Monad.op_Less_Star_Greater
                                                   FStar_Class_Monad.monad_option
                                                   () () (Obj.magic uu___17)
                                                   (Obj.magic uu___18)) in
                                            let uu___17 =
                                              FStar_TypeChecker_NBETerm.unembed
                                                (solve uu___5) cbs c1 in
                                            Obj.magic
                                              (FStar_Class_Monad.op_Less_Star_Greater
                                                 FStar_Class_Monad.monad_option
                                                 () () (Obj.magic uu___16)
                                                 (Obj.magic uu___17)) in
                                          let uu___16 =
                                            FStar_TypeChecker_NBETerm.unembed
                                              (solve uu___7) cbs d1 in
                                          Obj.magic
                                            (FStar_Class_Monad.op_Less_Star_Greater
                                               FStar_Class_Monad.monad_option
                                               () () (Obj.magic uu___15)
                                               (Obj.magic uu___16)) in
                                        FStar_Class_Monad.op_let_Bang
                                          FStar_Class_Monad.monad_option ()
                                          () (Obj.magic uu___14)
                                          (fun uu___15 ->
                                             (fun r1 ->
                                                let r1 = Obj.magic r1 in
                                                let uu___15 =
                                                  FStar_TypeChecker_NBETerm.embed
                                                    (solve uu___9) cbs r1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.return
                                                     FStar_Class_Monad.monad_option
                                                     () (Obj.magic uu___15)))
                                               uu___15)))
                              | uu___10 ->
                                  Obj.magic
                                    (Obj.repr FStar_Pervasives_Native.None) in
                            as_primitive_step_nbecbs true
                              (name, (Prims.of_int (4)), u_arity, interp,
                                nbe_interp)
let mk5 :
  'a 'b 'c 'd 'e 'r .
    Prims.int ->
      FStar_Ident.lid ->
        'a FStar_Syntax_Embeddings_Base.embedding ->
          'a FStar_TypeChecker_NBETerm.embedding ->
            'b FStar_Syntax_Embeddings_Base.embedding ->
              'b FStar_TypeChecker_NBETerm.embedding ->
                'c FStar_Syntax_Embeddings_Base.embedding ->
                  'c FStar_TypeChecker_NBETerm.embedding ->
                    'd FStar_Syntax_Embeddings_Base.embedding ->
                      'd FStar_TypeChecker_NBETerm.embedding ->
                        'e FStar_Syntax_Embeddings_Base.embedding ->
                          'e FStar_TypeChecker_NBETerm.embedding ->
                            'r FStar_Syntax_Embeddings_Base.embedding ->
                              'r FStar_TypeChecker_NBETerm.embedding ->
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
                                                        (FStar_Class_Monad.op_Less_Dollar_Greater
                                                           FStar_Class_Monad.monad_option
                                                           () ()
                                                           (fun uu___23 ->
                                                              (Obj.magic f)
                                                                uu___23)
                                                           (Obj.magic uu___22)) in
                                                    let uu___22 =
                                                      try_unembed_simple
                                                        uu___2 b1 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.op_Less_Star_Greater
                                                         FStar_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___21)
                                                         (Obj.magic uu___22)) in
                                                  let uu___21 =
                                                    try_unembed_simple uu___4
                                                      c1 in
                                                  Obj.magic
                                                    (FStar_Class_Monad.op_Less_Star_Greater
                                                       FStar_Class_Monad.monad_option
                                                       () ()
                                                       (Obj.magic uu___20)
                                                       (Obj.magic uu___21)) in
                                                let uu___20 =
                                                  try_unembed_simple uu___6
                                                    d1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_Less_Star_Greater
                                                     FStar_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___19)
                                                     (Obj.magic uu___20)) in
                                              let uu___19 =
                                                try_unembed_simple uu___8 e1 in
                                              Obj.magic
                                                (FStar_Class_Monad.op_Less_Star_Greater
                                                   FStar_Class_Monad.monad_option
                                                   () () (Obj.magic uu___18)
                                                   (Obj.magic uu___19)) in
                                            FStar_Class_Monad.op_let_Bang
                                              FStar_Class_Monad.monad_option
                                              () () (Obj.magic uu___17)
                                              (fun uu___18 ->
                                                 (fun r1 ->
                                                    let r1 = Obj.magic r1 in
                                                    let uu___18 =
                                                      embed_simple uu___10
                                                        psc1.psc_range r1 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.return
                                                         FStar_Class_Monad.monad_option
                                                         ()
                                                         (Obj.magic uu___18)))
                                                   uu___18)))
                                  | uu___12 ->
                                      Obj.magic
                                        (Obj.repr
                                           FStar_Pervasives_Native.None) in
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
                                                        FStar_TypeChecker_NBETerm.unembed
                                                          (solve uu___1) cbs
                                                          a1 in
                                                      Obj.magic
                                                        (FStar_Class_Monad.op_Less_Dollar_Greater
                                                           FStar_Class_Monad.monad_option
                                                           () ()
                                                           (fun uu___23 ->
                                                              (Obj.magic f)
                                                                uu___23)
                                                           (Obj.magic uu___22)) in
                                                    let uu___22 =
                                                      FStar_TypeChecker_NBETerm.unembed
                                                        (solve uu___3) cbs b1 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.op_Less_Star_Greater
                                                         FStar_Class_Monad.monad_option
                                                         () ()
                                                         (Obj.magic uu___21)
                                                         (Obj.magic uu___22)) in
                                                  let uu___21 =
                                                    FStar_TypeChecker_NBETerm.unembed
                                                      (solve uu___5) cbs c1 in
                                                  Obj.magic
                                                    (FStar_Class_Monad.op_Less_Star_Greater
                                                       FStar_Class_Monad.monad_option
                                                       () ()
                                                       (Obj.magic uu___20)
                                                       (Obj.magic uu___21)) in
                                                let uu___20 =
                                                  FStar_TypeChecker_NBETerm.unembed
                                                    (solve uu___7) cbs d1 in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_Less_Star_Greater
                                                     FStar_Class_Monad.monad_option
                                                     () ()
                                                     (Obj.magic uu___19)
                                                     (Obj.magic uu___20)) in
                                              let uu___19 =
                                                FStar_TypeChecker_NBETerm.unembed
                                                  (solve uu___9) cbs e1 in
                                              Obj.magic
                                                (FStar_Class_Monad.op_Less_Star_Greater
                                                   FStar_Class_Monad.monad_option
                                                   () () (Obj.magic uu___18)
                                                   (Obj.magic uu___19)) in
                                            FStar_Class_Monad.op_let_Bang
                                              FStar_Class_Monad.monad_option
                                              () () (Obj.magic uu___17)
                                              (fun uu___18 ->
                                                 (fun r1 ->
                                                    let r1 = Obj.magic r1 in
                                                    let uu___18 =
                                                      FStar_TypeChecker_NBETerm.embed
                                                        (solve uu___11) cbs
                                                        r1 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.return
                                                         FStar_Class_Monad.monad_option
                                                         ()
                                                         (Obj.magic uu___18)))
                                                   uu___18)))
                                  | uu___12 ->
                                      Obj.magic
                                        (Obj.repr
                                           FStar_Pervasives_Native.None) in
                                as_primitive_step_nbecbs true
                                  (name, (Prims.of_int (5)), u_arity, interp,
                                    nbe_interp)
let mixed_binary_op :
  'a 'b 'c .
    (FStar_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.arg -> 'b FStar_Pervasives_Native.option) ->
        (FStar_Compiler_Range_Type.range -> 'c -> FStar_Syntax_Syntax.term)
          ->
          (FStar_Compiler_Range_Type.range ->
             FStar_Syntax_Syntax.universes ->
               'a -> 'b -> 'c FStar_Pervasives_Native.option)
            ->
            psc ->
              FStar_Syntax_Embeddings_Base.norm_cb ->
                FStar_Syntax_Syntax.universes ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun embed_c ->
        fun f ->
          fun psc1 ->
            fun norm_cb ->
              fun univs ->
                fun args ->
                  match args with
                  | a1::b1::[] ->
                      let uu___ =
                        let uu___1 = as_a a1 in
                        let uu___2 = as_b b1 in (uu___1, uu___2) in
                      (match uu___ with
                       | (FStar_Pervasives_Native.Some a2,
                          FStar_Pervasives_Native.Some b2) ->
                           let uu___1 = f psc1.psc_range univs a2 b2 in
                           (match uu___1 with
                            | FStar_Pervasives_Native.Some c1 ->
                                let uu___2 = embed_c psc1.psc_range c1 in
                                FStar_Pervasives_Native.Some uu___2
                            | uu___2 -> FStar_Pervasives_Native.None)
                       | uu___1 -> FStar_Pervasives_Native.None)
                  | uu___ -> FStar_Pervasives_Native.None
let mixed_ternary_op :
  'a 'b 'c 'd .
    (FStar_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.arg -> 'b FStar_Pervasives_Native.option) ->
        (FStar_Syntax_Syntax.arg -> 'c FStar_Pervasives_Native.option) ->
          (FStar_Compiler_Range_Type.range -> 'd -> FStar_Syntax_Syntax.term)
            ->
            (FStar_Compiler_Range_Type.range ->
               FStar_Syntax_Syntax.universes ->
                 'a -> 'b -> 'c -> 'd FStar_Pervasives_Native.option)
              ->
              psc ->
                FStar_Syntax_Embeddings_Base.norm_cb ->
                  FStar_Syntax_Syntax.universes ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun as_c ->
        fun embed_d ->
          fun f ->
            fun psc1 ->
              fun norm_cb ->
                fun univs ->
                  fun args ->
                    match args with
                    | a1::b1::c1::[] ->
                        let uu___ =
                          let uu___1 = as_a a1 in
                          let uu___2 = as_b b1 in
                          let uu___3 = as_c c1 in (uu___1, uu___2, uu___3) in
                        (match uu___ with
                         | (FStar_Pervasives_Native.Some a2,
                            FStar_Pervasives_Native.Some b2,
                            FStar_Pervasives_Native.Some c2) ->
                             let uu___1 = f psc1.psc_range univs a2 b2 c2 in
                             (match uu___1 with
                              | FStar_Pervasives_Native.Some d1 ->
                                  let uu___2 = embed_d psc1.psc_range d1 in
                                  FStar_Pervasives_Native.Some uu___2
                              | uu___2 -> FStar_Pervasives_Native.None)
                         | uu___1 -> FStar_Pervasives_Native.None)
                    | uu___ -> FStar_Pervasives_Native.None
let decidable_eq :
  'uuuuu 'uuuuu1 .
    Prims.bool ->
      psc ->
        'uuuuu ->
          'uuuuu1 ->
            FStar_Syntax_Syntax.args ->
              FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun neg ->
    fun psc1 ->
      fun _norm_cb ->
        fun _us ->
          fun args ->
            let r = psc1.psc_range in
            let tru =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool true)) r in
            let fal =
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_bool false)) r in
            match args with
            | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
                let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
                (match uu___3 with
                 | FStar_Syntax_Util.Equal ->
                     FStar_Pervasives_Native.Some (if neg then fal else tru)
                 | FStar_Syntax_Util.NotEqual ->
                     FStar_Pervasives_Native.Some (if neg then tru else fal)
                 | uu___4 -> FStar_Pervasives_Native.None)
            | uu___ ->
                FStar_Compiler_Effect.failwith
                  "Unexpected number of arguments"
let (and_op :
  psc ->
    FStar_Syntax_Embeddings_Base.norm_cb ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc1 ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ =
                try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (false) ->
                   let uu___1 =
                     embed_simple FStar_Syntax_Embeddings.e_bool
                       psc1.psc_range false in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives_Native.Some (true) ->
                   FStar_Pervasives_Native.Some a2
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ ->
              FStar_Compiler_Effect.failwith "Unexpected number of arguments"
let (or_op :
  psc ->
    FStar_Syntax_Embeddings_Base.norm_cb ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc1 ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ =
                try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (true) ->
                   let uu___1 =
                     embed_simple FStar_Syntax_Embeddings.e_bool
                       psc1.psc_range true in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives_Native.Some (false) ->
                   FStar_Pervasives_Native.Some a2
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ ->
              FStar_Compiler_Effect.failwith "Unexpected number of arguments"
let (division_modulus_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    FStar_BigInt.t ->
      FStar_BigInt.t -> FStar_BigInt.t FStar_Pervasives_Native.option)
  =
  fun f ->
    fun x ->
      fun y ->
        let uu___ =
          let uu___1 = FStar_BigInt.to_int_fs y in uu___1 <> Prims.int_zero in
        if uu___
        then let uu___1 = f x y in FStar_Pervasives_Native.Some uu___1
        else FStar_Pervasives_Native.None
let (simple_ops : primitive_step Prims.list) =
  let uu___ =
    mk1 Prims.int_zero FStar_Parser_Const.string_of_int_lid
      FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
      FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
      (fun z ->
         let uu___1 = FStar_BigInt.to_int_fs z in Prims.string_of_int uu___1) in
  let uu___1 =
    let uu___2 =
      mk1 Prims.int_zero FStar_Parser_Const.int_of_string_lid
        FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
        (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_int)
        (FStar_TypeChecker_NBETerm.e_option FStar_TypeChecker_NBETerm.e_int)
        (fun uu___3 ->
           (fun s ->
              let uu___3 = FStar_Compiler_Util.safe_int_of_string s in
              Obj.magic
                (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option () ()
                   (fun uu___4 -> (Obj.magic FStar_BigInt.of_int_fs) uu___4)
                   (Obj.magic uu___3))) uu___3) in
    let uu___3 =
      let uu___4 =
        mk1 Prims.int_zero FStar_Parser_Const.string_of_bool_lid
          FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool
          FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
          Prims.string_of_bool in
      let uu___5 =
        let uu___6 =
          mk1 Prims.int_zero FStar_Parser_Const.bool_of_string_lid
            FStar_Syntax_Embeddings.e_string
            FStar_TypeChecker_NBETerm.e_string
            (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_bool)
            (FStar_TypeChecker_NBETerm.e_option
               FStar_TypeChecker_NBETerm.e_bool)
            (fun uu___7 ->
               match uu___7 with
               | "true" -> FStar_Pervasives_Native.Some true
               | "false" -> FStar_Pervasives_Native.Some false
               | uu___8 -> FStar_Pervasives_Native.None) in
        let uu___7 =
          let uu___8 =
            mk1 Prims.int_zero FStar_Parser_Const.op_Minus
              FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
              FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
              FStar_BigInt.minus_big_int in
          let uu___9 =
            let uu___10 =
              mk2 Prims.int_zero FStar_Parser_Const.op_Addition
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_Syntax_Embeddings.e_int FStar_TypeChecker_NBETerm.e_int
                FStar_BigInt.add_big_int in
            let uu___11 =
              let uu___12 =
                mk2 Prims.int_zero FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int FStar_BigInt.sub_big_int in
              let uu___13 =
                let uu___14 =
                  mk2 Prims.int_zero FStar_Parser_Const.op_Multiply
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int FStar_BigInt.mult_big_int in
                let uu___15 =
                  let uu___16 =
                    mk2 Prims.int_zero FStar_Parser_Const.op_LT
                      FStar_Syntax_Embeddings.e_int
                      FStar_TypeChecker_NBETerm.e_int
                      FStar_Syntax_Embeddings.e_int
                      FStar_TypeChecker_NBETerm.e_int
                      FStar_Syntax_Embeddings.e_bool
                      FStar_TypeChecker_NBETerm.e_bool
                      FStar_BigInt.lt_big_int in
                  let uu___17 =
                    let uu___18 =
                      mk2 Prims.int_zero FStar_Parser_Const.op_LTE
                        FStar_Syntax_Embeddings.e_int
                        FStar_TypeChecker_NBETerm.e_int
                        FStar_Syntax_Embeddings.e_int
                        FStar_TypeChecker_NBETerm.e_int
                        FStar_Syntax_Embeddings.e_bool
                        FStar_TypeChecker_NBETerm.e_bool
                        FStar_BigInt.le_big_int in
                    let uu___19 =
                      let uu___20 =
                        mk2 Prims.int_zero FStar_Parser_Const.op_GT
                          FStar_Syntax_Embeddings.e_int
                          FStar_TypeChecker_NBETerm.e_int
                          FStar_Syntax_Embeddings.e_int
                          FStar_TypeChecker_NBETerm.e_int
                          FStar_Syntax_Embeddings.e_bool
                          FStar_TypeChecker_NBETerm.e_bool
                          FStar_BigInt.gt_big_int in
                      let uu___21 =
                        let uu___22 =
                          mk2 Prims.int_zero FStar_Parser_Const.op_GTE
                            FStar_Syntax_Embeddings.e_int
                            FStar_TypeChecker_NBETerm.e_int
                            FStar_Syntax_Embeddings.e_int
                            FStar_TypeChecker_NBETerm.e_int
                            FStar_Syntax_Embeddings.e_bool
                            FStar_TypeChecker_NBETerm.e_bool
                            FStar_BigInt.ge_big_int in
                        let uu___23 =
                          let uu___24 =
                            mk2' Prims.int_zero
                              FStar_Parser_Const.op_Division
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              (division_modulus_op FStar_BigInt.div_big_int) in
                          let uu___25 =
                            let uu___26 =
                              mk2' Prims.int_zero
                                FStar_Parser_Const.op_Modulus
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                (division_modulus_op FStar_BigInt.mod_big_int) in
                            let uu___27 =
                              let uu___28 =
                                mk1 Prims.int_zero
                                  FStar_Parser_Const.op_Negation
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_TypeChecker_NBETerm.e_bool
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_TypeChecker_NBETerm.e_bool
                                  Prims.op_Negation in
                              let uu___29 =
                                let uu___30 =
                                  mk2 Prims.int_zero
                                    FStar_Parser_Const.string_concat_lid
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_TypeChecker_NBETerm.e_string
                                    FStar_Syntax_Embeddings.e_string_list
                                    FStar_TypeChecker_NBETerm.e_string_list
                                    FStar_Syntax_Embeddings.e_string
                                    FStar_TypeChecker_NBETerm.e_string
                                    FStar_Compiler_String.concat in
                                let uu___31 =
                                  let uu___32 =
                                    mk2 Prims.int_zero
                                      FStar_Parser_Const.string_split_lid
                                      (FStar_Syntax_Embeddings.e_list
                                         FStar_Syntax_Embeddings.e_char)
                                      (FStar_TypeChecker_NBETerm.e_list
                                         FStar_TypeChecker_NBETerm.e_char)
                                      FStar_Syntax_Embeddings.e_string
                                      FStar_TypeChecker_NBETerm.e_string
                                      FStar_Syntax_Embeddings.e_string_list
                                      FStar_TypeChecker_NBETerm.e_string_list
                                      FStar_Compiler_String.split in
                                  let uu___33 =
                                    let uu___34 =
                                      mk2 Prims.int_zero
                                        FStar_Parser_Const.prims_strcat_lid
                                        FStar_Syntax_Embeddings.e_string
                                        FStar_TypeChecker_NBETerm.e_string
                                        FStar_Syntax_Embeddings.e_string
                                        FStar_TypeChecker_NBETerm.e_string
                                        FStar_Syntax_Embeddings.e_string
                                        FStar_TypeChecker_NBETerm.e_string
                                        (fun s1 ->
                                           fun s2 -> Prims.strcat s1 s2) in
                                    let uu___35 =
                                      let uu___36 =
                                        mk2 Prims.int_zero
                                          FStar_Parser_Const.string_compare_lid
                                          FStar_Syntax_Embeddings.e_string
                                          FStar_TypeChecker_NBETerm.e_string
                                          FStar_Syntax_Embeddings.e_string
                                          FStar_TypeChecker_NBETerm.e_string
                                          FStar_Syntax_Embeddings.e_int
                                          FStar_TypeChecker_NBETerm.e_int
                                          (fun s1 ->
                                             fun s2 ->
                                               FStar_BigInt.of_int_fs
                                                 (FStar_Compiler_String.compare
                                                    s1 s2)) in
                                      let uu___37 =
                                        let uu___38 =
                                          mk1 Prims.int_zero
                                            FStar_Parser_Const.string_string_of_list_lid
                                            (FStar_Syntax_Embeddings.e_list
                                               FStar_Syntax_Embeddings.e_char)
                                            (FStar_TypeChecker_NBETerm.e_list
                                               FStar_TypeChecker_NBETerm.e_char)
                                            FStar_Syntax_Embeddings.e_string
                                            FStar_TypeChecker_NBETerm.e_string
                                            FStar_String.string_of_list in
                                        let uu___39 =
                                          let uu___40 =
                                            mk2 Prims.int_zero
                                              FStar_Parser_Const.string_make_lid
                                              FStar_Syntax_Embeddings.e_int
                                              FStar_TypeChecker_NBETerm.e_int
                                              FStar_Syntax_Embeddings.e_char
                                              FStar_TypeChecker_NBETerm.e_char
                                              FStar_Syntax_Embeddings.e_string
                                              FStar_TypeChecker_NBETerm.e_string
                                              (fun x ->
                                                 fun y ->
                                                   let uu___41 =
                                                     FStar_BigInt.to_int_fs x in
                                                   FStar_Compiler_String.make
                                                     uu___41 y) in
                                          let uu___41 =
                                            let uu___42 =
                                              mk1 Prims.int_zero
                                                FStar_Parser_Const.string_list_of_string_lid
                                                FStar_Syntax_Embeddings.e_string
                                                FStar_TypeChecker_NBETerm.e_string
                                                (FStar_Syntax_Embeddings.e_list
                                                   FStar_Syntax_Embeddings.e_char)
                                                (FStar_TypeChecker_NBETerm.e_list
                                                   FStar_TypeChecker_NBETerm.e_char)
                                                FStar_String.list_of_string in
                                            let uu___43 =
                                              let uu___44 =
                                                mk1 Prims.int_zero
                                                  FStar_Parser_Const.string_lowercase_lid
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_TypeChecker_NBETerm.e_string
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_TypeChecker_NBETerm.e_string
                                                  FStar_Compiler_String.lowercase in
                                              let uu___45 =
                                                let uu___46 =
                                                  mk1 Prims.int_zero
                                                    FStar_Parser_Const.string_uppercase_lid
                                                    FStar_Syntax_Embeddings.e_string
                                                    FStar_TypeChecker_NBETerm.e_string
                                                    FStar_Syntax_Embeddings.e_string
                                                    FStar_TypeChecker_NBETerm.e_string
                                                    FStar_Compiler_String.uppercase in
                                                let uu___47 =
                                                  let uu___48 =
                                                    mk2 Prims.int_zero
                                                      FStar_Parser_Const.string_index_lid
                                                      FStar_Syntax_Embeddings.e_string
                                                      FStar_TypeChecker_NBETerm.e_string
                                                      FStar_Syntax_Embeddings.e_int
                                                      FStar_TypeChecker_NBETerm.e_int
                                                      FStar_Syntax_Embeddings.e_char
                                                      FStar_TypeChecker_NBETerm.e_char
                                                      FStar_Compiler_String.index in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 Prims.int_zero
                                                        FStar_Parser_Const.string_index_of_lid
                                                        FStar_Syntax_Embeddings.e_string
                                                        FStar_TypeChecker_NBETerm.e_string
                                                        FStar_Syntax_Embeddings.e_char
                                                        FStar_TypeChecker_NBETerm.e_char
                                                        FStar_Syntax_Embeddings.e_int
                                                        FStar_TypeChecker_NBETerm.e_int
                                                        FStar_Compiler_String.index_of in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        mk3 Prims.int_zero
                                                          FStar_Parser_Const.string_sub_lid
                                                          FStar_Syntax_Embeddings.e_string
                                                          FStar_TypeChecker_NBETerm.e_string
                                                          FStar_Syntax_Embeddings.e_int
                                                          FStar_TypeChecker_NBETerm.e_int
                                                          FStar_Syntax_Embeddings.e_int
                                                          FStar_TypeChecker_NBETerm.e_int
                                                          FStar_Syntax_Embeddings.e_string
                                                          FStar_TypeChecker_NBETerm.e_string
                                                          (fun s ->
                                                             fun o ->
                                                               fun l ->
                                                                 let uu___53
                                                                   =
                                                                   FStar_BigInt.to_int_fs
                                                                    o in
                                                                 let uu___54
                                                                   =
                                                                   FStar_BigInt.to_int_fs
                                                                    l in
                                                                 FStar_Compiler_String.substring
                                                                   s uu___53
                                                                   uu___54) in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          mk5 Prims.int_zero
                                                            FStar_Parser_Const.mk_range_lid
                                                            FStar_Syntax_Embeddings.e_string
                                                            FStar_TypeChecker_NBETerm.e_string
                                                            FStar_Syntax_Embeddings.e_int
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            FStar_Syntax_Embeddings.e_int
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            FStar_Syntax_Embeddings.e_int
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            FStar_Syntax_Embeddings.e_int
                                                            FStar_TypeChecker_NBETerm.e_int
                                                            FStar_Syntax_Embeddings.e_range
                                                            FStar_TypeChecker_NBETerm.e_range
                                                            (fun fn ->
                                                               fun from_l ->
                                                                 fun from_c
                                                                   ->
                                                                   fun to_l
                                                                    ->
                                                                    fun to_c
                                                                    ->
                                                                    let uu___55
                                                                    =
                                                                    let uu___56
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    from_l in
                                                                    let uu___57
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    from_c in
                                                                    FStar_Compiler_Range_Type.mk_pos
                                                                    uu___56
                                                                    uu___57 in
                                                                    let uu___56
                                                                    =
                                                                    let uu___57
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    to_l in
                                                                    let uu___58
                                                                    =
                                                                    FStar_BigInt.to_int_fs
                                                                    to_c in
                                                                    FStar_Compiler_Range_Type.mk_pos
                                                                    uu___57
                                                                    uu___58 in
                                                                    FStar_Compiler_Range_Type.mk_range
                                                                    fn
                                                                    uu___55
                                                                    uu___56) in
                                                        [uu___54] in
                                                      uu___52 :: uu___53 in
                                                    uu___50 :: uu___51 in
                                                  uu___48 :: uu___49 in
                                                uu___46 :: uu___47 in
                                              uu___44 :: uu___45 in
                                            uu___42 :: uu___43 in
                                          uu___40 :: uu___41 in
                                        uu___38 :: uu___39 in
                                      uu___36 :: uu___37 in
                                    uu___34 :: uu___35 in
                                  uu___32 :: uu___33 in
                                uu___30 :: uu___31 in
                              uu___28 :: uu___29 in
                            uu___26 :: uu___27 in
                          uu___24 :: uu___25 in
                        uu___22 :: uu___23 in
                      uu___20 :: uu___21 in
                    uu___18 :: uu___19 in
                  uu___16 :: uu___17 in
                uu___14 :: uu___15 in
              uu___12 :: uu___13 in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
let (bogus_cbs : FStar_TypeChecker_NBETerm.nbe_cbs) =
  {
    FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
    FStar_TypeChecker_NBETerm.translate =
      (fun uu___ -> FStar_Compiler_Effect.failwith "bogus_cbs translate")
  }
let (issue_ops : primitive_step Prims.list) =
  let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Issue"; l] in
  let uu___ =
    let uu___1 = mk_lid "message_of_issue" in
    mk1 Prims.int_zero uu___1 FStar_Syntax_Embeddings.e_issue
      FStar_TypeChecker_NBETerm.e_issue
      (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_document)
      (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_document)
      FStar_Errors.__proj__Mkissue__item__issue_msg in
  let uu___1 =
    let uu___2 =
      let uu___3 = mk_lid "level_of_issue" in
      mk1 Prims.int_zero uu___3 FStar_Syntax_Embeddings.e_issue
        FStar_TypeChecker_NBETerm.e_issue FStar_Syntax_Embeddings.e_string
        FStar_TypeChecker_NBETerm.e_string
        (fun i ->
           FStar_Errors.string_of_issue_level i.FStar_Errors.issue_level) in
    let uu___3 =
      let uu___4 =
        let uu___5 = mk_lid "number_of_issue" in
        mk1 Prims.int_zero uu___5 FStar_Syntax_Embeddings.e_issue
          FStar_TypeChecker_NBETerm.e_issue
          (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_int)
          (FStar_TypeChecker_NBETerm.e_option FStar_TypeChecker_NBETerm.e_int)
          (fun uu___6 ->
             (fun i ->
                Obj.magic
                  (FStar_Class_Monad.fmap FStar_Class_Monad.monad_option ()
                     ()
                     (fun uu___6 -> (Obj.magic FStar_BigInt.of_int_fs) uu___6)
                     (Obj.magic i.FStar_Errors.issue_number))) uu___6) in
      let uu___5 =
        let uu___6 =
          let uu___7 = mk_lid "range_of_issue" in
          mk1 Prims.int_zero uu___7 FStar_Syntax_Embeddings.e_issue
            FStar_TypeChecker_NBETerm.e_issue
            (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_range)
            (FStar_TypeChecker_NBETerm.e_option
               FStar_TypeChecker_NBETerm.e_range)
            FStar_Errors.__proj__Mkissue__item__issue_range in
        let uu___7 =
          let uu___8 =
            let uu___9 = mk_lid "context_of_issue" in
            mk1 Prims.int_zero uu___9 FStar_Syntax_Embeddings.e_issue
              FStar_TypeChecker_NBETerm.e_issue
              FStar_Syntax_Embeddings.e_string_list
              FStar_TypeChecker_NBETerm.e_string_list
              FStar_Errors.__proj__Mkissue__item__issue_ctx in
          let uu___9 =
            let uu___10 =
              let uu___11 = mk_lid "render_issue" in
              mk1 Prims.int_zero uu___11 FStar_Syntax_Embeddings.e_issue
                FStar_TypeChecker_NBETerm.e_issue
                FStar_Syntax_Embeddings.e_string
                FStar_TypeChecker_NBETerm.e_string FStar_Errors.format_issue in
            let uu___11 =
              let uu___12 =
                let uu___13 = mk_lid "mk_issue_doc" in
                mk5 Prims.int_zero uu___13 FStar_Syntax_Embeddings.e_string
                  FStar_TypeChecker_NBETerm.e_string
                  (FStar_Syntax_Embeddings.e_list
                     FStar_Syntax_Embeddings.e_document)
                  (FStar_TypeChecker_NBETerm.e_list
                     FStar_TypeChecker_NBETerm.e_document)
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Syntax_Embeddings.e_range)
                  (FStar_TypeChecker_NBETerm.e_option
                     FStar_TypeChecker_NBETerm.e_range)
                  (FStar_Syntax_Embeddings.e_option
                     FStar_Syntax_Embeddings.e_int)
                  (FStar_TypeChecker_NBETerm.e_option
                     FStar_TypeChecker_NBETerm.e_int)
                  FStar_Syntax_Embeddings.e_string_list
                  FStar_TypeChecker_NBETerm.e_string_list
                  FStar_Syntax_Embeddings.e_issue
                  FStar_TypeChecker_NBETerm.e_issue
                  (fun level ->
                     fun msg ->
                       fun range ->
                         fun number ->
                           fun context ->
                             let uu___14 =
                               FStar_Errors.issue_level_of_string level in
                             let uu___15 =
                               Obj.magic
                                 (FStar_Class_Monad.fmap
                                    FStar_Class_Monad.monad_option () ()
                                    (fun uu___16 ->
                                       (Obj.magic FStar_BigInt.to_int_fs)
                                         uu___16) (Obj.magic number)) in
                             {
                               FStar_Errors.issue_msg = msg;
                               FStar_Errors.issue_level = uu___14;
                               FStar_Errors.issue_range = range;
                               FStar_Errors.issue_number = uu___15;
                               FStar_Errors.issue_ctx = context
                             }) in
              [uu___12] in
            uu___10 :: uu___11 in
          uu___8 :: uu___9 in
        uu___6 :: uu___7 in
      uu___4 :: uu___5 in
    uu___2 :: uu___3 in
  uu___ :: uu___1
let (doc_ops : primitive_step Prims.list) =
  let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Stubs"; "Pprint"; l] in
  let uu___ =
    let uu___1 = mk_lid "arbitrary_string" in
    mk1 Prims.int_zero uu___1 FStar_Syntax_Embeddings.e_string
      FStar_TypeChecker_NBETerm.e_string FStar_Syntax_Embeddings.e_document
      FStar_TypeChecker_NBETerm.e_document FStar_Pprint.arbitrary_string in
  let uu___1 =
    let uu___2 =
      let uu___3 = mk_lid "render" in
      mk1 Prims.int_zero uu___3 FStar_Syntax_Embeddings.e_document
        FStar_TypeChecker_NBETerm.e_document FStar_Syntax_Embeddings.e_string
        FStar_TypeChecker_NBETerm.e_string FStar_Pprint.render in
    [uu___2] in
  uu___ :: uu___1
let (seal_steps : primitive_step Prims.list) =
  FStar_Compiler_List.map
    (fun p ->
       let uu___ = as_primitive_step_nbecbs true p in
       {
         name = (uu___.name);
         arity = (uu___.arity);
         univ_arity = (uu___.univ_arity);
         auto_reflect = (uu___.auto_reflect);
         strong_reduction_ok = (uu___.strong_reduction_ok);
         requires_binder_substitution = (uu___.requires_binder_substitution);
         renorm_after = true;
         interpretation = (uu___.interpretation);
         interpretation_nbe = (uu___.interpretation_nbe)
       })
    [(FStar_Parser_Const.map_seal_lid, (Prims.of_int (4)),
       (Prims.of_int (2)),
       ((fun psc1 ->
           fun univs ->
             fun cbs ->
               fun args ->
                 match args with
                 | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                     let try_unembed e x =
                       FStar_Syntax_Embeddings_Base.try_unembed e x
                         FStar_Syntax_Embeddings_Base.id_norm_cb in
                     let uu___4 =
                       let uu___5 =
                         try_unembed FStar_Syntax_Embeddings.e_any ta in
                       let uu___6 =
                         try_unembed FStar_Syntax_Embeddings.e_any tb in
                       let uu___7 =
                         try_unembed
                           (FStar_Syntax_Embeddings.e_sealed
                              FStar_Syntax_Embeddings.e_any) s in
                       let uu___8 =
                         try_unembed FStar_Syntax_Embeddings.e_any f in
                       (uu___5, uu___6, uu___7, uu___8) in
                     (match uu___4 with
                      | (FStar_Pervasives_Native.Some ta1,
                         FStar_Pervasives_Native.Some tb1,
                         FStar_Pervasives_Native.Some s1,
                         FStar_Pervasives_Native.Some f1) ->
                          let r =
                            let uu___5 =
                              let uu___6 = FStar_Syntax_Syntax.as_arg s1 in
                              [uu___6] in
                            FStar_Syntax_Util.mk_app f1 uu___5 in
                          let emb =
                            FStar_Syntax_Embeddings_Base.set_type ta1
                              FStar_Syntax_Embeddings.e_any in
                          let uu___5 =
                            embed_simple
                              (FStar_Syntax_Embeddings.e_sealed emb)
                              psc1.psc_range r in
                          FStar_Pervasives_Native.Some uu___5
                      | uu___5 -> FStar_Pervasives_Native.None)
                 | uu___ -> FStar_Pervasives_Native.None)),
       ((fun cb ->
           fun univs ->
             fun args ->
               match args with
               | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                   let try_unembed e x =
                     FStar_TypeChecker_NBETerm.unembed e bogus_cbs x in
                   let uu___4 =
                     let uu___5 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any ta in
                     let uu___6 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any tb in
                     let uu___7 =
                       let uu___8 =
                         FStar_TypeChecker_NBETerm.e_sealed
                           FStar_TypeChecker_NBETerm.e_any in
                       try_unembed uu___8 s in
                     let uu___8 =
                       try_unembed FStar_TypeChecker_NBETerm.e_any f in
                     (uu___5, uu___6, uu___7, uu___8) in
                   (match uu___4 with
                    | (FStar_Pervasives_Native.Some ta1,
                       FStar_Pervasives_Native.Some tb1,
                       FStar_Pervasives_Native.Some s1,
                       FStar_Pervasives_Native.Some f1) ->
                        let r =
                          let uu___5 =
                            let uu___6 = FStar_TypeChecker_NBETerm.as_arg s1 in
                            [uu___6] in
                          cb.FStar_TypeChecker_NBETerm.iapp f1 uu___5 in
                        let emb =
                          FStar_TypeChecker_NBETerm.set_type ta1
                            FStar_TypeChecker_NBETerm.e_any in
                        let uu___5 =
                          let uu___6 = FStar_TypeChecker_NBETerm.e_sealed emb in
                          FStar_TypeChecker_NBETerm.embed uu___6 cb r in
                        FStar_Pervasives_Native.Some uu___5
                    | uu___5 -> FStar_Pervasives_Native.None)
               | uu___ -> FStar_Pervasives_Native.None)));
    (FStar_Parser_Const.bind_seal_lid, (Prims.of_int (4)),
      (Prims.of_int (2)),
      ((fun psc1 ->
          fun univs ->
            fun cbs ->
              fun args ->
                match args with
                | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                    let try_unembed e x =
                      FStar_Syntax_Embeddings_Base.try_unembed e x
                        FStar_Syntax_Embeddings_Base.id_norm_cb in
                    let uu___4 =
                      let uu___5 =
                        try_unembed FStar_Syntax_Embeddings.e_any ta in
                      let uu___6 =
                        try_unembed FStar_Syntax_Embeddings.e_any tb in
                      let uu___7 =
                        try_unembed
                          (FStar_Syntax_Embeddings.e_sealed
                             FStar_Syntax_Embeddings.e_any) s in
                      let uu___8 =
                        try_unembed FStar_Syntax_Embeddings.e_any f in
                      (uu___5, uu___6, uu___7, uu___8) in
                    (match uu___4 with
                     | (FStar_Pervasives_Native.Some ta1,
                        FStar_Pervasives_Native.Some tb1,
                        FStar_Pervasives_Native.Some s1,
                        FStar_Pervasives_Native.Some f1) ->
                         let r =
                           let uu___5 =
                             let uu___6 = FStar_Syntax_Syntax.as_arg s1 in
                             [uu___6] in
                           FStar_Syntax_Util.mk_app f1 uu___5 in
                         let uu___5 =
                           embed_simple FStar_Syntax_Embeddings.e_any
                             psc1.psc_range r in
                         FStar_Pervasives_Native.Some uu___5
                     | uu___5 -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None)),
      ((fun cb ->
          fun univs ->
            fun args ->
              match args with
              | (ta, uu___)::(tb, uu___1)::(s, uu___2)::(f, uu___3)::[] ->
                  let try_unembed e x =
                    FStar_TypeChecker_NBETerm.unembed e bogus_cbs x in
                  let uu___4 =
                    let uu___5 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any ta in
                    let uu___6 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any tb in
                    let uu___7 =
                      let uu___8 =
                        FStar_TypeChecker_NBETerm.e_sealed
                          FStar_TypeChecker_NBETerm.e_any in
                      try_unembed uu___8 s in
                    let uu___8 =
                      try_unembed FStar_TypeChecker_NBETerm.e_any f in
                    (uu___5, uu___6, uu___7, uu___8) in
                  (match uu___4 with
                   | (FStar_Pervasives_Native.Some ta1,
                      FStar_Pervasives_Native.Some tb1,
                      FStar_Pervasives_Native.Some s1,
                      FStar_Pervasives_Native.Some f1) ->
                       let r =
                         let uu___5 =
                           let uu___6 = FStar_TypeChecker_NBETerm.as_arg s1 in
                           [uu___6] in
                         cb.FStar_TypeChecker_NBETerm.iapp f1 uu___5 in
                       let emb =
                         FStar_TypeChecker_NBETerm.set_type ta1
                           FStar_TypeChecker_NBETerm.e_any in
                       let uu___5 = FStar_TypeChecker_NBETerm.embed emb cb r in
                       FStar_Pervasives_Native.Some uu___5
                   | uu___5 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None)))]
let (built_in_primitive_steps_list : primitive_step Prims.list) =
  let int_as_bounded r int_to_t n =
    let c = embed_simple FStar_Syntax_Embeddings.e_int r n in
    let int_to_t1 = FStar_Syntax_Syntax.fv_to_tm int_to_t in
    let uu___ = let uu___1 = FStar_Syntax_Syntax.as_arg c in [uu___1] in
    FStar_Syntax_Syntax.mk_Tm_app int_to_t1 uu___ r in
  let with_meta_ds r t m =
    match m with
    | FStar_Pervasives_Native.None -> t
    | FStar_Pervasives_Native.Some m1 ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_meta
             {
               FStar_Syntax_Syntax.tm2 = t;
               FStar_Syntax_Syntax.meta =
                 (FStar_Syntax_Syntax.Meta_desugared m1)
             }) r in
  let basic_ops =
    let uu___ =
      let u32_int_to_t =
        let uu___1 = FStar_Parser_Const.p2l ["FStar"; "UInt32"; "uint_to_t"] in
        FStar_Syntax_Syntax.lid_as_fv uu___1 FStar_Pervasives_Native.None in
      let uu___1 =
        FStar_TypeChecker_NBETerm.unary_op
          FStar_TypeChecker_NBETerm.arg_as_char
          (fun c ->
             let uu___2 =
               FStar_BigInt.of_int_fs (FStar_Compiler_Util.int_of_char c) in
             FStar_TypeChecker_NBETerm.int_as_bounded u32_int_to_t uu___2) in
      (FStar_Parser_Const.char_u32_of_char, Prims.int_one, Prims.int_zero,
        (unary_op arg_as_char
           (fun r ->
              fun c ->
                let uu___2 =
                  FStar_BigInt.of_int_fs (FStar_Compiler_Util.int_of_char c) in
                int_as_bounded r u32_int_to_t uu___2)), uu___1) in
    [uu___;
    (FStar_Parser_Const.op_And, (Prims.of_int (2)), Prims.int_zero, and_op,
      ((fun uu___1 -> FStar_TypeChecker_NBETerm.and_op)));
    (FStar_Parser_Const.op_Or, (Prims.of_int (2)), Prims.int_zero, or_op,
      ((fun uu___1 -> FStar_TypeChecker_NBETerm.or_op)));
    (FStar_Parser_Const.op_Eq, (Prims.of_int (3)), Prims.int_zero,
      (decidable_eq false),
      ((fun uu___1 -> FStar_TypeChecker_NBETerm.decidable_eq false)));
    (FStar_Parser_Const.op_notEq, (Prims.of_int (3)), Prims.int_zero,
      (decidable_eq true),
      ((fun uu___1 -> FStar_TypeChecker_NBETerm.decidable_eq true)))] in
  let bounded_arith_ops =
    let bounded_signed_int_types =
      [("Int8", (Prims.of_int (8)));
      ("Int16", (Prims.of_int (16)));
      ("Int32", (Prims.of_int (32)));
      ("Int64", (Prims.of_int (64)))] in
    let bounded_unsigned_int_types =
      [("UInt8", (Prims.of_int (8)));
      ("UInt16", (Prims.of_int (16)));
      ("UInt32", (Prims.of_int (32)));
      ("UInt64", (Prims.of_int (64)));
      ("UInt128", (Prims.of_int (128)));
      ("SizeT", (Prims.of_int (64)))] in
    let add_sub_mul_v_comparisons =
      FStar_Compiler_List.collect
        (fun uu___ ->
           match uu___ with
           | (m, uu___1) ->
               let uu___2 =
                 let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "add"] in
                 let uu___4 =
                   FStar_TypeChecker_NBETerm.binary_op
                     FStar_TypeChecker_NBETerm.arg_as_bounded_int
                     (fun uu___5 ->
                        fun uu___6 ->
                          match (uu___5, uu___6) with
                          | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                              let uu___9 =
                                let uu___10 = FStar_BigInt.add_big_int x y in
                                FStar_TypeChecker_NBETerm.int_as_bounded
                                  int_to_t uu___10 in
                              FStar_TypeChecker_NBETerm.with_meta_ds uu___9
                                m1) in
                 (uu___3, (Prims.of_int (2)), Prims.int_zero,
                   (binary_op arg_as_bounded_int
                      (fun r ->
                         fun uu___5 ->
                           fun uu___6 ->
                             match (uu___5, uu___6) with
                             | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                 let uu___9 =
                                   let uu___10 = FStar_BigInt.add_big_int x y in
                                   int_as_bounded r int_to_t uu___10 in
                                 with_meta_ds r uu___9 m1)), uu___4) in
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStar_Parser_Const.p2l ["FStar"; m; "sub"] in
                   let uu___6 =
                     FStar_TypeChecker_NBETerm.binary_op
                       FStar_TypeChecker_NBETerm.arg_as_bounded_int
                       (fun uu___7 ->
                          fun uu___8 ->
                            match (uu___7, uu___8) with
                            | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                let uu___11 =
                                  let uu___12 = FStar_BigInt.sub_big_int x y in
                                  FStar_TypeChecker_NBETerm.int_as_bounded
                                    int_to_t uu___12 in
                                FStar_TypeChecker_NBETerm.with_meta_ds
                                  uu___11 m1) in
                   (uu___5, (Prims.of_int (2)), Prims.int_zero,
                     (binary_op arg_as_bounded_int
                        (fun r ->
                           fun uu___7 ->
                             fun uu___8 ->
                               match (uu___7, uu___8) with
                               | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_BigInt.sub_big_int x y in
                                     int_as_bounded r int_to_t uu___12 in
                                   with_meta_ds r uu___11 m1)), uu___6) in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                     let uu___8 =
                       FStar_TypeChecker_NBETerm.binary_op
                         FStar_TypeChecker_NBETerm.arg_as_bounded_int
                         (fun uu___9 ->
                            fun uu___10 ->
                              match (uu___9, uu___10) with
                              | ((int_to_t, x, m1), (uu___11, y, uu___12)) ->
                                  let uu___13 =
                                    let uu___14 =
                                      FStar_BigInt.mult_big_int x y in
                                    FStar_TypeChecker_NBETerm.int_as_bounded
                                      int_to_t uu___14 in
                                  FStar_TypeChecker_NBETerm.with_meta_ds
                                    uu___13 m1) in
                     (uu___7, (Prims.of_int (2)), Prims.int_zero,
                       (binary_op arg_as_bounded_int
                          (fun r ->
                             fun uu___9 ->
                               fun uu___10 ->
                                 match (uu___9, uu___10) with
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
                                     let uu___13 =
                                       let uu___14 =
                                         FStar_BigInt.mult_big_int x y in
                                       int_as_bounded r int_to_t uu___14 in
                                     with_meta_ds r uu___13 m1)), uu___8) in
                   let uu___7 =
                     let uu___8 =
                       let uu___9 = FStar_Parser_Const.p2l ["FStar"; m; "v"] in
                       let uu___10 =
                         FStar_TypeChecker_NBETerm.unary_op
                           FStar_TypeChecker_NBETerm.arg_as_bounded_int
                           (fun uu___11 ->
                              match uu___11 with
                              | (int_to_t, x, m1) ->
                                  let uu___12 =
                                    FStar_TypeChecker_NBETerm.embed
                                      FStar_TypeChecker_NBETerm.e_int
                                      bogus_cbs x in
                                  FStar_TypeChecker_NBETerm.with_meta_ds
                                    uu___12 m1) in
                       (uu___9, Prims.int_one, Prims.int_zero,
                         (unary_op arg_as_bounded_int
                            (fun r ->
                               fun uu___11 ->
                                 match uu___11 with
                                 | (int_to_t, x, m1) ->
                                     let uu___12 =
                                       embed_simple
                                         FStar_Syntax_Embeddings.e_int r x in
                                     with_meta_ds r uu___12 m1)), uu___10) in
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStar_Parser_Const.p2l ["FStar"; m; "gt"] in
                         let uu___12 =
                           FStar_TypeChecker_NBETerm.binary_op
                             FStar_TypeChecker_NBETerm.arg_as_bounded_int
                             (fun uu___13 ->
                                fun uu___14 ->
                                  match (uu___13, uu___14) with
                                  | ((int_to_t, x, m1),
                                     (uu___15, y, uu___16)) ->
                                      let uu___17 =
                                        let uu___18 =
                                          FStar_BigInt.gt_big_int x y in
                                        FStar_TypeChecker_NBETerm.embed
                                          FStar_TypeChecker_NBETerm.e_bool
                                          bogus_cbs uu___18 in
                                      FStar_TypeChecker_NBETerm.with_meta_ds
                                        uu___17 m1) in
                         (uu___11, (Prims.of_int (2)), Prims.int_zero,
                           (binary_op arg_as_bounded_int
                              (fun r ->
                                 fun uu___13 ->
                                   fun uu___14 ->
                                     match (uu___13, uu___14) with
                                     | ((int_to_t, x, m1),
                                        (uu___15, y, uu___16)) ->
                                         let uu___17 =
                                           let uu___18 =
                                             FStar_BigInt.gt_big_int x y in
                                           embed_simple
                                             FStar_Syntax_Embeddings.e_bool r
                                             uu___18 in
                                         with_meta_ds r uu___17 m1)),
                           uu___12) in
                       let uu___11 =
                         let uu___12 =
                           let uu___13 =
                             FStar_Parser_Const.p2l ["FStar"; m; "gte"] in
                           let uu___14 =
                             FStar_TypeChecker_NBETerm.binary_op
                               FStar_TypeChecker_NBETerm.arg_as_bounded_int
                               (fun uu___15 ->
                                  fun uu___16 ->
                                    match (uu___15, uu___16) with
                                    | ((int_to_t, x, m1),
                                       (uu___17, y, uu___18)) ->
                                        let uu___19 =
                                          let uu___20 =
                                            FStar_BigInt.ge_big_int x y in
                                          FStar_TypeChecker_NBETerm.embed
                                            FStar_TypeChecker_NBETerm.e_bool
                                            bogus_cbs uu___20 in
                                        FStar_TypeChecker_NBETerm.with_meta_ds
                                          uu___19 m1) in
                           (uu___13, (Prims.of_int (2)), Prims.int_zero,
                             (binary_op arg_as_bounded_int
                                (fun r ->
                                   fun uu___15 ->
                                     fun uu___16 ->
                                       match (uu___15, uu___16) with
                                       | ((int_to_t, x, m1),
                                          (uu___17, y, uu___18)) ->
                                           let uu___19 =
                                             let uu___20 =
                                               FStar_BigInt.ge_big_int x y in
                                             embed_simple
                                               FStar_Syntax_Embeddings.e_bool
                                               r uu___20 in
                                           with_meta_ds r uu___19 m1)),
                             uu___14) in
                         let uu___13 =
                           let uu___14 =
                             let uu___15 =
                               FStar_Parser_Const.p2l ["FStar"; m; "lt"] in
                             let uu___16 =
                               FStar_TypeChecker_NBETerm.binary_op
                                 FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                 (fun uu___17 ->
                                    fun uu___18 ->
                                      match (uu___17, uu___18) with
                                      | ((int_to_t, x, m1),
                                         (uu___19, y, uu___20)) ->
                                          let uu___21 =
                                            let uu___22 =
                                              FStar_BigInt.lt_big_int x y in
                                            FStar_TypeChecker_NBETerm.embed
                                              FStar_TypeChecker_NBETerm.e_bool
                                              bogus_cbs uu___22 in
                                          FStar_TypeChecker_NBETerm.with_meta_ds
                                            uu___21 m1) in
                             (uu___15, (Prims.of_int (2)), Prims.int_zero,
                               (binary_op arg_as_bounded_int
                                  (fun r ->
                                     fun uu___17 ->
                                       fun uu___18 ->
                                         match (uu___17, uu___18) with
                                         | ((int_to_t, x, m1),
                                            (uu___19, y, uu___20)) ->
                                             let uu___21 =
                                               let uu___22 =
                                                 FStar_BigInt.lt_big_int x y in
                                               embed_simple
                                                 FStar_Syntax_Embeddings.e_bool
                                                 r uu___22 in
                                             with_meta_ds r uu___21 m1)),
                               uu___16) in
                           let uu___15 =
                             let uu___16 =
                               let uu___17 =
                                 FStar_Parser_Const.p2l ["FStar"; m; "lte"] in
                               let uu___18 =
                                 FStar_TypeChecker_NBETerm.binary_op
                                   FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                   (fun uu___19 ->
                                      fun uu___20 ->
                                        match (uu___19, uu___20) with
                                        | ((int_to_t, x, m1),
                                           (uu___21, y, uu___22)) ->
                                            let uu___23 =
                                              let uu___24 =
                                                FStar_BigInt.le_big_int x y in
                                              FStar_TypeChecker_NBETerm.embed
                                                FStar_TypeChecker_NBETerm.e_bool
                                                bogus_cbs uu___24 in
                                            FStar_TypeChecker_NBETerm.with_meta_ds
                                              uu___23 m1) in
                               (uu___17, (Prims.of_int (2)), Prims.int_zero,
                                 (binary_op arg_as_bounded_int
                                    (fun r ->
                                       fun uu___19 ->
                                         fun uu___20 ->
                                           match (uu___19, uu___20) with
                                           | ((int_to_t, x, m1),
                                              (uu___21, y, uu___22)) ->
                                               let uu___23 =
                                                 let uu___24 =
                                                   FStar_BigInt.le_big_int x
                                                     y in
                                                 embed_simple
                                                   FStar_Syntax_Embeddings.e_bool
                                                   r uu___24 in
                                               with_meta_ds r uu___23 m1)),
                                 uu___18) in
                             [uu___16] in
                           uu___14 :: uu___15 in
                         uu___12 :: uu___13 in
                       uu___10 :: uu___11 in
                     uu___8 :: uu___9 in
                   uu___6 :: uu___7 in
                 uu___4 :: uu___5 in
               uu___2 :: uu___3)
        (FStar_Compiler_List.op_At bounded_signed_int_types
           bounded_unsigned_int_types) in
    let unsigned_modulo_add_sub_mul_div_rem =
      FStar_Compiler_List.collect
        (fun uu___ ->
           match uu___ with
           | (m, sz) ->
               let modulus =
                 let uu___1 = FStar_BigInt.of_int_fs sz in
                 FStar_BigInt.shift_left_big_int FStar_BigInt.one uu___1 in
               let mod1 x = FStar_BigInt.mod_big_int x modulus in
               let uu___1 =
                 if sz = (Prims.of_int (128))
                 then []
                 else
                   (let uu___3 =
                      let uu___4 =
                        FStar_Parser_Const.p2l ["FStar"; m; "mul_mod"] in
                      let uu___5 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_bounded_int
                          (fun uu___6 ->
                             fun uu___7 ->
                               match (uu___6, uu___7) with
                               | ((int_to_t, x, m1), (uu___8, y, uu___9)) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_BigInt.mult_big_int x y in
                                       mod1 uu___12 in
                                     FStar_TypeChecker_NBETerm.int_as_bounded
                                       int_to_t uu___11 in
                                   FStar_TypeChecker_NBETerm.with_meta_ds
                                     uu___10 m1) in
                      (uu___4, (Prims.of_int (2)), Prims.int_zero,
                        (binary_op arg_as_bounded_int
                           (fun r ->
                              fun uu___6 ->
                                fun uu___7 ->
                                  match (uu___6, uu___7) with
                                  | ((int_to_t, x, m1), (uu___8, y, uu___9))
                                      ->
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            FStar_BigInt.mult_big_int x y in
                                          mod1 uu___12 in
                                        int_as_bounded r int_to_t uu___11 in
                                      with_meta_ds r uu___10 m1)), uu___5) in
                    [uu___3]) in
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Parser_Const.p2l ["FStar"; m; "add_mod"] in
                   let uu___5 =
                     FStar_TypeChecker_NBETerm.binary_op
                       FStar_TypeChecker_NBETerm.arg_as_bounded_int
                       (fun uu___6 ->
                          fun uu___7 ->
                            match (uu___6, uu___7) with
                            | ((int_to_t, x, m1), (uu___8, y, uu___9)) ->
                                let uu___10 =
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_BigInt.add_big_int x y in
                                    mod1 uu___12 in
                                  FStar_TypeChecker_NBETerm.int_as_bounded
                                    int_to_t uu___11 in
                                FStar_TypeChecker_NBETerm.with_meta_ds
                                  uu___10 m1) in
                   (uu___4, (Prims.of_int (2)), Prims.int_zero,
                     (binary_op arg_as_bounded_int
                        (fun r ->
                           fun uu___6 ->
                             fun uu___7 ->
                               match (uu___6, uu___7) with
                               | ((int_to_t, x, m1), (uu___8, y, uu___9)) ->
                                   let uu___10 =
                                     let uu___11 =
                                       let uu___12 =
                                         FStar_BigInt.add_big_int x y in
                                       mod1 uu___12 in
                                     int_as_bounded r int_to_t uu___11 in
                                   with_meta_ds r uu___10 m1)), uu___5) in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       FStar_Parser_Const.p2l ["FStar"; m; "sub_mod"] in
                     let uu___7 =
                       FStar_TypeChecker_NBETerm.binary_op
                         FStar_TypeChecker_NBETerm.arg_as_bounded_int
                         (fun uu___8 ->
                            fun uu___9 ->
                              match (uu___8, uu___9) with
                              | ((int_to_t, x, m1), (uu___10, y, uu___11)) ->
                                  let uu___12 =
                                    let uu___13 =
                                      let uu___14 =
                                        FStar_BigInt.sub_big_int x y in
                                      mod1 uu___14 in
                                    FStar_TypeChecker_NBETerm.int_as_bounded
                                      int_to_t uu___13 in
                                  FStar_TypeChecker_NBETerm.with_meta_ds
                                    uu___12 m1) in
                     (uu___6, (Prims.of_int (2)), Prims.int_zero,
                       (binary_op arg_as_bounded_int
                          (fun r ->
                             fun uu___8 ->
                               fun uu___9 ->
                                 match (uu___8, uu___9) with
                                 | ((int_to_t, x, m1), (uu___10, y, uu___11))
                                     ->
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           FStar_BigInt.sub_big_int x y in
                                         mod1 uu___14 in
                                       int_as_bounded r int_to_t uu___13 in
                                     with_meta_ds r uu___12 m1)), uu___7) in
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         FStar_Parser_Const.p2l ["FStar"; m; "div"] in
                       let uu___9 =
                         FStar_TypeChecker_NBETerm.binary_op
                           FStar_TypeChecker_NBETerm.arg_as_bounded_int
                           (fun uu___10 ->
                              fun uu___11 ->
                                match (uu___10, uu___11) with
                                | ((int_to_t, x, m1), (uu___12, y, uu___13))
                                    ->
                                    let uu___14 =
                                      let uu___15 =
                                        FStar_BigInt.div_big_int x y in
                                      FStar_TypeChecker_NBETerm.int_as_bounded
                                        int_to_t uu___15 in
                                    FStar_TypeChecker_NBETerm.with_meta_ds
                                      uu___14 m1) in
                       (uu___8, (Prims.of_int (2)), Prims.int_zero,
                         (binary_op arg_as_bounded_int
                            (fun r ->
                               fun uu___10 ->
                                 fun uu___11 ->
                                   match (uu___10, uu___11) with
                                   | ((int_to_t, x, m1),
                                      (uu___12, y, uu___13)) ->
                                       let uu___14 =
                                         let uu___15 =
                                           FStar_BigInt.div_big_int x y in
                                         int_as_bounded r int_to_t uu___15 in
                                       with_meta_ds r uu___14 m1)), uu___9) in
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           FStar_Parser_Const.p2l ["FStar"; m; "rem"] in
                         let uu___11 =
                           FStar_TypeChecker_NBETerm.binary_op
                             FStar_TypeChecker_NBETerm.arg_as_bounded_int
                             (fun uu___12 ->
                                fun uu___13 ->
                                  match (uu___12, uu___13) with
                                  | ((int_to_t, x, m1),
                                     (uu___14, y, uu___15)) ->
                                      let uu___16 =
                                        let uu___17 =
                                          FStar_BigInt.mod_big_int x y in
                                        FStar_TypeChecker_NBETerm.int_as_bounded
                                          int_to_t uu___17 in
                                      FStar_TypeChecker_NBETerm.with_meta_ds
                                        uu___16 m1) in
                         (uu___10, (Prims.of_int (2)), Prims.int_zero,
                           (binary_op arg_as_bounded_int
                              (fun r ->
                                 fun uu___12 ->
                                   fun uu___13 ->
                                     match (uu___12, uu___13) with
                                     | ((int_to_t, x, m1),
                                        (uu___14, y, uu___15)) ->
                                         let uu___16 =
                                           let uu___17 =
                                             FStar_BigInt.mod_big_int x y in
                                           int_as_bounded r int_to_t uu___17 in
                                         with_meta_ds r uu___16 m1)),
                           uu___11) in
                       [uu___9] in
                     uu___7 :: uu___8 in
                   uu___5 :: uu___6 in
                 uu___3 :: uu___4 in
               FStar_Compiler_List.op_At uu___1 uu___2)
        bounded_unsigned_int_types in
    let mask m =
      match m with
      | "UInt8" -> FStar_BigInt.of_hex "ff"
      | "UInt16" -> FStar_BigInt.of_hex "ffff"
      | "UInt32" -> FStar_BigInt.of_hex "ffffffff"
      | "UInt64" -> FStar_BigInt.of_hex "ffffffffffffffff"
      | "UInt128" -> FStar_BigInt.of_hex "ffffffffffffffffffffffffffffffff"
      | uu___ ->
          let uu___1 =
            FStar_Compiler_Util.format1
              "Impossible: bad string on mask: %s\n" m in
          FStar_Compiler_Effect.failwith uu___1 in
    let bitwise =
      FStar_Compiler_List.collect
        (fun uu___ ->
           match uu___ with
           | (m, uu___1) ->
               let uu___2 =
                 let uu___3 = FStar_Parser_Const.p2l ["FStar"; m; "logor"] in
                 let uu___4 =
                   FStar_TypeChecker_NBETerm.binary_op
                     FStar_TypeChecker_NBETerm.arg_as_bounded_int
                     (fun uu___5 ->
                        fun uu___6 ->
                          match (uu___5, uu___6) with
                          | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                              let uu___9 =
                                let uu___10 = FStar_BigInt.logor_big_int x y in
                                FStar_TypeChecker_NBETerm.int_as_bounded
                                  int_to_t uu___10 in
                              FStar_TypeChecker_NBETerm.with_meta_ds uu___9
                                m1) in
                 (uu___3, (Prims.of_int (2)), Prims.int_zero,
                   (binary_op arg_as_bounded_int
                      (fun r ->
                         fun uu___5 ->
                           fun uu___6 ->
                             match (uu___5, uu___6) with
                             | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_BigInt.logor_big_int x y in
                                   int_as_bounded r int_to_t uu___10 in
                                 with_meta_ds r uu___9 m1)), uu___4) in
               let uu___3 =
                 let uu___4 =
                   let uu___5 = FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
                   let uu___6 =
                     FStar_TypeChecker_NBETerm.binary_op
                       FStar_TypeChecker_NBETerm.arg_as_bounded_int
                       (fun uu___7 ->
                          fun uu___8 ->
                            match (uu___7, uu___8) with
                            | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                let uu___11 =
                                  let uu___12 =
                                    FStar_BigInt.logand_big_int x y in
                                  FStar_TypeChecker_NBETerm.int_as_bounded
                                    int_to_t uu___12 in
                                FStar_TypeChecker_NBETerm.with_meta_ds
                                  uu___11 m1) in
                   (uu___5, (Prims.of_int (2)), Prims.int_zero,
                     (binary_op arg_as_bounded_int
                        (fun r ->
                           fun uu___7 ->
                             fun uu___8 ->
                               match (uu___7, uu___8) with
                               | ((int_to_t, x, m1), (uu___9, y, uu___10)) ->
                                   let uu___11 =
                                     let uu___12 =
                                       FStar_BigInt.logand_big_int x y in
                                     int_as_bounded r int_to_t uu___12 in
                                   with_meta_ds r uu___11 m1)), uu___6) in
                 let uu___5 =
                   let uu___6 =
                     let uu___7 =
                       FStar_Parser_Const.p2l ["FStar"; m; "logxor"] in
                     let uu___8 =
                       FStar_TypeChecker_NBETerm.binary_op
                         FStar_TypeChecker_NBETerm.arg_as_bounded_int
                         (fun uu___9 ->
                            fun uu___10 ->
                              match (uu___9, uu___10) with
                              | ((int_to_t, x, m1), (uu___11, y, uu___12)) ->
                                  let uu___13 =
                                    let uu___14 =
                                      FStar_BigInt.logxor_big_int x y in
                                    FStar_TypeChecker_NBETerm.int_as_bounded
                                      int_to_t uu___14 in
                                  FStar_TypeChecker_NBETerm.with_meta_ds
                                    uu___13 m1) in
                     (uu___7, (Prims.of_int (2)), Prims.int_zero,
                       (binary_op arg_as_bounded_int
                          (fun r ->
                             fun uu___9 ->
                               fun uu___10 ->
                                 match (uu___9, uu___10) with
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
                                     let uu___13 =
                                       let uu___14 =
                                         FStar_BigInt.logxor_big_int x y in
                                       int_as_bounded r int_to_t uu___14 in
                                     with_meta_ds r uu___13 m1)), uu___8) in
                   let uu___7 =
                     let uu___8 =
                       let uu___9 =
                         FStar_Parser_Const.p2l ["FStar"; m; "lognot"] in
                       let uu___10 =
                         FStar_TypeChecker_NBETerm.unary_op
                           FStar_TypeChecker_NBETerm.arg_as_bounded_int
                           (fun uu___11 ->
                              match uu___11 with
                              | (int_to_t, x, d) ->
                                  let uu___12 =
                                    let uu___13 =
                                      let uu___14 =
                                        FStar_BigInt.lognot_big_int x in
                                      let uu___15 = mask m in
                                      FStar_BigInt.logand_big_int uu___14
                                        uu___15 in
                                    FStar_TypeChecker_NBETerm.int_as_bounded
                                      int_to_t uu___13 in
                                  FStar_TypeChecker_NBETerm.with_meta_ds
                                    uu___12 d) in
                       (uu___9, Prims.int_one, Prims.int_zero,
                         (unary_op arg_as_bounded_int
                            (fun r ->
                               fun uu___11 ->
                                 match uu___11 with
                                 | (int_to_t, x, d) ->
                                     let uu___12 =
                                       let uu___13 =
                                         let uu___14 =
                                           FStar_BigInt.lognot_big_int x in
                                         let uu___15 = mask m in
                                         FStar_BigInt.logand_big_int uu___14
                                           uu___15 in
                                       int_as_bounded r int_to_t uu___13 in
                                     with_meta_ds r uu___12 d)), uu___10) in
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStar_Parser_Const.p2l ["FStar"; m; "shift_left"] in
                         let uu___12 =
                           FStar_TypeChecker_NBETerm.binary_op
                             FStar_TypeChecker_NBETerm.arg_as_bounded_int
                             (fun uu___13 ->
                                fun uu___14 ->
                                  match (uu___13, uu___14) with
                                  | ((int_to_t, x, d), (uu___15, y, uu___16))
                                      ->
                                      let uu___17 =
                                        let uu___18 =
                                          let uu___19 =
                                            FStar_BigInt.shift_left_big_int x
                                              y in
                                          let uu___20 = mask m in
                                          FStar_BigInt.logand_big_int uu___19
                                            uu___20 in
                                        FStar_TypeChecker_NBETerm.int_as_bounded
                                          int_to_t uu___18 in
                                      FStar_TypeChecker_NBETerm.with_meta_ds
                                        uu___17 d) in
                         (uu___11, (Prims.of_int (2)), Prims.int_zero,
                           (binary_op arg_as_bounded_int
                              (fun r ->
                                 fun uu___13 ->
                                   fun uu___14 ->
                                     match (uu___13, uu___14) with
                                     | ((int_to_t, x, d),
                                        (uu___15, y, uu___16)) ->
                                         let uu___17 =
                                           let uu___18 =
                                             let uu___19 =
                                               FStar_BigInt.shift_left_big_int
                                                 x y in
                                             let uu___20 = mask m in
                                             FStar_BigInt.logand_big_int
                                               uu___19 uu___20 in
                                           int_as_bounded r int_to_t uu___18 in
                                         with_meta_ds r uu___17 d)), uu___12) in
                       let uu___11 =
                         let uu___12 =
                           let uu___13 =
                             FStar_Parser_Const.p2l
                               ["FStar"; m; "shift_right"] in
                           let uu___14 =
                             FStar_TypeChecker_NBETerm.binary_op
                               FStar_TypeChecker_NBETerm.arg_as_bounded_int
                               (fun uu___15 ->
                                  fun uu___16 ->
                                    match (uu___15, uu___16) with
                                    | ((int_to_t, x, d),
                                       (uu___17, y, uu___18)) ->
                                        let uu___19 =
                                          let uu___20 =
                                            FStar_BigInt.shift_right_big_int
                                              x y in
                                          FStar_TypeChecker_NBETerm.int_as_bounded
                                            int_to_t uu___20 in
                                        FStar_TypeChecker_NBETerm.with_meta_ds
                                          uu___19 d) in
                           (uu___13, (Prims.of_int (2)), Prims.int_zero,
                             (binary_op arg_as_bounded_int
                                (fun r ->
                                   fun uu___15 ->
                                     fun uu___16 ->
                                       match (uu___15, uu___16) with
                                       | ((int_to_t, x, d),
                                          (uu___17, y, uu___18)) ->
                                           let uu___19 =
                                             let uu___20 =
                                               FStar_BigInt.shift_right_big_int
                                                 x y in
                                             int_as_bounded r int_to_t
                                               uu___20 in
                                           with_meta_ds r uu___19 d)),
                             uu___14) in
                         [uu___12] in
                       uu___10 :: uu___11 in
                     uu___8 :: uu___9 in
                   uu___6 :: uu___7 in
                 uu___4 :: uu___5 in
               uu___2 :: uu___3) bounded_unsigned_int_types in
    FStar_Compiler_List.op_At add_sub_mul_v_comparisons
      (FStar_Compiler_List.op_At unsigned_modulo_add_sub_mul_div_rem bitwise) in
  let reveal_hide =
    (FStar_Parser_Const.reveal, (Prims.of_int (2)), Prims.int_one,
      (mixed_binary_op (fun x -> FStar_Pervasives_Native.Some x)
         (fun uu___ ->
            match uu___ with
            | (x, uu___1) ->
                let uu___2 = FStar_Syntax_Util.head_and_args x in
                (match uu___2 with
                 | (head, args) ->
                     let uu___3 =
                       FStar_Syntax_Util.is_fvar FStar_Parser_Const.hide head in
                     if uu___3
                     then
                       (match args with
                        | _t::(body, uu___4)::[] ->
                            FStar_Pervasives_Native.Some body
                        | uu___4 -> FStar_Pervasives_Native.None)
                     else FStar_Pervasives_Native.None))
         (fun r -> fun body -> body)
         (fun r ->
            fun _us ->
              fun _t -> fun body -> FStar_Pervasives_Native.Some body)),
      (FStar_TypeChecker_NBETerm.mixed_binary_op
         (fun x -> FStar_Pervasives_Native.Some x)
         (fun uu___ ->
            match uu___ with
            | (x, uu___1) ->
                let uu___2 = FStar_TypeChecker_NBETerm.nbe_t_of_t x in
                (match uu___2 with
                 | FStar_TypeChecker_NBETerm.FV
                     (fv, uu___3, (_t, uu___4)::(body, uu___5)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.hide
                     -> FStar_Pervasives_Native.Some body
                 | uu___3 -> FStar_Pervasives_Native.None))
         (fun body -> body)
         (fun _us -> fun _t -> fun body -> FStar_Pervasives_Native.Some body))) in
  let array_ops =
    let of_list_op =
      let emb_typ t =
        let uu___ =
          let uu___1 =
            FStar_Ident.string_of_lid
              FStar_Parser_Const.immutable_array_t_lid in
          (uu___1, [t]) in
        FStar_Syntax_Syntax.ET_app uu___ in
      let un_lazy universes t l r =
        let uu___ =
          let uu___1 =
            FStar_Syntax_Util.fvar_const
              FStar_Parser_Const.immutable_array_of_list_lid in
          FStar_Syntax_Syntax.mk_Tm_uinst uu___1 universes in
        let uu___1 =
          let uu___2 = FStar_Syntax_Syntax.iarg t in
          let uu___3 = let uu___4 = FStar_Syntax_Syntax.as_arg l in [uu___4] in
          uu___2 :: uu___3 in
        FStar_Syntax_Syntax.mk_Tm_app uu___ uu___1 r in
      (FStar_Parser_Const.immutable_array_of_list_lid, (Prims.of_int (2)),
        Prims.int_one,
        (mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           (fun uu___ ->
              match uu___ with
              | (l, q) ->
                  let uu___1 =
                    arg_as_list FStar_Syntax_Embeddings.e_any (l, q) in
                  (match uu___1 with
                   | FStar_Pervasives_Native.Some lst ->
                       FStar_Pervasives_Native.Some (l, lst)
                   | uu___2 -> FStar_Pervasives_Native.None))
           (fun r ->
              fun uu___ ->
                match uu___ with
                | (universes, elt_t, (l, blob)) ->
                    let uu___1 =
                      let uu___2 =
                        let uu___3 =
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                FStar_Syntax_Embeddings_Base.emb_typ_of
                                  FStar_Syntax_Embeddings.e_any () in
                              emb_typ uu___6 in
                            let uu___6 =
                              FStar_Thunk.mk
                                (fun uu___7 -> un_lazy universes elt_t l r) in
                            (uu___5, uu___6) in
                          FStar_Syntax_Syntax.Lazy_embedding uu___4 in
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Syntax_Util.fvar_const
                                FStar_Parser_Const.immutable_array_t_lid in
                            FStar_Syntax_Syntax.mk_Tm_uinst uu___6 universes in
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Syntax.as_arg elt_t in
                            [uu___7] in
                          FStar_Syntax_Syntax.mk_Tm_app uu___5 uu___6 r in
                        {
                          FStar_Syntax_Syntax.blob = blob;
                          FStar_Syntax_Syntax.lkind = uu___3;
                          FStar_Syntax_Syntax.ltyp = uu___4;
                          FStar_Syntax_Syntax.rng = r
                        } in
                      FStar_Syntax_Syntax.Tm_lazy uu___2 in
                    FStar_Syntax_Syntax.mk uu___1 r)
           (fun r ->
              fun universes ->
                fun elt_t ->
                  fun uu___ ->
                    match uu___ with
                    | (l, lst) ->
                        let blob = FStar_ImmutableArray_Base.of_list lst in
                        let uu___1 =
                          let uu___2 =
                            let uu___3 = FStar_Compiler_Dyn.mkdyn blob in
                            (l, uu___3) in
                          (universes, elt_t, uu___2) in
                        FStar_Pervasives_Native.Some uu___1)),
        (FStar_TypeChecker_NBETerm.mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           (fun uu___ ->
              match uu___ with
              | (l, q) ->
                  let uu___1 =
                    FStar_TypeChecker_NBETerm.arg_as_list
                      FStar_TypeChecker_NBETerm.e_any (l, q) in
                  (match uu___1 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some lst ->
                       FStar_Pervasives_Native.Some (l, lst)))
           (fun uu___ ->
              match uu___ with
              | (universes, elt_t, (l, blob)) ->
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Syntax_Embeddings_Base.emb_typ_of
                                FStar_Syntax_Embeddings.e_any () in
                            emb_typ uu___6 in
                          (blob, uu___5) in
                        FStar_Pervasives.Inr uu___4 in
                      let uu___4 =
                        FStar_Thunk.mk
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 =
                                   FStar_Syntax_Syntax.lid_as_fv
                                     FStar_Parser_Const.immutable_array_of_list_lid
                                     FStar_Pervasives_Native.None in
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_TypeChecker_NBETerm.as_arg l in
                                   [uu___10] in
                                 (uu___8, universes, uu___9) in
                               FStar_TypeChecker_NBETerm.FV uu___7 in
                             FStar_TypeChecker_NBETerm.mk_t uu___6) in
                      (uu___3, uu___4) in
                    FStar_TypeChecker_NBETerm.Lazy uu___2 in
                  FStar_TypeChecker_NBETerm.mk_t uu___1)
           (fun universes ->
              fun elt_t ->
                fun uu___ ->
                  match uu___ with
                  | (l, lst) ->
                      let blob = FStar_ImmutableArray_Base.of_list lst in
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStar_Compiler_Dyn.mkdyn blob in
                          (l, uu___3) in
                        (universes, elt_t, uu___2) in
                      FStar_Pervasives_Native.Some uu___1))) in
    let arg1_as_elt_t x =
      FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst x) in
    let arg2_as_blob x =
      let uu___ =
        let uu___1 =
          FStar_Syntax_Subst.compress (FStar_Pervasives_Native.fst x) in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = blob;
            FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
              (FStar_Syntax_Syntax.ET_app (head, uu___1), uu___2);
            FStar_Syntax_Syntax.ltyp = uu___3;
            FStar_Syntax_Syntax.rng = uu___4;_}
          when
          let uu___5 =
            FStar_Ident.string_of_lid
              FStar_Parser_Const.immutable_array_t_lid in
          head = uu___5 -> FStar_Pervasives_Native.Some blob
      | uu___1 -> FStar_Pervasives_Native.None in
    let arg2_as_blob_nbe x =
      match (FStar_Pervasives_Native.fst x).FStar_TypeChecker_NBETerm.nbe_t
      with
      | FStar_TypeChecker_NBETerm.Lazy
          (FStar_Pervasives.Inr
           (blob, FStar_Syntax_Syntax.ET_app (head, uu___)), uu___1)
          when
          let uu___2 =
            FStar_Ident.string_of_lid
              FStar_Parser_Const.immutable_array_t_lid in
          head = uu___2 -> FStar_Pervasives_Native.Some blob
      | uu___ -> FStar_Pervasives_Native.None in
    let length_op =
      let embed_int r i = embed_simple FStar_Syntax_Embeddings.e_int r i in
      let run_op blob =
        let uu___ =
          let uu___1 = FStar_Compiler_Dyn.undyn blob in
          FStar_Compiler_Util.array_length uu___1 in
        FStar_Pervasives_Native.Some uu___ in
      (FStar_Parser_Const.immutable_array_length_lid, (Prims.of_int (2)),
        Prims.int_one,
        (mixed_binary_op arg1_as_elt_t arg2_as_blob embed_int
           (fun _r -> fun _universes -> fun uu___ -> fun blob -> run_op blob)),
        (FStar_TypeChecker_NBETerm.mixed_binary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           arg2_as_blob_nbe
           (fun i ->
              FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
                bogus_cbs i)
           (fun _universes -> fun uu___ -> fun blob -> run_op blob))) in
    let index_op =
      (FStar_Parser_Const.immutable_array_index_lid, (Prims.of_int (3)),
        Prims.int_one,
        (mixed_ternary_op arg1_as_elt_t arg2_as_blob arg_as_int
           (fun r -> fun tm -> tm)
           (fun r ->
              fun _universes ->
                fun _t ->
                  fun blob ->
                    fun i ->
                      let uu___ =
                        let uu___1 = FStar_Compiler_Dyn.undyn blob in
                        FStar_Compiler_Util.array_index uu___1 i in
                      FStar_Pervasives_Native.Some uu___)),
        (FStar_TypeChecker_NBETerm.mixed_ternary_op
           (fun uu___ ->
              match uu___ with
              | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
           arg2_as_blob_nbe FStar_TypeChecker_NBETerm.arg_as_int
           (fun tm -> tm)
           (fun _universes ->
              fun _t ->
                fun blob ->
                  fun i ->
                    let uu___ =
                      let uu___1 = FStar_Compiler_Dyn.undyn blob in
                      FStar_Compiler_Util.array_index uu___1 i in
                    FStar_Pervasives_Native.Some uu___))) in
    [of_list_op; length_op; index_op] in
  let strong_steps =
    FStar_Compiler_List.map (as_primitive_step true)
      (FStar_Compiler_List.op_At basic_ops
         (FStar_Compiler_List.op_At bounded_arith_ops
            (FStar_Compiler_List.op_At [reveal_hide] array_ops))) in
  FStar_Compiler_List.op_At simple_ops
    (FStar_Compiler_List.op_At issue_ops
       (FStar_Compiler_List.op_At doc_ops
          (FStar_Compiler_List.op_At strong_steps seal_steps)))
let (equality_ops_list : primitive_step Prims.list) =
  let interp_prop_eq2 psc1 _norm_cb _univs args =
    let r = psc1.psc_range in
    match args with
    | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
        let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu___3 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = r;
                 FStar_Syntax_Syntax.vars =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.vars);
                 FStar_Syntax_Syntax.hash_code =
                   (FStar_Syntax_Util.t_true.FStar_Syntax_Syntax.hash_code)
               }
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some
               {
                 FStar_Syntax_Syntax.n =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = r;
                 FStar_Syntax_Syntax.vars =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.vars);
                 FStar_Syntax_Syntax.hash_code =
                   (FStar_Syntax_Util.t_false.FStar_Syntax_Syntax.hash_code)
               }
         | uu___4 -> FStar_Pervasives_Native.None)
    | uu___ ->
        FStar_Compiler_Effect.failwith "Unexpected number of arguments" in
  let propositional_equality =
    {
      name = FStar_Parser_Const.eq2_lid;
      arity = (Prims.of_int (3));
      univ_arity = Prims.int_one;
      auto_reflect = FStar_Pervasives_Native.None;
      strong_reduction_ok = true;
      requires_binder_substitution = false;
      renorm_after = false;
      interpretation = interp_prop_eq2;
      interpretation_nbe =
        (fun _cb -> fun _univs -> FStar_TypeChecker_NBETerm.interp_prop_eq2)
    } in
  [propositional_equality]
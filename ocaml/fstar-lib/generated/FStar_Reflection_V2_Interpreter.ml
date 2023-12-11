open Prims
let unembed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings_Base.norm_cb ->
          'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      fun norm_cb -> FStar_Syntax_Embeddings_Base.unembed uu___ x norm_cb
let try_unembed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Embeddings_Base.norm_cb ->
          'a FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun x ->
      fun norm_cb -> FStar_Syntax_Embeddings_Base.try_unembed uu___ x norm_cb
let embed :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Compiler_Range_Type.range ->
        'a ->
          FStar_Syntax_Embeddings_Base.norm_cb -> FStar_Syntax_Syntax.term
  =
  fun uu___ ->
    fun r ->
      fun x ->
        fun norm_cb ->
          let uu___1 = FStar_Syntax_Embeddings_Base.embed uu___ x in
          uu___1 r FStar_Pervasives_Native.None norm_cb
let int1 :
  'a 'r .
    FStar_Ident.lid ->
      'a FStar_Syntax_Embeddings_Base.embedding ->
        'r FStar_Syntax_Embeddings_Base.embedding ->
          ('a -> 'r) ->
            FStar_TypeChecker_Primops.psc ->
              FStar_Syntax_Embeddings_Base.norm_cb ->
                FStar_Syntax_Syntax.args ->
                  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uu___6 ->
    fun uu___5 ->
      fun uu___4 ->
        fun uu___3 ->
          fun uu___2 ->
            fun uu___1 ->
              fun uu___ ->
                (fun m ->
                   fun uu___ ->
                     fun uu___1 ->
                       fun f ->
                         fun psc ->
                           fun n ->
                             fun args ->
                               match args with
                               | (a1, uu___2)::[] ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___3 =
                                           let uu___4 =
                                             try_unembed uu___ a1 n in
                                           Obj.magic
                                             (FStar_Class_Monad.op_Less_Dollar_Greater
                                                FStar_Class_Monad.monad_option
                                                () ()
                                                (fun uu___5 ->
                                                   (Obj.magic f) uu___5)
                                                (Obj.magic uu___4)) in
                                         FStar_Class_Monad.op_let_Bang
                                           FStar_Class_Monad.monad_option ()
                                           () (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun v ->
                                                 let v = Obj.magic v in
                                                 let uu___4 =
                                                   let uu___5 =
                                                     FStar_TypeChecker_Primops.psc_range
                                                       psc in
                                                   embed uu___1 uu___5 v n in
                                                 Obj.magic
                                                   (FStar_Class_Monad.return
                                                      FStar_Class_Monad.monad_option
                                                      () (Obj.magic uu___4)))
                                                uu___4)))
                               | uu___2 ->
                                   Obj.magic
                                     (Obj.repr FStar_Pervasives_Native.None))
                  uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      'a FStar_Syntax_Embeddings_Base.embedding ->
        'b FStar_Syntax_Embeddings_Base.embedding ->
          'r FStar_Syntax_Embeddings_Base.embedding ->
            ('a -> 'b -> 'r) ->
              FStar_TypeChecker_Primops.psc ->
                FStar_Syntax_Embeddings_Base.norm_cb ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uu___7 ->
    fun uu___6 ->
      fun uu___5 ->
        fun uu___4 ->
          fun uu___3 ->
            fun uu___2 ->
              fun uu___1 ->
                fun uu___ ->
                  (fun m ->
                     fun uu___ ->
                       fun uu___1 ->
                         fun uu___2 ->
                           fun f ->
                             fun psc ->
                               fun n ->
                                 fun args ->
                                   match args with
                                   | (a1, uu___3)::(b1, uu___4)::[] ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   try_unembed uu___ a1 n in
                                                 Obj.magic
                                                   (FStar_Class_Monad.op_Less_Dollar_Greater
                                                      FStar_Class_Monad.monad_option
                                                      () ()
                                                      (fun uu___8 ->
                                                         (Obj.magic f) uu___8)
                                                      (Obj.magic uu___7)) in
                                               let uu___7 =
                                                 try_unembed uu___1 b1 n in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_Less_Star_Greater
                                                    FStar_Class_Monad.monad_option
                                                    () () (Obj.magic uu___6)
                                                    (Obj.magic uu___7)) in
                                             FStar_Class_Monad.op_let_Bang
                                               FStar_Class_Monad.monad_option
                                               () () (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun v ->
                                                     let v = Obj.magic v in
                                                     let uu___6 =
                                                       let uu___7 =
                                                         FStar_TypeChecker_Primops.psc_range
                                                           psc in
                                                       embed uu___2 uu___7 v
                                                         n in
                                                     Obj.magic
                                                       (FStar_Class_Monad.return
                                                          FStar_Class_Monad.monad_option
                                                          ()
                                                          (Obj.magic uu___6)))
                                                    uu___6)))
                                   | uu___3 ->
                                       Obj.magic
                                         (Obj.repr
                                            FStar_Pervasives_Native.None))
                    uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let int3 :
  'a 'b 'c 'r .
    FStar_Ident.lid ->
      'a FStar_Syntax_Embeddings_Base.embedding ->
        'b FStar_Syntax_Embeddings_Base.embedding ->
          'c FStar_Syntax_Embeddings_Base.embedding ->
            'r FStar_Syntax_Embeddings_Base.embedding ->
              ('a -> 'b -> 'c -> 'r) ->
                FStar_TypeChecker_Primops.psc ->
                  FStar_Syntax_Embeddings_Base.norm_cb ->
                    FStar_Syntax_Syntax.args ->
                      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun uu___8 ->
    fun uu___7 ->
      fun uu___6 ->
        fun uu___5 ->
          fun uu___4 ->
            fun uu___3 ->
              fun uu___2 ->
                fun uu___1 ->
                  fun uu___ ->
                    (fun m ->
                       fun uu___ ->
                         fun uu___1 ->
                           fun uu___2 ->
                             fun uu___3 ->
                               fun f ->
                                 fun psc ->
                                   fun n ->
                                     fun args ->
                                       match args with
                                       | (a1, uu___4)::(b1, uu___5)::
                                           (c1, uu___6)::[] ->
                                           Obj.magic
                                             (Obj.repr
                                                (let uu___7 =
                                                   let uu___8 =
                                                     let uu___9 =
                                                       let uu___10 =
                                                         try_unembed uu___ a1
                                                           n in
                                                       Obj.magic
                                                         (FStar_Class_Monad.op_Less_Dollar_Greater
                                                            FStar_Class_Monad.monad_option
                                                            () ()
                                                            (fun uu___11 ->
                                                               (Obj.magic f)
                                                                 uu___11)
                                                            (Obj.magic
                                                               uu___10)) in
                                                     let uu___10 =
                                                       try_unembed uu___1 b1
                                                         n in
                                                     Obj.magic
                                                       (FStar_Class_Monad.op_Less_Star_Greater
                                                          FStar_Class_Monad.monad_option
                                                          () ()
                                                          (Obj.magic uu___9)
                                                          (Obj.magic uu___10)) in
                                                   let uu___9 =
                                                     try_unembed uu___2 c1 n in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_Less_Star_Greater
                                                        FStar_Class_Monad.monad_option
                                                        () ()
                                                        (Obj.magic uu___8)
                                                        (Obj.magic uu___9)) in
                                                 FStar_Class_Monad.op_let_Bang
                                                   FStar_Class_Monad.monad_option
                                                   () () (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      (fun v ->
                                                         let v = Obj.magic v in
                                                         let uu___8 =
                                                           let uu___9 =
                                                             FStar_TypeChecker_Primops.psc_range
                                                               psc in
                                                           embed uu___3
                                                             uu___9 v n in
                                                         Obj.magic
                                                           (FStar_Class_Monad.return
                                                              FStar_Class_Monad.monad_option
                                                              ()
                                                              (Obj.magic
                                                                 uu___8)))
                                                        uu___8)))
                                       | uu___4 ->
                                           Obj.magic
                                             (Obj.repr
                                                FStar_Pervasives_Native.None))
                      uu___8 uu___7 uu___6 uu___5 uu___4 uu___3 uu___2 uu___1
                      uu___
let nbe_int1 :
  'a 'r .
    FStar_Ident.lid ->
      ('a -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'r FStar_TypeChecker_NBETerm.embedding ->
            FStar_TypeChecker_NBETerm.nbe_cbs ->
              FStar_TypeChecker_NBETerm.args ->
                FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m ->
    fun f ->
      fun ea ->
        fun er ->
          fun cb ->
            fun args ->
              match args with
              | (a1, uu___)::[] ->
                  let uu___1 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                  FStar_Compiler_Util.bind_opt uu___1
                    (fun a2 ->
                       let uu___2 =
                         let uu___3 = f a2 in
                         FStar_TypeChecker_NBETerm.embed er cb uu___3 in
                       FStar_Pervasives_Native.Some uu___2)
              | uu___ -> FStar_Pervasives_Native.None
let nbe_int2 :
  'a 'b 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'r FStar_TypeChecker_NBETerm.embedding ->
              FStar_TypeChecker_NBETerm.nbe_cbs ->
                FStar_TypeChecker_NBETerm.args ->
                  FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
  =
  fun m ->
    fun f ->
      fun ea ->
        fun eb ->
          fun er ->
            fun cb ->
              fun args ->
                match args with
                | (a1, uu___)::(b1, uu___1)::[] ->
                    let uu___2 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                    FStar_Compiler_Util.bind_opt uu___2
                      (fun a2 ->
                         let uu___3 =
                           FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                         FStar_Compiler_Util.bind_opt uu___3
                           (fun b2 ->
                              let uu___4 =
                                let uu___5 = f a2 b2 in
                                FStar_TypeChecker_NBETerm.embed er cb uu___5 in
                              FStar_Pervasives_Native.Some uu___4))
                | uu___ -> FStar_Pervasives_Native.None
let nbe_int3 :
  'a 'b 'c 'r .
    FStar_Ident.lid ->
      ('a -> 'b -> 'c -> 'r) ->
        'a FStar_TypeChecker_NBETerm.embedding ->
          'b FStar_TypeChecker_NBETerm.embedding ->
            'c FStar_TypeChecker_NBETerm.embedding ->
              'r FStar_TypeChecker_NBETerm.embedding ->
                FStar_TypeChecker_NBETerm.nbe_cbs ->
                  FStar_TypeChecker_NBETerm.args ->
                    FStar_TypeChecker_NBETerm.t
                      FStar_Pervasives_Native.option
  =
  fun m ->
    fun f ->
      fun ea ->
        fun eb ->
          fun ec ->
            fun er ->
              fun cb ->
                fun args ->
                  match args with
                  | (a1, uu___)::(b1, uu___1)::(c1, uu___2)::[] ->
                      let uu___3 = FStar_TypeChecker_NBETerm.unembed ea cb a1 in
                      FStar_Compiler_Util.bind_opt uu___3
                        (fun a2 ->
                           let uu___4 =
                             FStar_TypeChecker_NBETerm.unembed eb cb b1 in
                           FStar_Compiler_Util.bind_opt uu___4
                             (fun b2 ->
                                let uu___5 =
                                  FStar_TypeChecker_NBETerm.unembed ec cb c1 in
                                FStar_Compiler_Util.bind_opt uu___5
                                  (fun c2 ->
                                     let uu___6 =
                                       let uu___7 = f a2 b2 c2 in
                                       FStar_TypeChecker_NBETerm.embed er cb
                                         uu___7 in
                                     FStar_Pervasives_Native.Some uu___6)))
                  | uu___ -> FStar_Pervasives_Native.None
let (mklid : Prims.string -> FStar_Ident.lid) =
  fun nm -> FStar_Reflection_V2_Constants.fstar_refl_builtins_lid nm
let (mk_us :
  FStar_Ident.lid ->
    Prims.int ->
      Prims.int ->
        (FStar_TypeChecker_Primops.psc ->
           FStar_Syntax_Embeddings_Base.norm_cb ->
             FStar_Syntax_Syntax.args ->
               FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
          ->
          (FStar_TypeChecker_NBETerm.nbe_cbs ->
             FStar_TypeChecker_NBETerm.args ->
               FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
            -> FStar_TypeChecker_Primops.primitive_step)
  =
  fun l ->
    fun u_arity ->
      fun arity ->
        fun fn ->
          fun nbe_fn ->
            {
              FStar_TypeChecker_Primops.name = l;
              FStar_TypeChecker_Primops.arity = arity;
              FStar_TypeChecker_Primops.univ_arity = u_arity;
              FStar_TypeChecker_Primops.auto_reflect =
                FStar_Pervasives_Native.None;
              FStar_TypeChecker_Primops.strong_reduction_ok = true;
              FStar_TypeChecker_Primops.requires_binder_substitution = false;
              FStar_TypeChecker_Primops.renorm_after = false;
              FStar_TypeChecker_Primops.interpretation =
                (fun psc -> fun cbs -> fun _us -> fun args -> fn psc cbs args);
              FStar_TypeChecker_Primops.interpretation_nbe =
                (fun cbs -> fun _us -> fun args -> nbe_fn cbs args)
            }
let (mk :
  FStar_Ident.lid ->
    Prims.int ->
      (FStar_TypeChecker_Primops.psc ->
         FStar_Syntax_Embeddings_Base.norm_cb ->
           FStar_Syntax_Syntax.args ->
             FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
        ->
        (FStar_TypeChecker_NBETerm.nbe_cbs ->
           FStar_TypeChecker_NBETerm.args ->
             FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
          -> FStar_TypeChecker_Primops.primitive_step)
  =
  fun l ->
    fun arity ->
      fun fn -> fun nbe_fn -> mk_us l Prims.int_zero arity fn nbe_fn
type 'a dualemb =
  {
  s_emb: 'a FStar_Syntax_Embeddings_Base.embedding ;
  nbe_emb: 'a FStar_TypeChecker_NBETerm.embedding }
let __proj__Mkdualemb__item__s_emb :
  'a . 'a dualemb -> 'a FStar_Syntax_Embeddings_Base.embedding =
  fun projectee -> match projectee with | { s_emb; nbe_emb;_} -> s_emb
let __proj__Mkdualemb__item__nbe_emb :
  'a . 'a dualemb -> 'a FStar_TypeChecker_NBETerm.embedding =
  fun projectee -> match projectee with | { s_emb; nbe_emb;_} -> nbe_emb
let s_emb : 'a . 'a dualemb -> 'a FStar_Syntax_Embeddings_Base.embedding =
  fun projectee ->
    match projectee with | { s_emb = s_emb1; nbe_emb;_} -> s_emb1
let nbe_emb : 'a . 'a dualemb -> 'a FStar_TypeChecker_NBETerm.embedding =
  fun projectee ->
    match projectee with
    | { s_emb = s_emb1; nbe_emb = nbe_emb1;_} -> nbe_emb1
let emb_from_dual :
  'a . 'a dualemb -> 'a FStar_Syntax_Embeddings_Base.embedding =
  fun d -> d.s_emb
let (e_int : FStar_BigInt.t dualemb) =
  {
    s_emb = FStar_Syntax_Embeddings.e_int;
    nbe_emb = FStar_TypeChecker_NBETerm.e_int
  }
let (e_bool : Prims.bool dualemb) =
  {
    s_emb = FStar_Syntax_Embeddings.e_bool;
    nbe_emb = FStar_TypeChecker_NBETerm.e_bool
  }
let (e_string : Prims.string dualemb) =
  {
    s_emb = FStar_Syntax_Embeddings.e_string;
    nbe_emb = FStar_TypeChecker_NBETerm.e_string
  }
let (e_order : FStar_Order.order dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_order;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_order
  }
let (e_term : FStar_Syntax_Syntax.term dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_term;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_term
  }
let (e_term_view : FStar_Reflection_V2_Data.term_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_term_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_term_view
  }
let (e_fv : FStar_Syntax_Syntax.fv dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_fv;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_fv
  }
let (e_bv : FStar_Syntax_Syntax.bv dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_bv;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_bv
  }
let (e_namedv : FStar_Reflection_V2_Embeddings.namedv dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_namedv;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_namedv
  }
let (e_bv_view : FStar_Reflection_V2_Data.bv_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_bv_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_bv_view
  }
let (e_namedv_view : FStar_Reflection_V2_Data.namedv_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_namedv_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_namedv_view
  }
let (e_binding : FStar_Reflection_V2_Data.binding dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_binding;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_binding
  }
let (e_comp : FStar_Syntax_Syntax.comp dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_comp;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_comp
  }
let (e_comp_view : FStar_Reflection_V2_Data.comp_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_comp_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_comp_view
  }
let (e_universe : FStar_Syntax_Syntax.universe dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_universe;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_universe
  }
let (e_universe_view : FStar_Reflection_V2_Data.universe_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_universe_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_universe_view
  }
let (e_sigelt : FStar_Syntax_Syntax.sigelt dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_sigelt;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_sigelt
  }
let (e_sigelt_view : FStar_Reflection_V2_Data.sigelt_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_sigelt_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_sigelt_view
  }
let (e_binder : FStar_Syntax_Syntax.binder dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_binder;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_binder
  }
let (e_binder_view : FStar_Reflection_V2_Data.binder_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_binder_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_binder_view
  }
let (e_binders : FStar_Syntax_Syntax.binders dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_binders;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_binders
  }
let (e_letbinding : FStar_Syntax_Syntax.letbinding dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_letbinding;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_letbinding
  }
let (e_lb_view : FStar_Reflection_V2_Data.lb_view dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_lb_view;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_lb_view
  }
let (e_env : FStar_TypeChecker_Env.env dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_env;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_env
  }
let (e_aqualv : FStar_Reflection_V2_Data.aqualv dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_aqualv;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_aqualv
  }
let (e_vconfig : FStar_VConfig.vconfig dualemb) =
  {
    s_emb = FStar_Syntax_Embeddings.e_vconfig;
    nbe_emb = FStar_TypeChecker_NBETerm.e_vconfig
  }
let (e_qualifier : FStar_Reflection_V2_Data.qualifier dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_qualifier;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_qualifier
  }
let (e_range : FStar_Compiler_Range_Type.range dualemb) =
  {
    s_emb = FStar_Syntax_Embeddings.e_range;
    nbe_emb = FStar_TypeChecker_NBETerm.e_range
  }
let e_list : 'a . 'a dualemb -> 'a Prims.list dualemb =
  fun e ->
    {
      s_emb = (FStar_Syntax_Embeddings.e_list e.s_emb);
      nbe_emb = (FStar_TypeChecker_NBETerm.e_list e.nbe_emb)
    }
let e_option : 'a . 'a dualemb -> 'a FStar_Pervasives_Native.option dualemb =
  fun e ->
    {
      s_emb = (FStar_Syntax_Embeddings.e_option e.s_emb);
      nbe_emb = (FStar_TypeChecker_NBETerm.e_option e.nbe_emb)
    }
let e_tuple2 : 'a 'b . 'a dualemb -> 'b dualemb -> ('a * 'b) dualemb =
  fun ea ->
    fun eb ->
      {
        s_emb = (FStar_Syntax_Embeddings.e_tuple2 ea.s_emb eb.s_emb);
        nbe_emb = (FStar_TypeChecker_NBETerm.e_tuple2 ea.nbe_emb eb.nbe_emb)
      }
let nbe_dummy : 'a . unit -> 'a FStar_TypeChecker_NBETerm.embedding =
  fun uu___ ->
    FStar_TypeChecker_NBETerm.mk_emb
      (fun uu___1 ->
         fun uu___2 -> FStar_Compiler_Effect.failwith "nbe_dummy embed")
      (fun uu___1 ->
         fun uu___2 -> FStar_Compiler_Effect.failwith "nbe_dummy unembed")
      (fun uu___1 ->
         FStar_TypeChecker_NBETerm.mk_t FStar_TypeChecker_NBETerm.Unknown)
      (fun uu___1 -> FStar_Syntax_Syntax.ET_abstract)
let (e_ident : FStar_Ident.ident dualemb) =
  let uu___ = nbe_dummy () in
  { s_emb = FStar_Reflection_V2_Embeddings.e_ident; nbe_emb = uu___ }
let (e_subst_elt : FStar_Syntax_Syntax.subst_elt dualemb) =
  {
    s_emb = FStar_Reflection_V2_Embeddings.e_subst_elt;
    nbe_emb = FStar_Reflection_V2_NBEEmbeddings.e_subst_elt
  }
let mk1 :
  'a 'r .
    Prims.string ->
      'a dualemb ->
        'r dualemb -> ('a -> 'r) -> FStar_TypeChecker_Primops.primitive_step
  =
  fun nm ->
    fun ea ->
      fun er ->
        fun f ->
          let l = mklid nm in
          mk l Prims.int_one (int1 l (emb_from_dual ea) (emb_from_dual er) f)
            (nbe_int1 l f ea.nbe_emb er.nbe_emb)
let mk2 :
  'a 'b 'r .
    Prims.string ->
      'a dualemb ->
        'b dualemb ->
          'r dualemb ->
            ('a -> 'b -> 'r) -> FStar_TypeChecker_Primops.primitive_step
  =
  fun nm ->
    fun ea ->
      fun eb ->
        fun er ->
          fun f ->
            let l = mklid nm in
            mk l (Prims.of_int (2))
              (int2 l (emb_from_dual ea) (emb_from_dual eb)
                 (emb_from_dual er) f)
              (nbe_int2 l f ea.nbe_emb eb.nbe_emb er.nbe_emb)
let mk3 :
  'a 'b 'c 'r .
    Prims.string ->
      'a dualemb ->
        'b dualemb ->
          'c dualemb ->
            'r dualemb ->
              ('a -> 'b -> 'c -> 'r) ->
                FStar_TypeChecker_Primops.primitive_step
  =
  fun nm ->
    fun ea ->
      fun eb ->
        fun ec ->
          fun er ->
            fun f ->
              let l = mklid nm in
              mk l (Prims.of_int (3))
                (int3 l (emb_from_dual ea) (emb_from_dual eb)
                   (emb_from_dual ec) (emb_from_dual er) f)
                (nbe_int3 l f ea.nbe_emb eb.nbe_emb ec.nbe_emb er.nbe_emb)
let (reflection_primops :
  FStar_TypeChecker_Primops.primitive_step Prims.list) =
  let uu___ =
    mk1 "inspect_ln" e_term e_term_view
      FStar_Reflection_V2_Builtins.inspect_ln in
  let uu___1 =
    let uu___2 =
      mk1 "pack_ln" e_term_view e_term FStar_Reflection_V2_Builtins.pack_ln in
    let uu___3 =
      let uu___4 =
        mk1 "inspect_fv" e_fv (e_list e_string)
          FStar_Reflection_V2_Builtins.inspect_fv in
      let uu___5 =
        let uu___6 =
          mk1 "pack_fv" (e_list e_string) e_fv
            FStar_Reflection_V2_Builtins.pack_fv in
        let uu___7 =
          let uu___8 =
            mk1 "inspect_comp" e_comp e_comp_view
              FStar_Reflection_V2_Builtins.inspect_comp in
          let uu___9 =
            let uu___10 =
              mk1 "pack_comp" e_comp_view e_comp
                FStar_Reflection_V2_Builtins.pack_comp in
            let uu___11 =
              let uu___12 =
                mk1 "inspect_universe" e_universe e_universe_view
                  FStar_Reflection_V2_Builtins.inspect_universe in
              let uu___13 =
                let uu___14 =
                  mk1 "pack_universe" e_universe_view e_universe
                    FStar_Reflection_V2_Builtins.pack_universe in
                let uu___15 =
                  let uu___16 =
                    mk1 "inspect_sigelt" e_sigelt e_sigelt_view
                      FStar_Reflection_V2_Builtins.inspect_sigelt in
                  let uu___17 =
                    let uu___18 =
                      mk1 "pack_sigelt" e_sigelt_view e_sigelt
                        FStar_Reflection_V2_Builtins.pack_sigelt in
                    let uu___19 =
                      let uu___20 =
                        mk1 "inspect_lb" e_letbinding e_lb_view
                          FStar_Reflection_V2_Builtins.inspect_lb in
                      let uu___21 =
                        let uu___22 =
                          mk1 "pack_lb" e_lb_view e_letbinding
                            FStar_Reflection_V2_Builtins.pack_lb in
                        let uu___23 =
                          let uu___24 =
                            mk1 "inspect_namedv" e_namedv e_namedv_view
                              FStar_Reflection_V2_Builtins.inspect_namedv in
                          let uu___25 =
                            let uu___26 =
                              mk1 "pack_namedv" e_namedv_view e_namedv
                                FStar_Reflection_V2_Builtins.pack_namedv in
                            let uu___27 =
                              let uu___28 =
                                mk1 "inspect_bv" e_bv e_bv_view
                                  FStar_Reflection_V2_Builtins.inspect_bv in
                              let uu___29 =
                                let uu___30 =
                                  mk1 "pack_bv" e_bv_view e_bv
                                    FStar_Reflection_V2_Builtins.pack_bv in
                                let uu___31 =
                                  let uu___32 =
                                    mk1 "inspect_binder" e_binder
                                      e_binder_view
                                      FStar_Reflection_V2_Builtins.inspect_binder in
                                  let uu___33 =
                                    let uu___34 =
                                      mk1 "pack_binder" e_binder_view
                                        e_binder
                                        FStar_Reflection_V2_Builtins.pack_binder in
                                    let uu___35 =
                                      let uu___36 =
                                        mk1 "sigelt_opts" e_sigelt
                                          (e_option e_vconfig)
                                          FStar_Reflection_V2_Builtins.sigelt_opts in
                                      let uu___37 =
                                        let uu___38 =
                                          mk1 "embed_vconfig" e_vconfig
                                            e_term
                                            FStar_Reflection_V2_Builtins.embed_vconfig in
                                        let uu___39 =
                                          let uu___40 =
                                            mk1 "sigelt_attrs" e_sigelt
                                              (e_list e_term)
                                              FStar_Reflection_V2_Builtins.sigelt_attrs in
                                          let uu___41 =
                                            let uu___42 =
                                              mk2 "set_sigelt_attrs"
                                                (e_list e_term) e_sigelt
                                                e_sigelt
                                                FStar_Reflection_V2_Builtins.set_sigelt_attrs in
                                            let uu___43 =
                                              let uu___44 =
                                                mk1 "sigelt_quals" e_sigelt
                                                  (e_list e_qualifier)
                                                  FStar_Reflection_V2_Builtins.sigelt_quals in
                                              let uu___45 =
                                                let uu___46 =
                                                  mk2 "set_sigelt_quals"
                                                    (e_list e_qualifier)
                                                    e_sigelt e_sigelt
                                                    FStar_Reflection_V2_Builtins.set_sigelt_quals in
                                                let uu___47 =
                                                  let uu___48 =
                                                    mk2 "subst_term"
                                                      (e_list e_subst_elt)
                                                      e_term e_term
                                                      FStar_Reflection_V2_Builtins.subst_term in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      mk2 "subst_comp"
                                                        (e_list e_subst_elt)
                                                        e_comp e_comp
                                                        FStar_Reflection_V2_Builtins.subst_comp in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        mk2 "compare_bv" e_bv
                                                          e_bv e_order
                                                          FStar_Reflection_V2_Builtins.compare_bv in
                                                      let uu___53 =
                                                        let uu___54 =
                                                          mk2
                                                            "compare_namedv"
                                                            e_namedv e_namedv
                                                            e_order
                                                            FStar_Reflection_V2_Builtins.compare_namedv in
                                                        let uu___55 =
                                                          let uu___56 =
                                                            mk2 "lookup_attr"
                                                              e_term e_env
                                                              (e_list e_fv)
                                                              FStar_Reflection_V2_Builtins.lookup_attr in
                                                          let uu___57 =
                                                            let uu___58 =
                                                              mk1
                                                                "all_defs_in_env"
                                                                e_env
                                                                (e_list e_fv)
                                                                FStar_Reflection_V2_Builtins.all_defs_in_env in
                                                            let uu___59 =
                                                              let uu___60 =
                                                                mk2
                                                                  "defs_in_module"
                                                                  e_env
                                                                  (e_list
                                                                    e_string)
                                                                  (e_list
                                                                    e_fv)
                                                                  FStar_Reflection_V2_Builtins.defs_in_module in
                                                              let uu___61 =
                                                                let uu___62 =
                                                                  mk2
                                                                    "term_eq"
                                                                    e_term
                                                                    e_term
                                                                    e_bool
                                                                    FStar_Reflection_V2_Builtins.term_eq in
                                                                let uu___63 =
                                                                  let uu___64
                                                                    =
                                                                    mk1
                                                                    "moduleof"
                                                                    e_env
                                                                    (e_list
                                                                    e_string)
                                                                    FStar_Reflection_V2_Builtins.moduleof in
                                                                  let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    mk1
                                                                    "vars_of_env"
                                                                    e_env
                                                                    (e_list
                                                                    e_binding)
                                                                    FStar_Reflection_V2_Builtins.vars_of_env in
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    mk2
                                                                    "lookup_typ"
                                                                    e_env
                                                                    (e_list
                                                                    e_string)
                                                                    (e_option
                                                                    e_sigelt)
                                                                    FStar_Reflection_V2_Builtins.lookup_typ in
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    mk1
                                                                    "env_open_modules"
                                                                    e_env
                                                                    (e_list
                                                                    (e_list
                                                                    e_string))
                                                                    FStar_Reflection_V2_Builtins.env_open_modules in
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    mk1
                                                                    "implode_qn"
                                                                    (e_list
                                                                    e_string)
                                                                    e_string
                                                                    FStar_Reflection_V2_Builtins.implode_qn in
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    mk1
                                                                    "explode_qn"
                                                                    e_string
                                                                    (e_list
                                                                    e_string)
                                                                    FStar_Reflection_V2_Builtins.explode_qn in
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    mk2
                                                                    "compare_string"
                                                                    e_string
                                                                    e_string
                                                                    e_int
                                                                    FStar_Reflection_V2_Builtins.compare_string in
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    mk2
                                                                    "push_namedv"
                                                                    e_env
                                                                    e_namedv
                                                                    e_env
                                                                    FStar_Reflection_V2_Builtins.push_namedv in
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    mk1
                                                                    "range_of_term"
                                                                    e_term
                                                                    e_range
                                                                    FStar_Reflection_V2_Builtins.range_of_term in
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    mk1
                                                                    "range_of_sigelt"
                                                                    e_sigelt
                                                                    e_range
                                                                    FStar_Reflection_V2_Builtins.range_of_sigelt in
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    mk1
                                                                    "inspect_ident"
                                                                    e_ident
                                                                    (e_tuple2
                                                                    e_string
                                                                    e_range)
                                                                    FStar_Reflection_V2_Builtins.inspect_ident in
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    mk1
                                                                    "pack_ident"
                                                                    (e_tuple2
                                                                    e_string
                                                                    e_range)
                                                                    e_ident
                                                                    FStar_Reflection_V2_Builtins.pack_ident in
                                                                    [uu___86] in
                                                                    uu___84
                                                                    ::
                                                                    uu___85 in
                                                                    uu___82
                                                                    ::
                                                                    uu___83 in
                                                                    uu___80
                                                                    ::
                                                                    uu___81 in
                                                                    uu___78
                                                                    ::
                                                                    uu___79 in
                                                                    uu___76
                                                                    ::
                                                                    uu___77 in
                                                                    uu___74
                                                                    ::
                                                                    uu___75 in
                                                                    uu___72
                                                                    ::
                                                                    uu___73 in
                                                                    uu___70
                                                                    ::
                                                                    uu___71 in
                                                                    uu___68
                                                                    ::
                                                                    uu___69 in
                                                                    uu___66
                                                                    ::
                                                                    uu___67 in
                                                                  uu___64 ::
                                                                    uu___65 in
                                                                uu___62 ::
                                                                  uu___63 in
                                                              uu___60 ::
                                                                uu___61 in
                                                            uu___58 ::
                                                              uu___59 in
                                                          uu___56 :: uu___57 in
                                                        uu___54 :: uu___55 in
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
let (uu___243 : unit) =
  FStar_Compiler_List.iter FStar_TypeChecker_Cfg.register_extra_step
    reflection_primops
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
type primitive_step =
  {
  name: FStar_Ident.lid ;
  arity: Prims.int ;
  univ_arity: Prims.int ;
  auto_reflect: Prims.int FStar_Pervasives_Native.option ;
  strong_reduction_ok: Prims.bool ;
  requires_binder_substitution: Prims.bool ;
  renorm_after: Prims.bool ;
  interpretation:
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
    ;
  interpretation_nbe:
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_Syntax_Syntax.universes ->
        FStar_TypeChecker_NBETerm.args ->
          FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option
    }
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
  primitive_step ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { name; arity; univ_arity; auto_reflect; strong_reduction_ok;
        requires_binder_substitution; renorm_after; interpretation;
        interpretation_nbe;_} -> interpretation
let (__proj__Mkprimitive_step__item__interpretation_nbe :
  primitive_step ->
    FStar_TypeChecker_NBETerm.nbe_cbs ->
      FStar_Syntax_Syntax.universes ->
        FStar_TypeChecker_NBETerm.args ->
          FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)
  =
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
  fun emb ->
    fun r ->
      fun x ->
        let uu___ = FStar_Syntax_Embeddings_Base.embed emb x in
        uu___ r FStar_Pervasives_Native.None
          FStar_Syntax_Embeddings_Base.id_norm_cb
let try_unembed_simple :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.term -> 'a FStar_Pervasives_Native.option
  =
  fun emb ->
    fun x ->
      FStar_Syntax_Embeddings_Base.try_unembed emb x
        FStar_Syntax_Embeddings_Base.id_norm_cb
let (arg_as_int :
  FStar_Syntax_Syntax.arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a ->
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_int)
let (arg_as_bool :
  FStar_Syntax_Syntax.arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a ->
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_bool)
let (arg_as_char :
  FStar_Syntax_Syntax.arg -> FStar_Char.char FStar_Pervasives_Native.option)
  =
  fun a ->
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_char)
let (arg_as_string :
  FStar_Syntax_Syntax.arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a ->
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_string)
let arg_as_list :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.arg -> 'a Prims.list FStar_Pervasives_Native.option
  =
  fun e ->
    fun a1 ->
      let uu___ =
        let uu___1 = FStar_Syntax_Embeddings.e_list e in
        try_unembed_simple uu___1 in
      FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a1)
        uu___
let (arg_as_doc :
  FStar_Syntax_Syntax.arg ->
    FStar_Pprint.document FStar_Pervasives_Native.option)
  =
  fun a ->
    FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.fst a)
      (try_unembed_simple FStar_Syntax_Embeddings.e_document)
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
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun f ->
    unary_op arg_as_int
      (fun r ->
         fun x ->
           let uu___ = f x in
           embed_simple FStar_Syntax_Embeddings.e_int r uu___)
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_int
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_int r uu___)
let (unary_bool_op :
  (Prims.bool -> Prims.bool) ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun f ->
    unary_op arg_as_bool
      (fun r ->
         fun x ->
           let uu___ = f x in
           embed_simple FStar_Syntax_Embeddings.e_bool r uu___)
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_bool
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_bool r uu___)
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    psc ->
      FStar_Syntax_Embeddings_Base.norm_cb ->
        FStar_Syntax_Syntax.universes ->
          FStar_Syntax_Syntax.args ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun f ->
    binary_op arg_as_string
      (fun r ->
         fun x ->
           fun y ->
             let uu___ = f x y in
             embed_simple FStar_Syntax_Embeddings.e_string r uu___)
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
let (built_in_primitive_steps_list : primitive_step Prims.list) =
  let list_of_string' rng s =
    let name l =
      let uu___ =
        let uu___1 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
        FStar_Syntax_Syntax.Tm_fvar uu___1 in
      FStar_Syntax_Syntax.mk uu___ rng in
    let char_t = name FStar_Parser_Const.char_lid in
    let charterm c =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c)) rng in
    let uu___ =
      FStar_Compiler_List.map charterm (FStar_String.list_of_string s) in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Syntax_Util.mk_list char_t rng)
      uu___ in
  let string_of_list' rng l =
    let s = FStar_String.string_of_list l in FStar_Syntax_Util.exp_string s in
  let string_compare' rng s1 s2 =
    let r = FStar_Compiler_String.compare s1 s2 in
    let uu___ =
      let uu___1 = FStar_Compiler_Util.string_of_int r in
      FStar_BigInt.big_int_of_string uu___1 in
    embed_simple FStar_Syntax_Embeddings.e_int rng uu___ in
  let string_concat' psc1 _n _us args =
    match args with
    | a1::a2::[] ->
        let uu___ = arg_as_string a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_list FStar_Syntax_Embeddings.e_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_Compiler_String.concat s1 s2 in
                  let uu___2 =
                    embed_simple FStar_Syntax_Embeddings.e_string
                      psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_split' psc1 _norm_cb _us args =
    match args with
    | a1::a2::[] ->
        let uu___ = arg_as_list FStar_Syntax_Embeddings.e_char a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some s1 ->
             let uu___1 = arg_as_string a2 in
             (match uu___1 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_Compiler_String.split s1 s2 in
                  let uu___2 =
                    let uu___3 =
                      FStar_Syntax_Embeddings.e_list
                        FStar_Syntax_Embeddings.e_string in
                    embed_simple uu___3 psc1.psc_range r in
                  FStar_Pervasives_Native.Some uu___2
              | uu___2 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_substring' psc1 _norm_cb _us args =
    match args with
    | a1::a2::a3::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in
          let uu___3 = arg_as_int a3 in (uu___1, uu___2, uu___3) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s1, FStar_Pervasives_Native.Some n1,
            FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1 in
             let n21 = FStar_BigInt.to_int_fs n2 in
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_Compiler_String.substring s1 n11 n21 in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_string
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_of_int rng i =
    let uu___ = FStar_BigInt.string_of_big_int i in
    embed_simple FStar_Syntax_Embeddings.e_string rng uu___ in
  let string_of_bool rng b =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (if b then "true" else "false") in
  let int_of_string rng s =
    let r = FStar_Compiler_Util.safe_int_of_string s in
    let uu___ =
      FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_fsint in
    embed_simple uu___ rng r in
  let bool_of_string rng s =
    let r =
      match s with
      | "true" -> FStar_Pervasives_Native.Some true
      | "false" -> FStar_Pervasives_Native.Some false
      | uu___ -> FStar_Pervasives_Native.None in
    let uu___ =
      FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_bool in
    embed_simple uu___ rng r in
  let lowercase rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_Compiler_String.lowercase s) in
  let uppercase rng s =
    embed_simple FStar_Syntax_Embeddings.e_string rng
      (FStar_Compiler_String.uppercase s) in
  let string_index psc1 _norm_cb _us args =
    match args with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_int a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some i)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_Compiler_String.index s i in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_char
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let string_index_of psc1 _norm_cb _us args =
    match args with
    | a1::a2::[] ->
        let uu___ =
          let uu___1 = arg_as_string a1 in
          let uu___2 = arg_as_char a2 in (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some s, FStar_Pervasives_Native.Some c)
             ->
             (try
                (fun uu___1 ->
                   match () with
                   | () ->
                       let r = FStar_Compiler_String.index_of s c in
                       let uu___2 =
                         embed_simple FStar_Syntax_Embeddings.e_int
                           psc1.psc_range r in
                       FStar_Pervasives_Native.Some uu___2) ()
              with | uu___1 -> FStar_Pervasives_Native.None)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let mk_range psc1 _norm_cb _us args =
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu___ =
          let uu___1 = arg_as_string fn in
          let uu___2 = arg_as_int from_line in
          let uu___3 = arg_as_int from_col in
          let uu___4 = arg_as_int to_line in
          let uu___5 = arg_as_int to_col in
          (uu___1, uu___2, uu___3, uu___4, uu___5) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some fn1, FStar_Pervasives_Native.Some
            from_l, FStar_Pervasives_Native.Some from_c,
            FStar_Pervasives_Native.Some to_l, FStar_Pervasives_Native.Some
            to_c) ->
             let r =
               let uu___1 =
                 let uu___2 = FStar_BigInt.to_int_fs from_l in
                 let uu___3 = FStar_BigInt.to_int_fs from_c in
                 FStar_Compiler_Range_Type.mk_pos uu___2 uu___3 in
               let uu___2 =
                 let uu___3 = FStar_BigInt.to_int_fs to_l in
                 let uu___4 = FStar_BigInt.to_int_fs to_c in
                 FStar_Compiler_Range_Type.mk_pos uu___3 uu___4 in
               FStar_Compiler_Range_Type.mk_range fn1 uu___1 uu___2 in
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_range psc1.psc_range r in
             FStar_Pervasives_Native.Some uu___1
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> FStar_Pervasives_Native.None in
  let decidable_eq neg psc1 _norm_cb _us args =
    let r = psc1.psc_range in
    let tru =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true)) r in
    let fal =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false)) r in
    match args with
    | (_typ, uu___)::(a1, uu___1)::(a2, uu___2)::[] ->
        let uu___3 = FStar_Syntax_Util.eq_tm a1 a2 in
        (match uu___3 with
         | FStar_Syntax_Util.Equal ->
             FStar_Pervasives_Native.Some (if neg then fal else tru)
         | FStar_Syntax_Util.NotEqual ->
             FStar_Pervasives_Native.Some (if neg then tru else fal)
         | uu___4 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let and_op psc1 _norm_cb _us args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ = try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (false) ->
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_bool psc1.psc_range
                 false in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (true) ->
             FStar_Pervasives_Native.Some a2
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let or_op psc1 _norm_cb _us args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ = try_unembed_simple FStar_Syntax_Embeddings.e_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (true) ->
             let uu___1 =
               embed_simple FStar_Syntax_Embeddings.e_bool psc1.psc_range
                 true in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (false) ->
             FStar_Pervasives_Native.Some a2
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let division_modulus_op op psc1 _norm_cb _us args =
    match args with
    | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
        ->
        let uu___ =
          let uu___1 = try_unembed_simple FStar_Syntax_Embeddings.e_int a1 in
          let uu___2 = try_unembed_simple FStar_Syntax_Embeddings.e_int a2 in
          (uu___1, uu___2) in
        (match uu___ with
         | (FStar_Pervasives_Native.Some m, FStar_Pervasives_Native.Some n)
             ->
             let uu___1 =
               let uu___2 = FStar_BigInt.to_int_fs n in
               uu___2 <> Prims.int_zero in
             if uu___1
             then
               let uu___2 =
                 let uu___3 = op m n in
                 embed_simple FStar_Syntax_Embeddings.e_int psc1.psc_range
                   uu___3 in
               FStar_Pervasives_Native.Some uu___2
             else FStar_Pervasives_Native.None
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments" in
  let bogus_cbs =
    {
      FStar_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
      FStar_TypeChecker_NBETerm.translate =
        (fun uu___ -> failwith "bogus_cbs translate")
    } in
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
      let uu___1 =
        FStar_TypeChecker_NBETerm.unary_int_op
          (fun x -> FStar_BigInt.minus_big_int x) in
      (FStar_Parser_Const.op_Minus, Prims.int_one, Prims.int_zero,
        (unary_int_op (fun x -> FStar_BigInt.minus_big_int x)), uu___1) in
    let uu___1 =
      let uu___2 =
        let uu___3 =
          FStar_TypeChecker_NBETerm.binary_int_op
            (fun x -> fun y -> FStar_BigInt.add_big_int x y) in
        (FStar_Parser_Const.op_Addition, (Prims.of_int (2)), Prims.int_zero,
          (binary_int_op (fun x -> fun y -> FStar_BigInt.add_big_int x y)),
          uu___3) in
      let uu___3 =
        let uu___4 =
          let uu___5 =
            FStar_TypeChecker_NBETerm.binary_int_op
              (fun x -> fun y -> FStar_BigInt.sub_big_int x y) in
          (FStar_Parser_Const.op_Subtraction, (Prims.of_int (2)),
            Prims.int_zero,
            (binary_int_op (fun x -> fun y -> FStar_BigInt.sub_big_int x y)),
            uu___5) in
        let uu___5 =
          let uu___6 =
            let uu___7 =
              FStar_TypeChecker_NBETerm.binary_int_op
                (fun x -> fun y -> FStar_BigInt.mult_big_int x y) in
            (FStar_Parser_Const.op_Multiply, (Prims.of_int (2)),
              Prims.int_zero,
              (binary_int_op
                 (fun x -> fun y -> FStar_BigInt.mult_big_int x y)), uu___7) in
          let uu___7 =
            let uu___8 =
              let uu___9 = division_modulus_op FStar_BigInt.div_big_int in
              (FStar_Parser_Const.op_Division, (Prims.of_int (2)),
                Prims.int_zero, uu___9,
                (fun _us ->
                   FStar_TypeChecker_NBETerm.division_modulus_op
                     FStar_BigInt.div_big_int)) in
            let uu___9 =
              let uu___10 =
                let uu___11 =
                  FStar_TypeChecker_NBETerm.binary_op
                    FStar_TypeChecker_NBETerm.arg_as_int
                    (fun x ->
                       fun y ->
                         let uu___12 = FStar_BigInt.lt_big_int x y in
                         FStar_TypeChecker_NBETerm.embed
                           FStar_TypeChecker_NBETerm.e_bool bogus_cbs uu___12) in
                (FStar_Parser_Const.op_LT, (Prims.of_int (2)),
                  Prims.int_zero,
                  (binary_op arg_as_int
                     (fun r ->
                        fun x ->
                          fun y ->
                            let uu___12 = FStar_BigInt.lt_big_int x y in
                            embed_simple FStar_Syntax_Embeddings.e_bool r
                              uu___12)), uu___11) in
              let uu___11 =
                let uu___12 =
                  let uu___13 =
                    FStar_TypeChecker_NBETerm.binary_op
                      FStar_TypeChecker_NBETerm.arg_as_int
                      (fun x ->
                         fun y ->
                           let uu___14 = FStar_BigInt.le_big_int x y in
                           FStar_TypeChecker_NBETerm.embed
                             FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                             uu___14) in
                  (FStar_Parser_Const.op_LTE, (Prims.of_int (2)),
                    Prims.int_zero,
                    (binary_op arg_as_int
                       (fun r ->
                          fun x ->
                            fun y ->
                              let uu___14 = FStar_BigInt.le_big_int x y in
                              embed_simple FStar_Syntax_Embeddings.e_bool r
                                uu___14)), uu___13) in
                let uu___13 =
                  let uu___14 =
                    let uu___15 =
                      FStar_TypeChecker_NBETerm.binary_op
                        FStar_TypeChecker_NBETerm.arg_as_int
                        (fun x ->
                           fun y ->
                             let uu___16 = FStar_BigInt.gt_big_int x y in
                             FStar_TypeChecker_NBETerm.embed
                               FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                               uu___16) in
                    (FStar_Parser_Const.op_GT, (Prims.of_int (2)),
                      Prims.int_zero,
                      (binary_op arg_as_int
                         (fun r ->
                            fun x ->
                              fun y ->
                                let uu___16 = FStar_BigInt.gt_big_int x y in
                                embed_simple FStar_Syntax_Embeddings.e_bool r
                                  uu___16)), uu___15) in
                  let uu___15 =
                    let uu___16 =
                      let uu___17 =
                        FStar_TypeChecker_NBETerm.binary_op
                          FStar_TypeChecker_NBETerm.arg_as_int
                          (fun x ->
                             fun y ->
                               let uu___18 = FStar_BigInt.ge_big_int x y in
                               FStar_TypeChecker_NBETerm.embed
                                 FStar_TypeChecker_NBETerm.e_bool bogus_cbs
                                 uu___18) in
                      (FStar_Parser_Const.op_GTE, (Prims.of_int (2)),
                        Prims.int_zero,
                        (binary_op arg_as_int
                           (fun r ->
                              fun x ->
                                fun y ->
                                  let uu___18 = FStar_BigInt.ge_big_int x y in
                                  embed_simple FStar_Syntax_Embeddings.e_bool
                                    r uu___18)), uu___17) in
                    let uu___17 =
                      let uu___18 =
                        let uu___19 =
                          division_modulus_op FStar_BigInt.mod_big_int in
                        (FStar_Parser_Const.op_Modulus, (Prims.of_int (2)),
                          Prims.int_zero, uu___19,
                          (fun _us ->
                             FStar_TypeChecker_NBETerm.division_modulus_op
                               FStar_BigInt.mod_big_int)) in
                      let uu___19 =
                        let uu___20 =
                          let uu___21 =
                            FStar_TypeChecker_NBETerm.unary_bool_op
                              (fun x -> Prims.op_Negation x) in
                          (FStar_Parser_Const.op_Negation, Prims.int_one,
                            Prims.int_zero,
                            (unary_bool_op (fun x -> Prims.op_Negation x)),
                            uu___21) in
                        let uu___21 =
                          let uu___22 =
                            let uu___23 =
                              let uu___24 =
                                let u32_int_to_t =
                                  let uu___25 =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      ["FStar"; "UInt32"; "uint_to_t"]
                                      FStar_Parser_Const.p2l in
                                  FStar_Compiler_Effect.op_Bar_Greater
                                    uu___25
                                    (fun l ->
                                       FStar_Syntax_Syntax.lid_as_fv l
                                         FStar_Pervasives_Native.None) in
                                let uu___25 =
                                  FStar_TypeChecker_NBETerm.unary_op
                                    FStar_TypeChecker_NBETerm.arg_as_char
                                    (fun c ->
                                       let uu___26 =
                                         let uu___27 =
                                           FStar_Compiler_Effect.op_Bar_Greater
                                             c
                                             FStar_Compiler_Util.int_of_char in
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           uu___27 FStar_BigInt.of_int_fs in
                                       FStar_TypeChecker_NBETerm.int_as_bounded
                                         u32_int_to_t uu___26) in
                                (FStar_Parser_Const.char_u32_of_char,
                                  Prims.int_one, Prims.int_zero,
                                  (unary_op arg_as_char
                                     (fun r ->
                                        fun c ->
                                          let uu___26 =
                                            let uu___27 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                c
                                                FStar_Compiler_Util.int_of_char in
                                            FStar_Compiler_Effect.op_Bar_Greater
                                              uu___27 FStar_BigInt.of_int_fs in
                                          int_as_bounded r u32_int_to_t
                                            uu___26)), uu___25) in
                              let uu___25 =
                                let uu___26 =
                                  let uu___27 =
                                    FStar_TypeChecker_NBETerm.unary_op
                                      FStar_TypeChecker_NBETerm.arg_as_int
                                      FStar_TypeChecker_NBETerm.string_of_int in
                                  (FStar_Parser_Const.string_of_int_lid,
                                    Prims.int_one, Prims.int_zero,
                                    (unary_op arg_as_int string_of_int),
                                    uu___27) in
                                let uu___27 =
                                  let uu___28 =
                                    let uu___29 =
                                      FStar_TypeChecker_NBETerm.unary_op
                                        FStar_TypeChecker_NBETerm.arg_as_bool
                                        FStar_TypeChecker_NBETerm.string_of_bool in
                                    (FStar_Parser_Const.string_of_bool_lid,
                                      Prims.int_one, Prims.int_zero,
                                      (unary_op arg_as_bool string_of_bool),
                                      uu___29) in
                                  let uu___29 =
                                    let uu___30 =
                                      let uu___31 =
                                        FStar_TypeChecker_NBETerm.unary_op
                                          FStar_TypeChecker_NBETerm.arg_as_string
                                          FStar_TypeChecker_NBETerm.bool_of_string in
                                      (FStar_Parser_Const.bool_of_string_lid,
                                        Prims.int_one, Prims.int_zero,
                                        (unary_op arg_as_string
                                           bool_of_string), uu___31) in
                                    let uu___31 =
                                      let uu___32 =
                                        let uu___33 =
                                          FStar_TypeChecker_NBETerm.unary_op
                                            FStar_TypeChecker_NBETerm.arg_as_string
                                            FStar_TypeChecker_NBETerm.int_of_string in
                                        (FStar_Parser_Const.int_of_string_lid,
                                          Prims.int_one, Prims.int_zero,
                                          (unary_op arg_as_string
                                             int_of_string), uu___33) in
                                      let uu___33 =
                                        let uu___34 =
                                          let uu___35 =
                                            FStar_TypeChecker_NBETerm.unary_op
                                              FStar_TypeChecker_NBETerm.arg_as_string
                                              FStar_TypeChecker_NBETerm.list_of_string' in
                                          (FStar_Parser_Const.string_list_of_string_lid,
                                            Prims.int_one, Prims.int_zero,
                                            (unary_op arg_as_string
                                               list_of_string'), uu___35) in
                                        let uu___35 =
                                          let uu___36 =
                                            let uu___37 =
                                              FStar_TypeChecker_NBETerm.unary_op
                                                (FStar_TypeChecker_NBETerm.arg_as_list
                                                   FStar_TypeChecker_NBETerm.e_char)
                                                FStar_TypeChecker_NBETerm.string_of_list' in
                                            (FStar_Parser_Const.string_string_of_list_lid,
                                              Prims.int_one, Prims.int_zero,
                                              (unary_op
                                                 (arg_as_list
                                                    FStar_Syntax_Embeddings.e_char)
                                                 string_of_list'), uu___37) in
                                          let uu___37 =
                                            let uu___38 =
                                              let uu___39 =
                                                let uu___40 =
                                                  let uu___41 =
                                                    FStar_TypeChecker_NBETerm.binary_string_op
                                                      (fun x ->
                                                         fun y ->
                                                           Prims.strcat x y) in
                                                  (FStar_Parser_Const.prims_strcat_lid,
                                                    (Prims.of_int (2)),
                                                    Prims.int_zero,
                                                    (binary_string_op
                                                       (fun x ->
                                                          fun y ->
                                                            Prims.strcat x y)),
                                                    uu___41) in
                                                let uu___41 =
                                                  let uu___42 =
                                                    let uu___43 =
                                                      let uu___44 =
                                                        FStar_TypeChecker_NBETerm.binary_op
                                                          FStar_TypeChecker_NBETerm.arg_as_string
                                                          FStar_TypeChecker_NBETerm.string_compare' in
                                                      (FStar_Parser_Const.string_compare_lid,
                                                        (Prims.of_int (2)),
                                                        Prims.int_zero,
                                                        (binary_op
                                                           arg_as_string
                                                           string_compare'),
                                                        uu___44) in
                                                    let uu___44 =
                                                      let uu___45 =
                                                        let uu___46 =
                                                          FStar_TypeChecker_NBETerm.unary_op
                                                            FStar_TypeChecker_NBETerm.arg_as_string
                                                            FStar_TypeChecker_NBETerm.string_lowercase in
                                                        (FStar_Parser_Const.string_lowercase_lid,
                                                          Prims.int_one,
                                                          Prims.int_zero,
                                                          (unary_op
                                                             arg_as_string
                                                             lowercase),
                                                          uu___46) in
                                                      let uu___46 =
                                                        let uu___47 =
                                                          let uu___48 =
                                                            FStar_TypeChecker_NBETerm.unary_op
                                                              FStar_TypeChecker_NBETerm.arg_as_string
                                                              FStar_TypeChecker_NBETerm.string_uppercase in
                                                          (FStar_Parser_Const.string_uppercase_lid,
                                                            Prims.int_one,
                                                            Prims.int_zero,
                                                            (unary_op
                                                               arg_as_string
                                                               uppercase),
                                                            uu___48) in
                                                        let uu___48 =
                                                          let uu___49 =
                                                            let uu___50 =
                                                              let uu___51 =
                                                                let uu___52 =
                                                                  let uu___53
                                                                    =
                                                                    let uu___54
                                                                    =
                                                                    let uu___55
                                                                    =
                                                                    FStar_Parser_Const.p2l
                                                                    ["FStar";
                                                                    "Range";
                                                                    "mk_range"] in
                                                                    (uu___55,
                                                                    (Prims.of_int (5)),
                                                                    Prims.int_zero,
                                                                    mk_range,
                                                                    (fun
                                                                    uu___56
                                                                    ->
                                                                    FStar_TypeChecker_NBETerm.mk_range)) in
                                                                    [uu___54] in
                                                                  (FStar_Parser_Const.op_notEq,
                                                                    (Prims.of_int (3)),
                                                                    Prims.int_zero,
                                                                    (
                                                                    decidable_eq
                                                                    true),
                                                                    (
                                                                    fun
                                                                    uu___54
                                                                    ->
                                                                    FStar_TypeChecker_NBETerm.decidable_eq
                                                                    true)) ::
                                                                    uu___53 in
                                                                (FStar_Parser_Const.op_Eq,
                                                                  (Prims.of_int (3)),
                                                                  Prims.int_zero,
                                                                  (decidable_eq
                                                                    false),
                                                                  (fun
                                                                    uu___53
                                                                    ->
                                                                    FStar_TypeChecker_NBETerm.decidable_eq
                                                                    false))
                                                                  :: uu___52 in
                                                              (FStar_Parser_Const.string_sub_lid,
                                                                (Prims.of_int (3)),
                                                                Prims.int_zero,
                                                                string_substring',
                                                                (fun uu___52
                                                                   ->
                                                                   FStar_TypeChecker_NBETerm.string_substring'))
                                                                :: uu___51 in
                                                            (FStar_Parser_Const.string_index_of_lid,
                                                              (Prims.of_int (2)),
                                                              Prims.int_zero,
                                                              string_index_of,
                                                              (fun uu___51 ->
                                                                 FStar_TypeChecker_NBETerm.string_index_of))
                                                              :: uu___50 in
                                                          (FStar_Parser_Const.string_index_lid,
                                                            (Prims.of_int (2)),
                                                            Prims.int_zero,
                                                            string_index,
                                                            (fun uu___50 ->
                                                               FStar_TypeChecker_NBETerm.string_index))
                                                            :: uu___49 in
                                                        uu___47 :: uu___48 in
                                                      uu___45 :: uu___46 in
                                                    uu___43 :: uu___44 in
                                                  (FStar_Parser_Const.string_concat_lid,
                                                    (Prims.of_int (2)),
                                                    Prims.int_zero,
                                                    string_concat',
                                                    (fun uu___43 ->
                                                       FStar_TypeChecker_NBETerm.string_concat'))
                                                    :: uu___42 in
                                                uu___40 :: uu___41 in
                                              (FStar_Parser_Const.string_split_lid,
                                                (Prims.of_int (2)),
                                                Prims.int_zero,
                                                string_split',
                                                (fun uu___40 ->
                                                   FStar_TypeChecker_NBETerm.string_split'))
                                                :: uu___39 in
                                            (FStar_Parser_Const.string_make_lid,
                                              (Prims.of_int (2)),
                                              Prims.int_zero,
                                              (mixed_binary_op
                                                 (fun x -> arg_as_int x)
                                                 (fun x -> arg_as_char x)
                                                 (fun r ->
                                                    fun s ->
                                                      embed_simple
                                                        FStar_Syntax_Embeddings.e_string
                                                        r s)
                                                 (fun r ->
                                                    fun _us ->
                                                      fun x ->
                                                        fun y ->
                                                          let uu___39 =
                                                            let uu___40 =
                                                              FStar_BigInt.to_int_fs
                                                                x in
                                                            FStar_Compiler_String.make
                                                              uu___40 y in
                                                          FStar_Pervasives_Native.Some
                                                            uu___39)),
                                              (FStar_TypeChecker_NBETerm.mixed_binary_op
                                                 FStar_TypeChecker_NBETerm.arg_as_int
                                                 FStar_TypeChecker_NBETerm.arg_as_char
                                                 (FStar_TypeChecker_NBETerm.embed
                                                    FStar_TypeChecker_NBETerm.e_string
                                                    bogus_cbs)
                                                 (fun _us ->
                                                    fun x ->
                                                      fun y ->
                                                        let uu___39 =
                                                          let uu___40 =
                                                            FStar_BigInt.to_int_fs
                                                              x in
                                                          FStar_Compiler_String.make
                                                            uu___40 y in
                                                        FStar_Pervasives_Native.Some
                                                          uu___39)))
                                              :: uu___38 in
                                          uu___36 :: uu___37 in
                                        uu___34 :: uu___35 in
                                      uu___32 :: uu___33 in
                                    uu___30 :: uu___31 in
                                  uu___28 :: uu___29 in
                                uu___26 :: uu___27 in
                              uu___24 :: uu___25 in
                            (FStar_Parser_Const.op_Or, (Prims.of_int (2)),
                              Prims.int_zero, or_op,
                              (fun uu___24 -> FStar_TypeChecker_NBETerm.or_op))
                              :: uu___23 in
                          (FStar_Parser_Const.op_And, (Prims.of_int (2)),
                            Prims.int_zero, and_op,
                            (fun uu___23 -> FStar_TypeChecker_NBETerm.and_op))
                            :: uu___22 in
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
    uu___ :: uu___1 in
  let weak_ops = [] in
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
      FStar_Compiler_Effect.op_Bar_Greater
        (FStar_Compiler_List.op_At bounded_signed_int_types
           bounded_unsigned_int_types)
        (FStar_Compiler_List.collect
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
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___9 m1) in
                    (uu___3, (Prims.of_int (2)), Prims.int_zero,
                      (binary_op arg_as_bounded_int
                         (fun r ->
                            fun uu___5 ->
                              fun uu___6 ->
                                match (uu___5, uu___6) with
                                | ((int_to_t, x, m1), (uu___7, y, uu___8)) ->
                                    let uu___9 =
                                      let uu___10 =
                                        FStar_BigInt.add_big_int x y in
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
                                     let uu___12 =
                                       FStar_BigInt.sub_big_int x y in
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
                                  | ((int_to_t, x, m1), (uu___9, y, uu___10))
                                      ->
                                      let uu___11 =
                                        let uu___12 =
                                          FStar_BigInt.sub_big_int x y in
                                        int_as_bounded r int_to_t uu___12 in
                                      with_meta_ds r uu___11 m1)), uu___6) in
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          FStar_Parser_Const.p2l ["FStar"; m; "mul"] in
                        let uu___8 =
                          FStar_TypeChecker_NBETerm.binary_op
                            FStar_TypeChecker_NBETerm.arg_as_bounded_int
                            (fun uu___9 ->
                               fun uu___10 ->
                                 match (uu___9, uu___10) with
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
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
                                    | ((int_to_t, x, m1),
                                       (uu___11, y, uu___12)) ->
                                        let uu___13 =
                                          let uu___14 =
                                            FStar_BigInt.mult_big_int x y in
                                          int_as_bounded r int_to_t uu___14 in
                                        with_meta_ds r uu___13 m1)), uu___8) in
                      let uu___7 =
                        let uu___8 =
                          let uu___9 =
                            FStar_Parser_Const.p2l ["FStar"; m; "v"] in
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
                                                FStar_Syntax_Embeddings.e_bool
                                                r uu___18 in
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
                                                    FStar_BigInt.lt_big_int x
                                                      y in
                                                  embed_simple
                                                    FStar_Syntax_Embeddings.e_bool
                                                    r uu___22 in
                                                with_meta_ds r uu___21 m1)),
                                  uu___16) in
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 =
                                    FStar_Parser_Const.p2l
                                      ["FStar"; m; "lte"] in
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
                                                   FStar_BigInt.le_big_int x
                                                     y in
                                                 FStar_TypeChecker_NBETerm.embed
                                                   FStar_TypeChecker_NBETerm.e_bool
                                                   bogus_cbs uu___24 in
                                               FStar_TypeChecker_NBETerm.with_meta_ds
                                                 uu___23 m1) in
                                  (uu___17, (Prims.of_int (2)),
                                    Prims.int_zero,
                                    (binary_op arg_as_bounded_int
                                       (fun r ->
                                          fun uu___19 ->
                                            fun uu___20 ->
                                              match (uu___19, uu___20) with
                                              | ((int_to_t, x, m1),
                                                 (uu___21, y, uu___22)) ->
                                                  let uu___23 =
                                                    let uu___24 =
                                                      FStar_BigInt.le_big_int
                                                        x y in
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
                  uu___2 :: uu___3)) in
    let unsigned_modulo_add_sub_mul_div_rem =
      FStar_Compiler_Effect.op_Bar_Greater bounded_unsigned_int_types
        (FStar_Compiler_List.collect
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
                                  | ((int_to_t, x, m1), (uu___8, y, uu___9))
                                      ->
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
                                     | ((int_to_t, x, m1),
                                        (uu___8, y, uu___9)) ->
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
                                  | ((int_to_t, x, m1), (uu___8, y, uu___9))
                                      ->
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
                                 | ((int_to_t, x, m1), (uu___10, y, uu___11))
                                     ->
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
                                    | ((int_to_t, x, m1),
                                       (uu___10, y, uu___11)) ->
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
                                   | ((int_to_t, x, m1),
                                      (uu___12, y, uu___13)) ->
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
                                          with_meta_ds r uu___14 m1)),
                            uu___9) in
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
                                              int_as_bounded r int_to_t
                                                uu___17 in
                                            with_meta_ds r uu___16 m1)),
                              uu___11) in
                          [uu___9] in
                        uu___7 :: uu___8 in
                      uu___5 :: uu___6 in
                    uu___3 :: uu___4 in
                  FStar_Compiler_List.op_At uu___1 uu___2)) in
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
          failwith uu___1 in
    let bitwise =
      FStar_Compiler_Effect.op_Bar_Greater bounded_unsigned_int_types
        (FStar_Compiler_List.collect
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
                                   let uu___10 =
                                     FStar_BigInt.logor_big_int x y in
                                   FStar_TypeChecker_NBETerm.int_as_bounded
                                     int_to_t uu___10 in
                                 FStar_TypeChecker_NBETerm.with_meta_ds
                                   uu___9 m1) in
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
                      let uu___5 =
                        FStar_Parser_Const.p2l ["FStar"; m; "logand"] in
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
                                  | ((int_to_t, x, m1), (uu___9, y, uu___10))
                                      ->
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
                                 | ((int_to_t, x, m1), (uu___11, y, uu___12))
                                     ->
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
                                    | ((int_to_t, x, m1),
                                       (uu___11, y, uu___12)) ->
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
                                            FStar_BigInt.logand_big_int
                                              uu___14 uu___15 in
                                          int_as_bounded r int_to_t uu___13 in
                                        with_meta_ds r uu___12 d)), uu___10) in
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              FStar_Parser_Const.p2l
                                ["FStar"; m; "shift_left"] in
                            let uu___12 =
                              FStar_TypeChecker_NBETerm.binary_op
                                FStar_TypeChecker_NBETerm.arg_as_bounded_int
                                (fun uu___13 ->
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
                                              int_as_bounded r int_to_t
                                                uu___18 in
                                            with_meta_ds r uu___17 d)),
                              uu___12) in
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
                  uu___2 :: uu___3)) in
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
            FStar_Compiler_Effect.op_Bar_Greater
              FStar_Parser_Const.immutable_array_t_lid
              FStar_Ident.string_of_lid in
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
                                  FStar_Syntax_Embeddings.e_any in
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
                                FStar_Syntax_Embeddings.e_any in
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
                             FStar_Compiler_Effect.op_Less_Bar
                               FStar_TypeChecker_NBETerm.mk_t uu___6) in
                      (uu___3, uu___4) in
                    FStar_TypeChecker_NBETerm.Lazy uu___2 in
                  FStar_Compiler_Effect.op_Less_Bar
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
  let issue_ops =
    let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Issue"; l] in
    let arg_as_issue x =
      FStar_Syntax_Embeddings_Base.try_unembed
        FStar_Syntax_Embeddings.e_issue (FStar_Pervasives_Native.fst x)
        FStar_Syntax_Embeddings_Base.id_norm_cb in
    let option_int_as_option_z oi =
      match oi with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some i ->
          let uu___ = FStar_BigInt.of_int_fs i in
          FStar_Pervasives_Native.Some uu___ in
    let option_z_as_option_int zi =
      match zi with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some i ->
          let uu___ = FStar_BigInt.to_int_fs i in
          FStar_Pervasives_Native.Some uu___ in
    let nbe_arg_as_issue x =
      FStar_TypeChecker_NBETerm.unembed FStar_TypeChecker_NBETerm.e_issue
        bogus_cbs (FStar_Pervasives_Native.fst x) in
    let nbe_str s =
      FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_string
        bogus_cbs s in
    let nbe_int s =
      FStar_TypeChecker_NBETerm.embed FStar_TypeChecker_NBETerm.e_int
        bogus_cbs s in
    let nbe_option_int oi =
      let em =
        let uu___ =
          FStar_TypeChecker_NBETerm.e_option FStar_TypeChecker_NBETerm.e_int in
        FStar_TypeChecker_NBETerm.embed uu___ bogus_cbs in
      let uu___ = option_int_as_option_z oi in em uu___ in
    let uu___ =
      let uu___1 = mk_lid "message_of_issue" in
      let uu___2 =
        FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
          (fun issue ->
             let uu___3 =
               FStar_TypeChecker_NBETerm.e_list
                 FStar_TypeChecker_NBETerm.e_document in
             FStar_TypeChecker_NBETerm.embed uu___3 bogus_cbs
               issue.FStar_Errors.issue_msg) in
      (uu___1, Prims.int_one, Prims.int_zero,
        (unary_op arg_as_issue
           (fun _r ->
              fun issue ->
                let uu___3 =
                  FStar_Syntax_Embeddings.e_list
                    FStar_Syntax_Embeddings.e_document in
                embed_simple uu___3 FStar_Compiler_Range_Type.dummyRange
                  issue.FStar_Errors.issue_msg)), uu___2) in
    let uu___1 =
      let uu___2 =
        let uu___3 = mk_lid "level_of_issue" in
        let uu___4 =
          FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
            (fun issue ->
               let uu___5 =
                 FStar_Errors.string_of_issue_level
                   issue.FStar_Errors.issue_level in
               nbe_str uu___5) in
        (uu___3, Prims.int_one, Prims.int_zero,
          (unary_op arg_as_issue
             (fun _r ->
                fun issue ->
                  let uu___5 =
                    FStar_Errors.string_of_issue_level
                      issue.FStar_Errors.issue_level in
                  FStar_Syntax_Util.exp_string uu___5)), uu___4) in
      let uu___3 =
        let uu___4 =
          let uu___5 = mk_lid "number_of_issue" in
          let uu___6 =
            FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
              (fun issue -> nbe_option_int issue.FStar_Errors.issue_number) in
          (uu___5, Prims.int_one, Prims.int_zero,
            (unary_op arg_as_issue
               (fun _r ->
                  fun issue ->
                    let uu___7 =
                      FStar_Syntax_Embeddings.e_option
                        FStar_Syntax_Embeddings.e_int in
                    let uu___8 =
                      option_int_as_option_z issue.FStar_Errors.issue_number in
                    embed_simple uu___7 FStar_Compiler_Range_Type.dummyRange
                      uu___8)), uu___6) in
        let uu___5 =
          let uu___6 =
            let uu___7 = mk_lid "range_of_issue" in
            let uu___8 =
              FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
                (fun issue ->
                   let uu___9 =
                     FStar_TypeChecker_NBETerm.e_option
                       FStar_TypeChecker_NBETerm.e_range in
                   FStar_TypeChecker_NBETerm.embed uu___9 bogus_cbs
                     issue.FStar_Errors.issue_range) in
            (uu___7, Prims.int_one, Prims.int_zero,
              (unary_op arg_as_issue
                 (fun _r ->
                    fun issue ->
                      let uu___9 =
                        FStar_Syntax_Embeddings.e_option
                          FStar_Syntax_Embeddings.e_range in
                      embed_simple uu___9
                        FStar_Compiler_Range_Type.dummyRange
                        issue.FStar_Errors.issue_range)), uu___8) in
          let uu___7 =
            let uu___8 =
              let uu___9 = mk_lid "context_of_issue" in
              let uu___10 =
                FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
                  (fun issue ->
                     let uu___11 =
                       FStar_TypeChecker_NBETerm.e_list
                         FStar_TypeChecker_NBETerm.e_string in
                     FStar_TypeChecker_NBETerm.embed uu___11 bogus_cbs
                       issue.FStar_Errors.issue_ctx) in
              (uu___9, Prims.int_one, Prims.int_zero,
                (unary_op arg_as_issue
                   (fun _r ->
                      fun issue ->
                        let uu___11 =
                          FStar_Syntax_Embeddings.e_list
                            FStar_Syntax_Embeddings.e_string in
                        embed_simple uu___11
                          FStar_Compiler_Range_Type.dummyRange
                          issue.FStar_Errors.issue_ctx)), uu___10) in
            let uu___9 =
              let uu___10 =
                let uu___11 = mk_lid "render_issue" in
                let uu___12 =
                  FStar_TypeChecker_NBETerm.unary_op nbe_arg_as_issue
                    (fun issue ->
                       let uu___13 = FStar_Errors.format_issue issue in
                       nbe_str uu___13) in
                (uu___11, Prims.int_one, Prims.int_zero,
                  (unary_op arg_as_issue
                     (fun _r ->
                        fun issue ->
                          let uu___13 = FStar_Errors.format_issue issue in
                          FStar_Syntax_Util.exp_string uu___13)), uu___12) in
              let uu___11 =
                let uu___12 =
                  let uu___13 = mk_lid "mk_issue_doc" in
                  (uu___13, (Prims.of_int (5)), Prims.int_zero,
                    (fun psc1 ->
                       fun univs ->
                         fun cbs ->
                           fun args ->
                             match args with
                             | (level, uu___14)::(msg, uu___15)::(range,
                                                                  uu___16)::
                                 (number, uu___17)::(context, uu___18)::[] ->
                                 let try_unembed e x =
                                   FStar_Syntax_Embeddings_Base.try_unembed e
                                     x
                                     FStar_Syntax_Embeddings_Base.id_norm_cb in
                                 let uu___19 =
                                   let uu___20 =
                                     try_unembed
                                       FStar_Syntax_Embeddings.e_string level in
                                   let uu___21 =
                                     let uu___22 =
                                       FStar_Syntax_Embeddings.e_list
                                         FStar_Syntax_Embeddings.e_document in
                                     try_unembed uu___22 msg in
                                   let uu___22 =
                                     let uu___23 =
                                       FStar_Syntax_Embeddings.e_option
                                         FStar_Syntax_Embeddings.e_range in
                                     try_unembed uu___23 range in
                                   let uu___23 =
                                     let uu___24 =
                                       FStar_Syntax_Embeddings.e_option
                                         FStar_Syntax_Embeddings.e_int in
                                     try_unembed uu___24 number in
                                   let uu___24 =
                                     let uu___25 =
                                       FStar_Syntax_Embeddings.e_list
                                         FStar_Syntax_Embeddings.e_string in
                                     try_unembed uu___25 context in
                                   (uu___20, uu___21, uu___22, uu___23,
                                     uu___24) in
                                 (match uu___19 with
                                  | (FStar_Pervasives_Native.Some level1,
                                     FStar_Pervasives_Native.Some msg1,
                                     FStar_Pervasives_Native.Some range1,
                                     FStar_Pervasives_Native.Some number1,
                                     FStar_Pervasives_Native.Some context1)
                                      ->
                                      let issue =
                                        let uu___20 =
                                          FStar_Errors.issue_level_of_string
                                            level1 in
                                        let uu___21 =
                                          option_z_as_option_int number1 in
                                        {
                                          FStar_Errors.issue_msg = msg1;
                                          FStar_Errors.issue_level = uu___20;
                                          FStar_Errors.issue_range = range1;
                                          FStar_Errors.issue_number = uu___21;
                                          FStar_Errors.issue_ctx = context1
                                        } in
                                      let uu___20 =
                                        embed_simple
                                          FStar_Syntax_Embeddings.e_issue
                                          psc1.psc_range issue in
                                      FStar_Pervasives_Native.Some uu___20
                                  | uu___20 -> FStar_Pervasives_Native.None)
                             | uu___14 -> FStar_Pervasives_Native.None),
                    (fun univs ->
                       fun args ->
                         match args with
                         | (level, uu___14)::(msg, uu___15)::(range, uu___16)::
                             (number, uu___17)::(context, uu___18)::[] ->
                             let try_unembed e x =
                               FStar_TypeChecker_NBETerm.unembed e bogus_cbs
                                 x in
                             let uu___19 =
                               let uu___20 =
                                 try_unembed
                                   FStar_TypeChecker_NBETerm.e_string level in
                               let uu___21 =
                                 let uu___22 =
                                   FStar_TypeChecker_NBETerm.e_list
                                     FStar_TypeChecker_NBETerm.e_document in
                                 try_unembed uu___22 msg in
                               let uu___22 =
                                 let uu___23 =
                                   FStar_TypeChecker_NBETerm.e_option
                                     FStar_TypeChecker_NBETerm.e_range in
                                 try_unembed uu___23 range in
                               let uu___23 =
                                 let uu___24 =
                                   FStar_TypeChecker_NBETerm.e_option
                                     FStar_TypeChecker_NBETerm.e_int in
                                 try_unembed uu___24 number in
                               let uu___24 =
                                 let uu___25 =
                                   FStar_TypeChecker_NBETerm.e_list
                                     FStar_TypeChecker_NBETerm.e_string in
                                 try_unembed uu___25 context in
                               (uu___20, uu___21, uu___22, uu___23, uu___24) in
                             (match uu___19 with
                              | (FStar_Pervasives_Native.Some level1,
                                 FStar_Pervasives_Native.Some msg1,
                                 FStar_Pervasives_Native.Some range1,
                                 FStar_Pervasives_Native.Some number1,
                                 FStar_Pervasives_Native.Some context1) ->
                                  let issue =
                                    let uu___20 =
                                      FStar_Errors.issue_level_of_string
                                        level1 in
                                    let uu___21 =
                                      option_z_as_option_int number1 in
                                    {
                                      FStar_Errors.issue_msg = msg1;
                                      FStar_Errors.issue_level = uu___20;
                                      FStar_Errors.issue_range = range1;
                                      FStar_Errors.issue_number = uu___21;
                                      FStar_Errors.issue_ctx = context1
                                    } in
                                  let uu___20 =
                                    FStar_TypeChecker_NBETerm.embed
                                      FStar_TypeChecker_NBETerm.e_issue
                                      bogus_cbs issue in
                                  FStar_Pervasives_Native.Some uu___20
                              | uu___20 -> FStar_Pervasives_Native.None)
                         | uu___14 -> FStar_Pervasives_Native.None)) in
                [uu___12] in
              uu___10 :: uu___11 in
            uu___8 :: uu___9 in
          uu___6 :: uu___7 in
        uu___4 :: uu___5 in
      uu___2 :: uu___3 in
    uu___ :: uu___1 in
  let doc_ops =
    let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Stubs"; "Pprint"; l] in
    let uu___ =
      let uu___1 = mk_lid "arbitrary_string" in
      let uu___2 =
        FStar_TypeChecker_NBETerm.unary_op
          FStar_TypeChecker_NBETerm.arg_as_string
          (fun str ->
             let uu___3 = FStar_Pprint.arbitrary_string str in
             FStar_TypeChecker_NBETerm.embed
               FStar_TypeChecker_NBETerm.e_document bogus_cbs uu___3) in
      (uu___1, Prims.int_one, Prims.int_zero,
        (unary_op arg_as_string
           (fun r ->
              fun str ->
                let uu___3 = FStar_Pprint.arbitrary_string str in
                embed_simple FStar_Syntax_Embeddings.e_document r uu___3)),
        uu___2) in
    let uu___1 =
      let uu___2 =
        let uu___3 = mk_lid "render" in
        let uu___4 =
          FStar_TypeChecker_NBETerm.unary_op
            FStar_TypeChecker_NBETerm.arg_as_doc
            (fun doc ->
               let uu___5 = FStar_Pprint.render doc in
               FStar_TypeChecker_NBETerm.embed
                 FStar_TypeChecker_NBETerm.e_string bogus_cbs uu___5) in
        (uu___3, Prims.int_one, Prims.int_zero,
          (unary_op arg_as_doc
             (fun r ->
                fun doc ->
                  let uu___5 = FStar_Pprint.render doc in
                  embed_simple FStar_Syntax_Embeddings.e_string r uu___5)),
          uu___4) in
      [uu___2] in
    uu___ :: uu___1 in
  let seal_steps =
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
                         let uu___8 =
                           FStar_Syntax_Embeddings.e_sealed
                             FStar_Syntax_Embeddings.e_any in
                         try_unembed uu___8 s in
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
                            let uu___6 = FStar_Syntax_Embeddings.e_sealed emb in
                            embed_simple uu___6 psc1.psc_range r in
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
                        let uu___8 =
                          FStar_Syntax_Embeddings.e_sealed
                            FStar_Syntax_Embeddings.e_any in
                        try_unembed uu___8 s in
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
              | uu___ -> FStar_Pervasives_Native.None)))] in
  let strong_steps =
    let uu___ =
      FStar_Compiler_List.map (as_primitive_step true)
        (FStar_Compiler_List.op_At basic_ops
           (FStar_Compiler_List.op_At bounded_arith_ops
              (FStar_Compiler_List.op_At [reveal_hide]
                 (FStar_Compiler_List.op_At array_ops
                    (FStar_Compiler_List.op_At issue_ops doc_ops))))) in
    let uu___1 =
      FStar_Compiler_List.map
        (fun p ->
           let uu___2 = as_primitive_step_nbecbs true p in
           {
             name = (uu___2.name);
             arity = (uu___2.arity);
             univ_arity = (uu___2.univ_arity);
             auto_reflect = (uu___2.auto_reflect);
             strong_reduction_ok = (uu___2.strong_reduction_ok);
             requires_binder_substitution =
               (uu___2.requires_binder_substitution);
             renorm_after = true;
             interpretation = (uu___2.interpretation);
             interpretation_nbe = (uu___2.interpretation_nbe)
           }) seal_steps in
    FStar_Compiler_List.op_At uu___ uu___1 in
  let weak_steps = FStar_Compiler_List.map (as_primitive_step false) weak_ops in
  FStar_Compiler_List.op_At strong_steps weak_steps
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
    | uu___ -> failwith "Unexpected number of arguments" in
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
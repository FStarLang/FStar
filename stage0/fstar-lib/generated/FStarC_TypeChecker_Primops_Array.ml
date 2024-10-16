open Prims
let (as_primitive_step :
  Prims.bool ->
    (FStarC_Ident.lident * Prims.int * Prims.int *
      FStarC_TypeChecker_Primops_Base.interp_t *
      (FStarC_Syntax_Syntax.universes ->
         FStarC_TypeChecker_NBETerm.args ->
           FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option))
      -> FStarC_TypeChecker_Primops_Base.primitive_step)
  =
  fun is_strong ->
    fun uu___ ->
      match uu___ with
      | (l, arity, u_arity, f, f_nbe) ->
          FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
            (l, arity, u_arity, f,
              (fun cb -> fun univs -> fun args -> f_nbe univs args))
let (arg_as_int :
  FStarC_Syntax_Syntax.arg -> FStarC_BigInt.t FStar_Pervasives_Native.option)
  =
  fun a ->
    FStarC_TypeChecker_Primops_Base.try_unembed_simple
      FStarC_Syntax_Embeddings.e_int (FStar_Pervasives_Native.fst a)
let arg_as_list :
  'a .
    'a FStarC_Syntax_Embeddings_Base.embedding ->
      FStarC_Syntax_Syntax.arg ->
        'a Prims.list FStar_Pervasives_Native.option
  =
  fun e ->
    fun a1 ->
      FStarC_TypeChecker_Primops_Base.try_unembed_simple
        (FStarC_Syntax_Embeddings.e_list e) (FStar_Pervasives_Native.fst a1)
let mixed_binary_op :
  'a 'b 'c .
    (FStarC_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStarC_Syntax_Syntax.arg -> 'b FStar_Pervasives_Native.option) ->
        (FStarC_Compiler_Range_Type.range -> 'c -> FStarC_Syntax_Syntax.term)
          ->
          (FStarC_Compiler_Range_Type.range ->
             FStarC_Syntax_Syntax.universes ->
               'a -> 'b -> 'c FStar_Pervasives_Native.option)
            ->
            FStarC_TypeChecker_Primops_Base.psc ->
              FStarC_Syntax_Embeddings_Base.norm_cb ->
                FStarC_Syntax_Syntax.universes ->
                  FStarC_Syntax_Syntax.args ->
                    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun embed_c ->
        fun f ->
          fun psc ->
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
                           let uu___1 =
                             f psc.FStarC_TypeChecker_Primops_Base.psc_range
                               univs a2 b2 in
                           (match uu___1 with
                            | FStar_Pervasives_Native.Some c1 ->
                                let uu___2 =
                                  embed_c
                                    psc.FStarC_TypeChecker_Primops_Base.psc_range
                                    c1 in
                                FStar_Pervasives_Native.Some uu___2
                            | uu___2 -> FStar_Pervasives_Native.None)
                       | uu___1 -> FStar_Pervasives_Native.None)
                  | uu___ -> FStar_Pervasives_Native.None
let mixed_ternary_op :
  'a 'b 'c 'd .
    (FStarC_Syntax_Syntax.arg -> 'a FStar_Pervasives_Native.option) ->
      (FStarC_Syntax_Syntax.arg -> 'b FStar_Pervasives_Native.option) ->
        (FStarC_Syntax_Syntax.arg -> 'c FStar_Pervasives_Native.option) ->
          (FStarC_Compiler_Range_Type.range ->
             'd -> FStarC_Syntax_Syntax.term)
            ->
            (FStarC_Compiler_Range_Type.range ->
               FStarC_Syntax_Syntax.universes ->
                 'a -> 'b -> 'c -> 'd FStar_Pervasives_Native.option)
              ->
              FStarC_TypeChecker_Primops_Base.psc ->
                FStarC_Syntax_Embeddings_Base.norm_cb ->
                  FStarC_Syntax_Syntax.universes ->
                    FStarC_Syntax_Syntax.args ->
                      FStarC_Syntax_Syntax.term
                        FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun as_c ->
        fun embed_d ->
          fun f ->
            fun psc ->
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
                             let uu___1 =
                               f
                                 psc.FStarC_TypeChecker_Primops_Base.psc_range
                                 univs a2 b2 c2 in
                             (match uu___1 with
                              | FStar_Pervasives_Native.Some d1 ->
                                  let uu___2 =
                                    embed_d
                                      psc.FStarC_TypeChecker_Primops_Base.psc_range
                                      d1 in
                                  FStar_Pervasives_Native.Some uu___2
                              | uu___2 -> FStar_Pervasives_Native.None)
                         | uu___1 -> FStar_Pervasives_Native.None)
                    | uu___ -> FStar_Pervasives_Native.None
let (bogus_cbs : FStarC_TypeChecker_NBETerm.nbe_cbs) =
  {
    FStarC_TypeChecker_NBETerm.iapp = (fun h -> fun _args -> h);
    FStarC_TypeChecker_NBETerm.translate =
      (fun uu___ -> failwith "bogus_cbs translate")
  }
let (ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let of_list_op =
    let emb_typ t =
      let uu___ =
        let uu___1 =
          FStarC_Ident.string_of_lid
            FStarC_Parser_Const.immutable_array_t_lid in
        (uu___1, [t]) in
      FStarC_Syntax_Syntax.ET_app uu___ in
    let un_lazy universes t l r =
      let uu___ =
        let uu___1 =
          FStarC_Syntax_Util.fvar_const
            FStarC_Parser_Const.immutable_array_of_list_lid in
        FStarC_Syntax_Syntax.mk_Tm_uinst uu___1 universes in
      let uu___1 =
        let uu___2 = FStarC_Syntax_Syntax.iarg t in
        let uu___3 = let uu___4 = FStarC_Syntax_Syntax.as_arg l in [uu___4] in
        uu___2 :: uu___3 in
      FStarC_Syntax_Syntax.mk_Tm_app uu___ uu___1 r in
    (FStarC_Parser_Const.immutable_array_of_list_lid, (Prims.of_int (2)),
      Prims.int_one,
      (mixed_binary_op
         (fun uu___ ->
            match uu___ with
            | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
         (fun uu___ ->
            match uu___ with
            | (l, q) ->
                let uu___1 =
                  arg_as_list FStarC_Syntax_Embeddings.e_any (l, q) in
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
                              FStarC_Syntax_Embeddings_Base.emb_typ_of
                                FStarC_Syntax_Embeddings.e_any () in
                            emb_typ uu___6 in
                          let uu___6 =
                            FStarC_Thunk.mk
                              (fun uu___7 -> un_lazy universes elt_t l r) in
                          (uu___5, uu___6) in
                        FStarC_Syntax_Syntax.Lazy_embedding uu___4 in
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            FStarC_Syntax_Util.fvar_const
                              FStarC_Parser_Const.immutable_array_t_lid in
                          FStarC_Syntax_Syntax.mk_Tm_uinst uu___6 universes in
                        let uu___6 =
                          let uu___7 = FStarC_Syntax_Syntax.as_arg elt_t in
                          [uu___7] in
                        FStarC_Syntax_Syntax.mk_Tm_app uu___5 uu___6 r in
                      {
                        FStarC_Syntax_Syntax.blob = blob;
                        FStarC_Syntax_Syntax.lkind = uu___3;
                        FStarC_Syntax_Syntax.ltyp = uu___4;
                        FStarC_Syntax_Syntax.rng = r
                      } in
                    FStarC_Syntax_Syntax.Tm_lazy uu___2 in
                  FStarC_Syntax_Syntax.mk uu___1 r)
         (fun r ->
            fun universes ->
              fun elt_t ->
                fun uu___ ->
                  match uu___ with
                  | (l, lst) ->
                      let blob = FStar_ImmutableArray_Base.of_list lst in
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStarC_Dyn.mkdyn blob in (l, uu___3) in
                        (universes, elt_t, uu___2) in
                      FStar_Pervasives_Native.Some uu___1)),
      (FStarC_TypeChecker_NBETerm.mixed_binary_op
         (fun uu___ ->
            match uu___ with
            | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
         (fun uu___ ->
            match uu___ with
            | (l, q) ->
                let uu___1 =
                  FStarC_TypeChecker_NBETerm.arg_as_list
                    FStarC_TypeChecker_NBETerm.e_any (l, q) in
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
                            FStarC_Syntax_Embeddings_Base.emb_typ_of
                              FStarC_Syntax_Embeddings.e_any () in
                          emb_typ uu___6 in
                        (blob, uu___5) in
                      FStar_Pervasives.Inr uu___4 in
                    let uu___4 =
                      FStarC_Thunk.mk
                        (fun uu___5 ->
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Syntax_Syntax.lid_as_fv
                                   FStarC_Parser_Const.immutable_array_of_list_lid
                                   FStar_Pervasives_Native.None in
                               let uu___9 =
                                 let uu___10 =
                                   FStarC_TypeChecker_NBETerm.as_arg l in
                                 [uu___10] in
                               (uu___8, universes, uu___9) in
                             FStarC_TypeChecker_NBETerm.FV uu___7 in
                           FStarC_TypeChecker_NBETerm.mk_t uu___6) in
                    (uu___3, uu___4) in
                  FStarC_TypeChecker_NBETerm.Lazy uu___2 in
                FStarC_TypeChecker_NBETerm.mk_t uu___1)
         (fun universes ->
            fun elt_t ->
              fun uu___ ->
                match uu___ with
                | (l, lst) ->
                    let blob = FStar_ImmutableArray_Base.of_list lst in
                    let uu___1 =
                      let uu___2 =
                        let uu___3 = FStarC_Dyn.mkdyn blob in (l, uu___3) in
                      (universes, elt_t, uu___2) in
                    FStar_Pervasives_Native.Some uu___1))) in
  let arg1_as_elt_t x =
    FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst x) in
  let arg2_as_blob x =
    let uu___ =
      let uu___1 =
        FStarC_Syntax_Subst.compress (FStar_Pervasives_Native.fst x) in
      uu___1.FStarC_Syntax_Syntax.n in
    match uu___ with
    | FStarC_Syntax_Syntax.Tm_lazy
        { FStarC_Syntax_Syntax.blob = blob;
          FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_embedding
            (FStarC_Syntax_Syntax.ET_app (head, uu___1), uu___2);
          FStarC_Syntax_Syntax.ltyp = uu___3;
          FStarC_Syntax_Syntax.rng = uu___4;_}
        when
        let uu___5 =
          FStarC_Ident.string_of_lid
            FStarC_Parser_Const.immutable_array_t_lid in
        head = uu___5 -> FStar_Pervasives_Native.Some blob
    | uu___1 -> FStar_Pervasives_Native.None in
  let arg2_as_blob_nbe x =
    match (FStar_Pervasives_Native.fst x).FStarC_TypeChecker_NBETerm.nbe_t
    with
    | FStarC_TypeChecker_NBETerm.Lazy
        (FStar_Pervasives.Inr
         (blob, FStarC_Syntax_Syntax.ET_app (head, uu___)), uu___1)
        when
        let uu___2 =
          FStarC_Ident.string_of_lid
            FStarC_Parser_Const.immutable_array_t_lid in
        head = uu___2 -> FStar_Pervasives_Native.Some blob
    | uu___ -> FStar_Pervasives_Native.None in
  let length_op =
    let embed_int r i =
      FStarC_TypeChecker_Primops_Base.embed_simple
        FStarC_Syntax_Embeddings.e_int r i in
    let run_op blob =
      let uu___ =
        let uu___1 = FStarC_Dyn.undyn blob in
        FStarC_Compiler_Util.array_length uu___1 in
      FStar_Pervasives_Native.Some uu___ in
    (FStarC_Parser_Const.immutable_array_length_lid, (Prims.of_int (2)),
      Prims.int_one,
      (mixed_binary_op arg1_as_elt_t arg2_as_blob embed_int
         (fun _r -> fun _universes -> fun uu___ -> fun blob -> run_op blob)),
      (FStarC_TypeChecker_NBETerm.mixed_binary_op
         (fun uu___ ->
            match uu___ with
            | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
         arg2_as_blob_nbe
         (fun i ->
            FStarC_TypeChecker_NBETerm.embed FStarC_TypeChecker_NBETerm.e_int
              bogus_cbs i)
         (fun _universes -> fun uu___ -> fun blob -> run_op blob))) in
  let index_op =
    (FStarC_Parser_Const.immutable_array_index_lid, (Prims.of_int (3)),
      Prims.int_one,
      (mixed_ternary_op arg1_as_elt_t arg2_as_blob arg_as_int
         (fun r -> fun tm -> tm)
         (fun r ->
            fun _universes ->
              fun _t ->
                fun blob ->
                  fun i ->
                    let uu___ =
                      let uu___1 = FStarC_Dyn.undyn blob in
                      FStarC_Compiler_Util.array_index uu___1 i in
                    FStar_Pervasives_Native.Some uu___)),
      (FStarC_TypeChecker_NBETerm.mixed_ternary_op
         (fun uu___ ->
            match uu___ with
            | (elt_t, uu___1) -> FStar_Pervasives_Native.Some elt_t)
         arg2_as_blob_nbe FStarC_TypeChecker_NBETerm.arg_as_int
         (fun tm -> tm)
         (fun _universes ->
            fun _t ->
              fun blob ->
                fun i ->
                  let uu___ =
                    let uu___1 = FStarC_Dyn.undyn blob in
                    FStarC_Compiler_Util.array_index uu___1 i in
                  FStar_Pervasives_Native.Some uu___))) in
  FStarC_Compiler_List.map (as_primitive_step true)
    [of_list_op; length_op; index_op]
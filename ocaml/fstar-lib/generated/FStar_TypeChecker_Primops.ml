open Prims
let (arg_as_int :
  FStar_Syntax_Syntax.arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a ->
    FStar_TypeChecker_Primops_Base.try_unembed_simple
      FStar_Syntax_Embeddings.e_int (FStar_Pervasives_Native.fst a)
let arg_as_list :
  'a .
    'a FStar_Syntax_Embeddings_Base.embedding ->
      FStar_Syntax_Syntax.arg -> 'a Prims.list FStar_Pervasives_Native.option
  =
  fun e ->
    fun a1 ->
      FStar_TypeChecker_Primops_Base.try_unembed_simple
        (FStar_Syntax_Embeddings.e_list e) (FStar_Pervasives_Native.fst a1)
let (as_primitive_step :
  Prims.bool ->
    (FStar_Ident.lident * Prims.int * Prims.int *
      FStar_TypeChecker_Primops_Base.interp_t *
      (FStar_Syntax_Syntax.universes ->
         FStar_TypeChecker_NBETerm.args ->
           FStar_TypeChecker_NBETerm.t FStar_Pervasives_Native.option))
      -> FStar_TypeChecker_Primops_Base.primitive_step)
  =
  fun is_strong ->
    fun uu___ ->
      match uu___ with
      | (l, arity, u_arity, f, f_nbe) ->
          FStar_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
            (l, arity, u_arity, f,
              (fun cb -> fun univs -> fun args -> f_nbe univs args))
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
            FStar_TypeChecker_Primops_Base.psc ->
              FStar_Syntax_Embeddings_Base.norm_cb ->
                FStar_Syntax_Syntax.universes ->
                  FStar_Syntax_Syntax.args ->
                    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
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
                             f psc.FStar_TypeChecker_Primops_Base.psc_range
                               univs a2 b2 in
                           (match uu___1 with
                            | FStar_Pervasives_Native.Some c1 ->
                                let uu___2 =
                                  embed_c
                                    psc.FStar_TypeChecker_Primops_Base.psc_range
                                    c1 in
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
              FStar_TypeChecker_Primops_Base.psc ->
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
                               f psc.FStar_TypeChecker_Primops_Base.psc_range
                                 univs a2 b2 c2 in
                             (match uu___1 with
                              | FStar_Pervasives_Native.Some d1 ->
                                  let uu___2 =
                                    embed_d
                                      psc.FStar_TypeChecker_Primops_Base.psc_range
                                      d1 in
                                  FStar_Pervasives_Native.Some uu___2
                              | uu___2 -> FStar_Pervasives_Native.None)
                         | uu___1 -> FStar_Pervasives_Native.None)
                    | uu___ -> FStar_Pervasives_Native.None
let (and_op :
  FStar_TypeChecker_Primops_Base.psc ->
    FStar_Syntax_Embeddings_Base.norm_cb ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ =
                FStar_TypeChecker_Primops_Base.try_unembed_simple
                  FStar_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (false) ->
                   let uu___1 =
                     FStar_TypeChecker_Primops_Base.embed_simple
                       FStar_Syntax_Embeddings.e_bool
                       psc.FStar_TypeChecker_Primops_Base.psc_range false in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives_Native.Some (true) ->
                   FStar_Pervasives_Native.Some a2
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ ->
              FStar_Compiler_Effect.failwith "Unexpected number of arguments"
let (or_op :
  FStar_TypeChecker_Primops_Base.psc ->
    FStar_Syntax_Embeddings_Base.norm_cb ->
      FStar_Syntax_Syntax.universes ->
        FStar_Syntax_Syntax.args ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun psc ->
    fun _norm_cb ->
      fun _us ->
        fun args ->
          match args with
          | (a1, FStar_Pervasives_Native.None)::(a2,
                                                 FStar_Pervasives_Native.None)::[]
              ->
              let uu___ =
                FStar_TypeChecker_Primops_Base.try_unembed_simple
                  FStar_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (true) ->
                   let uu___1 =
                     FStar_TypeChecker_Primops_Base.embed_simple
                       FStar_Syntax_Embeddings.e_bool
                       psc.FStar_TypeChecker_Primops_Base.psc_range true in
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
let (simple_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let uu___ =
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
      FStar_Parser_Const.string_of_int_lid FStar_Syntax_Embeddings.e_int
      FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_string
      FStar_TypeChecker_NBETerm.e_string
      (fun z ->
         let uu___1 = FStar_BigInt.to_int_fs z in Prims.string_of_int uu___1) in
  let uu___1 =
    let uu___2 =
      FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
        FStar_Parser_Const.int_of_string_lid FStar_Syntax_Embeddings.e_string
        FStar_TypeChecker_NBETerm.e_string
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
        FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
          FStar_Parser_Const.string_of_bool_lid
          FStar_Syntax_Embeddings.e_bool FStar_TypeChecker_NBETerm.e_bool
          FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
          Prims.string_of_bool in
      let uu___5 =
        let uu___6 =
          FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
            FStar_Parser_Const.bool_of_string_lid
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
            FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero
              FStar_Parser_Const.op_Minus FStar_Syntax_Embeddings.e_int
              FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
              FStar_TypeChecker_NBETerm.e_int FStar_BigInt.minus_big_int in
          let uu___9 =
            let uu___10 =
              FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                FStar_Parser_Const.op_Addition FStar_Syntax_Embeddings.e_int
                FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
                FStar_TypeChecker_NBETerm.e_int FStar_Syntax_Embeddings.e_int
                FStar_TypeChecker_NBETerm.e_int FStar_BigInt.add_big_int in
            let uu___11 =
              let uu___12 =
                FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                  FStar_Parser_Const.op_Subtraction
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int
                  FStar_Syntax_Embeddings.e_int
                  FStar_TypeChecker_NBETerm.e_int FStar_BigInt.sub_big_int in
              let uu___13 =
                let uu___14 =
                  FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                    FStar_Parser_Const.op_Multiply
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int
                    FStar_Syntax_Embeddings.e_int
                    FStar_TypeChecker_NBETerm.e_int FStar_BigInt.mult_big_int in
                let uu___15 =
                  let uu___16 =
                    FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                      FStar_Parser_Const.op_LT FStar_Syntax_Embeddings.e_int
                      FStar_TypeChecker_NBETerm.e_int
                      FStar_Syntax_Embeddings.e_int
                      FStar_TypeChecker_NBETerm.e_int
                      FStar_Syntax_Embeddings.e_bool
                      FStar_TypeChecker_NBETerm.e_bool
                      FStar_BigInt.lt_big_int in
                  let uu___17 =
                    let uu___18 =
                      FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        FStar_Parser_Const.op_LTE
                        FStar_Syntax_Embeddings.e_int
                        FStar_TypeChecker_NBETerm.e_int
                        FStar_Syntax_Embeddings.e_int
                        FStar_TypeChecker_NBETerm.e_int
                        FStar_Syntax_Embeddings.e_bool
                        FStar_TypeChecker_NBETerm.e_bool
                        FStar_BigInt.le_big_int in
                    let uu___19 =
                      let uu___20 =
                        FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          FStar_Parser_Const.op_GT
                          FStar_Syntax_Embeddings.e_int
                          FStar_TypeChecker_NBETerm.e_int
                          FStar_Syntax_Embeddings.e_int
                          FStar_TypeChecker_NBETerm.e_int
                          FStar_Syntax_Embeddings.e_bool
                          FStar_TypeChecker_NBETerm.e_bool
                          FStar_BigInt.gt_big_int in
                      let uu___21 =
                        let uu___22 =
                          FStar_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            FStar_Parser_Const.op_GTE
                            FStar_Syntax_Embeddings.e_int
                            FStar_TypeChecker_NBETerm.e_int
                            FStar_Syntax_Embeddings.e_int
                            FStar_TypeChecker_NBETerm.e_int
                            FStar_Syntax_Embeddings.e_bool
                            FStar_TypeChecker_NBETerm.e_bool
                            FStar_BigInt.ge_big_int in
                        let uu___23 =
                          let uu___24 =
                            FStar_TypeChecker_Primops_Base.mk2'
                              Prims.int_zero FStar_Parser_Const.op_Division
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              FStar_Syntax_Embeddings.e_int
                              FStar_TypeChecker_NBETerm.e_int
                              (division_modulus_op FStar_BigInt.div_big_int)
                              (division_modulus_op FStar_BigInt.div_big_int) in
                          let uu___25 =
                            let uu___26 =
                              FStar_TypeChecker_Primops_Base.mk2'
                                Prims.int_zero FStar_Parser_Const.op_Modulus
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                FStar_Syntax_Embeddings.e_int
                                FStar_TypeChecker_NBETerm.e_int
                                (division_modulus_op FStar_BigInt.mod_big_int)
                                (division_modulus_op FStar_BigInt.div_big_int) in
                            let uu___27 =
                              let uu___28 =
                                FStar_TypeChecker_Primops_Base.mk1
                                  Prims.int_zero
                                  FStar_Parser_Const.op_Negation
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_TypeChecker_NBETerm.e_bool
                                  FStar_Syntax_Embeddings.e_bool
                                  FStar_TypeChecker_NBETerm.e_bool
                                  Prims.op_Negation in
                              let uu___29 =
                                let uu___30 =
                                  FStar_TypeChecker_Primops_Base.mk2
                                    Prims.int_zero
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
                                    FStar_TypeChecker_Primops_Base.mk2
                                      Prims.int_zero
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
                                      FStar_TypeChecker_Primops_Base.mk2
                                        Prims.int_zero
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
                                        FStar_TypeChecker_Primops_Base.mk2
                                          Prims.int_zero
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
                                          FStar_TypeChecker_Primops_Base.mk1
                                            Prims.int_zero
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
                                            FStar_TypeChecker_Primops_Base.mk2
                                              Prims.int_zero
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
                                              FStar_TypeChecker_Primops_Base.mk1
                                                Prims.int_zero
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
                                                FStar_TypeChecker_Primops_Base.mk1
                                                  Prims.int_zero
                                                  FStar_Parser_Const.string_lowercase_lid
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_TypeChecker_NBETerm.e_string
                                                  FStar_Syntax_Embeddings.e_string
                                                  FStar_TypeChecker_NBETerm.e_string
                                                  FStar_Compiler_String.lowercase in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStar_TypeChecker_Primops_Base.mk1
                                                    Prims.int_zero
                                                    FStar_Parser_Const.string_uppercase_lid
                                                    FStar_Syntax_Embeddings.e_string
                                                    FStar_TypeChecker_NBETerm.e_string
                                                    FStar_Syntax_Embeddings.e_string
                                                    FStar_TypeChecker_NBETerm.e_string
                                                    FStar_Compiler_String.uppercase in
                                                let uu___47 =
                                                  let uu___48 =
                                                    FStar_TypeChecker_Primops_Base.mk2
                                                      Prims.int_zero
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
                                                      FStar_TypeChecker_Primops_Base.mk2
                                                        Prims.int_zero
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
                                                        FStar_TypeChecker_Primops_Base.mk3
                                                          Prims.int_zero
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
                                                          FStar_TypeChecker_Primops_Base.mk5
                                                            Prims.int_zero
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
let (issue_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let mk_lid l = FStar_Parser_Const.p2l ["FStar"; "Issue"; l] in
  let uu___ =
    let uu___1 = mk_lid "message_of_issue" in
    FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___1
      FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
      (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_document)
      (FStar_TypeChecker_NBETerm.e_list FStar_TypeChecker_NBETerm.e_document)
      FStar_Errors.__proj__Mkissue__item__issue_msg in
  let uu___1 =
    let uu___2 =
      let uu___3 = mk_lid "level_of_issue" in
      FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___3
        FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
        FStar_Syntax_Embeddings.e_string FStar_TypeChecker_NBETerm.e_string
        (fun i ->
           FStar_Errors.string_of_issue_level i.FStar_Errors.issue_level) in
    let uu___3 =
      let uu___4 =
        let uu___5 = mk_lid "number_of_issue" in
        FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___5
          FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
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
          FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___7
            FStar_Syntax_Embeddings.e_issue FStar_TypeChecker_NBETerm.e_issue
            (FStar_Syntax_Embeddings.e_option FStar_Syntax_Embeddings.e_range)
            (FStar_TypeChecker_NBETerm.e_option
               FStar_TypeChecker_NBETerm.e_range)
            FStar_Errors.__proj__Mkissue__item__issue_range in
        let uu___7 =
          let uu___8 =
            let uu___9 = mk_lid "context_of_issue" in
            FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___9
              FStar_Syntax_Embeddings.e_issue
              FStar_TypeChecker_NBETerm.e_issue
              FStar_Syntax_Embeddings.e_string_list
              FStar_TypeChecker_NBETerm.e_string_list
              FStar_Errors.__proj__Mkissue__item__issue_ctx in
          let uu___9 =
            let uu___10 =
              let uu___11 = mk_lid "render_issue" in
              FStar_TypeChecker_Primops_Base.mk1 Prims.int_zero uu___11
                FStar_Syntax_Embeddings.e_issue
                FStar_TypeChecker_NBETerm.e_issue
                FStar_Syntax_Embeddings.e_string
                FStar_TypeChecker_NBETerm.e_string FStar_Errors.format_issue in
            let uu___11 =
              let uu___12 =
                let uu___13 = mk_lid "mk_issue_doc" in
                FStar_TypeChecker_Primops_Base.mk5 Prims.int_zero uu___13
                  FStar_Syntax_Embeddings.e_string
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
let (seal_steps : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStar_Compiler_List.map
    (fun p ->
       let uu___ =
         FStar_TypeChecker_Primops_Base.as_primitive_step_nbecbs true p in
       {
         FStar_TypeChecker_Primops_Base.name =
           (uu___.FStar_TypeChecker_Primops_Base.name);
         FStar_TypeChecker_Primops_Base.arity =
           (uu___.FStar_TypeChecker_Primops_Base.arity);
         FStar_TypeChecker_Primops_Base.univ_arity =
           (uu___.FStar_TypeChecker_Primops_Base.univ_arity);
         FStar_TypeChecker_Primops_Base.auto_reflect =
           (uu___.FStar_TypeChecker_Primops_Base.auto_reflect);
         FStar_TypeChecker_Primops_Base.strong_reduction_ok =
           (uu___.FStar_TypeChecker_Primops_Base.strong_reduction_ok);
         FStar_TypeChecker_Primops_Base.requires_binder_substitution =
           (uu___.FStar_TypeChecker_Primops_Base.requires_binder_substitution);
         FStar_TypeChecker_Primops_Base.renorm_after = true;
         FStar_TypeChecker_Primops_Base.interpretation =
           (uu___.FStar_TypeChecker_Primops_Base.interpretation);
         FStar_TypeChecker_Primops_Base.interpretation_nbe =
           (uu___.FStar_TypeChecker_Primops_Base.interpretation_nbe)
       })
    [(FStar_Parser_Const.map_seal_lid, (Prims.of_int (4)),
       (Prims.of_int (2)),
       ((fun psc ->
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
                            FStar_TypeChecker_Primops_Base.embed_simple
                              (FStar_Syntax_Embeddings.e_sealed emb)
                              psc.FStar_TypeChecker_Primops_Base.psc_range r in
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
      ((fun psc ->
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
                           FStar_TypeChecker_Primops_Base.embed_simple
                             FStar_Syntax_Embeddings.e_any
                             psc.FStar_TypeChecker_Primops_Base.psc_range r in
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
let (array_ops : FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  let of_list_op =
    let emb_typ t =
      let uu___ =
        let uu___1 =
          FStar_Ident.string_of_lid FStar_Parser_Const.immutable_array_t_lid in
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
                let uu___1 = arg_as_list FStar_Syntax_Embeddings.e_any (l, q) in
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
          FStar_Ident.string_of_lid FStar_Parser_Const.immutable_array_t_lid in
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
          FStar_Ident.string_of_lid FStar_Parser_Const.immutable_array_t_lid in
        head = uu___2 -> FStar_Pervasives_Native.Some blob
    | uu___ -> FStar_Pervasives_Native.None in
  let length_op =
    let embed_int r i =
      FStar_TypeChecker_Primops_Base.embed_simple
        FStar_Syntax_Embeddings.e_int r i in
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
         arg2_as_blob_nbe FStar_TypeChecker_NBETerm.arg_as_int (fun tm -> tm)
         (fun _universes ->
            fun _t ->
              fun blob ->
                fun i ->
                  let uu___ =
                    let uu___1 = FStar_Compiler_Dyn.undyn blob in
                    FStar_Compiler_Util.array_index uu___1 i in
                  FStar_Pervasives_Native.Some uu___))) in
  FStar_Compiler_List.map (as_primitive_step true)
    [of_list_op; length_op; index_op]
let (short_circuit_ops :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStar_Compiler_List.map (as_primitive_step true)
    [(FStar_Parser_Const.op_And, (Prims.of_int (2)), Prims.int_zero, and_op,
       ((fun _us -> FStar_TypeChecker_NBETerm.and_op)));
    (FStar_Parser_Const.op_Or, (Prims.of_int (2)), Prims.int_zero, or_op,
      ((fun _us -> FStar_TypeChecker_NBETerm.or_op)))]
let (built_in_primitive_steps_list :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStar_Compiler_List.op_At simple_ops
    (FStar_Compiler_List.op_At short_circuit_ops
       (FStar_Compiler_List.op_At issue_ops
          (FStar_Compiler_List.op_At array_ops
             (FStar_Compiler_List.op_At seal_steps
                (FStar_Compiler_List.op_At
                   FStar_TypeChecker_Primops_Erased.ops
                   (FStar_Compiler_List.op_At
                      FStar_TypeChecker_Primops_Docs.ops
                      (FStar_Compiler_List.op_At
                         FStar_TypeChecker_Primops_MachineInts.ops
                         FStar_TypeChecker_Primops_Eq.dec_eq_ops)))))))
let (equality_ops_list :
  FStar_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStar_TypeChecker_Primops_Eq.prop_eq_ops
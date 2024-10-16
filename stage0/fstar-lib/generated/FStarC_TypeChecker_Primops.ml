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
let (and_op :
  FStarC_TypeChecker_Primops_Base.psc ->
    FStarC_Syntax_Embeddings_Base.norm_cb ->
      FStarC_Syntax_Syntax.universes ->
        FStarC_Syntax_Syntax.args ->
          FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
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
                FStarC_TypeChecker_Primops_Base.try_unembed_simple
                  FStarC_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (false) ->
                   let uu___1 =
                     FStarC_TypeChecker_Primops_Base.embed_simple
                       FStarC_Syntax_Embeddings.e_bool
                       psc.FStarC_TypeChecker_Primops_Base.psc_range false in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives_Native.Some (true) ->
                   FStar_Pervasives_Native.Some a2
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ -> failwith "Unexpected number of arguments"
let (or_op :
  FStarC_TypeChecker_Primops_Base.psc ->
    FStarC_Syntax_Embeddings_Base.norm_cb ->
      FStarC_Syntax_Syntax.universes ->
        FStarC_Syntax_Syntax.args ->
          FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
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
                FStarC_TypeChecker_Primops_Base.try_unembed_simple
                  FStarC_Syntax_Embeddings.e_bool a1 in
              (match uu___ with
               | FStar_Pervasives_Native.Some (true) ->
                   let uu___1 =
                     FStarC_TypeChecker_Primops_Base.embed_simple
                       FStarC_Syntax_Embeddings.e_bool
                       psc.FStarC_TypeChecker_Primops_Base.psc_range true in
                   FStar_Pervasives_Native.Some uu___1
               | FStar_Pervasives_Native.Some (false) ->
                   FStar_Pervasives_Native.Some a2
               | uu___1 -> FStar_Pervasives_Native.None)
          | uu___ -> failwith "Unexpected number of arguments"
let (division_modulus_op :
  (FStarC_BigInt.t -> FStarC_BigInt.t -> FStarC_BigInt.t) ->
    FStarC_BigInt.t ->
      FStarC_BigInt.t -> FStarC_BigInt.t FStar_Pervasives_Native.option)
  =
  fun f ->
    fun x ->
      fun y ->
        let uu___ =
          let uu___1 = FStarC_BigInt.to_int_fs y in uu___1 <> Prims.int_zero in
        if uu___
        then let uu___1 = f x y in FStar_Pervasives_Native.Some uu___1
        else FStar_Pervasives_Native.None
let (simple_ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
      FStarC_Parser_Const.string_of_int_lid FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_string
      FStarC_TypeChecker_NBETerm.e_string
      (fun z ->
         let uu___1 = FStarC_BigInt.to_int_fs z in Prims.string_of_int uu___1) in
  let uu___1 =
    let uu___2 =
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
        FStarC_Parser_Const.int_of_string_lid
        FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
        (FStarC_Syntax_Embeddings.e_option FStarC_Syntax_Embeddings.e_int)
        (FStarC_TypeChecker_NBETerm.e_option FStarC_TypeChecker_NBETerm.e_int)
        (fun uu___3 ->
           (fun s ->
              let uu___3 = FStarC_Compiler_Util.safe_int_of_string s in
              Obj.magic
                (FStarC_Class_Monad.fmap FStarC_Class_Monad.monad_option ()
                   ()
                   (fun uu___4 -> (Obj.magic FStarC_BigInt.of_int_fs) uu___4)
                   (Obj.magic uu___3))) uu___3) in
    let uu___3 =
      let uu___4 =
        FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
          FStarC_Parser_Const.string_of_bool_lid
          FStarC_Syntax_Embeddings.e_bool FStarC_TypeChecker_NBETerm.e_bool
          FStarC_Syntax_Embeddings.e_string
          FStarC_TypeChecker_NBETerm.e_string Prims.string_of_bool in
      let uu___5 =
        let uu___6 =
          FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
            FStarC_Parser_Const.bool_of_string_lid
            FStarC_Syntax_Embeddings.e_string
            FStarC_TypeChecker_NBETerm.e_string
            (FStarC_Syntax_Embeddings.e_option
               FStarC_Syntax_Embeddings.e_bool)
            (FStarC_TypeChecker_NBETerm.e_option
               FStarC_TypeChecker_NBETerm.e_bool)
            (fun uu___7 ->
               match uu___7 with
               | "true" -> FStar_Pervasives_Native.Some true
               | "false" -> FStar_Pervasives_Native.Some false
               | uu___8 -> FStar_Pervasives_Native.None) in
        let uu___7 =
          let uu___8 =
            FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
              FStarC_Parser_Const.op_Minus FStarC_Syntax_Embeddings.e_int
              FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
              FStarC_TypeChecker_NBETerm.e_int FStarC_BigInt.minus_big_int in
          let uu___9 =
            let uu___10 =
              FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                FStarC_Parser_Const.op_Addition
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int FStarC_BigInt.add_big_int in
            let uu___11 =
              let uu___12 =
                FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                  FStarC_Parser_Const.op_Subtraction
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int FStarC_BigInt.sub_big_int in
              let uu___13 =
                let uu___14 =
                  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                    FStarC_Parser_Const.op_Multiply
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int
                    FStarC_BigInt.mult_big_int in
                let uu___15 =
                  let uu___16 =
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                      FStarC_Parser_Const.op_LT
                      FStarC_Syntax_Embeddings.e_int
                      FStarC_TypeChecker_NBETerm.e_int
                      FStarC_Syntax_Embeddings.e_int
                      FStarC_TypeChecker_NBETerm.e_int
                      FStarC_Syntax_Embeddings.e_bool
                      FStarC_TypeChecker_NBETerm.e_bool
                      FStarC_BigInt.lt_big_int in
                  let uu___17 =
                    let uu___18 =
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        FStarC_Parser_Const.op_LTE
                        FStarC_Syntax_Embeddings.e_int
                        FStarC_TypeChecker_NBETerm.e_int
                        FStarC_Syntax_Embeddings.e_int
                        FStarC_TypeChecker_NBETerm.e_int
                        FStarC_Syntax_Embeddings.e_bool
                        FStarC_TypeChecker_NBETerm.e_bool
                        FStarC_BigInt.le_big_int in
                    let uu___19 =
                      let uu___20 =
                        FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          FStarC_Parser_Const.op_GT
                          FStarC_Syntax_Embeddings.e_int
                          FStarC_TypeChecker_NBETerm.e_int
                          FStarC_Syntax_Embeddings.e_int
                          FStarC_TypeChecker_NBETerm.e_int
                          FStarC_Syntax_Embeddings.e_bool
                          FStarC_TypeChecker_NBETerm.e_bool
                          FStarC_BigInt.gt_big_int in
                      let uu___21 =
                        let uu___22 =
                          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            FStarC_Parser_Const.op_GTE
                            FStarC_Syntax_Embeddings.e_int
                            FStarC_TypeChecker_NBETerm.e_int
                            FStarC_Syntax_Embeddings.e_int
                            FStarC_TypeChecker_NBETerm.e_int
                            FStarC_Syntax_Embeddings.e_bool
                            FStarC_TypeChecker_NBETerm.e_bool
                            FStarC_BigInt.ge_big_int in
                        let uu___23 =
                          let uu___24 =
                            FStarC_TypeChecker_Primops_Base.mk2'
                              Prims.int_zero FStarC_Parser_Const.op_Division
                              FStarC_Syntax_Embeddings.e_int
                              FStarC_TypeChecker_NBETerm.e_int
                              FStarC_Syntax_Embeddings.e_int
                              FStarC_TypeChecker_NBETerm.e_int
                              FStarC_Syntax_Embeddings.e_int
                              FStarC_TypeChecker_NBETerm.e_int
                              (division_modulus_op FStarC_BigInt.div_big_int)
                              (division_modulus_op FStarC_BigInt.div_big_int) in
                          let uu___25 =
                            let uu___26 =
                              FStarC_TypeChecker_Primops_Base.mk2'
                                Prims.int_zero FStarC_Parser_Const.op_Modulus
                                FStarC_Syntax_Embeddings.e_int
                                FStarC_TypeChecker_NBETerm.e_int
                                FStarC_Syntax_Embeddings.e_int
                                FStarC_TypeChecker_NBETerm.e_int
                                FStarC_Syntax_Embeddings.e_int
                                FStarC_TypeChecker_NBETerm.e_int
                                (division_modulus_op
                                   FStarC_BigInt.mod_big_int)
                                (division_modulus_op
                                   FStarC_BigInt.mod_big_int) in
                            let uu___27 =
                              let uu___28 =
                                FStarC_TypeChecker_Primops_Base.mk1
                                  Prims.int_zero
                                  FStarC_Parser_Const.op_Negation
                                  FStarC_Syntax_Embeddings.e_bool
                                  FStarC_TypeChecker_NBETerm.e_bool
                                  FStarC_Syntax_Embeddings.e_bool
                                  FStarC_TypeChecker_NBETerm.e_bool
                                  Prims.op_Negation in
                              let uu___29 =
                                let uu___30 =
                                  FStarC_TypeChecker_Primops_Base.mk2
                                    Prims.int_zero
                                    FStarC_Parser_Const.string_concat_lid
                                    FStarC_Syntax_Embeddings.e_string
                                    FStarC_TypeChecker_NBETerm.e_string
                                    FStarC_Syntax_Embeddings.e_string_list
                                    FStarC_TypeChecker_NBETerm.e_string_list
                                    FStarC_Syntax_Embeddings.e_string
                                    FStarC_TypeChecker_NBETerm.e_string
                                    FStarC_Compiler_String.concat in
                                let uu___31 =
                                  let uu___32 =
                                    FStarC_TypeChecker_Primops_Base.mk2
                                      Prims.int_zero
                                      FStarC_Parser_Const.string_split_lid
                                      (FStarC_Syntax_Embeddings.e_list
                                         FStarC_Syntax_Embeddings.e_char)
                                      (FStarC_TypeChecker_NBETerm.e_list
                                         FStarC_TypeChecker_NBETerm.e_char)
                                      FStarC_Syntax_Embeddings.e_string
                                      FStarC_TypeChecker_NBETerm.e_string
                                      FStarC_Syntax_Embeddings.e_string_list
                                      FStarC_TypeChecker_NBETerm.e_string_list
                                      FStarC_Compiler_String.split in
                                  let uu___33 =
                                    let uu___34 =
                                      FStarC_TypeChecker_Primops_Base.mk2
                                        Prims.int_zero
                                        FStarC_Parser_Const.prims_strcat_lid
                                        FStarC_Syntax_Embeddings.e_string
                                        FStarC_TypeChecker_NBETerm.e_string
                                        FStarC_Syntax_Embeddings.e_string
                                        FStarC_TypeChecker_NBETerm.e_string
                                        FStarC_Syntax_Embeddings.e_string
                                        FStarC_TypeChecker_NBETerm.e_string
                                        (fun s1 ->
                                           fun s2 -> Prims.strcat s1 s2) in
                                    let uu___35 =
                                      let uu___36 =
                                        FStarC_TypeChecker_Primops_Base.mk2
                                          Prims.int_zero
                                          FStarC_Parser_Const.string_compare_lid
                                          FStarC_Syntax_Embeddings.e_string
                                          FStarC_TypeChecker_NBETerm.e_string
                                          FStarC_Syntax_Embeddings.e_string
                                          FStarC_TypeChecker_NBETerm.e_string
                                          FStarC_Syntax_Embeddings.e_int
                                          FStarC_TypeChecker_NBETerm.e_int
                                          (fun s1 ->
                                             fun s2 ->
                                               FStarC_BigInt.of_int_fs
                                                 (FStarC_Compiler_String.compare
                                                    s1 s2)) in
                                      let uu___37 =
                                        let uu___38 =
                                          FStarC_TypeChecker_Primops_Base.mk1
                                            Prims.int_zero
                                            FStarC_Parser_Const.string_string_of_list_lid
                                            (FStarC_Syntax_Embeddings.e_list
                                               FStarC_Syntax_Embeddings.e_char)
                                            (FStarC_TypeChecker_NBETerm.e_list
                                               FStarC_TypeChecker_NBETerm.e_char)
                                            FStarC_Syntax_Embeddings.e_string
                                            FStarC_TypeChecker_NBETerm.e_string
                                            FStar_String.string_of_list in
                                        let uu___39 =
                                          let uu___40 =
                                            FStarC_TypeChecker_Primops_Base.mk2
                                              Prims.int_zero
                                              FStarC_Parser_Const.string_make_lid
                                              FStarC_Syntax_Embeddings.e_int
                                              FStarC_TypeChecker_NBETerm.e_int
                                              FStarC_Syntax_Embeddings.e_char
                                              FStarC_TypeChecker_NBETerm.e_char
                                              FStarC_Syntax_Embeddings.e_string
                                              FStarC_TypeChecker_NBETerm.e_string
                                              (fun x ->
                                                 fun y ->
                                                   let uu___41 =
                                                     FStarC_BigInt.to_int_fs
                                                       x in
                                                   FStarC_Compiler_String.make
                                                     uu___41 y) in
                                          let uu___41 =
                                            let uu___42 =
                                              FStarC_TypeChecker_Primops_Base.mk1
                                                Prims.int_zero
                                                FStarC_Parser_Const.string_list_of_string_lid
                                                FStarC_Syntax_Embeddings.e_string
                                                FStarC_TypeChecker_NBETerm.e_string
                                                (FStarC_Syntax_Embeddings.e_list
                                                   FStarC_Syntax_Embeddings.e_char)
                                                (FStarC_TypeChecker_NBETerm.e_list
                                                   FStarC_TypeChecker_NBETerm.e_char)
                                                FStar_String.list_of_string in
                                            let uu___43 =
                                              let uu___44 =
                                                FStarC_TypeChecker_Primops_Base.mk1
                                                  Prims.int_zero
                                                  FStarC_Parser_Const.string_lowercase_lid
                                                  FStarC_Syntax_Embeddings.e_string
                                                  FStarC_TypeChecker_NBETerm.e_string
                                                  FStarC_Syntax_Embeddings.e_string
                                                  FStarC_TypeChecker_NBETerm.e_string
                                                  FStarC_Compiler_String.lowercase in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStarC_TypeChecker_Primops_Base.mk1
                                                    Prims.int_zero
                                                    FStarC_Parser_Const.string_uppercase_lid
                                                    FStarC_Syntax_Embeddings.e_string
                                                    FStarC_TypeChecker_NBETerm.e_string
                                                    FStarC_Syntax_Embeddings.e_string
                                                    FStarC_TypeChecker_NBETerm.e_string
                                                    FStarC_Compiler_String.uppercase in
                                                let uu___47 =
                                                  let uu___48 =
                                                    FStarC_TypeChecker_Primops_Base.mk2
                                                      Prims.int_zero
                                                      FStarC_Parser_Const.string_index_lid
                                                      FStarC_Syntax_Embeddings.e_string
                                                      FStarC_TypeChecker_NBETerm.e_string
                                                      FStarC_Syntax_Embeddings.e_int
                                                      FStarC_TypeChecker_NBETerm.e_int
                                                      FStarC_Syntax_Embeddings.e_char
                                                      FStarC_TypeChecker_NBETerm.e_char
                                                      FStarC_Compiler_String.index in
                                                  let uu___49 =
                                                    let uu___50 =
                                                      FStarC_TypeChecker_Primops_Base.mk2
                                                        Prims.int_zero
                                                        FStarC_Parser_Const.string_index_of_lid
                                                        FStarC_Syntax_Embeddings.e_string
                                                        FStarC_TypeChecker_NBETerm.e_string
                                                        FStarC_Syntax_Embeddings.e_char
                                                        FStarC_TypeChecker_NBETerm.e_char
                                                        FStarC_Syntax_Embeddings.e_int
                                                        FStarC_TypeChecker_NBETerm.e_int
                                                        FStarC_Compiler_String.index_of in
                                                    let uu___51 =
                                                      let uu___52 =
                                                        FStarC_TypeChecker_Primops_Base.mk3
                                                          Prims.int_zero
                                                          FStarC_Parser_Const.string_sub_lid
                                                          FStarC_Syntax_Embeddings.e_string
                                                          FStarC_TypeChecker_NBETerm.e_string
                                                          FStarC_Syntax_Embeddings.e_int
                                                          FStarC_TypeChecker_NBETerm.e_int
                                                          FStarC_Syntax_Embeddings.e_int
                                                          FStarC_TypeChecker_NBETerm.e_int
                                                          FStarC_Syntax_Embeddings.e_string
                                                          FStarC_TypeChecker_NBETerm.e_string
                                                          (fun s ->
                                                             fun o ->
                                                               fun l ->
                                                                 let uu___53
                                                                   =
                                                                   FStarC_BigInt.to_int_fs
                                                                    o in
                                                                 let uu___54
                                                                   =
                                                                   FStarC_BigInt.to_int_fs
                                                                    l in
                                                                 FStarC_Compiler_String.substring
                                                                   s uu___53
                                                                   uu___54) in
                                                      [uu___52] in
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
let (short_circuit_ops :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStarC_Compiler_List.map (as_primitive_step true)
    [(FStarC_Parser_Const.op_And, (Prims.of_int (2)), Prims.int_zero, and_op,
       ((fun _us -> FStarC_TypeChecker_NBETerm.and_op)));
    (FStarC_Parser_Const.op_Or, (Prims.of_int (2)), Prims.int_zero, or_op,
      ((fun _us -> FStarC_TypeChecker_NBETerm.or_op)))]
let (built_in_primitive_steps_list :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list) =
  FStarC_Compiler_List.op_At simple_ops
    (FStarC_Compiler_List.op_At short_circuit_ops
       (FStarC_Compiler_List.op_At FStarC_TypeChecker_Primops_Issue.ops
          (FStarC_Compiler_List.op_At FStarC_TypeChecker_Primops_Array.ops
             (FStarC_Compiler_List.op_At
                FStarC_TypeChecker_Primops_Sealed.ops
                (FStarC_Compiler_List.op_At
                   FStarC_TypeChecker_Primops_Erased.ops
                   (FStarC_Compiler_List.op_At
                      FStarC_TypeChecker_Primops_Docs.ops
                      (FStarC_Compiler_List.op_At
                         FStarC_TypeChecker_Primops_MachineInts.ops
                         (FStarC_Compiler_List.op_At
                            FStarC_TypeChecker_Primops_Errors_Msg.ops
                            (FStarC_Compiler_List.op_At
                               FStarC_TypeChecker_Primops_Range.ops
                               FStarC_TypeChecker_Primops_Real.ops)))))))))
let (env_dependent_ops :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  = fun env -> FStarC_TypeChecker_Primops_Eq.dec_eq_ops env
let (simplification_ops_list :
  FStarC_TypeChecker_Env.env_t ->
    FStarC_TypeChecker_Primops_Base.primitive_step Prims.list)
  =
  fun env ->
    let uu___ = FStarC_TypeChecker_Primops_Eq.prop_eq_ops env in
    FStarC_Compiler_List.op_At uu___
      FStarC_TypeChecker_Primops_Real.simplify_ops
open Prims
let as_primitive_step (is_strong : Prims.bool)
  (uu___ :
    (FStarC_Ident.lident * Prims.int * Prims.int *
      FStarC_TypeChecker_Primops_Base.interp_t *
      (FStarC_Syntax_Syntax.universes ->
         FStarC_TypeChecker_NBETerm.args ->
           FStarC_TypeChecker_NBETerm.t FStar_Pervasives_Native.option)))
  : FStarC_TypeChecker_Primops_Base.primitive_step=
  match uu___ with
  | (l, arity, u_arity, f, f_nbe) ->
      FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
        (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))
let and_op (psc : FStarC_TypeChecker_Primops_Base.psc)
  (_norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (_us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
      ->
      let uu___ =
        FStarC_TypeChecker_Primops_Base.try_unembed_simple
          FStarC_Syntax_Embeddings.e_bool a1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some false ->
           let uu___1 =
             FStarC_TypeChecker_Primops_Base.embed_simple
               FStarC_Syntax_Embeddings.e_bool
               psc.FStarC_TypeChecker_Primops_Base.psc_range false in
           FStar_Pervasives_Native.Some uu___1
       | FStar_Pervasives_Native.Some true -> FStar_Pervasives_Native.Some a2
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> failwith "Unexpected number of arguments"
let or_op (psc : FStarC_TypeChecker_Primops_Base.psc)
  (_norm_cb : FStarC_Syntax_Embeddings_Base.norm_cb)
  (_us : FStarC_Syntax_Syntax.universes) (args : FStarC_Syntax_Syntax.args) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match args with
  | (a1, FStar_Pervasives_Native.None)::(a2, FStar_Pervasives_Native.None)::[]
      ->
      let uu___ =
        FStarC_TypeChecker_Primops_Base.try_unembed_simple
          FStarC_Syntax_Embeddings.e_bool a1 in
      (match uu___ with
       | FStar_Pervasives_Native.Some true ->
           let uu___1 =
             FStarC_TypeChecker_Primops_Base.embed_simple
               FStarC_Syntax_Embeddings.e_bool
               psc.FStarC_TypeChecker_Primops_Base.psc_range true in
           FStar_Pervasives_Native.Some uu___1
       | FStar_Pervasives_Native.Some false ->
           FStar_Pervasives_Native.Some a2
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> failwith "Unexpected number of arguments"
let division_modulus_op (f : Prims.int -> Prims.int -> Prims.int)
  (x : Prims.int) (y : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  if y <> Prims.int_zero
  then let uu___ = f x y in FStar_Pervasives_Native.Some uu___
  else FStar_Pervasives_Native.None
let simple_ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ =
    FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
      FStarC_Parser_Const.string_of_int_lid FStarC_Syntax_Embeddings.e_int
      FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_string
      FStarC_TypeChecker_NBETerm.e_string
      (fun z -> FStarC_Class_Show.show FStarC_Class_Show.showable_int z) in
  let uu___1 =
    let uu___2 =
      FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
        FStarC_Parser_Const.int_of_string_lid
        FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
        (FStarC_Syntax_Embeddings.e_option FStarC_Syntax_Embeddings.e_int)
        (FStarC_TypeChecker_NBETerm.e_option FStarC_TypeChecker_NBETerm.e_int)
        (fun s -> FStarC_Util.safe_int_of_string s) in
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
              FStarC_TypeChecker_NBETerm.e_int (fun x -> - x) in
          let uu___9 =
            let uu___10 =
              FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                FStarC_Parser_Const.op_Addition
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int
                FStarC_Syntax_Embeddings.e_int
                FStarC_TypeChecker_NBETerm.e_int (+) in
            let uu___11 =
              let uu___12 =
                FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                  FStarC_Parser_Const.op_Subtraction
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int
                  FStarC_Syntax_Embeddings.e_int
                  FStarC_TypeChecker_NBETerm.e_int (-) in
              let uu___13 =
                let uu___14 =
                  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                    FStarC_Parser_Const.op_Multiply
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int
                    FStarC_Syntax_Embeddings.e_int
                    FStarC_TypeChecker_NBETerm.e_int ( * ) in
                let uu___15 =
                  let uu___16 =
                    FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                      FStarC_Parser_Const.op_LT
                      FStarC_Syntax_Embeddings.e_int
                      FStarC_TypeChecker_NBETerm.e_int
                      FStarC_Syntax_Embeddings.e_int
                      FStarC_TypeChecker_NBETerm.e_int
                      FStarC_Syntax_Embeddings.e_bool
                      FStarC_TypeChecker_NBETerm.e_bool (<) in
                  let uu___17 =
                    let uu___18 =
                      FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                        FStarC_Parser_Const.op_LTE
                        FStarC_Syntax_Embeddings.e_int
                        FStarC_TypeChecker_NBETerm.e_int
                        FStarC_Syntax_Embeddings.e_int
                        FStarC_TypeChecker_NBETerm.e_int
                        FStarC_Syntax_Embeddings.e_bool
                        FStarC_TypeChecker_NBETerm.e_bool (<=) in
                    let uu___19 =
                      let uu___20 =
                        FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                          FStarC_Parser_Const.op_GT
                          FStarC_Syntax_Embeddings.e_int
                          FStarC_TypeChecker_NBETerm.e_int
                          FStarC_Syntax_Embeddings.e_int
                          FStarC_TypeChecker_NBETerm.e_int
                          FStarC_Syntax_Embeddings.e_bool
                          FStarC_TypeChecker_NBETerm.e_bool (>) in
                      let uu___21 =
                        let uu___22 =
                          FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
                            FStarC_Parser_Const.op_GTE
                            FStarC_Syntax_Embeddings.e_int
                            FStarC_TypeChecker_NBETerm.e_int
                            FStarC_Syntax_Embeddings.e_int
                            FStarC_TypeChecker_NBETerm.e_int
                            FStarC_Syntax_Embeddings.e_bool
                            FStarC_TypeChecker_NBETerm.e_bool (>=) in
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
                              (division_modulus_op (/))
                              (division_modulus_op (/)) in
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
                                (division_modulus_op (mod))
                                (division_modulus_op (mod)) in
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
                                    FStarC_String.concat in
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
                                      FStarC_String.split in
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
                                        (fun s1 s2 -> Prims.strcat s1 s2) in
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
                                          (fun s1 s2 ->
                                             FStarC_String.compare s1 s2) in
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
                                              (fun x y ->
                                                 FStarC_String.make x y) in
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
                                                  FStarC_String.lowercase in
                                              let uu___45 =
                                                let uu___46 =
                                                  FStarC_TypeChecker_Primops_Base.mk1
                                                    Prims.int_zero
                                                    FStarC_Parser_Const.string_uppercase_lid
                                                    FStarC_Syntax_Embeddings.e_string
                                                    FStarC_TypeChecker_NBETerm.e_string
                                                    FStarC_Syntax_Embeddings.e_string
                                                    FStarC_TypeChecker_NBETerm.e_string
                                                    FStarC_String.uppercase in
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
                                                      FStarC_String.index in
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
                                                        FStarC_String.index_of in
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
                                                          (fun s o l ->
                                                             FStarC_String.substring
                                                               s o l) in
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
let short_circuit_ops :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  FStarC_List.map (as_primitive_step true)
    [(FStarC_Parser_Const.op_And, (Prims.of_int (2)), Prims.int_zero, and_op,
       ((fun _us -> FStarC_TypeChecker_NBETerm.and_op)));
    (FStarC_Parser_Const.op_Or, (Prims.of_int (2)), Prims.int_zero, or_op,
      ((fun _us -> FStarC_TypeChecker_NBETerm.or_op)))]
let built_in_primitive_steps_list :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  FStarC_List.op_At simple_ops
    (FStarC_List.op_At short_circuit_ops
       (FStarC_List.op_At FStarC_TypeChecker_Primops_Issue.ops
          (FStarC_List.op_At FStarC_TypeChecker_Primops_Array.ops
             (FStarC_List.op_At FStarC_TypeChecker_Primops_Sealed.ops
                (FStarC_List.op_At FStarC_TypeChecker_Primops_Erased.ops
                   (FStarC_List.op_At FStarC_TypeChecker_Primops_Docs.ops
                      (FStarC_List.op_At
                         FStarC_TypeChecker_Primops_MachineInts.ops
                         (FStarC_List.op_At
                            FStarC_TypeChecker_Primops_Errors_Msg.ops
                            (FStarC_List.op_At
                               FStarC_TypeChecker_Primops_Range.ops
                               FStarC_TypeChecker_Primops_Real.ops)))))))))
let env_dependent_ops (env : FStarC_TypeChecker_Env.env_t) :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  FStarC_TypeChecker_Primops_Eq.dec_eq_ops env
let simplification_ops_list (env : FStarC_TypeChecker_Env.env_t) :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let uu___ = FStarC_TypeChecker_Primops_Eq.prop_eq_ops env in
  FStarC_List.op_At uu___
    (FStarC_List.op_At FStarC_TypeChecker_Primops_Real.simplify_ops
       FStarC_TypeChecker_Primops_Erased.simplify_ops)

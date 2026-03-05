open Prims
let as_primitive_step (is_strong : Prims.bool) (l : FStarC_Ident.lident)
  (arity : Prims.int) (u_arity : Prims.int)
  (f : FStarC_TypeChecker_Primops_Base.interp_t)
  (f_nbe : FStarC_TypeChecker_Primops_Base.nbe_interp_t) :
  FStarC_TypeChecker_Primops_Base.primitive_step=
  FStarC_TypeChecker_Primops_Base.as_primitive_step_nbecbs is_strong
    (l, arity, u_arity, f, f_nbe)
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
       | FStar_Pervasives_Native.Some (false) ->
           let uu___1 =
             FStarC_TypeChecker_Primops_Base.embed_simple
               FStarC_Syntax_Embeddings.e_bool
               psc.FStarC_TypeChecker_Primops_Base.psc_range false in
           FStar_Pervasives_Native.Some uu___1
       | FStar_Pervasives_Native.Some (true) ->
           FStar_Pervasives_Native.Some a2
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStarC_Effect.failwith "Unexpected number of arguments"
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
       | FStar_Pervasives_Native.Some (true) ->
           let uu___1 =
             FStarC_TypeChecker_Primops_Base.embed_simple
               FStarC_Syntax_Embeddings.e_bool
               psc.FStarC_TypeChecker_Primops_Base.psc_range true in
           FStar_Pervasives_Native.Some uu___1
       | FStar_Pervasives_Native.Some (false) ->
           FStar_Pervasives_Native.Some a2
       | uu___1 -> FStar_Pervasives_Native.None)
  | uu___ -> FStarC_Effect.failwith "Unexpected number of arguments"
let division_modulus_op (f : Prims.int -> Prims.int -> Prims.int)
  (x : Prims.int) (y : Prims.int) : Prims.int FStar_Pervasives_Native.option=
  if y <> Prims.int_zero
  then FStar_Pervasives_Native.Some (f x y)
  else FStar_Pervasives_Native.None
let simple_ops : FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  [FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
     FStarC_Parser_Const.string_of_int_lid FStarC_Syntax_Embeddings.e_int
     FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_string
     FStarC_TypeChecker_NBETerm.e_string
     (fun z -> FStarC_Class_Show.show FStarC_Class_Show.showable_int z);
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.int_of_string_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string
    (FStarC_Syntax_Embeddings.e_option FStarC_Syntax_Embeddings.e_int)
    (FStarC_TypeChecker_NBETerm.e_option FStarC_TypeChecker_NBETerm.e_int)
    (fun s -> FStarC_Util.safe_int_of_string s);
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.string_of_bool_lid FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string Prims.string_of_bool;
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.bool_of_string_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string
    (FStarC_Syntax_Embeddings.e_option FStarC_Syntax_Embeddings.e_bool)
    (FStarC_TypeChecker_NBETerm.e_option FStarC_TypeChecker_NBETerm.e_bool)
    (fun uu___ ->
       match uu___ with
       | "true" -> FStar_Pervasives_Native.Some true
       | "false" -> FStar_Pervasives_Native.Some false
       | uu___1 -> FStar_Pervasives_Native.None);
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.op_Minus FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int (fun x -> - x);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_Addition FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int (+);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_Subtraction FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int (-);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_Multiply FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int ( * );
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_LT FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool (<);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_LTE FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool (<=);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_GT FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool (>);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.op_GTE FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool (>=);
  FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
    FStarC_Parser_Const.op_Division FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int (division_modulus_op (/))
    (division_modulus_op (/));
  FStarC_TypeChecker_Primops_Base.mk2' Prims.int_zero
    FStarC_Parser_Const.op_Modulus FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int (division_modulus_op (mod))
    (division_modulus_op (mod));
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.op_Negation FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool FStarC_Syntax_Embeddings.e_bool
    FStarC_TypeChecker_NBETerm.e_bool Prims.op_Negation;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_concat_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string
    FStarC_Syntax_Embeddings.e_string_list
    FStarC_TypeChecker_NBETerm.e_string_list
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_String.concat;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_split_lid
    (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_char)
    (FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_char)
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_Syntax_Embeddings.e_string_list
    FStarC_TypeChecker_NBETerm.e_string_list FStarC_String.split;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.prims_strcat_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string (fun s1 s2 -> Prims.strcat s1 s2);
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_compare_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int
    (fun s1 s2 -> FStarC_String.compare s1 s2);
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.string_string_of_list_lid
    (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_char)
    (FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_char)
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStar_String.string_of_list;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_make_lid FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_char
    FStarC_TypeChecker_NBETerm.e_char FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string (fun x y -> FStarC_String.make x y);
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.string_list_of_string_lid
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    (FStarC_Syntax_Embeddings.e_list FStarC_Syntax_Embeddings.e_char)
    (FStarC_TypeChecker_NBETerm.e_list FStarC_TypeChecker_NBETerm.e_char)
    FStar_String.list_of_string;
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.string_lowercase_lid
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_String.lowercase;
  FStarC_TypeChecker_Primops_Base.mk1 Prims.int_zero
    FStarC_Parser_Const.string_uppercase_lid
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_Syntax_Embeddings.e_string FStarC_TypeChecker_NBETerm.e_string
    FStarC_String.uppercase;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_index_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_char
    FStarC_TypeChecker_NBETerm.e_char FStarC_String.index;
  FStarC_TypeChecker_Primops_Base.mk2 Prims.int_zero
    FStarC_Parser_Const.string_index_of_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_char
    FStarC_TypeChecker_NBETerm.e_char FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_String.index_of;
  FStarC_TypeChecker_Primops_Base.mk3 Prims.int_zero
    FStarC_Parser_Const.string_sub_lid FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_int
    FStarC_TypeChecker_NBETerm.e_int FStarC_Syntax_Embeddings.e_string
    FStarC_TypeChecker_NBETerm.e_string
    (fun s o l -> FStarC_String.substring s o l)]
let short_circuit_ops :
  FStarC_TypeChecker_Primops_Base.primitive_step Prims.list=
  let nbe_and _cb _us args = FStarC_TypeChecker_NBETerm.and_op args in
  let nbe_or _cb _us args = FStarC_TypeChecker_NBETerm.or_op args in
  let s1 =
    as_primitive_step true FStarC_Parser_Const.op_And (Prims.of_int (2))
      Prims.int_zero and_op nbe_and in
  let s2 =
    as_primitive_step true FStarC_Parser_Const.op_Or (Prims.of_int (2))
      Prims.int_zero or_op nbe_or in
  [s1; s2]
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

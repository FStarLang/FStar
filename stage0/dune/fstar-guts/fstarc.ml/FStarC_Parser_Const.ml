open Prims
let p2l (l : FStarC_Ident.path) : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path l FStarC_Range_Type.dummyRange
let pconst (s : Prims.string) : FStarC_Ident.lident= p2l ["Prims"; s]
let psconst (s : Prims.string) : FStarC_Ident.lident=
  p2l ["FStar"; "Pervasives"; s]
let attr (s : Prims.string) : FStarC_Ident.lident=
  p2l ["FStar"; "Attributes"; s]
let psnconst (s : Prims.string) : FStarC_Ident.lident=
  p2l ["FStar"; "Pervasives"; "Native"; s]
let prims_lid : FStarC_Ident.lident= p2l ["Prims"]
let pervasives_native_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Pervasives"; "Native"]
let pervasives_lid : FStarC_Ident.lident= p2l ["FStar"; "Pervasives"]
let fstar_ns_lid : FStarC_Ident.lident= p2l ["FStar"]
let bool_lid : FStarC_Ident.lident= pconst "bool"
let unit_lid : FStarC_Ident.lident= pconst "unit"
let squash_lid : FStarC_Ident.lident= pconst "squash"
let auto_squash_lid : FStarC_Ident.lident= pconst "auto_squash"
let string_lid : FStarC_Ident.lident= pconst "string"
let bytes_lid : FStarC_Ident.lident= pconst "bytes"
let int_lid : FStarC_Ident.lident= pconst "int"
let exn_lid : FStarC_Ident.lident= pconst "exn"
let list_lid : FStarC_Ident.lident= pconst "list"
let immutable_array_t_lid : FStarC_Ident.lident=
  p2l ["FStar"; "ImmutableArray"; "Base"; "t"]
let immutable_array_of_list_lid : FStarC_Ident.lident=
  p2l ["FStar"; "ImmutableArray"; "Base"; "of_list"]
let immutable_array_length_lid : FStarC_Ident.lident=
  p2l ["FStar"; "ImmutableArray"; "Base"; "length"]
let immutable_array_index_lid : FStarC_Ident.lident=
  p2l ["FStar"; "ImmutableArray"; "Base"; "index"]
let eqtype_lid : FStarC_Ident.lident= pconst "eqtype"
let option_lid : FStarC_Ident.lident= psnconst "option"
let either_lid : FStarC_Ident.lident= psconst "either"
let pattern_lid : FStarC_Ident.lident= psconst "pattern"
let lex_t_lid : FStarC_Ident.lident= pconst "lex_t"
let lextop_lid : FStarC_Ident.lident= pconst "LexTop"
let lexcons_lid : FStarC_Ident.lident= pconst "LexCons"
let precedes_lid : FStarC_Ident.lident= pconst "precedes"
let smtpat_lid : FStarC_Ident.lident= psconst "smt_pat"
let smtpatOr_lid : FStarC_Ident.lident= psconst "smt_pat_or"
let monadic_lid : FStarC_Ident.lident= pconst "M"
let spinoff_lid : FStarC_Ident.lident= psconst "spinoff"
let inl_lid : FStarC_Ident.lident= psconst "Inl"
let inr_lid : FStarC_Ident.lident= psconst "Inr"
let int8_lid : FStarC_Ident.lident= p2l ["FStar"; "Int8"; "t"]
let uint8_lid : FStarC_Ident.lident= p2l ["FStar"; "UInt8"; "t"]
let int16_lid : FStarC_Ident.lident= p2l ["FStar"; "Int16"; "t"]
let uint16_lid : FStarC_Ident.lident= p2l ["FStar"; "UInt16"; "t"]
let int32_lid : FStarC_Ident.lident= p2l ["FStar"; "Int32"; "t"]
let uint32_lid : FStarC_Ident.lident= p2l ["FStar"; "UInt32"; "t"]
let int64_lid : FStarC_Ident.lident= p2l ["FStar"; "Int64"; "t"]
let uint64_lid : FStarC_Ident.lident= p2l ["FStar"; "UInt64"; "t"]
let sizet_lid : FStarC_Ident.lident= p2l ["FStar"; "SizeT"; "t"]
let salloc_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "salloc"]
let swrite_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "op_Colon_Equals"]
let sread_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "op_Bang"]
let max_lid : FStarC_Ident.lident= p2l ["max"]
let real_lid : FStarC_Ident.lident= p2l ["FStar"; "Real"; "real"]
let float_lid : FStarC_Ident.lident= p2l ["FStar"; "Float"; "float"]
let char_lid : FStarC_Ident.lident= p2l ["FStar"; "Char"; "char"]
let heap_lid : FStarC_Ident.lident= p2l ["FStar"; "Heap"; "heap"]
let logical_lid : FStarC_Ident.lident= pconst "logical"
let prop_lid : FStarC_Ident.lident= pconst "prop"
let smt_theory_symbol_attr_lid : FStarC_Ident.lident=
  pconst "smt_theory_symbol"
let true_lid : FStarC_Ident.lident= pconst "l_True"
let false_lid : FStarC_Ident.lident= pconst "l_False"
let and_lid : FStarC_Ident.lident= pconst "l_and"
let or_lid : FStarC_Ident.lident= pconst "l_or"
let not_lid : FStarC_Ident.lident= pconst "l_not"
let imp_lid : FStarC_Ident.lident= pconst "l_imp"
let iff_lid : FStarC_Ident.lident= pconst "l_iff"
let ite_lid : FStarC_Ident.lident= pconst "l_ITE"
let exists_lid : FStarC_Ident.lident= pconst "l_Exists"
let forall_lid : FStarC_Ident.lident= pconst "l_Forall"
let haseq_lid : FStarC_Ident.lident= pconst "hasEq"
let b2t_lid : FStarC_Ident.lident= pconst "b2t"
let admit_lid : FStarC_Ident.lident= pconst "admit"
let magic_lid : FStarC_Ident.lident= pconst "magic"
let has_type_lid : FStarC_Ident.lident= pconst "has_type"
let c_true_lid : FStarC_Ident.lident= pconst "trivial"
let empty_type_lid : FStarC_Ident.lident= pconst "empty"
let c_and_lid : FStarC_Ident.lident= pconst "pair"
let c_or_lid : FStarC_Ident.lident= pconst "sum"
let eq2_lid : FStarC_Ident.lident= pconst "eq2"
let eq3_lid : FStarC_Ident.lident= pconst "op_Equals_Equals_Equals"
let c_eq2_lid : FStarC_Ident.lident= pconst "equals"
let cons_lid : FStarC_Ident.lident= pconst "Cons"
let nil_lid : FStarC_Ident.lident= pconst "Nil"
let some_lid : FStarC_Ident.lident= psnconst "Some"
let none_lid : FStarC_Ident.lident= psnconst "None"
let assume_lid : FStarC_Ident.lident= pconst "_assume"
let assert_lid : FStarC_Ident.lident= pconst "_assert"
let pure_wp_lid : FStarC_Ident.lident= pconst "pure_wp"
let pure_wp_monotonic_lid : FStarC_Ident.lident= pconst "pure_wp_monotonic"
let pure_wp_monotonic0_lid : FStarC_Ident.lident= pconst "pure_wp_monotonic0"
let trivial_pure_post_lid : FStarC_Ident.lident= psconst "trivial_pure_post"
let pure_assert_wp_lid : FStarC_Ident.lident= pconst "pure_assert_wp0"
let pure_assume_wp_lid : FStarC_Ident.lident= pconst "pure_assume_wp0"
let assert_norm_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Pervasives"; "assert_norm"]
let list_append_lid : FStarC_Ident.lident= p2l ["FStar"; "List"; "append"]
let list_tot_append_lid : FStarC_Ident.lident=
  p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let id_lid : FStarC_Ident.lident= psconst "id"
let seq_cons_lid : FStarC_Ident.lident= p2l ["FStar"; "Seq"; "Base"; "cons"]
let seq_empty_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Seq"; "Base"; "empty"]
let c2l (s : Prims.string) : FStarC_Ident.lident= p2l ["FStar"; "Char"; s]
let char_u32_of_char : FStarC_Ident.lident= c2l "u32_of_char"
let s2l (n : Prims.string) : FStarC_Ident.lident= p2l ["FStar"; "String"; n]
let string_list_of_string_lid : FStarC_Ident.lident= s2l "list_of_string"
let string_string_of_list_lid : FStarC_Ident.lident= s2l "string_of_list"
let string_make_lid : FStarC_Ident.lident= s2l "make"
let string_split_lid : FStarC_Ident.lident= s2l "split"
let string_concat_lid : FStarC_Ident.lident= s2l "concat"
let string_compare_lid : FStarC_Ident.lident= s2l "compare"
let string_lowercase_lid : FStarC_Ident.lident= s2l "lowercase"
let string_uppercase_lid : FStarC_Ident.lident= s2l "uppercase"
let string_index_lid : FStarC_Ident.lident= s2l "index"
let string_index_of_lid : FStarC_Ident.lident= s2l "index_of"
let string_sub_lid : FStarC_Ident.lident= s2l "sub"
let prims_strcat_lid : FStarC_Ident.lident= pconst "strcat"
let prims_op_Hat_lid : FStarC_Ident.lident= pconst "op_Hat"
let let_in_typ : FStarC_Ident.lident= p2l ["Prims"; "Let"]
let string_of_int_lid : FStarC_Ident.lident= p2l ["Prims"; "string_of_int"]
let string_of_bool_lid : FStarC_Ident.lident= p2l ["Prims"; "string_of_bool"]
let int_of_string_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Parse"; "int_of_string"]
let bool_of_string_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Parse"; "bool_of_string"]
let string_compare : FStarC_Ident.lident= p2l ["FStar"; "String"; "compare"]
let order_lid : FStarC_Ident.lident= p2l ["FStar"; "Order"; "order"]
let vconfig_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "VConfig"; "vconfig"]
let mkvconfig_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "VConfig"; "Mkvconfig"]
let op_Eq : FStarC_Ident.lident= pconst "op_Equality"
let op_notEq : FStarC_Ident.lident= pconst "op_disEquality"
let op_LT : FStarC_Ident.lident= pconst "op_LessThan"
let op_LTE : FStarC_Ident.lident= pconst "op_LessThanOrEqual"
let op_GT : FStarC_Ident.lident= pconst "op_GreaterThan"
let op_GTE : FStarC_Ident.lident= pconst "op_GreaterThanOrEqual"
let op_Subtraction : FStarC_Ident.lident= pconst "op_Subtraction"
let op_Minus : FStarC_Ident.lident= pconst "op_Minus"
let op_Addition : FStarC_Ident.lident= pconst "op_Addition"
let op_Multiply : FStarC_Ident.lident= pconst "op_Multiply"
let op_Division : FStarC_Ident.lident= pconst "op_Division"
let op_Modulus : FStarC_Ident.lident= pconst "op_Modulus"
let op_And : FStarC_Ident.lident= pconst "op_AmpAmp"
let op_Or : FStarC_Ident.lident= pconst "op_BarBar"
let op_Negation : FStarC_Ident.lident= pconst "op_Negation"
let subtype_of_lid : FStarC_Ident.lident= pconst "subtype_of"
let real_const (s : Prims.string) : FStarC_Ident.lident=
  p2l ["FStar"; "Real"; s]
let real_op_LT : FStarC_Ident.lident= real_const "op_Less_Dot"
let real_op_LTE : FStarC_Ident.lident= real_const "op_Less_Equals_Dot"
let real_op_GT : FStarC_Ident.lident= real_const "op_Greater_Dot"
let real_op_GTE : FStarC_Ident.lident= real_const "op_Greater_Equals_Dot"
let real_op_Subtraction : FStarC_Ident.lident=
  real_const "op_Subtraction_Dot"
let real_op_Addition : FStarC_Ident.lident= real_const "op_Plus_Dot"
let real_op_Multiply : FStarC_Ident.lident= real_const "op_Star_Dot"
let real_op_Division : FStarC_Ident.lident= real_const "op_Slash_Dot"
let real_of_int : FStarC_Ident.lident= real_const "of_int"
let bvconst (s : Prims.string) : FStarC_Ident.lident= p2l ["FStar"; "BV"; s]
let bv_t_lid : FStarC_Ident.lident= bvconst "bv_t"
let nat_to_bv_lid : FStarC_Ident.lident= bvconst "int2bv"
let bv_to_nat_lid : FStarC_Ident.lident= bvconst "bv2int"
let bv_and_lid : FStarC_Ident.lident= bvconst "bvand"
let bv_xor_lid : FStarC_Ident.lident= bvconst "bvxor"
let bv_or_lid : FStarC_Ident.lident= bvconst "bvor"
let bv_add_lid : FStarC_Ident.lident= bvconst "bvadd"
let bv_sub_lid : FStarC_Ident.lident= bvconst "bvsub"
let bv_shift_left_lid : FStarC_Ident.lident= bvconst "bvshl"
let bv_shift_right_lid : FStarC_Ident.lident= bvconst "bvshr"
let bv_udiv_lid : FStarC_Ident.lident= bvconst "bvdiv"
let bv_mod_lid : FStarC_Ident.lident= bvconst "bvmod"
let bv_mul_lid : FStarC_Ident.lident= bvconst "bvmul"
let bv_shift_left'_lid : FStarC_Ident.lident= bvconst "bvshl'"
let bv_shift_right'_lid : FStarC_Ident.lident= bvconst "bvshr'"
let bv_udiv_unsafe_lid : FStarC_Ident.lident= bvconst "bvdiv_unsafe"
let bv_mod_unsafe_lid : FStarC_Ident.lident= bvconst "bvmod_unsafe"
let bv_mul'_lid : FStarC_Ident.lident= bvconst "bvmul'"
let bv_ult_lid : FStarC_Ident.lident= bvconst "bvult"
let bv_uext_lid : FStarC_Ident.lident= bvconst "bv_uext"
let bv_not_lid : FStarC_Ident.lident= bvconst "bvnot"
let array_lid : FStarC_Ident.lident= p2l ["FStar"; "Array"; "array"]
let array_of_list_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Array"; "of_list"]
let st_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"]
let write_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "write"]
let read_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "read"]
let alloc_lid : FStarC_Ident.lident= p2l ["FStar"; "ST"; "alloc"]
let op_ColonEq : FStarC_Ident.lident= p2l ["FStar"; "ST"; "op_Colon_Equals"]
let ref_lid : FStarC_Ident.lident= p2l ["FStar"; "Heap"; "ref"]
let heap_addr_of_lid : FStarC_Ident.lident= p2l ["FStar"; "Heap"; "addr_of"]
let set_empty : FStarC_Ident.lident= p2l ["FStar"; "Set"; "empty"]
let set_singleton : FStarC_Ident.lident= p2l ["FStar"; "Set"; "singleton"]
let set_union : FStarC_Ident.lident= p2l ["FStar"; "Set"; "union"]
let fstar_hyperheap_lid : FStarC_Ident.lident= p2l ["FStar"; "HyperHeap"]
let rref_lid : FStarC_Ident.lident= p2l ["FStar"; "HyperHeap"; "rref"]
let erased_lid : FStarC_Ident.lident= p2l ["FStar"; "Ghost"; "erased"]
let effect_PURE_lid : FStarC_Ident.lident= pconst "PURE"
let effect_Pure_lid : FStarC_Ident.lident= pconst "Pure"
let effect_Tot_lid : FStarC_Ident.lident= pconst "Tot"
let effect_Lemma_lid : FStarC_Ident.lident= psconst "Lemma"
let effect_GTot_lid : FStarC_Ident.lident= pconst "GTot"
let effect_GHOST_lid : FStarC_Ident.lident= pconst "GHOST"
let effect_Ghost_lid : FStarC_Ident.lident= pconst "Ghost"
let effect_DIV_lid : FStarC_Ident.lident= psconst "DIV"
let effect_Div_lid : FStarC_Ident.lident= psconst "Div"
let effect_Dv_lid : FStarC_Ident.lident= psconst "Dv"
let ef_base (uu___ : unit) : Prims.string Prims.list=
  let uu___1 = FStarC_Options.ml_ish () in
  if uu___1
  then
    let uu___2 = FStarC_Options.ml_ish_effect () in
    FStarC_String.split [46] uu___2
  else ["FStar"; "All"]
let effect_ALL_lid (uu___ : unit) : FStarC_Ident.lident=
  let uu___1 = let uu___2 = ef_base () in FStarC_List.op_At uu___2 ["ALL"] in
  p2l uu___1
let effect_ML_lid (uu___ : unit) : FStarC_Ident.lident=
  let uu___1 = let uu___2 = ef_base () in FStarC_List.op_At uu___2 ["ML"] in
  p2l uu___1
let failwith_lid (uu___ : unit) : FStarC_Ident.lident=
  let uu___1 =
    let uu___2 = ef_base () in FStarC_List.op_At uu___2 ["failwith"] in
  p2l uu___1
let try_with_lid (uu___ : unit) : FStarC_Ident.lident=
  let uu___1 =
    let uu___2 = ef_base () in FStarC_List.op_At uu___2 ["try_with"] in
  p2l uu___1
let as_requires : FStarC_Ident.lident= pconst "as_requires"
let as_ensures : FStarC_Ident.lident= pconst "as_ensures"
let decreases_lid : FStarC_Ident.lident= pconst "decreases"
let reveal : FStarC_Ident.lident= p2l ["FStar"; "Ghost"; "reveal"]
let hide : FStarC_Ident.lident= p2l ["FStar"; "Ghost"; "hide"]
let labeled_lid : FStarC_Ident.lident= p2l ["FStar"; "Range"; "labeled"]
let __range_lid : FStarC_Ident.lident= p2l ["FStar"; "Range"; "__range"]
let range_lid : FStarC_Ident.lident= p2l ["FStar"; "Range"; "range"]
let range_0 : FStarC_Ident.lident= p2l ["FStar"; "Range"; "range_0"]
let mk_range_lid : FStarC_Ident.lident= p2l ["FStar"; "Range"; "mk_range"]
let __mk_range_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Range"; "__mk_range"]
let __explode_range_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Range"; "explode"]
let join_range_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Range"; "join_range"]
let guard_free : FStarC_Ident.lident= pconst "guard_free"
let inversion_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Pervasives"; "inversion"]
let normalize : FStarC_Ident.lident= psconst "normalize"
let normalize_term : FStarC_Ident.lident= psconst "normalize_term"
let norm : FStarC_Ident.lident= psconst "norm"
let mk_norm_step_lid (l : Prims.string) : FStarC_Ident.lident=
  p2l ["FStar"; "NormSteps"; l]
let norm_step_lid : FStarC_Ident.lident= mk_norm_step_lid "norm_step"
let steps_simpl : FStarC_Ident.lident= mk_norm_step_lid "simplify"
let steps_weak : FStarC_Ident.lident= mk_norm_step_lid "weak"
let steps_hnf : FStarC_Ident.lident= mk_norm_step_lid "hnf"
let steps_primops : FStarC_Ident.lident= mk_norm_step_lid "primops"
let steps_zeta : FStarC_Ident.lident= mk_norm_step_lid "zeta"
let steps_zeta_full : FStarC_Ident.lident= mk_norm_step_lid "zeta_full"
let steps_iota : FStarC_Ident.lident= mk_norm_step_lid "iota"
let steps_delta : FStarC_Ident.lident= mk_norm_step_lid "delta"
let steps_reify : FStarC_Ident.lident= mk_norm_step_lid "reify_"
let steps_norm_debug : FStarC_Ident.lident= mk_norm_step_lid "norm_debug"
let steps_unfoldonly : FStarC_Ident.lident= mk_norm_step_lid "delta_only"
let steps_unfoldonce : FStarC_Ident.lident= mk_norm_step_lid "delta_once"
let steps_unfoldfully : FStarC_Ident.lident= mk_norm_step_lid "delta_fully"
let steps_unfoldattr : FStarC_Ident.lident= mk_norm_step_lid "delta_attr"
let steps_unfoldqual : FStarC_Ident.lident=
  mk_norm_step_lid "delta_qualifier"
let steps_unfoldnamespace : FStarC_Ident.lident=
  mk_norm_step_lid "delta_namespace"
let steps_unascribe : FStarC_Ident.lident= mk_norm_step_lid "unascribe"
let steps_nbe : FStarC_Ident.lident= mk_norm_step_lid "nbe"
let steps_unmeta : FStarC_Ident.lident= mk_norm_step_lid "unmeta"
let deprecated_attr : FStarC_Ident.lident= pconst "deprecated"
let warn_on_use_attr : FStarC_Ident.lident= pconst "warn_on_use"
let inline_let_attr : FStarC_Ident.lident= attr "inline_let"
let inline_let_vc_attr : FStarC_Ident.lident= attr "inline_let_vc"
let no_inline_let_attr : FStarC_Ident.lident= attr "no_inline_let"
let rename_let_attr : FStarC_Ident.lident= attr "rename_let"
let plugin_attr : FStarC_Ident.lident= attr "plugin"
let tcnorm_attr : FStarC_Ident.lident= attr "tcnorm"
let dm4f_bind_range_attr : FStarC_Ident.lident= attr "dm4f_bind_range"
let must_erase_for_extraction_attr : FStarC_Ident.lident=
  attr "must_erase_for_extraction"
let strict_on_arguments_attr : FStarC_Ident.lident=
  attr "strict_on_arguments"
let resolve_implicits_attr_string : FStarC_Ident.lident=
  attr "resolve_implicits"
let override_resolve_implicits_handler_lid : FStarC_Ident.lident=
  attr "override_resolve_implicits_handler"
let handle_smt_goals_attr : FStarC_Ident.lident= attr "handle_smt_goals"
let erasable_attr : FStarC_Ident.lident= attr "erasable"
let fail_attr : FStarC_Ident.lident= attr "expect_failure"
let fail_lax_attr : FStarC_Ident.lident= attr "expect_lax_failure"
let unification_tag_lid : FStarC_Ident.lident= attr "defer_to"
let comment_attr : FStarC_Ident.lident= attr "Comment"
let c_inline_attr : FStarC_Ident.lident= attr "CInline"
let attr_substitute_lid : FStarC_Ident.lident= attr "Substitute"
let normalize_for_extraction_lid : FStarC_Ident.lident=
  psconst "normalize_for_extraction"
let normalize_for_extraction_type_lid : FStarC_Ident.lident=
  psconst "normalize_for_extraction_type"
let tcdecltime_attr : FStarC_Ident.lident= attr "tcdecltime"
let noextract_to_attr : FStarC_Ident.lident= attr "noextract_to"
let unifier_hint_injective_lid : FStarC_Ident.lident=
  attr "unifier_hint_injective"
let commute_nested_matches_lid : FStarC_Ident.lident=
  attr "commute_nested_matches"
let ite_soundness_by_attr : FStarC_Ident.lident= attr "ite_soundness_by"
let default_effect_attr : FStarC_Ident.lident= attr "default_effect"
let top_level_effect_attr : FStarC_Ident.lident= attr "top_level_effect"
let effect_parameter_attr : FStarC_Ident.lident= attr "effect_param"
let bind_has_range_args_attr : FStarC_Ident.lident=
  attr "bind_has_range_args"
let primitive_extraction_attr : FStarC_Ident.lident=
  attr "primitive_extraction"
let binder_strictly_positive_attr : FStarC_Ident.lident=
  attr "strictly_positive"
let binder_unused_attr : FStarC_Ident.lident= attr "unused"
let no_auto_projectors_decls_attr : FStarC_Ident.lident=
  attr "no_auto_projectors_decls"
let no_auto_projectors_attr : FStarC_Ident.lident= attr "no_auto_projectors"
let no_subtping_attr_lid : FStarC_Ident.lident= attr "no_subtyping"
let admit_termination_lid : FStarC_Ident.lident= attr "admit_termination"
let admitted_lid : FStarC_Ident.lident= attr "admitted"
let unrefine_binder_attr : FStarC_Ident.lident= pconst "unrefine"
let do_not_unrefine_attr : FStarC_Ident.lident= pconst "do_not_unrefine"
let desugar_of_variant_record_lid : FStarC_Ident.lident=
  attr "desugar_of_variant_record"
let coercion_lid : FStarC_Ident.lident= attr "coercion"
let projector_attr : FStarC_Ident.lident= pconst "projector"
let discriminator_attr : FStarC_Ident.lident= pconst "discriminator"
let remove_unused_type_parameters_lid : FStarC_Ident.lident=
  psconst "remove_unused_type_parameters"
let well_founded_relation_lid : FStarC_Ident.lident=
  p2l ["FStar"; "WellFounded"; "well_founded_relation"]
let gen_reset : ((unit -> Prims.int) * (unit -> unit))=
  let x = FStarC_Effect.mk_ref Prims.int_zero in
  let gen uu___ = FStarC_Util.incr x; FStarC_Util.read x in
  let reset uu___ = FStarC_Util.write x Prims.int_zero in (gen, reset)
let next_id : unit -> Prims.int= FStar_Pervasives_Native.fst gen_reset
let sli (l : FStarC_Ident.lident) : Prims.string=
  let uu___ = FStarC_Options.print_real_names () in
  if uu___
  then FStarC_Ident.string_of_lid l
  else
    (let uu___2 = FStarC_Ident.ident_of_lid l in
     FStarC_Ident.string_of_id uu___2)
let const_to_string (x : FStarC_Const.sconst) : Prims.string=
  match x with
  | FStarC_Const.Const_effect -> "Effect"
  | FStarC_Const.Const_unit -> "()"
  | FStarC_Const.Const_bool b -> if b then "true" else "false"
  | FStarC_Const.Const_real r -> Prims.strcat r "R"
  | FStarC_Const.Const_string (s, uu___) -> FStarC_Format.fmt1 "\"%s\"" s
  | FStarC_Const.Const_int (x1, uu___) -> x1
  | FStarC_Const.Const_char c ->
      Prims.strcat "'" (Prims.strcat (FStarC_Util.string_of_char c) "'")
  | FStarC_Const.Const_range r -> FStarC_Range_Ops.string_of_range r
  | FStarC_Const.Const_range_of -> "range_of"
  | FStarC_Const.Const_set_range_of -> "set_range_of"
  | FStarC_Const.Const_reify lopt ->
      let uu___ =
        match lopt with
        | FStar_Pervasives_Native.None -> ""
        | FStar_Pervasives_Native.Some l ->
            let uu___1 = FStarC_Ident.string_of_lid l in
            FStarC_Format.fmt1 "<%s>" uu___1 in
      FStarC_Format.fmt1 "reify%s" uu___
  | FStarC_Const.Const_reflect l ->
      let uu___ = sli l in FStarC_Format.fmt1 "[[%s.reflect]]" uu___
let is_name (lid : FStarC_Ident.lident) : Prims.bool=
  let c =
    let uu___ =
      let uu___1 = FStarC_Ident.ident_of_lid lid in
      FStarC_Ident.string_of_id uu___1 in
    FStarC_Util.char_at uu___ Prims.int_zero in
  FStarC_Util.is_upper c
let term_view_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Reflection"; "V1"; "Data"; "term_view"]
let fstar_tactics_lid' (s : Prims.string Prims.list) : FStarC_Ident.lid=
  FStarC_Ident.lid_of_path (FStarC_List.op_At ["FStar"; "Tactics"] s)
    FStarC_Range_Type.dummyRange
let fstar_stubs_tactics_lid' (s : Prims.string Prims.list) :
  FStarC_Ident.lid=
  FStarC_Ident.lid_of_path
    (FStarC_List.op_At ["FStar"; "Stubs"; "Tactics"] s)
    FStarC_Range_Type.dummyRange
let fstar_tactics_lid (s : Prims.string) : FStarC_Ident.lid=
  fstar_tactics_lid' [s]
let tac_lid : FStarC_Ident.lid= fstar_tactics_lid' ["Effect"; "tac"]
let tac_bind_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "tac_bind"]
let lift_div_tac_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "lift_div_tac"]
let tactic_lid : FStarC_Ident.lid= fstar_tactics_lid' ["Effect"; "tactic"]
let tac_opaque_attr : FStarC_Ident.lident= pconst "tac_opaque"
let meta_projectors_attr : FStarC_Ident.lid=
  fstar_tactics_lid' ["MkProjectors"; "meta_projectors"]
let mk_projs_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["MkProjectors"; "mk_projs"]
let mk_class_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Typeclasses"; "mk_class"]
let tcresolve_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Typeclasses"; "tcresolve"]
let tcclass_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Typeclasses"; "tcclass"]
let tcinstance_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Typeclasses"; "tcinstance"]
let no_method_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Typeclasses"; "no_method"]
let effect_TAC_lid : FStarC_Ident.lid= fstar_tactics_lid' ["Effect"; "TAC"]
let effect_Tac_lid : FStarC_Ident.lid= fstar_tactics_lid' ["Effect"; "Tac"]
let by_tactic_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "with_tactic"]
let rewrite_by_tactic_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "rewrite_with_tactic"]
let synth_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "synth_by_tactic"]
let assert_by_tactic_lid : FStarC_Ident.lid=
  fstar_tactics_lid' ["Effect"; "assert_by_tactic"]
let fstar_syntax_syntax_term : FStarC_Ident.lident=
  FStarC_Ident.lid_of_str "FStarC.Syntax.Syntax.term"
let binder_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path
    ["FStar"; "Stubs"; "Reflection"; "Types"; "binder"]
    FStarC_Range_Type.dummyRange
let binders_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path
    ["FStar"; "Stubs"; "Reflection"; "Types"; "binders"]
    FStarC_Range_Type.dummyRange
let bv_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["FStar"; "Stubs"; "Reflection"; "Types"; "bv"]
    FStarC_Range_Type.dummyRange
let fv_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["FStar"; "Stubs"; "Reflection"; "Types"; "fv"]
    FStarC_Range_Type.dummyRange
let postprocess_with : FStarC_Ident.lident=
  p2l ["FStar"; "Tactics"; "Effect"; "postprocess_with"]
let postprocess_type : FStarC_Ident.lident=
  p2l ["FStar"; "Tactics"; "Effect"; "postprocess_type"]
let preprocess_with : FStarC_Ident.lident=
  p2l ["FStar"; "Tactics"; "Effect"; "preprocess_with"]
let postprocess_extr_with : FStarC_Ident.lident=
  p2l ["FStar"; "Tactics"; "Effect"; "postprocess_for_extraction_with"]
let term_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "term"]
let ctx_uvar_and_subst_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "ctx_uvar_and_subst"]
let universe_uvar_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "universe_uvar"]
let check_with_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["FStar"; "Stubs"; "VConfig"; "check_with"]
    FStarC_Range_Type.dummyRange
let decls_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Reflection"; "Types"; "decls"]
let dsl_typing_builtin (s : Prims.string) : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path
    (FStarC_List.op_At ["FStar"; "Reflection"; "Typing"; "Builtins"] [s])
    FStarC_Range_Type.dummyRange
let dsl_tac_typ_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["FStar"; "Reflection"; "Typing"; "dsl_tac_t"]
    FStarC_Range_Type.dummyRange
let calc_lid (i : Prims.string) : FStarC_Ident.lid=
  FStarC_Ident.lid_of_path ["FStar"; "Calc"; i] FStarC_Range_Type.dummyRange
let calc_init_lid : FStarC_Ident.lid= calc_lid "calc_init"
let calc_step_lid : FStarC_Ident.lid= calc_lid "calc_step"
let calc_finish_lid : FStarC_Ident.lid= calc_lid "calc_finish"
let calc_push_impl_lid : FStarC_Ident.lid= calc_lid "calc_push_impl"
let classical_sugar_lid (i : Prims.string) : FStarC_Ident.lid=
  FStarC_Ident.lid_of_path ["FStar"; "Classical"; "Sugar"; i]
    FStarC_Range_Type.dummyRange
let forall_intro_lid : FStarC_Ident.lid= classical_sugar_lid "forall_intro"
let exists_intro_lid : FStarC_Ident.lid= classical_sugar_lid "exists_intro"
let implies_intro_lid : FStarC_Ident.lid= classical_sugar_lid "implies_intro"
let or_intro_left_lid : FStarC_Ident.lid= classical_sugar_lid "or_intro_left"
let or_intro_right_lid : FStarC_Ident.lid=
  classical_sugar_lid "or_intro_right"
let and_intro_lid : FStarC_Ident.lid= classical_sugar_lid "and_intro"
let forall_elim_lid : FStarC_Ident.lid= classical_sugar_lid "forall_elim"
let exists_elim_lid : FStarC_Ident.lid= classical_sugar_lid "exists_elim"
let implies_elim_lid : FStarC_Ident.lid= classical_sugar_lid "implies_elim"
let or_elim_lid : FStarC_Ident.lid= classical_sugar_lid "or_elim"
let and_elim_lid : FStarC_Ident.lid= classical_sugar_lid "and_elim"
let match_returns_def_name : Prims.string=
  Prims.strcat FStarC_Ident.reserved_prefix "_ret_"
let steel_memory_inv_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "Memory"; "inv"]
    FStarC_Range_Type.dummyRange
let steel_new_invariant_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "new_invariant"]
    FStarC_Range_Type.dummyRange
let steel_st_new_invariant_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "ST"; "Util"; "new_invariant"]
    FStarC_Range_Type.dummyRange
let steel_with_invariant_g_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "with_invariant_g"]
    FStarC_Range_Type.dummyRange
let steel_st_with_invariant_g_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "ST"; "Util"; "with_invariant_g"]
    FStarC_Range_Type.dummyRange
let steel_with_invariant_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "Effect"; "Atomic"; "with_invariant"]
    FStarC_Range_Type.dummyRange
let steel_st_with_invariant_lid : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["Steel"; "ST"; "Util"; "with_invariant"]
    FStarC_Range_Type.dummyRange
let fext_lid (s : Prims.string) : FStarC_Ident.lident=
  FStarC_Ident.lid_of_path ["FStar"; "FunctionalExtensionality"; s]
    FStarC_Range_Type.dummyRange
let fext_on_domain_lid : FStarC_Ident.lident= fext_lid "on_domain"
let fext_on_dom_lid : FStarC_Ident.lident= fext_lid "on_dom"
let fext_on_domain_g_lid : FStarC_Ident.lident= fext_lid "on_domain_g"
let fext_on_dom_g_lid : FStarC_Ident.lident= fext_lid "on_dom_g"
let sealed_lid : FStarC_Ident.lident= p2l ["FStar"; "Sealed"; "sealed"]
let seal_lid : FStarC_Ident.lident= p2l ["FStar"; "Sealed"; "seal"]
let unseal_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Tactics"; "Unseal"; "unseal"]
let map_seal_lid : FStarC_Ident.lident= p2l ["FStar"; "Sealed"; "map_seal"]
let bind_seal_lid : FStarC_Ident.lident= p2l ["FStar"; "Sealed"; "bind_seal"]
let tref_lid : FStarC_Ident.lident=
  p2l ["FStar"; "Stubs"; "Tactics"; "Types"; "tref"]
let document_lid : FStarC_Ident.lident= p2l ["FStar"; "Pprint"; "document"]
let issue_lid : FStarC_Ident.lident= p2l ["FStar"; "Issue"; "issue"]
let extract_as_impure_effect_lid : FStarC_Ident.lident=
  attr "extract_as_impure_effect"

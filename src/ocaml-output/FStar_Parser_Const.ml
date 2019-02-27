open Prims
let (p2l : FStar_Ident.path -> FStar_Ident.lident) =
  fun l  -> FStar_Ident.lid_of_path l FStar_Range.dummyRange 
let (pconst : Prims.string -> FStar_Ident.lident) =
  fun s  -> p2l ["Prims"; s] 
let (psconst : Prims.string -> FStar_Ident.lident) =
  fun s  -> p2l ["FStar"; "Pervasives"; s] 
let (psnconst : Prims.string -> FStar_Ident.lident) =
  fun s  -> p2l ["FStar"; "Pervasives"; "Native"; s] 
let (prims_lid : FStar_Ident.lident) = p2l ["Prims"] 
let (pervasives_native_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "Native"] 
let (pervasives_lid : FStar_Ident.lident) = p2l ["FStar"; "Pervasives"] 
let (fstar_ns_lid : FStar_Ident.lident) = p2l ["FStar"] 
let (bool_lid : FStar_Ident.lident) = pconst "bool" 
let (unit_lid : FStar_Ident.lident) = pconst "unit" 
let (squash_lid : FStar_Ident.lident) = pconst "squash" 
let (auto_squash_lid : FStar_Ident.lident) = pconst "auto_squash" 
let (string_lid : FStar_Ident.lident) = pconst "string" 
let (bytes_lid : FStar_Ident.lident) = pconst "bytes" 
let (int_lid : FStar_Ident.lident) = pconst "int" 
let (exn_lid : FStar_Ident.lident) = pconst "exn" 
let (list_lid : FStar_Ident.lident) = pconst "list" 
let (eqtype_lid : FStar_Ident.lident) = pconst "eqtype" 
let (option_lid : FStar_Ident.lident) = psnconst "option" 
let (either_lid : FStar_Ident.lident) = psconst "either" 
let (pattern_lid : FStar_Ident.lident) = pconst "pattern" 
let (precedes_lid : FStar_Ident.lident) = pconst "precedes" 
let (lex_t_lid : FStar_Ident.lident) = pconst "lex_t" 
let (lexcons_lid : FStar_Ident.lident) = pconst "LexCons" 
let (lextop_lid : FStar_Ident.lident) = pconst "LexTop" 
let (smtpat_lid : FStar_Ident.lident) = pconst "smt_pat" 
let (smtpatOr_lid : FStar_Ident.lident) = pconst "smt_pat_or" 
let (monadic_lid : FStar_Ident.lident) = pconst "M" 
let (spinoff_lid : FStar_Ident.lident) = pconst "spinoff" 
let (inl_lid : FStar_Ident.lident) = psconst "Inl" 
let (inr_lid : FStar_Ident.lident) = psconst "Inr" 
let (int8_lid : FStar_Ident.lident) = p2l ["FStar"; "Int8"; "t"] 
let (uint8_lid : FStar_Ident.lident) = p2l ["FStar"; "UInt8"; "t"] 
let (int16_lid : FStar_Ident.lident) = p2l ["FStar"; "Int16"; "t"] 
let (uint16_lid : FStar_Ident.lident) = p2l ["FStar"; "UInt16"; "t"] 
let (int32_lid : FStar_Ident.lident) = p2l ["FStar"; "Int32"; "t"] 
let (uint32_lid : FStar_Ident.lident) = p2l ["FStar"; "UInt32"; "t"] 
let (int64_lid : FStar_Ident.lident) = p2l ["FStar"; "Int64"; "t"] 
let (uint64_lid : FStar_Ident.lident) = p2l ["FStar"; "UInt64"; "t"] 
let (salloc_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"; "salloc"] 
let (swrite_lid : FStar_Ident.lident) =
  p2l ["FStar"; "ST"; "op_Colon_Equals"] 
let (sread_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"; "op_Bang"] 
let (max_lid : FStar_Ident.lident) = p2l ["max"] 
let (real_lid : FStar_Ident.lident) = p2l ["FStar"; "Real"; "real"] 
let (float_lid : FStar_Ident.lident) = p2l ["FStar"; "Float"; "float"] 
let (char_lid : FStar_Ident.lident) = p2l ["FStar"; "Char"; "char"] 
let (heap_lid : FStar_Ident.lident) = p2l ["FStar"; "Heap"; "heap"] 
let (logical_lid : FStar_Ident.lident) = pconst "logical" 
let (true_lid : FStar_Ident.lident) = pconst "l_True" 
let (false_lid : FStar_Ident.lident) = pconst "l_False" 
let (and_lid : FStar_Ident.lident) = pconst "l_and" 
let (or_lid : FStar_Ident.lident) = pconst "l_or" 
let (not_lid : FStar_Ident.lident) = pconst "l_not" 
let (imp_lid : FStar_Ident.lident) = pconst "l_imp" 
let (iff_lid : FStar_Ident.lident) = pconst "l_iff" 
let (ite_lid : FStar_Ident.lident) = pconst "l_ITE" 
let (exists_lid : FStar_Ident.lident) = pconst "l_Exists" 
let (forall_lid : FStar_Ident.lident) = pconst "l_Forall" 
let (haseq_lid : FStar_Ident.lident) = pconst "hasEq" 
let (b2t_lid : FStar_Ident.lident) = pconst "b2t" 
let (admit_lid : FStar_Ident.lident) = pconst "admit" 
let (magic_lid : FStar_Ident.lident) = pconst "magic" 
let (has_type_lid : FStar_Ident.lident) = pconst "has_type" 
let (c_true_lid : FStar_Ident.lident) = pconst "c_True" 
let (c_false_lid : FStar_Ident.lident) = pconst "c_False" 
let (c_and_lid : FStar_Ident.lident) = pconst "c_and" 
let (c_or_lid : FStar_Ident.lident) = pconst "c_or" 
let (dtuple2_lid : FStar_Ident.lident) = pconst "dtuple2" 
let (eq2_lid : FStar_Ident.lident) = pconst "eq2" 
let (eq3_lid : FStar_Ident.lident) = pconst "eq3" 
let (c_eq2_lid : FStar_Ident.lident) = pconst "equals" 
let (c_eq3_lid : FStar_Ident.lident) = pconst "h_equals" 
let (cons_lid : FStar_Ident.lident) = pconst "Cons" 
let (nil_lid : FStar_Ident.lident) = pconst "Nil" 
let (some_lid : FStar_Ident.lident) = psnconst "Some" 
let (none_lid : FStar_Ident.lident) = psnconst "None" 
let (assume_lid : FStar_Ident.lident) = pconst "_assume" 
let (assert_lid : FStar_Ident.lident) = pconst "_assert" 
let (assert_norm_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "assert_norm"] 
let (list_append_lid : FStar_Ident.lident) = p2l ["FStar"; "List"; "append"] 
let (list_tot_append_lid : FStar_Ident.lident) =
  p2l ["FStar"; "List"; "Tot"; "Base"; "append"] 
let (s2l : Prims.string -> FStar_Ident.lident) =
  fun n1  -> p2l ["FStar"; "String"; n1] 
let (string_list_of_string_lid : FStar_Ident.lident) = s2l "list_of_string" 
let (string_string_of_list_lid : FStar_Ident.lident) = s2l "string_of_list" 
let (string_make_lid : FStar_Ident.lident) = s2l "make" 
let (string_split_lid : FStar_Ident.lident) = s2l "split" 
let (string_concat_lid : FStar_Ident.lident) = s2l "concat" 
let (string_compare_lid : FStar_Ident.lident) = s2l "compare" 
let (string_lowercase_lid : FStar_Ident.lident) = s2l "lowercase" 
let (string_uppercase_lid : FStar_Ident.lident) = s2l "uppercase" 
let (string_index_lid : FStar_Ident.lident) = s2l "index" 
let (string_index_of_lid : FStar_Ident.lident) = s2l "index_of" 
let (string_sub_lid : FStar_Ident.lident) = s2l "sub" 
let (prims_strcat_lid : FStar_Ident.lident) = pconst "strcat" 
let (prims_op_Hat_lid : FStar_Ident.lident) = pconst "op_Hat" 
let (let_in_typ : FStar_Ident.lident) = p2l ["Prims"; "Let"] 
let (string_of_int_lid : FStar_Ident.lident) = p2l ["Prims"; "string_of_int"] 
let (string_of_bool_lid : FStar_Ident.lident) =
  p2l ["Prims"; "string_of_bool"] 
let (string_compare : FStar_Ident.lident) =
  p2l ["FStar"; "String"; "compare"] 
let (order_lid : FStar_Ident.lident) = p2l ["FStar"; "Order"; "order"] 
let (op_Eq : FStar_Ident.lident) = pconst "op_Equality" 
let (op_notEq : FStar_Ident.lident) = pconst "op_disEquality" 
let (op_LT : FStar_Ident.lident) = pconst "op_LessThan" 
let (op_LTE : FStar_Ident.lident) = pconst "op_LessThanOrEqual" 
let (op_GT : FStar_Ident.lident) = pconst "op_GreaterThan" 
let (op_GTE : FStar_Ident.lident) = pconst "op_GreaterThanOrEqual" 
let (op_Subtraction : FStar_Ident.lident) = pconst "op_Subtraction" 
let (op_Minus : FStar_Ident.lident) = pconst "op_Minus" 
let (op_Addition : FStar_Ident.lident) = pconst "op_Addition" 
let (op_Multiply : FStar_Ident.lident) = pconst "op_Multiply" 
let (op_Division : FStar_Ident.lident) = pconst "op_Division" 
let (op_Modulus : FStar_Ident.lident) = pconst "op_Modulus" 
let (op_And : FStar_Ident.lident) = pconst "op_AmpAmp" 
let (op_Or : FStar_Ident.lident) = pconst "op_BarBar" 
let (op_Negation : FStar_Ident.lident) = pconst "op_Negation" 
let (real_const : Prims.string -> FStar_Ident.lident) =
  fun s  -> p2l ["FStar"; "Real"; s] 
let (real_op_LT : FStar_Ident.lident) = real_const "op_Less_Dot" 
let (real_op_LTE : FStar_Ident.lident) = real_const "op_Less_Equals_Dot" 
let (real_op_GT : FStar_Ident.lident) = real_const "op_Greater_Dot" 
let (real_op_GTE : FStar_Ident.lident) = real_const "op_Greater_Equals_Dot" 
let (real_op_Subtraction : FStar_Ident.lident) =
  real_const "op_Subtraction_Dot" 
let (real_op_Addition : FStar_Ident.lident) = real_const "op_Plus_Dot" 
let (real_op_Multiply : FStar_Ident.lident) = real_const "op_Star_Dot" 
let (real_op_Division : FStar_Ident.lident) = real_const "op_Slash_Dot" 
let (real_of_int : FStar_Ident.lident) = real_const "of_int" 
let (bvconst : Prims.string -> FStar_Ident.lident) =
  fun s  -> p2l ["FStar"; "BV"; s] 
let (bv_t_lid : FStar_Ident.lident) = bvconst "bv_t" 
let (nat_to_bv_lid : FStar_Ident.lident) = bvconst "int2bv" 
let (bv_to_nat_lid : FStar_Ident.lident) = bvconst "bv2int" 
let (bv_and_lid : FStar_Ident.lident) = bvconst "bvand" 
let (bv_xor_lid : FStar_Ident.lident) = bvconst "bvxor" 
let (bv_or_lid : FStar_Ident.lident) = bvconst "bvor" 
let (bv_add_lid : FStar_Ident.lident) = bvconst "bvadd" 
let (bv_sub_lid : FStar_Ident.lident) = bvconst "bvsub" 
let (bv_shift_left_lid : FStar_Ident.lident) = bvconst "bvshl" 
let (bv_shift_right_lid : FStar_Ident.lident) = bvconst "bvshr" 
let (bv_udiv_lid : FStar_Ident.lident) = bvconst "bvdiv" 
let (bv_mod_lid : FStar_Ident.lident) = bvconst "bvmod" 
let (bv_mul_lid : FStar_Ident.lident) = bvconst "bvmul" 
let (bv_ult_lid : FStar_Ident.lident) = bvconst "bvult" 
let (bv_uext_lid : FStar_Ident.lident) = bvconst "bv_uext" 
let (array_lid : FStar_Ident.lident) = p2l ["FStar"; "Array"; "array"] 
let (array_mk_array_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Array"; "mk_array"] 
let (st_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"] 
let (write_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"; "write"] 
let (read_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"; "read"] 
let (alloc_lid : FStar_Ident.lident) = p2l ["FStar"; "ST"; "alloc"] 
let (op_ColonEq : FStar_Ident.lident) =
  p2l ["FStar"; "ST"; "op_Colon_Equals"] 
let (ref_lid : FStar_Ident.lident) = p2l ["FStar"; "Heap"; "ref"] 
let (heap_addr_of_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Heap"; "addr_of"] 
let (set_empty : FStar_Ident.lident) = p2l ["FStar"; "Set"; "empty"] 
let (set_singleton : FStar_Ident.lident) = p2l ["FStar"; "Set"; "singleton"] 
let (set_union : FStar_Ident.lident) = p2l ["FStar"; "Set"; "union"] 
let (fstar_hyperheap_lid : FStar_Ident.lident) = p2l ["FStar"; "HyperHeap"] 
let (rref_lid : FStar_Ident.lident) = p2l ["FStar"; "HyperHeap"; "rref"] 
let (erased_lid : FStar_Ident.lident) = p2l ["FStar"; "Ghost"; "erased"] 
let (effect_PURE_lid : FStar_Ident.lident) = pconst "PURE" 
let (effect_Pure_lid : FStar_Ident.lident) = pconst "Pure" 
let (effect_Tot_lid : FStar_Ident.lident) = pconst "Tot" 
let (effect_Lemma_lid : FStar_Ident.lident) = pconst "Lemma" 
let (effect_GTot_lid : FStar_Ident.lident) = pconst "GTot" 
let (effect_GHOST_lid : FStar_Ident.lident) = pconst "GHOST" 
let (effect_Ghost_lid : FStar_Ident.lident) = pconst "Ghost" 
let (effect_DIV_lid : FStar_Ident.lident) = psconst "DIV" 
let (effect_Div_lid : FStar_Ident.lident) = psconst "Div" 
let (effect_Dv_lid : FStar_Ident.lident) = psconst "Dv" 
let (all_lid : FStar_Ident.lident) = p2l ["FStar"; "All"] 
let (effect_ALL_lid : FStar_Ident.lident) = p2l ["FStar"; "All"; "ALL"] 
let (effect_ML_lid : FStar_Ident.lident) = p2l ["FStar"; "All"; "ML"] 
let (failwith_lid : FStar_Ident.lident) = p2l ["FStar"; "All"; "failwith"] 
let (pipe_right_lid : FStar_Ident.lident) =
  p2l ["FStar"; "All"; "pipe_right"] 
let (pipe_left_lid : FStar_Ident.lident) = p2l ["FStar"; "All"; "pipe_left"] 
let (try_with_lid : FStar_Ident.lident) = p2l ["FStar"; "All"; "try_with"] 
let (as_requires : FStar_Ident.lident) = pconst "as_requires" 
let (as_ensures : FStar_Ident.lident) = pconst "as_ensures" 
let (decreases_lid : FStar_Ident.lident) = pconst "decreases" 
let (term_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Reflection"; "Types"; "term"] 
let (decls_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Reflection"; "Data"; "decls"] 
let (ctx_uvar_and_subst_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Reflection"; "Types"; "ctx_uvar_and_subst"] 
let (range_lid : FStar_Ident.lident) = pconst "range" 
let (range_of_lid : FStar_Ident.lident) = pconst "range_of" 
let (labeled_lid : FStar_Ident.lident) = pconst "labeled" 
let (range_0 : FStar_Ident.lident) = pconst "range_0" 
let (guard_free : FStar_Ident.lident) = pconst "guard_free" 
let (inversion_lid : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "inversion"] 
let (with_type_lid : FStar_Ident.lident) = psconst "with_type" 
let (normalize : FStar_Ident.lident) = psconst "normalize" 
let (normalize_term : FStar_Ident.lident) = psconst "normalize_term" 
let (norm : FStar_Ident.lident) = psconst "norm" 
let (steps_simpl : FStar_Ident.lident) = psconst "simplify" 
let (steps_weak : FStar_Ident.lident) = psconst "weak" 
let (steps_hnf : FStar_Ident.lident) = psconst "hnf" 
let (steps_primops : FStar_Ident.lident) = psconst "primops" 
let (steps_zeta : FStar_Ident.lident) = psconst "zeta" 
let (steps_iota : FStar_Ident.lident) = psconst "iota" 
let (steps_delta : FStar_Ident.lident) = psconst "delta" 
let (steps_reify : FStar_Ident.lident) = psconst "reify_" 
let (steps_unfoldonly : FStar_Ident.lident) = psconst "delta_only" 
let (steps_unfoldfully : FStar_Ident.lident) = psconst "delta_fully" 
let (steps_unfoldattr : FStar_Ident.lident) = psconst "delta_attr" 
let (steps_nbe : FStar_Ident.lident) = psconst "nbe" 
let (deprecated_attr : FStar_Ident.lident) = pconst "deprecated" 
let (inline_let_attr : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "inline_let"] 
let (plugin_attr : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "plugin"] 
let (tcnorm_attr : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "tcnorm"] 
let (dm4f_bind_range_attr : FStar_Ident.lident) =
  p2l ["FStar"; "Pervasives"; "dm4f_bind_range"] 
let (must_erase_for_extraction_attr : FStar_Ident.lident) =
  psconst "must_erase_for_extraction" 
let (fail_attr : FStar_Ident.lident) = psconst "expect_failure" 
let (fail_lax_attr : FStar_Ident.lident) = psconst "expect_lax_failure" 
let (tcdecltime_attr : FStar_Ident.lident) = psconst "tcdecltime" 
let (assume_strictly_positive_attr_lid : FStar_Ident.lident) =
  psconst "assume_strictly_positive" 
let (unifier_hint_injective_lid : FStar_Ident.lident) =
  psconst "unifier_hint_injective" 
let (postprocess_with : FStar_Ident.lident) =
  p2l ["FStar"; "Tactics"; "Effect"; "postprocess_with"] 
let (postprocess_extr_with : FStar_Ident.lident) =
  p2l ["FStar"; "Tactics"; "Effect"; "postprocess_for_extraction_with"] 
let (gen_reset : ((unit -> Prims.int) * (unit -> unit))) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0")  in
  let gen1 uu____37610 = FStar_Util.incr x; FStar_Util.read x  in
  let reset uu____37673 = FStar_Util.write x (Prims.parse_int "0")  in
  (gen1, reset) 
let (next_id : unit -> Prims.int) = FStar_Pervasives_Native.fst gen_reset 
let (sli : FStar_Ident.lident -> Prims.string) =
  fun l  ->
    let uu____37726 = FStar_Options.print_real_names ()  in
    if uu____37726
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
  
let (const_to_string : FStar_Const.sconst -> Prims.string) =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_real r -> FStar_String.op_Hat r "R"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (s,uu____37755) ->
        FStar_Util.format1 "\"%s\"" s
    | FStar_Const.Const_bytearray uu____37759 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____37768) -> x1
    | FStar_Const.Const_char c ->
        let uu____37785 =
          FStar_String.op_Hat (FStar_Util.string_of_char c) "'"  in
        FStar_String.op_Hat "'" uu____37785
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_range_of  -> "range_of"
    | FStar_Const.Const_set_range_of  -> "set_range_of"
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____37794 = sli l  in
        FStar_Util.format1 "[[%s.reflect]]" uu____37794
  
let (mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun r  ->
      let t =
        let uu____37812 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "tuple%s" uu____37812  in
      let uu____37815 = psnconst t  in
      FStar_Ident.set_lid_range uu____37815 r
  
let (lid_tuple2 : FStar_Ident.lident) =
  mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange 
let (is_tuple_constructor_string : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Native.tuple" 
let (is_tuple_constructor_lid : FStar_Ident.ident -> Prims.bool) =
  fun lid  ->
    let uu____37836 = FStar_Ident.text_of_id lid  in
    is_tuple_constructor_string uu____37836
  
let (mk_tuple_data_lid :
  Prims.int -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun r  ->
      let t =
        let uu____37853 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mktuple%s" uu____37853  in
      let uu____37856 = psnconst t  in
      FStar_Ident.set_lid_range uu____37856 r
  
let (lid_Mktuple2 : FStar_Ident.lident) =
  mk_tuple_data_lid (Prims.parse_int "2") FStar_Range.dummyRange 
let (is_tuple_datacon_string : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Native.Mktuple" 
let (is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool) =
  fun f  ->
    fun n1  ->
      let uu____37884 = mk_tuple_data_lid n1 FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f uu____37884
  
let (is_tuple_data_lid' : FStar_Ident.lident -> Prims.bool) =
  fun f  -> is_tuple_datacon_string f.FStar_Ident.str 
let (mod_prefix_dtuple : Prims.int -> Prims.string -> FStar_Ident.lident) =
  fun n1  -> if n1 = (Prims.parse_int "2") then pconst else psconst 
let (mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun r  ->
      let t =
        let uu____37932 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "dtuple%s" uu____37932  in
      let uu____37935 =
        let uu____37936 = mod_prefix_dtuple n1  in uu____37936 t  in
      FStar_Ident.set_lid_range uu____37935 r
  
let (is_dtuple_constructor_string : Prims.string -> Prims.bool) =
  fun s  ->
    (s = "Prims.dtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.dtuple")
  
let (is_dtuple_constructor_lid : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> is_dtuple_constructor_string lid.FStar_Ident.str 
let (mk_dtuple_data_lid :
  Prims.int -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun r  ->
      let t =
        let uu____37977 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mkdtuple%s" uu____37977  in
      let uu____37980 =
        let uu____37981 = mod_prefix_dtuple n1  in uu____37981 t  in
      FStar_Ident.set_lid_range uu____37980 r
  
let (is_dtuple_datacon_string : Prims.string -> Prims.bool) =
  fun s  ->
    (s = "Prims.Mkdtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.Mkdtuple")
  
let (is_dtuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool) =
  fun f  ->
    fun n1  ->
      let uu____38014 = mk_dtuple_data_lid n1 FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f uu____38014
  
let (is_dtuple_data_lid' : FStar_Ident.lident -> Prims.bool) =
  fun f  ->
    let uu____38022 = FStar_Ident.text_of_lid f  in
    is_dtuple_datacon_string uu____38022
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let (fstar_tactics_lid' : Prims.string Prims.list -> FStar_Ident.lid) =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] s)
      FStar_Range.dummyRange
  
let (fstar_tactics_lid : Prims.string -> FStar_Ident.lid) =
  fun s  -> fstar_tactics_lid' [s] 
let (tactic_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Effect"; "tactic"] 
let (mk_class_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Typeclasses"; "mk_class"] 
let (tcresolve_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Typeclasses"; "tcresolve"] 
let (tcinstance_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Typeclasses"; "tcinstance"] 
let (effect_TAC_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Effect"; "TAC"] 
let (effect_Tac_lid : FStar_Ident.lid) = fstar_tactics_lid' ["Effect"; "Tac"] 
let (by_tactic_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Effect"; "with_tactic"] 
let (synth_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Effect"; "synth_by_tactic"] 
let (assert_by_tactic_lid : FStar_Ident.lid) =
  fstar_tactics_lid' ["Effect"; "assert_by_tactic"] 
let (fstar_syntax_syntax_term : FStar_Ident.lident) =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.term" 
let (binder_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Types"; "binder"]
    FStar_Range.dummyRange
  
let (binders_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Types"; "binders"]
    FStar_Range.dummyRange
  
let (bv_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Types"; "bv"]
    FStar_Range.dummyRange
  
let (fv_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Types"; "fv"]
    FStar_Range.dummyRange
  
let (norm_step_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Syntax"; "Embeddings"; "norm_step"]
    FStar_Range.dummyRange
  
let (calc_lid : Prims.string -> FStar_Ident.lid) =
  fun i  ->
    FStar_Ident.lid_of_path ["FStar"; "Calc"; i] FStar_Range.dummyRange
  
let (calc_init_lid : FStar_Ident.lid) = calc_lid "calc_init" 
let (calc_step_lid : FStar_Ident.lid) = calc_lid "calc_step" 
let (calc_finish_lid : FStar_Ident.lid) = calc_lid "calc_finish" 
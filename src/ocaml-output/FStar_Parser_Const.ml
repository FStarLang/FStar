open Prims
let p2l: Prims.string Prims.list -> FStar_Ident.lident =
  fun l  -> FStar_Ident.lid_of_path l FStar_Range.dummyRange
let pconst: Prims.string -> FStar_Ident.lident = fun s  -> p2l ["Prims"; s]
let psconst: Prims.string -> FStar_Ident.lident =
  fun s  -> p2l ["FStar"; "Pervasives"; s]
let psnconst: Prims.string -> FStar_Ident.lident =
  fun s  -> p2l ["FStar"; "Pervasives"; "Native"; s]
let prims_lid: FStar_Ident.lident = p2l ["Prims"]
let pervasives_lid: FStar_Ident.lident = p2l ["FStar"; "Pervasives"]
let fstar_ns_lid: FStar_Ident.lident = p2l ["FStar"]
let bool_lid: FStar_Ident.lident = pconst "bool"
let unit_lid: FStar_Ident.lident = pconst "unit"
let squash_lid: FStar_Ident.lident = pconst "squash"
let string_lid: FStar_Ident.lident = pconst "string"
let bytes_lid: FStar_Ident.lident = pconst "bytes"
let int_lid: FStar_Ident.lident = pconst "int"
let exn_lid: FStar_Ident.lident = pconst "exn"
let list_lid: FStar_Ident.lident = pconst "list"
let option_lid: FStar_Ident.lident = psnconst "option"
let either_lid: FStar_Ident.lident = psconst "either"
let pattern_lid: FStar_Ident.lident = pconst "pattern"
let precedes_lid: FStar_Ident.lident = pconst "precedes"
let lex_t_lid: FStar_Ident.lident = pconst "lex_t"
let lexcons_lid: FStar_Ident.lident = pconst "LexCons"
let lextop_lid: FStar_Ident.lident = pconst "LexTop"
let smtpat_lid: FStar_Ident.lident = pconst "smt_pat"
let smtpatOr_lid: FStar_Ident.lident = pconst "smt_pat_or"
let monadic_lid: FStar_Ident.lident = pconst "M"
let spinoff_lid: FStar_Ident.lident = pconst "spinoff"
let int8_lid: FStar_Ident.lident = p2l ["FStar"; "Int8"; "t"]
let uint8_lid: FStar_Ident.lident = p2l ["FStar"; "UInt8"; "t"]
let int16_lid: FStar_Ident.lident = p2l ["FStar"; "Int16"; "t"]
let uint16_lid: FStar_Ident.lident = p2l ["FStar"; "UInt16"; "t"]
let int32_lid: FStar_Ident.lident = p2l ["FStar"; "Int32"; "t"]
let uint32_lid: FStar_Ident.lident = p2l ["FStar"; "UInt32"; "t"]
let int64_lid: FStar_Ident.lident = p2l ["FStar"; "Int64"; "t"]
let uint64_lid: FStar_Ident.lident = p2l ["FStar"; "UInt64"; "t"]
let salloc_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "salloc"]
let swrite_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "op_Colon_Equals"]
let sread_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "op_Bang"]
let max_lid: FStar_Ident.lident = p2l ["max"]
let float_lid: FStar_Ident.lident = p2l ["FStar"; "Float"; "float"]
let char_lid: FStar_Ident.lident = p2l ["FStar"; "Char"; "char"]
let heap_lid: FStar_Ident.lident = p2l ["FStar"; "Heap"; "heap"]
let true_lid: FStar_Ident.lident = pconst "l_True"
let false_lid: FStar_Ident.lident = pconst "l_False"
let and_lid: FStar_Ident.lident = pconst "l_and"
let or_lid: FStar_Ident.lident = pconst "l_or"
let not_lid: FStar_Ident.lident = pconst "l_not"
let imp_lid: FStar_Ident.lident = pconst "l_imp"
let iff_lid: FStar_Ident.lident = pconst "l_iff"
let ite_lid: FStar_Ident.lident = pconst "l_ITE"
let exists_lid: FStar_Ident.lident = pconst "l_Exists"
let forall_lid: FStar_Ident.lident = pconst "l_Forall"
let haseq_lid: FStar_Ident.lident = pconst "hasEq"
let b2t_lid: FStar_Ident.lident = pconst "b2t"
let admit_lid: FStar_Ident.lident = pconst "admit"
let magic_lid: FStar_Ident.lident = pconst "magic"
let has_type_lid: FStar_Ident.lident = pconst "has_type"
let c_true_lid: FStar_Ident.lident = pconst "c_True"
let c_false_lid: FStar_Ident.lident = pconst "c_False"
let c_and_lid: FStar_Ident.lident = pconst "c_and"
let c_or_lid: FStar_Ident.lident = pconst "c_or"
let dtuple2_lid: FStar_Ident.lident = pconst "dtuple2"
let eq2_lid: FStar_Ident.lident = pconst "eq2"
let eq3_lid: FStar_Ident.lident = pconst "eq3"
let c_eq2_lid: FStar_Ident.lident = pconst "equals"
let c_eq3_lid: FStar_Ident.lident = pconst "h_equals"
let cons_lid: FStar_Ident.lident = pconst "Cons"
let nil_lid: FStar_Ident.lident = pconst "Nil"
let some_lid: FStar_Ident.lident = psnconst "Some"
let none_lid: FStar_Ident.lident = psnconst "None"
let assume_lid: FStar_Ident.lident = pconst "_assume"
let assert_lid: FStar_Ident.lident = pconst "_assert"
let list_append_lid: FStar_Ident.lident = p2l ["FStar"; "List"; "append"]
let list_tot_append_lid: FStar_Ident.lident =
  p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let strcat_lid: FStar_Ident.lident = p2l ["Prims"; "strcat"]
let strcat_lid': FStar_Ident.lident = p2l ["FStar"; "String"; "strcat"]
let let_in_typ: FStar_Ident.lident = p2l ["Prims"; "Let"]
let string_of_int_lid: FStar_Ident.lident = p2l ["Prims"; "string_of_int"]
let string_of_bool_lid: FStar_Ident.lident = p2l ["Prims"; "string_of_bool"]
let string_compare: FStar_Ident.lident = p2l ["FStar"; "String"; "compare"]
let op_Eq: FStar_Ident.lident = pconst "op_Equality"
let op_notEq: FStar_Ident.lident = pconst "op_disEquality"
let op_LT: FStar_Ident.lident = pconst "op_LessThan"
let op_LTE: FStar_Ident.lident = pconst "op_LessThanOrEqual"
let op_GT: FStar_Ident.lident = pconst "op_GreaterThan"
let op_GTE: FStar_Ident.lident = pconst "op_GreaterThanOrEqual"
let op_Subtraction: FStar_Ident.lident = pconst "op_Subtraction"
let op_Minus: FStar_Ident.lident = pconst "op_Minus"
let op_Addition: FStar_Ident.lident = pconst "op_Addition"
let op_Multiply: FStar_Ident.lident = pconst "op_Multiply"
let op_Division: FStar_Ident.lident = pconst "op_Division"
let op_Modulus: FStar_Ident.lident = pconst "op_Modulus"
let op_And: FStar_Ident.lident = pconst "op_AmpAmp"
let op_Or: FStar_Ident.lident = pconst "op_BarBar"
let op_Negation: FStar_Ident.lident = pconst "op_Negation"
let bvconst: Prims.string -> FStar_Ident.lident =
  fun s  -> p2l ["FStar"; "BV"; s]
let bv_t_lid: FStar_Ident.lident = bvconst "bv_t"
let nat_to_bv_lid: FStar_Ident.lident = bvconst "int2bv"
let bv_to_nat_lid: FStar_Ident.lident = bvconst "bv2int"
let bv_and_lid: FStar_Ident.lident = bvconst "bvand"
let bv_xor_lid: FStar_Ident.lident = bvconst "bvxor"
let bv_or_lid: FStar_Ident.lident = bvconst "bvor"
let bv_shift_left_lid: FStar_Ident.lident = bvconst "bvshl"
let bv_shift_right_lid: FStar_Ident.lident = bvconst "bvshr"
let bv_udiv_lid: FStar_Ident.lident = bvconst "bvdiv"
let bv_mod_lid: FStar_Ident.lident = bvconst "bvmod"
let bv_mul_lid: FStar_Ident.lident = bvconst "bvmul"
let bv_ult_lid: FStar_Ident.lident = bvconst "bvult"
let bv_uext_lid: FStar_Ident.lident = bvconst "bv_uext"
let array_lid: FStar_Ident.lident = p2l ["FStar"; "Array"; "array"]
let array_mk_array_lid: FStar_Ident.lident =
  p2l ["FStar"; "Array"; "mk_array"]
let st_lid: FStar_Ident.lident = p2l ["FStar"; "ST"]
let write_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "write"]
let read_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "read"]
let alloc_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "alloc"]
let op_ColonEq: FStar_Ident.lident = p2l ["FStar"; "ST"; "op_Colon_Equals"]
let ref_lid: FStar_Ident.lident = p2l ["FStar"; "Heap"; "ref"]
let heap_addr_of_lid: FStar_Ident.lident = p2l ["FStar"; "Heap"; "addr_of"]
let set_empty: FStar_Ident.lident = p2l ["FStar"; "Set"; "empty"]
let set_singleton: FStar_Ident.lident = p2l ["FStar"; "Set"; "singleton"]
let set_union: FStar_Ident.lident = p2l ["FStar"; "Set"; "union"]
let fstar_hyperheap_lid: FStar_Ident.lident = p2l ["FStar"; "HyperHeap"]
let rref_lid: FStar_Ident.lident = p2l ["FStar"; "HyperHeap"; "rref"]
let erased_lid: FStar_Ident.lident = p2l ["FStar"; "Ghost"; "erased"]
let effect_PURE_lid: FStar_Ident.lident = pconst "PURE"
let effect_Pure_lid: FStar_Ident.lident = pconst "Pure"
let effect_Tot_lid: FStar_Ident.lident = pconst "Tot"
let effect_Lemma_lid: FStar_Ident.lident = pconst "Lemma"
let effect_GTot_lid: FStar_Ident.lident = pconst "GTot"
let effect_GHOST_lid: FStar_Ident.lident = pconst "GHOST"
let effect_Ghost_lid: FStar_Ident.lident = pconst "Ghost"
let effect_DIV_lid: FStar_Ident.lident = pconst "DIV"
let all_lid: FStar_Ident.lident = p2l ["FStar"; "All"]
let effect_ALL_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "ALL"]
let effect_ML_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "ML"]
let failwith_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "failwith"]
let pipe_right_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "pipe_right"]
let pipe_left_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "pipe_left"]
let try_with_lid: FStar_Ident.lident = p2l ["FStar"; "All"; "try_with"]
let as_requires: FStar_Ident.lident = pconst "as_requires"
let as_ensures: FStar_Ident.lident = pconst "as_ensures"
let decreases_lid: FStar_Ident.lident = pconst "decreases"
let term_lid: FStar_Ident.lident =
  p2l ["FStar"; "Reflection"; "Types"; "term"]
let range_lid: FStar_Ident.lident = pconst "range"
let range_of_lid: FStar_Ident.lident = pconst "range_of"
let labeled_lid: FStar_Ident.lident = pconst "labeled"
let range_0: FStar_Ident.lident = pconst "range_0"
let guard_free: FStar_Ident.lident = pconst "guard_free"
let inversion_lid: FStar_Ident.lident =
  p2l ["FStar"; "Pervasives"; "inversion"]
let normalize: FStar_Ident.lident = pconst "normalize"
let normalize_term: FStar_Ident.lident = pconst "normalize_term"
let norm: FStar_Ident.lident = pconst "norm"
let steps_simpl: FStar_Ident.lident = pconst "Simpl"
let steps_weak: FStar_Ident.lident = pconst "Weak"
let steps_hnf: FStar_Ident.lident = pconst "HNF"
let steps_primops: FStar_Ident.lident = pconst "Primops"
let steps_zeta: FStar_Ident.lident = pconst "Zeta"
let steps_iota: FStar_Ident.lident = pconst "Iota"
let steps_delta: FStar_Ident.lident = pconst "Delta"
let steps_unfoldonly: FStar_Ident.lident = pconst "UnfoldOnly"
let gen_reset:
  (Prims.unit -> Prims.int,Prims.unit -> Prims.unit)
    FStar_Pervasives_Native.tuple2
  =
  let x = FStar_Util.mk_ref (Prims.parse_int "0") in
  let gen1 uu____39 = FStar_Util.incr x; FStar_Util.read x in
  let reset uu____79 = FStar_Util.write x (Prims.parse_int "0") in
  (gen1, reset)
let next_id: Prims.unit -> Prims.int = FStar_Pervasives_Native.fst gen_reset
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____109 = FStar_Options.print_real_names () in
    if uu____109
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (s,uu____119) -> FStar_Util.format1 "\"%s\"" s
    | FStar_Const.Const_bytearray uu____120 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____128) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____144 = sli l in
        FStar_Util.format1 "[[%s.reflect]]" uu____144
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____154 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____154 in
      let uu____155 = psnconst t in FStar_Ident.set_lid_range uu____155 r
let lid_tuple2: FStar_Ident.lident =
  mk_tuple_lid (Prims.parse_int "2") FStar_Range.dummyRange
let is_tuple_constructor_string: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Native.tuple"
let is_tuple_constructor_lid: FStar_Ident.ident -> Prims.bool =
  fun lid  -> is_tuple_constructor_string (FStar_Ident.text_of_id lid)
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____173 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____173 in
      let uu____174 = psnconst t in FStar_Ident.set_lid_range uu____174 r
let lid_Mktuple2: FStar_Ident.lident =
  mk_tuple_data_lid (Prims.parse_int "2") FStar_Range.dummyRange
let is_tuple_datacon_string: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Native.Mktuple"
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____187 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____187
let is_tuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> is_tuple_datacon_string f.FStar_Ident.str
let mod_prefix_dtuple: Prims.int -> Prims.string -> FStar_Ident.lident =
  fun n1  -> if n1 = (Prims.parse_int "2") then pconst else psconst
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____212 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____212 in
      let uu____213 = let uu____214 = mod_prefix_dtuple n1 in uu____214 t in
      FStar_Ident.set_lid_range uu____213 r
let is_dtuple_constructor_string: Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.dtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.dtuple")
let is_dtuple_constructor_lid: FStar_Ident.lident -> Prims.bool =
  fun lid  -> is_dtuple_constructor_string lid.FStar_Ident.str
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____234 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____234 in
      let uu____235 = let uu____236 = mod_prefix_dtuple n1 in uu____236 t in
      FStar_Ident.set_lid_range uu____235 r
let is_dtuple_datacon_string: Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.Mkdtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.Mkdtuple")
let is_dtuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____251 = mk_dtuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____251
let is_dtuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> is_dtuple_datacon_string (FStar_Ident.text_of_lid f)
let is_name: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0") in
    FStar_Util.is_upper c
let fstar_tactics_lid': Prims.string Prims.list -> FStar_Ident.lid =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] s)
      FStar_Range.dummyRange
let fstar_tactics_lid: Prims.string -> FStar_Ident.lid =
  fun s  -> fstar_tactics_lid' [s]
let tactic_lid: FStar_Ident.lid = fstar_tactics_lid' ["Effect"; "tactic"]
let u_tac_lid: FStar_Ident.lid = fstar_tactics_lid' ["Effect"; "__tac"]
let tac_effect_lid: FStar_Ident.lid = fstar_tactics_lid "TAC"
let by_tactic_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Effect"; "__by_tactic"]
let synth_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Effect"; "synth_by_tactic"]
let assert_by_tactic_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Effect"; "assert_by_tactic"]
let reify_tactic_lid: FStar_Ident.lid =
  fstar_tactics_lid' ["Effect"; "reify_tactic"]
let quote_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Builtins"; "quote"]
    FStar_Range.dummyRange
let fstar_refl_embed_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Tactics"; "Builtins"; "__embed"]
    FStar_Range.dummyRange
let fstar_syntax_syntax_term: FStar_Ident.lident =
  FStar_Ident.lid_of_str "FStar.Syntax.Syntax.term"
let fstar_reflection_types_binder_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Types"; "binder"]
    FStar_Range.dummyRange
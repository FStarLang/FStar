open Prims
let p2l: Prims.string Prims.list -> FStar_Ident.lident =
  fun l  -> FStar_Ident.lid_of_path l FStar_Range.dummyRange
let pconst: Prims.string -> FStar_Ident.lident = fun s  -> p2l ["Prims"; s]
let psconst: Prims.string -> FStar_Ident.lident =
  fun s  -> p2l ["FStar"; "Pervasives"; s]
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
let option_lid: FStar_Ident.lident = psconst "option"
let either_lid: FStar_Ident.lident = psconst "either"
let pattern_lid: FStar_Ident.lident = pconst "pattern"
let precedes_lid: FStar_Ident.lident = pconst "precedes"
let lex_t_lid: FStar_Ident.lident = pconst "lex_t"
let lexcons_lid: FStar_Ident.lident = pconst "LexCons"
let lextop_lid: FStar_Ident.lident = pconst "LexTop"
let smtpat_lid: FStar_Ident.lident = pconst "SMTPat"
let smtpatT_lid: FStar_Ident.lident = pconst "SMTPatT"
let smtpatOr_lid: FStar_Ident.lident = pconst "SMTPatOr"
let monadic_lid: FStar_Ident.lident = pconst "M"
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
let eq2_lid: FStar_Ident.lident = pconst "eq2"
let eq3_lid: FStar_Ident.lident = pconst "eq3"
let cons_lid: FStar_Ident.lident = pconst "Cons"
let nil_lid: FStar_Ident.lident = pconst "Nil"
let assume_lid: FStar_Ident.lident = pconst "_assume"
let assert_lid: FStar_Ident.lident = pconst "_assert"
let list_append_lid: FStar_Ident.lident = p2l ["FStar"; "List"; "append"]
let list_tot_append_lid: FStar_Ident.lident =
  p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let strcat_lid: FStar_Ident.lident = p2l ["Prims"; "strcat"]
let let_in_typ: FStar_Ident.lident = p2l ["Prims"; "Let"]
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
let array_lid: FStar_Ident.lident = p2l ["FStar"; "Array"; "array"]
let array_mk_array_lid: FStar_Ident.lident =
  p2l ["FStar"; "Array"; "mk_array"]
let st_lid: FStar_Ident.lident = p2l ["FStar"; "ST"]
let write_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "write"]
let read_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "read"]
let alloc_lid: FStar_Ident.lident = p2l ["FStar"; "ST"; "alloc"]
let op_ColonEq: FStar_Ident.lident = p2l ["FStar"; "ST"; "op_Colon_Equals"]
let ref_lid: FStar_Ident.lident = p2l ["FStar"; "Heap"; "ref"]
let heap_ref: FStar_Ident.lident = p2l ["FStar"; "Heap"; "Ref"]
let set_empty: FStar_Ident.lident = p2l ["FStar"; "Set"; "empty"]
let set_singleton: FStar_Ident.lident = p2l ["FStar"; "Set"; "singleton"]
let set_union: FStar_Ident.lident = p2l ["FStar"; "Set"; "union"]
let fstar_hyperheap_lid: FStar_Ident.lident = p2l ["FStar"; "HyperHeap"]
let rref_lid: FStar_Ident.lident = p2l ["FStar"; "HyperHeap"; "rref"]
let tset_empty: FStar_Ident.lident = p2l ["FStar"; "TSet"; "empty"]
let tset_singleton: FStar_Ident.lident = p2l ["FStar"; "TSet"; "singleton"]
let tset_union: FStar_Ident.lident = p2l ["FStar"; "TSet"; "union"]
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
let range_lid: FStar_Ident.lident = pconst "range"
let range_of_lid: FStar_Ident.lident = pconst "range_of"
let labeled_lid: FStar_Ident.lident = pconst "labeled"
let range_0: FStar_Ident.lident = pconst "range_0"
let guard_free: FStar_Ident.lident = pconst "guard_free"
let normalize: FStar_Ident.lident = pconst "normalize"
let normalize_term: FStar_Ident.lident = pconst "normalize_term"
let gen_reset: ((Prims.unit -> Prims.int)* (Prims.unit -> Prims.unit)) =
  let x = FStar_Util.mk_ref (Prims.parse_int "0") in
  let gen1 uu____24 = FStar_Util.incr x; FStar_Util.read x in
  let reset uu____34 = FStar_Util.write x (Prims.parse_int "0") in
  (gen1, reset)
let next_id: Prims.unit -> Prims.int = fst gen_reset
let sli: FStar_Ident.lident -> Prims.string =
  fun l  ->
    let uu____50 = FStar_Options.print_real_names () in
    if uu____50
    then l.FStar_Ident.str
    else (l.FStar_Ident.ident).FStar_Ident.idText
let const_to_string: FStar_Const.sconst -> Prims.string =
  fun x  ->
    match x with
    | FStar_Const.Const_effect  -> "Effect"
    | FStar_Const.Const_unit  -> "()"
    | FStar_Const.Const_bool b -> if b then "true" else "false"
    | FStar_Const.Const_float x1 -> FStar_Util.string_of_float x1
    | FStar_Const.Const_string (bytes,uu____59) ->
        FStar_Util.format1 "\"%s\"" (FStar_Util.string_of_bytes bytes)
    | FStar_Const.Const_bytearray uu____62 -> "<bytearray>"
    | FStar_Const.Const_int (x1,uu____67) -> x1
    | FStar_Const.Const_char c ->
        Prims.strcat "'" (Prims.strcat (FStar_Util.string_of_char c) "'")
    | FStar_Const.Const_range r -> FStar_Range.string_of_range r
    | FStar_Const.Const_reify  -> "reify"
    | FStar_Const.Const_reflect l ->
        let uu____77 = sli l in FStar_Util.format1 "[[%s.reflect]]" uu____77
let mod_prefix_dtuple: Prims.int -> Prims.string -> FStar_Ident.lident =
  fun n1  -> if n1 = (Prims.parse_int "2") then pconst else psconst
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____95 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____95 in
      let uu____96 = psconst t in FStar_Ident.set_lid_range uu____96 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____104 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____104 in
      let uu____105 = let uu____106 = mod_prefix_dtuple n1 in uu____106 t in
      FStar_Ident.set_lid_range uu____105 r
let is_dtuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple"
let is_tuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  ->
    (f.FStar_Ident.nsstr = "FStar.Pervasives") &&
      (FStar_Util.starts_with (f.FStar_Ident.ident).FStar_Ident.idText
         "Mktuple")
let is_name: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0") in
    FStar_Util.is_upper c
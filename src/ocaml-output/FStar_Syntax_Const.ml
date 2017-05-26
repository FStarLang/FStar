open Prims
let mk:
  FStar_Syntax_Syntax.term' ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  = fun t  -> FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange
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
let kunary:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun k  ->
    fun k'  ->
      let uu____25 =
        let uu____26 =
          let uu____34 =
            let uu____36 = FStar_Syntax_Syntax.null_binder k in [uu____36] in
          let uu____37 = FStar_Syntax_Syntax.mk_Total k' in
          (uu____34, uu____37) in
        FStar_Syntax_Syntax.Tm_arrow uu____26 in
      mk uu____25
let kbin:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun k1  ->
    fun k2  ->
      fun k'  ->
        let uu____48 =
          let uu____49 =
            let uu____57 =
              let uu____59 = FStar_Syntax_Syntax.null_binder k1 in
              let uu____60 =
                let uu____62 = FStar_Syntax_Syntax.null_binder k2 in
                [uu____62] in
              uu____59 :: uu____60 in
            let uu____63 = FStar_Syntax_Syntax.mk_Total k' in
            (uu____57, uu____63) in
          FStar_Syntax_Syntax.Tm_arrow uu____49 in
        mk uu____48
let ktern:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term
  =
  fun k1  ->
    fun k2  ->
      fun k3  ->
        fun k'  ->
          let uu____77 =
            let uu____78 =
              let uu____86 =
                let uu____88 = FStar_Syntax_Syntax.null_binder k1 in
                let uu____89 =
                  let uu____91 = FStar_Syntax_Syntax.null_binder k2 in
                  let uu____92 =
                    let uu____94 = FStar_Syntax_Syntax.null_binder k3 in
                    [uu____94] in
                  uu____91 :: uu____92 in
                uu____88 :: uu____89 in
              let uu____95 = FStar_Syntax_Syntax.mk_Total k' in
              (uu____86, uu____95) in
            FStar_Syntax_Syntax.Tm_arrow uu____78 in
          mk uu____77
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
let exp_true_bool: FStar_Syntax_Syntax.term =
  mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
let exp_false_bool: FStar_Syntax_Syntax.term =
  mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
let exp_unit: FStar_Syntax_Syntax.term =
  mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
let exp_int: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (s, None)))
let exp_string: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string
            ((FStar_Util.unicode_of_string s), FStar_Range.dummyRange)))
let cons_lid: FStar_Ident.lident = pconst "Cons"
let nil_lid: FStar_Ident.lident = pconst "Nil"
let some_lid: FStar_Ident.lident = psconst "Some"
let none_lid: FStar_Ident.lident = psconst "None"
let assume_lid: FStar_Ident.lident = pconst "_assume"
let assert_lid: FStar_Ident.lident = pconst "_assert"
let list_append_lid: FStar_Ident.lident = p2l ["FStar"; "List"; "append"]
let list_tot_append_lid: FStar_Ident.lident =
  p2l ["FStar"; "List"; "Tot"; "Base"; "append"]
let strcat_lid: FStar_Ident.lident = p2l ["Prims"; "strcat"]
let let_in_typ: FStar_Ident.lident = p2l ["Prims"; "Let"]
let string_of_int_lid: FStar_Ident.lident = p2l ["Prims"; "string_of_int"]
let string_of_bool_lid: FStar_Ident.lident = p2l ["Prims"; "string_of_bool"]
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
let fstar_tactics_lid: Prims.string -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Tactics"] [s])
      FStar_Range.dummyRange
let tactic_lid: FStar_Ident.lident = fstar_tactics_lid "tactic"
let by_tactic_lid: FStar_Ident.lident = fstar_tactics_lid "by_tactic"
let reify_tactic_lid: FStar_Ident.lident = fstar_tactics_lid "reify_tactic"
let fstar_tactics_embed_lid: FStar_Ident.lident = fstar_tactics_lid "__embed"
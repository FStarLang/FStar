
open Prims
# 22 "FStar.Syntax.Const.fst"
let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

# 24 "FStar.Syntax.Const.fst"
let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

# 25 "FStar.Syntax.Const.fst"
let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 26 "FStar.Syntax.Const.fst"
let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 27 "FStar.Syntax.Const.fst"
let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 28 "FStar.Syntax.Const.fst"
let bool_lid : FStar_Ident.lident = (pconst "bool")

# 31 "FStar.Syntax.Const.fst"
let unit_lid : FStar_Ident.lident = (pconst "unit")

# 32 "FStar.Syntax.Const.fst"
let string_lid : FStar_Ident.lident = (pconst "string")

# 33 "FStar.Syntax.Const.fst"
let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 34 "FStar.Syntax.Const.fst"
let int_lid : FStar_Ident.lident = (pconst "int")

# 35 "FStar.Syntax.Const.fst"
let exn_lid : FStar_Ident.lident = (pconst "exn")

# 36 "FStar.Syntax.Const.fst"
let list_lid : FStar_Ident.lident = (pconst "list")

# 37 "FStar.Syntax.Const.fst"
let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 38 "FStar.Syntax.Const.fst"
let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 39 "FStar.Syntax.Const.fst"
let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 40 "FStar.Syntax.Const.fst"
let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 41 "FStar.Syntax.Const.fst"
let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 42 "FStar.Syntax.Const.fst"
let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 43 "FStar.Syntax.Const.fst"
let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 44 "FStar.Syntax.Const.fst"
let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 45 "FStar.Syntax.Const.fst"
let int8_lid : FStar_Ident.lident = (p2l (("FStar")::("Int8")::("int8")::[]))

# 47 "FStar.Syntax.Const.fst"
let uint8_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt8")::("uint8")::[]))

# 48 "FStar.Syntax.Const.fst"
let int16_lid : FStar_Ident.lident = (p2l (("FStar")::("Int16")::("int16")::[]))

# 49 "FStar.Syntax.Const.fst"
let uint16_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt16")::("uint16")::[]))

# 50 "FStar.Syntax.Const.fst"
let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 51 "FStar.Syntax.Const.fst"
let uint32_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt32")::("uint32")::[]))

# 52 "FStar.Syntax.Const.fst"
let int64_lid : FStar_Ident.lident = (p2l (("FStar")::("Int64")::("int64")::[]))

# 53 "FStar.Syntax.Const.fst"
let uint64_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt64")::("uint64")::[]))

# 54 "FStar.Syntax.Const.fst"
let float_lid : FStar_Ident.lident = (p2l (("FStar")::("Float")::("float")::[]))

# 56 "FStar.Syntax.Const.fst"
let char_lid : FStar_Ident.lident = (p2l (("FStar")::("Char")::("char")::[]))

# 58 "FStar.Syntax.Const.fst"
let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 60 "FStar.Syntax.Const.fst"
let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _123_15 = (let _123_14 = (let _123_13 = (let _123_11 = (FStar_Syntax_Syntax.null_binder k)
in (_123_11)::[])
in (let _123_12 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_13, _123_12)))
in FStar_Syntax_Syntax.Tm_arrow (_123_14))
in (mk _123_15)))

# 63 "FStar.Syntax.Const.fst"
let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _123_28 = (let _123_27 = (let _123_26 = (let _123_24 = (FStar_Syntax_Syntax.null_binder k1)
in (let _123_23 = (let _123_22 = (FStar_Syntax_Syntax.null_binder k2)
in (_123_22)::[])
in (_123_24)::_123_23))
in (let _123_25 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_26, _123_25)))
in FStar_Syntax_Syntax.Tm_arrow (_123_27))
in (mk _123_28)))

# 64 "FStar.Syntax.Const.fst"
let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _123_45 = (let _123_44 = (let _123_43 = (let _123_41 = (FStar_Syntax_Syntax.null_binder k1)
in (let _123_40 = (let _123_39 = (FStar_Syntax_Syntax.null_binder k2)
in (let _123_38 = (let _123_37 = (FStar_Syntax_Syntax.null_binder k3)
in (_123_37)::[])
in (_123_39)::_123_38))
in (_123_41)::_123_40))
in (let _123_42 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_43, _123_42)))
in FStar_Syntax_Syntax.Tm_arrow (_123_44))
in (mk _123_45)))

# 67 "FStar.Syntax.Const.fst"
let true_lid : FStar_Ident.lident = (pconst "l_True")

# 68 "FStar.Syntax.Const.fst"
let false_lid : FStar_Ident.lident = (pconst "l_False")

# 69 "FStar.Syntax.Const.fst"
let and_lid : FStar_Ident.lident = (pconst "l_and")

# 70 "FStar.Syntax.Const.fst"
let or_lid : FStar_Ident.lident = (pconst "l_or")

# 71 "FStar.Syntax.Const.fst"
let not_lid : FStar_Ident.lident = (pconst "l_not")

# 72 "FStar.Syntax.Const.fst"
let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 73 "FStar.Syntax.Const.fst"
let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 74 "FStar.Syntax.Const.fst"
let ite_lid : FStar_Ident.lident = (pconst "l_ITE")

# 75 "FStar.Syntax.Const.fst"
let exists_lid : FStar_Ident.lident = (pconst "l_Exists")

# 76 "FStar.Syntax.Const.fst"
let forall_lid : FStar_Ident.lident = (pconst "l_Forall")

# 77 "FStar.Syntax.Const.fst"
let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 78 "FStar.Syntax.Const.fst"
let admit_lid : FStar_Ident.lident = (pconst "admit")

# 79 "FStar.Syntax.Const.fst"
let magic_lid : FStar_Ident.lident = (pconst "magic")

# 80 "FStar.Syntax.Const.fst"
let has_type_lid : FStar_Ident.lident = (pconst "has_type")

# 81 "FStar.Syntax.Const.fst"
let eq2_lid : FStar_Ident.lident = (pconst "eq2")

# 84 "FStar.Syntax.Const.fst"
let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 87 "FStar.Syntax.Const.fst"
let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 88 "FStar.Syntax.Const.fst"
let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 89 "FStar.Syntax.Const.fst"
let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 90 "FStar.Syntax.Const.fst"
let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 91 "FStar.Syntax.Const.fst"
let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 92 "FStar.Syntax.Const.fst"
let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 93 "FStar.Syntax.Const.fst"
let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 94 "FStar.Syntax.Const.fst"
let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 95 "FStar.Syntax.Const.fst"
let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 96 "FStar.Syntax.Const.fst"
let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 99 "FStar.Syntax.Const.fst"
let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 100 "FStar.Syntax.Const.fst"
let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 101 "FStar.Syntax.Const.fst"
let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 102 "FStar.Syntax.Const.fst"
let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 103 "FStar.Syntax.Const.fst"
let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 104 "FStar.Syntax.Const.fst"
let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 105 "FStar.Syntax.Const.fst"
let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 106 "FStar.Syntax.Const.fst"
let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 107 "FStar.Syntax.Const.fst"
let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 108 "FStar.Syntax.Const.fst"
let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 109 "FStar.Syntax.Const.fst"
let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 110 "FStar.Syntax.Const.fst"
let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 111 "FStar.Syntax.Const.fst"
let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 112 "FStar.Syntax.Const.fst"
let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 113 "FStar.Syntax.Const.fst"
let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 116 "FStar.Syntax.Const.fst"
let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 117 "FStar.Syntax.Const.fst"
let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 120 "FStar.Syntax.Const.fst"
let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 121 "FStar.Syntax.Const.fst"
let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 122 "FStar.Syntax.Const.fst"
let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 123 "FStar.Syntax.Const.fst"
let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 124 "FStar.Syntax.Const.fst"
let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 127 "FStar.Syntax.Const.fst"
let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 128 "FStar.Syntax.Const.fst"
let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 129 "FStar.Syntax.Const.fst"
let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 130 "FStar.Syntax.Const.fst"
let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 131 "FStar.Syntax.Const.fst"
let fstar_hyperheap_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::[]))

# 132 "FStar.Syntax.Const.fst"
let rref_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::("rref")::[]))

# 133 "FStar.Syntax.Const.fst"
let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 136 "FStar.Syntax.Const.fst"
let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 137 "FStar.Syntax.Const.fst"
let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 138 "FStar.Syntax.Const.fst"
let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 139 "FStar.Syntax.Const.fst"
let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 140 "FStar.Syntax.Const.fst"
let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 141 "FStar.Syntax.Const.fst"
let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 142 "FStar.Syntax.Const.fst"
let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 145 "FStar.Syntax.Const.fst"
let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 146 "FStar.Syntax.Const.fst"
let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 147 "FStar.Syntax.Const.fst"
let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 148 "FStar.Syntax.Const.fst"
let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 149 "FStar.Syntax.Const.fst"
let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 150 "FStar.Syntax.Const.fst"
let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 151 "FStar.Syntax.Const.fst"
let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 153 "FStar.Syntax.Const.fst"
let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 154 "FStar.Syntax.Const.fst"
let decreases_lid : FStar_Ident.lident = (pconst "decreases")

# 155 "FStar.Syntax.Const.fst"
let range_of_lid : FStar_Ident.lident = (pconst "range_of")

# 157 "FStar.Syntax.Const.fst"
let labeled_lid : FStar_Ident.lident = (pconst "labeled")






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
let char_lid : FStar_Ident.lident = (pconst "char")

# 35 "FStar.Syntax.Const.fst"
let int_lid : FStar_Ident.lident = (pconst "int")

# 36 "FStar.Syntax.Const.fst"
let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 37 "FStar.Syntax.Const.fst"
let int64_lid : FStar_Ident.lident = (pconst "int64")

# 38 "FStar.Syntax.Const.fst"
let float_lid : FStar_Ident.lident = (pconst "float")

# 39 "FStar.Syntax.Const.fst"
let exn_lid : FStar_Ident.lident = (pconst "exn")

# 40 "FStar.Syntax.Const.fst"
let list_lid : FStar_Ident.lident = (pconst "list")

# 41 "FStar.Syntax.Const.fst"
let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 42 "FStar.Syntax.Const.fst"
let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 43 "FStar.Syntax.Const.fst"
let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 44 "FStar.Syntax.Const.fst"
let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 45 "FStar.Syntax.Const.fst"
let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 46 "FStar.Syntax.Const.fst"
let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 47 "FStar.Syntax.Const.fst"
let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 48 "FStar.Syntax.Const.fst"
let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 49 "FStar.Syntax.Const.fst"
let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 51 "FStar.Syntax.Const.fst"
let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 52 "FStar.Syntax.Const.fst"
let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 53 "FStar.Syntax.Const.fst"
let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _115_15 = (let _115_14 = (let _115_13 = (let _115_11 = (FStar_Syntax_Syntax.null_binder k)
in (_115_11)::[])
in (let _115_12 = (FStar_Syntax_Syntax.mk_Total k')
in (_115_13, _115_12)))
in FStar_Syntax_Syntax.Tm_arrow (_115_14))
in (mk _115_15)))

# 56 "FStar.Syntax.Const.fst"
let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _115_28 = (let _115_27 = (let _115_26 = (let _115_24 = (FStar_Syntax_Syntax.null_binder k1)
in (let _115_23 = (let _115_22 = (FStar_Syntax_Syntax.null_binder k2)
in (_115_22)::[])
in (_115_24)::_115_23))
in (let _115_25 = (FStar_Syntax_Syntax.mk_Total k')
in (_115_26, _115_25)))
in FStar_Syntax_Syntax.Tm_arrow (_115_27))
in (mk _115_28)))

# 57 "FStar.Syntax.Const.fst"
let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _115_45 = (let _115_44 = (let _115_43 = (let _115_41 = (FStar_Syntax_Syntax.null_binder k1)
in (let _115_40 = (let _115_39 = (FStar_Syntax_Syntax.null_binder k2)
in (let _115_38 = (let _115_37 = (FStar_Syntax_Syntax.null_binder k3)
in (_115_37)::[])
in (_115_39)::_115_38))
in (_115_41)::_115_40))
in (let _115_42 = (FStar_Syntax_Syntax.mk_Total k')
in (_115_43, _115_42)))
in FStar_Syntax_Syntax.Tm_arrow (_115_44))
in (mk _115_45)))

# 60 "FStar.Syntax.Const.fst"
let true_lid : FStar_Ident.lident = (pconst "l_True")

# 61 "FStar.Syntax.Const.fst"
let false_lid : FStar_Ident.lident = (pconst "l_False")

# 62 "FStar.Syntax.Const.fst"
let and_lid : FStar_Ident.lident = (pconst "l_and")

# 63 "FStar.Syntax.Const.fst"
let or_lid : FStar_Ident.lident = (pconst "l_or")

# 64 "FStar.Syntax.Const.fst"
let not_lid : FStar_Ident.lident = (pconst "l_not")

# 65 "FStar.Syntax.Const.fst"
let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 66 "FStar.Syntax.Const.fst"
let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 67 "FStar.Syntax.Const.fst"
let ite_lid : FStar_Ident.lident = (pconst "l_ITE")

# 68 "FStar.Syntax.Const.fst"
let exists_lid : FStar_Ident.lident = (pconst "l_Exists")

# 69 "FStar.Syntax.Const.fst"
let forall_lid : FStar_Ident.lident = (pconst "l_Forall")

# 70 "FStar.Syntax.Const.fst"
let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 71 "FStar.Syntax.Const.fst"
let admit_lid : FStar_Ident.lident = (pconst "admit")

# 72 "FStar.Syntax.Const.fst"
let magic_lid : FStar_Ident.lident = (pconst "magic")

# 73 "FStar.Syntax.Const.fst"
let has_type_lid : FStar_Ident.lident = (pconst "has_type")

# 74 "FStar.Syntax.Const.fst"
let eq2_lid : FStar_Ident.lident = (pconst "eq2")

# 77 "FStar.Syntax.Const.fst"
let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 80 "FStar.Syntax.Const.fst"
let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 81 "FStar.Syntax.Const.fst"
let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 82 "FStar.Syntax.Const.fst"
let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 83 "FStar.Syntax.Const.fst"
let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 84 "FStar.Syntax.Const.fst"
let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 85 "FStar.Syntax.Const.fst"
let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 86 "FStar.Syntax.Const.fst"
let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 87 "FStar.Syntax.Const.fst"
let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 88 "FStar.Syntax.Const.fst"
let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 89 "FStar.Syntax.Const.fst"
let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 92 "FStar.Syntax.Const.fst"
let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 93 "FStar.Syntax.Const.fst"
let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 94 "FStar.Syntax.Const.fst"
let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 95 "FStar.Syntax.Const.fst"
let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 96 "FStar.Syntax.Const.fst"
let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 97 "FStar.Syntax.Const.fst"
let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 98 "FStar.Syntax.Const.fst"
let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 99 "FStar.Syntax.Const.fst"
let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 100 "FStar.Syntax.Const.fst"
let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 101 "FStar.Syntax.Const.fst"
let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 102 "FStar.Syntax.Const.fst"
let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 103 "FStar.Syntax.Const.fst"
let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 104 "FStar.Syntax.Const.fst"
let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 105 "FStar.Syntax.Const.fst"
let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 106 "FStar.Syntax.Const.fst"
let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 109 "FStar.Syntax.Const.fst"
let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 110 "FStar.Syntax.Const.fst"
let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 113 "FStar.Syntax.Const.fst"
let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 114 "FStar.Syntax.Const.fst"
let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 115 "FStar.Syntax.Const.fst"
let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 116 "FStar.Syntax.Const.fst"
let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 117 "FStar.Syntax.Const.fst"
let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 120 "FStar.Syntax.Const.fst"
let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 121 "FStar.Syntax.Const.fst"
let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 122 "FStar.Syntax.Const.fst"
let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 123 "FStar.Syntax.Const.fst"
let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 124 "FStar.Syntax.Const.fst"
let fstar_hyperheap_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::[]))

# 125 "FStar.Syntax.Const.fst"
let rref_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::("rref")::[]))

# 126 "FStar.Syntax.Const.fst"
let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 129 "FStar.Syntax.Const.fst"
let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 130 "FStar.Syntax.Const.fst"
let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 131 "FStar.Syntax.Const.fst"
let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 132 "FStar.Syntax.Const.fst"
let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 133 "FStar.Syntax.Const.fst"
let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 134 "FStar.Syntax.Const.fst"
let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 135 "FStar.Syntax.Const.fst"
let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 138 "FStar.Syntax.Const.fst"
let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 139 "FStar.Syntax.Const.fst"
let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 140 "FStar.Syntax.Const.fst"
let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 141 "FStar.Syntax.Const.fst"
let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 142 "FStar.Syntax.Const.fst"
let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 143 "FStar.Syntax.Const.fst"
let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 144 "FStar.Syntax.Const.fst"
let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 146 "FStar.Syntax.Const.fst"
let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 147 "FStar.Syntax.Const.fst"
let decreases_lid : FStar_Ident.lident = (pconst "decreases")

# 148 "FStar.Syntax.Const.fst"
let range_of_lid : FStar_Ident.lident = (pconst "range_of")

# 150 "FStar.Syntax.Const.fst"
let labeled_lid : FStar_Ident.lident = (pconst "labeled")





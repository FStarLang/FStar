
open Prims
# 24 "FStar.Syntax.Const.fst"
let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

# 25 "FStar.Syntax.Const.fst"
let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

# 26 "FStar.Syntax.Const.fst"
let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 27 "FStar.Syntax.Const.fst"
let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 28 "FStar.Syntax.Const.fst"
let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 31 "FStar.Syntax.Const.fst"
let bool_lid : FStar_Ident.lident = (pconst "bool")

# 32 "FStar.Syntax.Const.fst"
let unit_lid : FStar_Ident.lident = (pconst "unit")

# 33 "FStar.Syntax.Const.fst"
let string_lid : FStar_Ident.lident = (pconst "string")

# 34 "FStar.Syntax.Const.fst"
let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 35 "FStar.Syntax.Const.fst"
let char_lid : FStar_Ident.lident = (pconst "char")

# 36 "FStar.Syntax.Const.fst"
let int_lid : FStar_Ident.lident = (pconst "int")

# 37 "FStar.Syntax.Const.fst"
let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 38 "FStar.Syntax.Const.fst"
let int64_lid : FStar_Ident.lident = (pconst "int64")

# 39 "FStar.Syntax.Const.fst"
let float_lid : FStar_Ident.lident = (pconst "float")

# 40 "FStar.Syntax.Const.fst"
let exn_lid : FStar_Ident.lident = (pconst "exn")

# 41 "FStar.Syntax.Const.fst"
let list_lid : FStar_Ident.lident = (pconst "list")

# 42 "FStar.Syntax.Const.fst"
let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 43 "FStar.Syntax.Const.fst"
let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 44 "FStar.Syntax.Const.fst"
let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 45 "FStar.Syntax.Const.fst"
let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 46 "FStar.Syntax.Const.fst"
let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 47 "FStar.Syntax.Const.fst"
let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 48 "FStar.Syntax.Const.fst"
let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 49 "FStar.Syntax.Const.fst"
let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 51 "FStar.Syntax.Const.fst"
let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 52 "FStar.Syntax.Const.fst"
let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 53 "FStar.Syntax.Const.fst"
let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 56 "FStar.Syntax.Const.fst"
let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _111_15 = (let _111_14 = (let _111_13 = (let _111_11 = (FStar_Syntax_Syntax.null_binder k)
in (_111_11)::[])
in (let _111_12 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_13, _111_12)))
in FStar_Syntax_Syntax.Tm_arrow (_111_14))
in (mk _111_15)))

# 57 "FStar.Syntax.Const.fst"
let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _111_28 = (let _111_27 = (let _111_26 = (let _111_24 = (FStar_Syntax_Syntax.null_binder k1)
in (let _111_23 = (let _111_22 = (FStar_Syntax_Syntax.null_binder k2)
in (_111_22)::[])
in (_111_24)::_111_23))
in (let _111_25 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_26, _111_25)))
in FStar_Syntax_Syntax.Tm_arrow (_111_27))
in (mk _111_28)))

# 58 "FStar.Syntax.Const.fst"
let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _111_45 = (let _111_44 = (let _111_43 = (let _111_41 = (FStar_Syntax_Syntax.null_binder k1)
in (let _111_40 = (let _111_39 = (FStar_Syntax_Syntax.null_binder k2)
in (let _111_38 = (let _111_37 = (FStar_Syntax_Syntax.null_binder k3)
in (_111_37)::[])
in (_111_39)::_111_38))
in (_111_41)::_111_40))
in (let _111_42 = (FStar_Syntax_Syntax.mk_Total k')
in (_111_43, _111_42)))
in FStar_Syntax_Syntax.Tm_arrow (_111_44))
in (mk _111_45)))

# 61 "FStar.Syntax.Const.fst"
let true_lid : FStar_Ident.lident = (pconst "True")

# 62 "FStar.Syntax.Const.fst"
let false_lid : FStar_Ident.lident = (pconst "False")

# 63 "FStar.Syntax.Const.fst"
let and_lid : FStar_Ident.lident = (pconst "l_and")

# 64 "FStar.Syntax.Const.fst"
let or_lid : FStar_Ident.lident = (pconst "l_or")

# 65 "FStar.Syntax.Const.fst"
let not_lid : FStar_Ident.lident = (pconst "l_not")

# 66 "FStar.Syntax.Const.fst"
let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 67 "FStar.Syntax.Const.fst"
let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 68 "FStar.Syntax.Const.fst"
let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 69 "FStar.Syntax.Const.fst"
let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 70 "FStar.Syntax.Const.fst"
let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 71 "FStar.Syntax.Const.fst"
let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 72 "FStar.Syntax.Const.fst"
let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 73 "FStar.Syntax.Const.fst"
let admit_lid : FStar_Ident.lident = (pconst "admit")

# 74 "FStar.Syntax.Const.fst"
let magic_lid : FStar_Ident.lident = (pconst "magic")

# 75 "FStar.Syntax.Const.fst"
let has_type_lid : FStar_Ident.lident = (pconst "has_type")

# 78 "FStar.Syntax.Const.fst"
let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 79 "FStar.Syntax.Const.fst"
let neq_lid : FStar_Ident.lident = (pconst "neq")

# 80 "FStar.Syntax.Const.fst"
let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 83 "FStar.Syntax.Const.fst"
let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 84 "FStar.Syntax.Const.fst"
let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 85 "FStar.Syntax.Const.fst"
let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 86 "FStar.Syntax.Const.fst"
let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 87 "FStar.Syntax.Const.fst"
let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 88 "FStar.Syntax.Const.fst"
let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 89 "FStar.Syntax.Const.fst"
let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 90 "FStar.Syntax.Const.fst"
let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 91 "FStar.Syntax.Const.fst"
let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 92 "FStar.Syntax.Const.fst"
let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 95 "FStar.Syntax.Const.fst"
let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 96 "FStar.Syntax.Const.fst"
let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 97 "FStar.Syntax.Const.fst"
let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 98 "FStar.Syntax.Const.fst"
let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 99 "FStar.Syntax.Const.fst"
let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 100 "FStar.Syntax.Const.fst"
let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 101 "FStar.Syntax.Const.fst"
let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 102 "FStar.Syntax.Const.fst"
let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 103 "FStar.Syntax.Const.fst"
let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 104 "FStar.Syntax.Const.fst"
let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 105 "FStar.Syntax.Const.fst"
let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 106 "FStar.Syntax.Const.fst"
let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 107 "FStar.Syntax.Const.fst"
let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 108 "FStar.Syntax.Const.fst"
let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 109 "FStar.Syntax.Const.fst"
let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 112 "FStar.Syntax.Const.fst"
let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 113 "FStar.Syntax.Const.fst"
let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 116 "FStar.Syntax.Const.fst"
let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 117 "FStar.Syntax.Const.fst"
let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 118 "FStar.Syntax.Const.fst"
let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 119 "FStar.Syntax.Const.fst"
let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 120 "FStar.Syntax.Const.fst"
let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 123 "FStar.Syntax.Const.fst"
let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 124 "FStar.Syntax.Const.fst"
let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 125 "FStar.Syntax.Const.fst"
let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 126 "FStar.Syntax.Const.fst"
let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 127 "FStar.Syntax.Const.fst"
let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 130 "FStar.Syntax.Const.fst"
let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 131 "FStar.Syntax.Const.fst"
let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 132 "FStar.Syntax.Const.fst"
let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 133 "FStar.Syntax.Const.fst"
let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 134 "FStar.Syntax.Const.fst"
let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 135 "FStar.Syntax.Const.fst"
let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 136 "FStar.Syntax.Const.fst"
let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 139 "FStar.Syntax.Const.fst"
let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 140 "FStar.Syntax.Const.fst"
let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 141 "FStar.Syntax.Const.fst"
let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 142 "FStar.Syntax.Const.fst"
let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 143 "FStar.Syntax.Const.fst"
let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 144 "FStar.Syntax.Const.fst"
let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 145 "FStar.Syntax.Const.fst"
let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 147 "FStar.Syntax.Const.fst"
let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 148 "FStar.Syntax.Const.fst"
let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 149 "FStar.Syntax.Const.fst"
let decreases_lid : FStar_Ident.lident = (pconst "decreases")

# 151 "FStar.Syntax.Const.fst"
let range_of_lid : FStar_Ident.lident = (pconst "range_of")

# 152 "FStar.Syntax.Const.fst"
let labeled_lid : FStar_Ident.lident = (pconst "labeled")






open Prims
# 22 "FStar.Absyn.Const.fst"
let p2l : FStar_Absyn_Syntax.path  ->  FStar_Absyn_Syntax.lident = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

# 23 "FStar.Absyn.Const.fst"
let pconst : Prims.string  ->  FStar_Absyn_Syntax.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 24 "FStar.Absyn.Const.fst"
let prims_lid : FStar_Absyn_Syntax.lident = (p2l (("Prims")::[]))

# 25 "FStar.Absyn.Const.fst"
let fstar_ns_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::[]))

# 28 "FStar.Absyn.Const.fst"
let bool_lid : FStar_Absyn_Syntax.lident = (pconst "bool")

# 29 "FStar.Absyn.Const.fst"
let unit_lid : FStar_Absyn_Syntax.lident = (pconst "unit")

# 30 "FStar.Absyn.Const.fst"
let string_lid : FStar_Absyn_Syntax.lident = (pconst "string")

# 31 "FStar.Absyn.Const.fst"
let bytes_lid : FStar_Absyn_Syntax.lident = (pconst "bytes")

# 32 "FStar.Absyn.Const.fst"
let char_lid : FStar_Absyn_Syntax.lident = (pconst "char")

# 33 "FStar.Absyn.Const.fst"
let int_lid : FStar_Absyn_Syntax.lident = (pconst "int")

# 34 "FStar.Absyn.Const.fst"
let uint8_lid : FStar_Absyn_Syntax.lident = (pconst "uint8")

# 35 "FStar.Absyn.Const.fst"
let int64_lid : FStar_Absyn_Syntax.lident = (pconst "int64")

# 36 "FStar.Absyn.Const.fst"
let float_lid : FStar_Absyn_Syntax.lident = (pconst "float")

# 37 "FStar.Absyn.Const.fst"
let exn_lid : FStar_Absyn_Syntax.lident = (pconst "exn")

# 38 "FStar.Absyn.Const.fst"
let list_lid : FStar_Absyn_Syntax.lident = (pconst "list")

# 39 "FStar.Absyn.Const.fst"
let pattern_lid : FStar_Absyn_Syntax.lident = (pconst "pattern")

# 40 "FStar.Absyn.Const.fst"
let precedes_lid : FStar_Absyn_Syntax.lident = (pconst "Precedes")

# 41 "FStar.Absyn.Const.fst"
let lex_t_lid : FStar_Absyn_Syntax.lident = (pconst "lex_t")

# 42 "FStar.Absyn.Const.fst"
let lexcons_lid : FStar_Absyn_Syntax.lident = (pconst "LexCons")

# 43 "FStar.Absyn.Const.fst"
let lextop_lid : FStar_Absyn_Syntax.lident = (pconst "LexTop")

# 44 "FStar.Absyn.Const.fst"
let smtpat_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPat")

# 45 "FStar.Absyn.Const.fst"
let smtpatT_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPatT")

# 46 "FStar.Absyn.Const.fst"
let smtpatOr_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPatOr")

# 48 "FStar.Absyn.Const.fst"
let int32_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 49 "FStar.Absyn.Const.fst"
let int31_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 50 "FStar.Absyn.Const.fst"
let heap_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 53 "FStar.Absyn.Const.fst"
let kunary : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k k' -> (let _98_11 = (let _98_10 = (let _98_9 = (FStar_Absyn_Syntax.null_t_binder k)
in (_98_9)::[])
in (_98_10, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _98_11 FStar_Absyn_Syntax.dummyRange)))

# 54 "FStar.Absyn.Const.fst"
let kbin : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k' -> (let _98_22 = (let _98_21 = (let _98_20 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _98_19 = (let _98_18 = (FStar_Absyn_Syntax.null_t_binder k2)
in (_98_18)::[])
in (_98_20)::_98_19))
in (_98_21, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _98_22 FStar_Absyn_Syntax.dummyRange)))

# 55 "FStar.Absyn.Const.fst"
let ktern : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k3 k' -> (let _98_37 = (let _98_36 = (let _98_35 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _98_34 = (let _98_33 = (FStar_Absyn_Syntax.null_t_binder k2)
in (let _98_32 = (let _98_31 = (FStar_Absyn_Syntax.null_t_binder k3)
in (_98_31)::[])
in (_98_33)::_98_32))
in (_98_35)::_98_34))
in (_98_36, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _98_37 FStar_Absyn_Syntax.dummyRange)))

# 58 "FStar.Absyn.Const.fst"
let true_lid : FStar_Absyn_Syntax.lident = (pconst "True")

# 59 "FStar.Absyn.Const.fst"
let false_lid : FStar_Absyn_Syntax.lident = (pconst "False")

# 60 "FStar.Absyn.Const.fst"
let and_lid : FStar_Absyn_Syntax.lident = (pconst "l_and")

# 61 "FStar.Absyn.Const.fst"
let or_lid : FStar_Absyn_Syntax.lident = (pconst "l_or")

# 62 "FStar.Absyn.Const.fst"
let not_lid : FStar_Absyn_Syntax.lident = (pconst "l_not")

# 63 "FStar.Absyn.Const.fst"
let imp_lid : FStar_Absyn_Syntax.lident = (pconst "l_imp")

# 64 "FStar.Absyn.Const.fst"
let iff_lid : FStar_Absyn_Syntax.lident = (pconst "l_iff")

# 65 "FStar.Absyn.Const.fst"
let ite_lid : FStar_Absyn_Syntax.lident = (pconst "ITE")

# 66 "FStar.Absyn.Const.fst"
let exists_lid : FStar_Absyn_Syntax.lident = (pconst "Exists")

# 67 "FStar.Absyn.Const.fst"
let forall_lid : FStar_Absyn_Syntax.lident = (pconst "Forall")

# 68 "FStar.Absyn.Const.fst"
let exTyp_lid : FStar_Absyn_Syntax.lident = (pconst "ExistsTyp")

# 69 "FStar.Absyn.Const.fst"
let allTyp_lid : FStar_Absyn_Syntax.lident = (pconst "ForallTyp")

# 70 "FStar.Absyn.Const.fst"
let b2t_lid : FStar_Absyn_Syntax.lident = (pconst "b2t")

# 71 "FStar.Absyn.Const.fst"
let using_IH : FStar_Absyn_Syntax.lident = (pconst "InductionHyp")

# 72 "FStar.Absyn.Const.fst"
let using_lem : FStar_Absyn_Syntax.lident = (pconst "Using")

# 73 "FStar.Absyn.Const.fst"
let admit_lid : FStar_Absyn_Syntax.lident = (pconst "admit")

# 74 "FStar.Absyn.Const.fst"
let magic_lid : FStar_Absyn_Syntax.lident = (pconst "magic")

# 77 "FStar.Absyn.Const.fst"
let eq_lid : FStar_Absyn_Syntax.lident = (pconst "Eq")

# 78 "FStar.Absyn.Const.fst"
let eq2_lid : FStar_Absyn_Syntax.lident = (pconst "Eq2")

# 79 "FStar.Absyn.Const.fst"
let eqA_lid : FStar_Absyn_Syntax.lident = (pconst "EqA")

# 80 "FStar.Absyn.Const.fst"
let eqT_lid : FStar_Absyn_Syntax.lident = (pconst "EqTyp")

# 81 "FStar.Absyn.Const.fst"
let neq_lid : FStar_Absyn_Syntax.lident = (pconst "neq")

# 82 "FStar.Absyn.Const.fst"
let neq2_lid : FStar_Absyn_Syntax.lident = (pconst "neq2")

# 85 "FStar.Absyn.Const.fst"
let exp_true_bool : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

# 86 "FStar.Absyn.Const.fst"
let exp_false_bool : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

# 87 "FStar.Absyn.Const.fst"
let exp_unit : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None FStar_Absyn_Syntax.dummyRange)

# 88 "FStar.Absyn.Const.fst"
let cons_lid : FStar_Absyn_Syntax.lident = (pconst "Cons")

# 89 "FStar.Absyn.Const.fst"
let nil_lid : FStar_Absyn_Syntax.lident = (pconst "Nil")

# 90 "FStar.Absyn.Const.fst"
let assume_lid : FStar_Absyn_Syntax.lident = (pconst "_assume")

# 91 "FStar.Absyn.Const.fst"
let assert_lid : FStar_Absyn_Syntax.lident = (pconst "_assert")

# 92 "FStar.Absyn.Const.fst"
let list_append_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("List")::("append")::[]))

# 93 "FStar.Absyn.Const.fst"
let strcat_lid : FStar_Absyn_Syntax.lident = (p2l (("Prims")::("strcat")::[]))

# 94 "FStar.Absyn.Const.fst"
let let_in_typ : FStar_Absyn_Syntax.lident = (p2l (("Prims")::("Let")::[]))

# 97 "FStar.Absyn.Const.fst"
let op_Eq : FStar_Absyn_Syntax.lident = (pconst "op_Equality")

# 98 "FStar.Absyn.Const.fst"
let op_notEq : FStar_Absyn_Syntax.lident = (pconst "op_disEquality")

# 99 "FStar.Absyn.Const.fst"
let op_LT : FStar_Absyn_Syntax.lident = (pconst "op_LessThan")

# 100 "FStar.Absyn.Const.fst"
let op_LTE : FStar_Absyn_Syntax.lident = (pconst "op_LessThanOrEqual")

# 101 "FStar.Absyn.Const.fst"
let op_GT : FStar_Absyn_Syntax.lident = (pconst "op_GreaterThan")

# 102 "FStar.Absyn.Const.fst"
let op_GTE : FStar_Absyn_Syntax.lident = (pconst "op_GreaterThanOrEqual")

# 103 "FStar.Absyn.Const.fst"
let op_Subtraction : FStar_Absyn_Syntax.lident = (pconst "op_Subtraction")

# 104 "FStar.Absyn.Const.fst"
let op_Minus : FStar_Absyn_Syntax.lident = (pconst "op_Minus")

# 105 "FStar.Absyn.Const.fst"
let op_Addition : FStar_Absyn_Syntax.lident = (pconst "op_Addition")

# 106 "FStar.Absyn.Const.fst"
let op_Multiply : FStar_Absyn_Syntax.lident = (pconst "op_Multiply")

# 107 "FStar.Absyn.Const.fst"
let op_Division : FStar_Absyn_Syntax.lident = (pconst "op_Division")

# 108 "FStar.Absyn.Const.fst"
let op_Modulus : FStar_Absyn_Syntax.lident = (pconst "op_Modulus")

# 109 "FStar.Absyn.Const.fst"
let op_And : FStar_Absyn_Syntax.lident = (pconst "op_AmpAmp")

# 110 "FStar.Absyn.Const.fst"
let op_Or : FStar_Absyn_Syntax.lident = (pconst "op_BarBar")

# 111 "FStar.Absyn.Const.fst"
let op_Negation : FStar_Absyn_Syntax.lident = (pconst "op_Negation")

# 114 "FStar.Absyn.Const.fst"
let array_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 115 "FStar.Absyn.Const.fst"
let array_mk_array_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 118 "FStar.Absyn.Const.fst"
let st_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::[]))

# 119 "FStar.Absyn.Const.fst"
let write_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 120 "FStar.Absyn.Const.fst"
let read_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 121 "FStar.Absyn.Const.fst"
let alloc_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 122 "FStar.Absyn.Const.fst"
let op_ColonEq : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 125 "FStar.Absyn.Const.fst"
let ref_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 126 "FStar.Absyn.Const.fst"
let heap_ref : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 127 "FStar.Absyn.Const.fst"
let set_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::[]))

# 128 "FStar.Absyn.Const.fst"
let set_empty : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 129 "FStar.Absyn.Const.fst"
let set_singleton : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 130 "FStar.Absyn.Const.fst"
let set_union : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 133 "FStar.Absyn.Const.fst"
let effect_PURE_lid : FStar_Absyn_Syntax.lident = (pconst "PURE")

# 134 "FStar.Absyn.Const.fst"
let effect_Pure_lid : FStar_Absyn_Syntax.lident = (pconst "Pure")

# 135 "FStar.Absyn.Const.fst"
let effect_Tot_lid : FStar_Absyn_Syntax.lident = (pconst "Tot")

# 136 "FStar.Absyn.Const.fst"
let effect_Lemma_lid : FStar_Absyn_Syntax.lident = (pconst "Lemma")

# 137 "FStar.Absyn.Const.fst"
let effect_GTot_lid : FStar_Absyn_Syntax.lident = (pconst "GTot")

# 138 "FStar.Absyn.Const.fst"
let effect_GHOST_lid : FStar_Absyn_Syntax.lident = (pconst "GHOST")

# 139 "FStar.Absyn.Const.fst"
let effect_Ghost_lid : FStar_Absyn_Syntax.lident = (pconst "Ghost")

# 142 "FStar.Absyn.Const.fst"
let all_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::[]))

# 143 "FStar.Absyn.Const.fst"
let effect_ALL_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 144 "FStar.Absyn.Const.fst"
let effect_ML_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 145 "FStar.Absyn.Const.fst"
let failwith_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 146 "FStar.Absyn.Const.fst"
let pipe_right_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 147 "FStar.Absyn.Const.fst"
let pipe_left_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 148 "FStar.Absyn.Const.fst"
let try_with_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 150 "FStar.Absyn.Const.fst"
let as_requires : FStar_Absyn_Syntax.lident = (pconst "as_requires")

# 151 "FStar.Absyn.Const.fst"
let as_ensures : FStar_Absyn_Syntax.lident = (pconst "as_ensures")

# 152 "FStar.Absyn.Const.fst"
let decreases_lid : FStar_Absyn_Syntax.lident = (pconst "decreases")





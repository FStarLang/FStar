
open Prims
# 20 "FStar.Absyn.Const.fst"
let p2l : FStar_Absyn_Syntax.path  ->  FStar_Absyn_Syntax.lident = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

# 22 "FStar.Absyn.Const.fst"
let pconst : Prims.string  ->  FStar_Absyn_Syntax.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 23 "FStar.Absyn.Const.fst"
let prims_lid : FStar_Absyn_Syntax.lident = (p2l (("Prims")::[]))

# 24 "FStar.Absyn.Const.fst"
let fstar_ns_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::[]))

# 25 "FStar.Absyn.Const.fst"
let bool_lid : FStar_Absyn_Syntax.lident = (pconst "bool")

# 28 "FStar.Absyn.Const.fst"
let unit_lid : FStar_Absyn_Syntax.lident = (pconst "unit")

# 29 "FStar.Absyn.Const.fst"
let string_lid : FStar_Absyn_Syntax.lident = (pconst "string")

# 30 "FStar.Absyn.Const.fst"
let bytes_lid : FStar_Absyn_Syntax.lident = (pconst "bytes")

# 31 "FStar.Absyn.Const.fst"
let int_lid : FStar_Absyn_Syntax.lident = (pconst "int")

# 32 "FStar.Absyn.Const.fst"
let exn_lid : FStar_Absyn_Syntax.lident = (pconst "exn")

# 33 "FStar.Absyn.Const.fst"
let list_lid : FStar_Absyn_Syntax.lident = (pconst "list")

# 34 "FStar.Absyn.Const.fst"
let pattern_lid : FStar_Absyn_Syntax.lident = (pconst "pattern")

# 35 "FStar.Absyn.Const.fst"
let precedes_lid : FStar_Absyn_Syntax.lident = (pconst "Precedes")

# 36 "FStar.Absyn.Const.fst"
let lex_t_lid : FStar_Absyn_Syntax.lident = (pconst "lex_t")

# 37 "FStar.Absyn.Const.fst"
let lexcons_lid : FStar_Absyn_Syntax.lident = (pconst "LexCons")

# 38 "FStar.Absyn.Const.fst"
let lextop_lid : FStar_Absyn_Syntax.lident = (pconst "LexTop")

# 39 "FStar.Absyn.Const.fst"
let smtpat_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPat")

# 40 "FStar.Absyn.Const.fst"
let smtpatT_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPatT")

# 41 "FStar.Absyn.Const.fst"
let smtpatOr_lid : FStar_Absyn_Syntax.lident = (pconst "SMTPatOr")

# 42 "FStar.Absyn.Const.fst"
let int8_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int8")::("int8")::[]))

# 44 "FStar.Absyn.Const.fst"
let uint8_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("UInt8")::("uint8")::[]))

# 45 "FStar.Absyn.Const.fst"
let int16_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int16")::("int16")::[]))

# 46 "FStar.Absyn.Const.fst"
let uint16_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("UInt16")::("uint16")::[]))

# 47 "FStar.Absyn.Const.fst"
let int32_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 48 "FStar.Absyn.Const.fst"
let uint32_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("UInt32")::("uint32")::[]))

# 49 "FStar.Absyn.Const.fst"
let int64_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Int64")::("int64")::[]))

# 50 "FStar.Absyn.Const.fst"
let uint64_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("UInt64")::("uint64")::[]))

# 51 "FStar.Absyn.Const.fst"
let float_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Float")::("float")::[]))

# 53 "FStar.Absyn.Const.fst"
let char_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Char")::("char")::[]))

# 55 "FStar.Absyn.Const.fst"
let heap_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 57 "FStar.Absyn.Const.fst"
let kunary : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k k' -> (let _118_11 = (let _118_10 = (let _118_9 = (FStar_Absyn_Syntax.null_t_binder k)
in (_118_9)::[])
in (_118_10, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _118_11 FStar_Absyn_Syntax.dummyRange)))

# 60 "FStar.Absyn.Const.fst"
let kbin : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k' -> (let _118_22 = (let _118_21 = (let _118_20 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _118_19 = (let _118_18 = (FStar_Absyn_Syntax.null_t_binder k2)
in (_118_18)::[])
in (_118_20)::_118_19))
in (_118_21, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _118_22 FStar_Absyn_Syntax.dummyRange)))

# 61 "FStar.Absyn.Const.fst"
let ktern : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k3 k' -> (let _118_37 = (let _118_36 = (let _118_35 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _118_34 = (let _118_33 = (FStar_Absyn_Syntax.null_t_binder k2)
in (let _118_32 = (let _118_31 = (FStar_Absyn_Syntax.null_t_binder k3)
in (_118_31)::[])
in (_118_33)::_118_32))
in (_118_35)::_118_34))
in (_118_36, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _118_37 FStar_Absyn_Syntax.dummyRange)))

# 64 "FStar.Absyn.Const.fst"
let true_lid : FStar_Absyn_Syntax.lident = (pconst "True")

# 65 "FStar.Absyn.Const.fst"
let false_lid : FStar_Absyn_Syntax.lident = (pconst "False")

# 66 "FStar.Absyn.Const.fst"
let and_lid : FStar_Absyn_Syntax.lident = (pconst "l_and")

# 67 "FStar.Absyn.Const.fst"
let or_lid : FStar_Absyn_Syntax.lident = (pconst "l_or")

# 68 "FStar.Absyn.Const.fst"
let not_lid : FStar_Absyn_Syntax.lident = (pconst "l_not")

# 69 "FStar.Absyn.Const.fst"
let imp_lid : FStar_Absyn_Syntax.lident = (pconst "l_imp")

# 70 "FStar.Absyn.Const.fst"
let iff_lid : FStar_Absyn_Syntax.lident = (pconst "l_iff")

# 71 "FStar.Absyn.Const.fst"
let ite_lid : FStar_Absyn_Syntax.lident = (pconst "ITE")

# 72 "FStar.Absyn.Const.fst"
let exists_lid : FStar_Absyn_Syntax.lident = (pconst "Exists")

# 73 "FStar.Absyn.Const.fst"
let forall_lid : FStar_Absyn_Syntax.lident = (pconst "Forall")

# 74 "FStar.Absyn.Const.fst"
let exTyp_lid : FStar_Absyn_Syntax.lident = (pconst "ExistsTyp")

# 75 "FStar.Absyn.Const.fst"
let allTyp_lid : FStar_Absyn_Syntax.lident = (pconst "ForallTyp")

# 76 "FStar.Absyn.Const.fst"
let b2t_lid : FStar_Absyn_Syntax.lident = (pconst "b2t")

# 77 "FStar.Absyn.Const.fst"
let using_IH : FStar_Absyn_Syntax.lident = (pconst "InductionHyp")

# 78 "FStar.Absyn.Const.fst"
let using_lem : FStar_Absyn_Syntax.lident = (pconst "Using")

# 79 "FStar.Absyn.Const.fst"
let admit_lid : FStar_Absyn_Syntax.lident = (pconst "admit")

# 80 "FStar.Absyn.Const.fst"
let magic_lid : FStar_Absyn_Syntax.lident = (pconst "magic")

# 81 "FStar.Absyn.Const.fst"
let eq_lid : FStar_Absyn_Syntax.lident = (pconst "Eq")

# 84 "FStar.Absyn.Const.fst"
let eq2_lid : FStar_Absyn_Syntax.lident = (pconst "Eq2")

# 85 "FStar.Absyn.Const.fst"
let eqA_lid : FStar_Absyn_Syntax.lident = (pconst "EqA")

# 86 "FStar.Absyn.Const.fst"
let eqT_lid : FStar_Absyn_Syntax.lident = (pconst "EqTyp")

# 87 "FStar.Absyn.Const.fst"
let neq_lid : FStar_Absyn_Syntax.lident = (pconst "neq")

# 88 "FStar.Absyn.Const.fst"
let neq2_lid : FStar_Absyn_Syntax.lident = (pconst "neq2")

# 89 "FStar.Absyn.Const.fst"
let exp_true_bool : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

# 92 "FStar.Absyn.Const.fst"
let exp_false_bool : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

# 93 "FStar.Absyn.Const.fst"
let exp_unit : FStar_Absyn_Syntax.exp = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None FStar_Absyn_Syntax.dummyRange)

# 94 "FStar.Absyn.Const.fst"
let cons_lid : FStar_Absyn_Syntax.lident = (pconst "Cons")

# 95 "FStar.Absyn.Const.fst"
let nil_lid : FStar_Absyn_Syntax.lident = (pconst "Nil")

# 96 "FStar.Absyn.Const.fst"
let assume_lid : FStar_Absyn_Syntax.lident = (pconst "_assume")

# 97 "FStar.Absyn.Const.fst"
let assert_lid : FStar_Absyn_Syntax.lident = (pconst "_assert")

# 98 "FStar.Absyn.Const.fst"
let list_append_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("List")::("append")::[]))

# 99 "FStar.Absyn.Const.fst"
let strcat_lid : FStar_Absyn_Syntax.lident = (p2l (("Prims")::("strcat")::[]))

# 100 "FStar.Absyn.Const.fst"
let let_in_typ : FStar_Absyn_Syntax.lident = (p2l (("Prims")::("Let")::[]))

# 101 "FStar.Absyn.Const.fst"
let op_Eq : FStar_Absyn_Syntax.lident = (pconst "op_Equality")

# 104 "FStar.Absyn.Const.fst"
let op_notEq : FStar_Absyn_Syntax.lident = (pconst "op_disEquality")

# 105 "FStar.Absyn.Const.fst"
let op_LT : FStar_Absyn_Syntax.lident = (pconst "op_LessThan")

# 106 "FStar.Absyn.Const.fst"
let op_LTE : FStar_Absyn_Syntax.lident = (pconst "op_LessThanOrEqual")

# 107 "FStar.Absyn.Const.fst"
let op_GT : FStar_Absyn_Syntax.lident = (pconst "op_GreaterThan")

# 108 "FStar.Absyn.Const.fst"
let op_GTE : FStar_Absyn_Syntax.lident = (pconst "op_GreaterThanOrEqual")

# 109 "FStar.Absyn.Const.fst"
let op_Subtraction : FStar_Absyn_Syntax.lident = (pconst "op_Subtraction")

# 110 "FStar.Absyn.Const.fst"
let op_Minus : FStar_Absyn_Syntax.lident = (pconst "op_Minus")

# 111 "FStar.Absyn.Const.fst"
let op_Addition : FStar_Absyn_Syntax.lident = (pconst "op_Addition")

# 112 "FStar.Absyn.Const.fst"
let op_Multiply : FStar_Absyn_Syntax.lident = (pconst "op_Multiply")

# 113 "FStar.Absyn.Const.fst"
let op_Division : FStar_Absyn_Syntax.lident = (pconst "op_Division")

# 114 "FStar.Absyn.Const.fst"
let op_Modulus : FStar_Absyn_Syntax.lident = (pconst "op_Modulus")

# 115 "FStar.Absyn.Const.fst"
let op_And : FStar_Absyn_Syntax.lident = (pconst "op_AmpAmp")

# 116 "FStar.Absyn.Const.fst"
let op_Or : FStar_Absyn_Syntax.lident = (pconst "op_BarBar")

# 117 "FStar.Absyn.Const.fst"
let op_Negation : FStar_Absyn_Syntax.lident = (pconst "op_Negation")

# 118 "FStar.Absyn.Const.fst"
let array_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 121 "FStar.Absyn.Const.fst"
let array_mk_array_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 122 "FStar.Absyn.Const.fst"
let st_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::[]))

# 125 "FStar.Absyn.Const.fst"
let write_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 126 "FStar.Absyn.Const.fst"
let read_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 127 "FStar.Absyn.Const.fst"
let alloc_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 128 "FStar.Absyn.Const.fst"
let op_ColonEq : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 129 "FStar.Absyn.Const.fst"
let ref_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 132 "FStar.Absyn.Const.fst"
let heap_ref : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 133 "FStar.Absyn.Const.fst"
let set_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::[]))

# 134 "FStar.Absyn.Const.fst"
let set_empty : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 135 "FStar.Absyn.Const.fst"
let set_singleton : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 136 "FStar.Absyn.Const.fst"
let set_union : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 137 "FStar.Absyn.Const.fst"
let effect_PURE_lid : FStar_Absyn_Syntax.lident = (pconst "PURE")

# 140 "FStar.Absyn.Const.fst"
let effect_Pure_lid : FStar_Absyn_Syntax.lident = (pconst "Pure")

# 141 "FStar.Absyn.Const.fst"
let effect_Tot_lid : FStar_Absyn_Syntax.lident = (pconst "Tot")

# 142 "FStar.Absyn.Const.fst"
let effect_Lemma_lid : FStar_Absyn_Syntax.lident = (pconst "Lemma")

# 143 "FStar.Absyn.Const.fst"
let effect_GTot_lid : FStar_Absyn_Syntax.lident = (pconst "GTot")

# 144 "FStar.Absyn.Const.fst"
let effect_GHOST_lid : FStar_Absyn_Syntax.lident = (pconst "GHOST")

# 145 "FStar.Absyn.Const.fst"
let effect_Ghost_lid : FStar_Absyn_Syntax.lident = (pconst "Ghost")

# 146 "FStar.Absyn.Const.fst"
let all_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::[]))

# 149 "FStar.Absyn.Const.fst"
let effect_ALL_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 150 "FStar.Absyn.Const.fst"
let effect_ML_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 151 "FStar.Absyn.Const.fst"
let failwith_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 152 "FStar.Absyn.Const.fst"
let pipe_right_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 153 "FStar.Absyn.Const.fst"
let pipe_left_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 154 "FStar.Absyn.Const.fst"
let try_with_lid : FStar_Absyn_Syntax.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 155 "FStar.Absyn.Const.fst"
let as_requires : FStar_Absyn_Syntax.lident = (pconst "as_requires")

# 157 "FStar.Absyn.Const.fst"
let as_ensures : FStar_Absyn_Syntax.lident = (pconst "as_ensures")

# 158 "FStar.Absyn.Const.fst"
let decreases_lid : FStar_Absyn_Syntax.lident = (pconst "decreases")





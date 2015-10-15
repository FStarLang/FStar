
open Prims
let p2l = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

let pconst = (fun s -> (p2l (("Prims")::(s)::[])))

let prims_lid = (p2l (("Prims")::[]))

let fstar_ns_lid = (p2l (("FStar")::[]))

let bool_lid = (pconst "bool")

let unit_lid = (pconst "unit")

let string_lid = (pconst "string")

let bytes_lid = (pconst "bytes")

let char_lid = (pconst "char")

let int_lid = (pconst "int")

let uint8_lid = (pconst "uint8")

let int64_lid = (pconst "int64")

let float_lid = (pconst "float")

let exn_lid = (pconst "exn")

let list_lid = (pconst "list")

let pattern_lid = (pconst "pattern")

let precedes_lid = (pconst "Precedes")

let lex_t_lid = (pconst "lex_t")

let lexcons_lid = (pconst "LexCons")

let lextop_lid = (pconst "LexTop")

let int32_lid = (p2l (("FStar")::("Int32")::("int32")::[]))

let int31_lid = (p2l (("FStar")::("Int31")::("int31")::[]))

let heap_lid = (p2l (("FStar")::("Heap")::("heap")::[]))

let kunary = (fun k k' -> (let _89_11 = (let _89_10 = (let _89_9 = (FStar_Absyn_Syntax.null_t_binder k)
in (_89_9)::[])
in (_89_10, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _89_11 FStar_Absyn_Syntax.dummyRange)))

let kbin = (fun k1 k2 k' -> (let _89_22 = (let _89_21 = (let _89_20 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _89_19 = (let _89_18 = (FStar_Absyn_Syntax.null_t_binder k2)
in (_89_18)::[])
in (_89_20)::_89_19))
in (_89_21, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _89_22 FStar_Absyn_Syntax.dummyRange)))

let ktern = (fun k1 k2 k3 k' -> (let _89_37 = (let _89_36 = (let _89_35 = (FStar_Absyn_Syntax.null_t_binder k1)
in (let _89_34 = (let _89_33 = (FStar_Absyn_Syntax.null_t_binder k2)
in (let _89_32 = (let _89_31 = (FStar_Absyn_Syntax.null_t_binder k3)
in (_89_31)::[])
in (_89_33)::_89_32))
in (_89_35)::_89_34))
in (_89_36, k'))
in (FStar_Absyn_Syntax.mk_Kind_arrow _89_37 FStar_Absyn_Syntax.dummyRange)))

let true_lid = (pconst "True")

let false_lid = (pconst "False")

let and_lid = (pconst "l_and")

let or_lid = (pconst "l_or")

let not_lid = (pconst "l_not")

let imp_lid = (pconst "l_imp")

let iff_lid = (pconst "l_iff")

let ite_lid = (pconst "ITE")

let exists_lid = (pconst "Exists")

let forall_lid = (pconst "Forall")

let exTyp_lid = (pconst "ExistsTyp")

let allTyp_lid = (pconst "ForallTyp")

let b2t_lid = (pconst "b2t")

let using_IH = (pconst "InductionHyp")

let using_lem = (pconst "Using")

let admit_lid = (pconst "admit")

let magic_lid = (pconst "magic")

let eq_lid = (pconst "Eq")

let eq2_lid = (pconst "Eq2")

let eqA_lid = (pconst "EqA")

let eqT_lid = (pconst "EqTyp")

let neq_lid = (pconst "neq")

let neq2_lid = (pconst "neq2")

let exp_true_bool = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Absyn_Syntax.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

let exp_false_bool = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Absyn_Syntax.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

let exp_unit = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Absyn_Syntax.Const_unit None FStar_Absyn_Syntax.dummyRange)

let cons_lid = (pconst "Cons")

let nil_lid = (pconst "Nil")

let assume_lid = (pconst "_assume")

let assert_lid = (pconst "_assert")

let list_append_lid = (p2l (("FStar")::("List")::("append")::[]))

let strcat_lid = (p2l (("Prims")::("strcat")::[]))

let op_Eq = (pconst "op_Equality")

let op_notEq = (pconst "op_disEquality")

let op_LT = (pconst "op_LessThan")

let op_LTE = (pconst "op_LessThanOrEqual")

let op_GT = (pconst "op_GreaterThan")

let op_GTE = (pconst "op_GreaterThanOrEqual")

let op_Subtraction = (pconst "op_Subtraction")

let op_Minus = (pconst "op_Minus")

let op_Addition = (pconst "op_Addition")

let op_Multiply = (pconst "op_Multiply")

let op_Division = (pconst "op_Division")

let op_Modulus = (pconst "op_Modulus")

let op_And = (pconst "op_AmpAmp")

let op_Or = (pconst "op_BarBar")

let op_Negation = (pconst "op_Negation")

let array_lid = (p2l (("FStar")::("Array")::("array")::[]))

let array_mk_array_lid = (p2l (("FStar")::("Array")::("mk_array")::[]))

let st_lid = (p2l (("FStar")::("ST")::[]))

let write_lid = (p2l (("FStar")::("ST")::("write")::[]))

let read_lid = (p2l (("FStar")::("ST")::("read")::[]))

let alloc_lid = (p2l (("FStar")::("ST")::("alloc")::[]))

let op_ColonEq = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

let ref_lid = (p2l (("FStar")::("Heap")::("ref")::[]))

let heap_ref = (p2l (("FStar")::("Heap")::("Ref")::[]))

let set_empty = (p2l (("FStar")::("Set")::("empty")::[]))

let set_singleton = (p2l (("FStar")::("Set")::("singleton")::[]))

let set_union = (p2l (("FStar")::("Set")::("union")::[]))

let effect_PURE_lid = (pconst "PURE")

let effect_Pure_lid = (pconst "Pure")

let effect_Tot_lid = (pconst "Tot")

let effect_Lemma_lid = (pconst "Lemma")

let effect_GTot_lid = (pconst "GTot")

let effect_GHOST_lid = (pconst "GHOST")

let effect_Ghost_lid = (pconst "Ghost")

let all_lid = (p2l (("FStar")::("All")::[]))

let effect_ALL_lid = (p2l (("FStar")::("All")::("ALL")::[]))

let effect_ML_lid = (p2l (("FStar")::("All")::("ML")::[]))

let failwith_lid = (p2l (("FStar")::("All")::("failwith")::[]))

let pipe_right_lid = (p2l (("FStar")::("All")::("pipe_right")::[]))

let pipe_left_lid = (p2l (("FStar")::("All")::("pipe_left")::[]))

let try_with_lid = (p2l (("FStar")::("All")::("try_with")::[]))

let as_requires = (pconst "as_requires")

let as_ensures = (pconst "as_ensures")

let decreases_lid = (pconst "decreases")

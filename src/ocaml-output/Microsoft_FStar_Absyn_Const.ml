
let p2l = (fun ( l  :  Microsoft_FStar_Absyn_Syntax.path ) -> (Microsoft_FStar_Absyn_Syntax.lid_of_path l Microsoft_FStar_Absyn_Syntax.dummyRange))

let pconst = (fun ( s  :  string ) -> (p2l (("Prims")::(s)::[])))

let prims_lid = (p2l (("Prims")::[]))

let heap_lid = (pconst "heap")

let bool_lid = (pconst "bool")

let unit_lid = (pconst "unit")

let string_lid = (pconst "string")

let bytes_lid = (pconst "bytes")

let char_lid = (pconst "char")

let int_lid = (pconst "int")

let uint8_lid = (pconst "uint8")

let int32_lid = (p2l (("Int32")::("int32")::[]))

let int31_lid = (p2l (("Int31")::("int31")::[]))

let int64_lid = (pconst "int64")

let float_lid = (pconst "float")

let exn_lid = (pconst "exn")

let precedes_lid = (pconst "Precedes")

let lex_t_lid = (pconst "lex_t")

let lexcons_lid = (pconst "LexCons")

let lextop_lid = (pconst "LexTop")

let kunary = (fun ( k  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k'  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_4326 = (let _52_4325 = (let _52_4324 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k)
in (_52_4324)::[])
in (_52_4325, k'))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_4326 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let kbin = (fun ( k1  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k2  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k'  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_4337 = (let _52_4336 = (let _52_4335 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k1)
in (let _52_4334 = (let _52_4333 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k2)
in (_52_4333)::[])
in (_52_4335)::_52_4334))
in (_52_4336, k'))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_4337 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let ktern = (fun ( k1  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k2  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k3  :  Microsoft_FStar_Absyn_Syntax.knd ) ( k'  :  Microsoft_FStar_Absyn_Syntax.knd ) -> (let _52_4352 = (let _52_4351 = (let _52_4350 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k1)
in (let _52_4349 = (let _52_4348 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k2)
in (let _52_4347 = (let _52_4346 = (Microsoft_FStar_Absyn_Syntax.null_t_binder k3)
in (_52_4346)::[])
in (_52_4348)::_52_4347))
in (_52_4350)::_52_4349))
in (_52_4351, k'))
in (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow _52_4352 Microsoft_FStar_Absyn_Syntax.dummyRange)))

let true_lid = (pconst "True")

let false_lid = (pconst "False")

let and_lid = (pconst "l_and")

let or_lid = (pconst "l_or")

let not_lid = (pconst "l_not")

let lbl_lid = (pconst "LBL")

let imp_lid = (pconst "l_imp")

let iff_lid = (pconst "l_iff")

let ite_lid = (pconst "ITE")

let exists_lid = (pconst "Exists")

let forall_lid = (pconst "Forall")

let exTyp_lid = (pconst "ExistsTyp")

let allTyp_lid = (pconst "ForallTyp")

let b2t_lid = (pconst "b2t")

let using_IH = (pconst "InductionHyp")

let admit_lid = (pconst "admit")

let magic_lid = (pconst "magic")

let eq_lid = (pconst "Eq")

let eq2_lid = (pconst "Eq2")

let eqA_lid = (pconst "EqA")

let eqT_lid = (pconst "EqTyp")

let neq_lid = (pconst "neq")

let neq2_lid = (pconst "neq2")

let exp_true_bool = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (true)) None Microsoft_FStar_Absyn_Syntax.dummyRange)

let exp_false_bool = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant (Microsoft_FStar_Absyn_Syntax.Const_bool (false)) None Microsoft_FStar_Absyn_Syntax.dummyRange)

let exp_unit = (Microsoft_FStar_Absyn_Syntax.mk_Exp_constant Microsoft_FStar_Absyn_Syntax.Const_unit None Microsoft_FStar_Absyn_Syntax.dummyRange)

let cons_lid = (pconst "Cons")

let nil_lid = (pconst "Nil")

let ref_lid = (pconst "ref")

let assume_lid = (pconst "_assume")

let assert_lid = (pconst "_assert")

let pipe_right_lid = (pconst "pipe_right")

let pipe_left_lid = (pconst "pipe_left")

let list_append_lid = (p2l (("List")::("append")::[]))

let strcat_lid = (p2l (("String")::("strcat")::[]))

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

let try_with_lid = (pconst "try_with")

let array_lid = (p2l (("Array")::("array")::[]))

let array_mk_array_lid = (p2l (("Array")::("mk_array")::[]))

let write_lid = (p2l (("ST")::("write")::[]))

let read_lid = (p2l (("ST")::("read")::[]))

let alloc_lid = (p2l (("ST")::("alloc")::[]))

let op_ColonEq = (p2l (("ST")::("op_Colon_Equals")::[]))

let set_empty = (p2l (("Set")::("empty")::[]))

let heap_ref = (p2l (("Heap")::("Ref")::[]))

let set_singleton = (p2l (("Set")::("singleton")::[]))

let set_union = (p2l (("Set")::("union")::[]))

let effect_PURE_lid = (pconst "PURE")

let effect_Pure_lid = (pconst "Pure")

let effect_Tot_lid = (pconst "Tot")

let effect_ALL_lid = (pconst "ALL")

let effect_ML_lid = (pconst "ML")

let effect_Lemma_lid = (pconst "Lemma")

let effect_GTot_lid = (pconst "GTot")

let effect_GHOST_lid = (pconst "GHOST")

let effect_Ghost_lid = (pconst "Ghost")

let as_requires = (pconst "as_requires")

let as_ensures = (pconst "as_ensures")

let decreases_lid = (pconst "decreases")

let failwith_lid = (pconst "failwith")





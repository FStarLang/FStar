
let p2l = (fun l -> (Microsoft_FStar_Absyn_Syntax.lid_of_path l Microsoft_FStar_Absyn_Syntax.dummyRange))

let pconst = (fun s -> (p2l (("Prims")::(s)::[])))

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

let lex_t_lid = (pconst "lex\x5ft")

let lexcons_lid = (pconst "LexCons")

let lextop_lid = (pconst "LexTop")

let kunary = (fun k k' -> (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder k))::[], k') Microsoft_FStar_Absyn_Syntax.dummyRange))

let kbin = (fun k1 k2 k' -> (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder k1))::((Microsoft_FStar_Absyn_Syntax.null_t_binder k2))::[], k') Microsoft_FStar_Absyn_Syntax.dummyRange))

let ktern = (fun k1 k2 k3 k' -> (Microsoft_FStar_Absyn_Syntax.mk_Kind_arrow (((Microsoft_FStar_Absyn_Syntax.null_t_binder k1))::((Microsoft_FStar_Absyn_Syntax.null_t_binder k2))::((Microsoft_FStar_Absyn_Syntax.null_t_binder k3))::[], k') Microsoft_FStar_Absyn_Syntax.dummyRange))

let true_lid = (pconst "True")

let false_lid = (pconst "False")

let and_lid = (pconst "l\x5fand")

let or_lid = (pconst "l\x5for")

let not_lid = (pconst "l\x5fnot")

let lbl_lid = (pconst "LBL")

let imp_lid = (pconst "l\x5fimp")

let iff_lid = (pconst "l\x5fiff")

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

let assume_lid = (pconst "\x5fassume")

let assert_lid = (pconst "\x5fassert")

let pipe_right_lid = (pconst "pipe\x5fright")

let pipe_left_lid = (pconst "pipe\x5fleft")

let list_append_lid = (p2l (("List")::("append")::[]))

let strcat_lid = (p2l (("String")::("strcat")::[]))

let op_Eq = (pconst "op\x5fEquality")

let op_notEq = (pconst "op\x5fdisEquality")

let op_LT = (pconst "op\x5fLessThan")

let op_LTE = (pconst "op\x5fLessThanOrEqual")

let op_GT = (pconst "op\x5fGreaterThan")

let op_GTE = (pconst "op\x5fGreaterThanOrEqual")

let op_Subtraction = (pconst "op\x5fSubtraction")

let op_Minus = (pconst "op\x5fMinus")

let op_Addition = (pconst "op\x5fAddition")

let op_Multiply = (pconst "op\x5fMultiply")

let op_Division = (pconst "op\x5fDivision")

let op_Modulus = (pconst "op\x5fModulus")

let op_And = (pconst "op\x5fAmpAmp")

let op_Or = (pconst "op\x5fBarBar")

let op_Negation = (pconst "op\x5fNegation")

let try_with_lid = (pconst "try\x5fwith")

let array_lid = (p2l (("Array")::("array")::[]))

let array_mk_array_lid = (p2l (("Array")::("mk\x5farray")::[]))

let write_lid = (p2l (("ST")::("write")::[]))

let read_lid = (p2l (("ST")::("read")::[]))

let alloc_lid = (p2l (("ST")::("alloc")::[]))

let op_ColonEq = (p2l (("ST")::("op\x5fColon\x5fEquals")::[]))

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

let as_requires = (pconst "as\x5frequires")

let as_ensures = (pconst "as\x5fensures")

let decreases_lid = (pconst "decreases")





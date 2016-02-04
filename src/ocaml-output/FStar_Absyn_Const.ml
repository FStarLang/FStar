
open Prims
let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

let bool_lid : FStar_Ident.lident = (pconst "bool")

let unit_lid : FStar_Ident.lident = (pconst "unit")

let string_lid : FStar_Ident.lident = (pconst "string")

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

let char_lid : FStar_Ident.lident = (pconst "char")

let int_lid : FStar_Ident.lident = (pconst "int")

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

let int64_lid : FStar_Ident.lident = (pconst "int64")

let float_lid : FStar_Ident.lident = (pconst "float")

let exn_lid : FStar_Ident.lident = (pconst "exn")

let list_lid : FStar_Ident.lident = (pconst "list")

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

let precedes_lid : FStar_Ident.lident = (pconst "Precedes")

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

let kunary : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k))::[], k') FStar_Absyn_Syntax.dummyRange))

let kbin : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::[], k') FStar_Absyn_Syntax.dummyRange))

let ktern : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k3 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::((FStar_Absyn_Syntax.null_t_binder k3))::[], k') FStar_Absyn_Syntax.dummyRange))

let true_lid : FStar_Ident.lident = (pconst "True")

let false_lid : FStar_Ident.lident = (pconst "False")

let and_lid : FStar_Ident.lident = (pconst "l_and")

let or_lid : FStar_Ident.lident = (pconst "l_or")

let not_lid : FStar_Ident.lident = (pconst "l_not")

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

let ite_lid : FStar_Ident.lident = (pconst "ITE")

let exists_lid : FStar_Ident.lident = (pconst "Exists")

let forall_lid : FStar_Ident.lident = (pconst "Forall")

let exTyp_lid : FStar_Ident.lident = (pconst "ExistsTyp")

let allTyp_lid : FStar_Ident.lident = (pconst "ForallTyp")

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

let using_lem : FStar_Ident.lident = (pconst "Using")

let admit_lid : FStar_Ident.lident = (pconst "admit")

let magic_lid : FStar_Ident.lident = (pconst "magic")

let eq_lid : FStar_Ident.lident = (pconst "Eq")

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

let eqA_lid : FStar_Ident.lident = (pconst "EqA")

let eqT_lid : FStar_Ident.lident = (pconst "EqTyp")

let neq_lid : FStar_Ident.lident = (pconst "neq")

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

let exp_true_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

let exp_false_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

let exp_unit : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None FStar_Absyn_Syntax.dummyRange)

let cons_lid : FStar_Ident.lident = (pconst "Cons")

let nil_lid : FStar_Ident.lident = (pconst "Nil")

let assume_lid : FStar_Ident.lident = (pconst "_assume")

let assert_lid : FStar_Ident.lident = (pconst "_assert")

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

let op_Division : FStar_Ident.lident = (pconst "op_Division")

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

let set_lid : FStar_Ident.lident = (p2l (("FStar")::("Set")::[]))

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

let as_requires : FStar_Ident.lident = (pconst "as_requires")

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





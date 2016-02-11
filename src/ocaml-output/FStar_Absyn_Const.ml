
open Prims
# 22 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

# 23 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 24 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 25 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 28 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let bool_lid : FStar_Ident.lident = (pconst "bool")

# 29 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let unit_lid : FStar_Ident.lident = (pconst "unit")

# 30 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let string_lid : FStar_Ident.lident = (pconst "string")

# 31 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 32 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let char_lid : FStar_Ident.lident = (pconst "char")

# 33 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let int_lid : FStar_Ident.lident = (pconst "int")

# 34 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 35 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let int64_lid : FStar_Ident.lident = (pconst "int64")

# 36 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let float_lid : FStar_Ident.lident = (pconst "float")

# 37 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exn_lid : FStar_Ident.lident = (pconst "exn")

# 38 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let list_lid : FStar_Ident.lident = (pconst "list")

# 39 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 40 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let precedes_lid : FStar_Ident.lident = (pconst "Precedes")

# 41 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 42 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 43 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 44 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 45 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 46 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 48 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 49 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 50 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 53 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let kunary : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k))::[], k') FStar_Absyn_Syntax.dummyRange))

# 54 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let kbin : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::[], k') FStar_Absyn_Syntax.dummyRange))

# 55 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let ktern : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k3 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::((FStar_Absyn_Syntax.null_t_binder k3))::[], k') FStar_Absyn_Syntax.dummyRange))

# 58 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let true_lid : FStar_Ident.lident = (pconst "True")

# 59 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let false_lid : FStar_Ident.lident = (pconst "False")

# 60 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let and_lid : FStar_Ident.lident = (pconst "l_and")

# 61 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let or_lid : FStar_Ident.lident = (pconst "l_or")

# 62 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let not_lid : FStar_Ident.lident = (pconst "l_not")

# 63 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 64 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 65 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 66 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 67 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 68 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exTyp_lid : FStar_Ident.lident = (pconst "ExistsTyp")

# 69 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let allTyp_lid : FStar_Ident.lident = (pconst "ForallTyp")

# 70 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 71 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 72 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let using_lem : FStar_Ident.lident = (pconst "Using")

# 73 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let admit_lid : FStar_Ident.lident = (pconst "admit")

# 74 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let magic_lid : FStar_Ident.lident = (pconst "magic")

# 77 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let eq_lid : FStar_Ident.lident = (pconst "Eq")

# 78 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 79 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let eqA_lid : FStar_Ident.lident = (pconst "EqA")

# 80 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let eqT_lid : FStar_Ident.lident = (pconst "EqTyp")

# 81 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let neq_lid : FStar_Ident.lident = (pconst "neq")

# 82 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 85 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exp_true_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

# 86 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exp_false_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

# 87 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let exp_unit : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None FStar_Absyn_Syntax.dummyRange)

# 88 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 89 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 90 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 91 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 92 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 93 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 94 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 97 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 98 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 99 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 100 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 101 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 102 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 103 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 104 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 105 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 106 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 107 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 108 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 109 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 110 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 111 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 114 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 115 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 118 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 119 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 120 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 121 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 125 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 126 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 127 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let set_lid : FStar_Ident.lident = (p2l (("FStar")::("Set")::[]))

# 128 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 129 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 130 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 133 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 134 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 135 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 136 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 137 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 138 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 139 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 142 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 143 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 144 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 145 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 146 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 147 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 148 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 150 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 151 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 152 "C:\\Users\\nswamy\\workspace\\FStar\\src\\absyn\\const.fs"

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





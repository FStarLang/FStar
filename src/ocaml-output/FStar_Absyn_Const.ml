
open Prims
# 20 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Absyn_Syntax.lid_of_path l FStar_Absyn_Syntax.dummyRange))

# 22 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 23 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 24 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 25 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let bool_lid : FStar_Ident.lident = (pconst "bool")

# 28 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let unit_lid : FStar_Ident.lident = (pconst "unit")

# 29 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let string_lid : FStar_Ident.lident = (pconst "string")

# 30 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 31 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let char_lid : FStar_Ident.lident = (pconst "char")

# 32 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let int_lid : FStar_Ident.lident = (pconst "int")

# 33 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let int64_lid : FStar_Ident.lident = (pconst "int64")

# 35 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let float_lid : FStar_Ident.lident = (pconst "float")

# 36 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exn_lid : FStar_Ident.lident = (pconst "exn")

# 37 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let list_lid : FStar_Ident.lident = (pconst "list")

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 39 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let precedes_lid : FStar_Ident.lident = (pconst "Precedes")

# 40 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 41 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 42 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 43 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 44 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 45 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 46 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 48 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 50 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let kunary : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k))::[], k') FStar_Absyn_Syntax.dummyRange))

# 53 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let kbin : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::[], k') FStar_Absyn_Syntax.dummyRange))

# 54 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let ktern : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k1 k2 k3 k' -> (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k1))::((FStar_Absyn_Syntax.null_t_binder k2))::((FStar_Absyn_Syntax.null_t_binder k3))::[], k') FStar_Absyn_Syntax.dummyRange))

# 57 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let true_lid : FStar_Ident.lident = (pconst "True")

# 58 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let false_lid : FStar_Ident.lident = (pconst "False")

# 59 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let and_lid : FStar_Ident.lident = (pconst "l_and")

# 60 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let or_lid : FStar_Ident.lident = (pconst "l_or")

# 61 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let not_lid : FStar_Ident.lident = (pconst "l_not")

# 62 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 63 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 64 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 65 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 66 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 67 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exTyp_lid : FStar_Ident.lident = (pconst "ExistsTyp")

# 68 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let allTyp_lid : FStar_Ident.lident = (pconst "ForallTyp")

# 69 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 70 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let using_lem : FStar_Ident.lident = (pconst "Using")

# 72 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let admit_lid : FStar_Ident.lident = (pconst "admit")

# 73 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let magic_lid : FStar_Ident.lident = (pconst "magic")

# 74 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let eq_lid : FStar_Ident.lident = (pconst "Eq")

# 77 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 78 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let eqA_lid : FStar_Ident.lident = (pconst "EqA")

# 79 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let eqT_lid : FStar_Ident.lident = (pconst "EqTyp")

# 80 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let neq_lid : FStar_Ident.lident = (pconst "neq")

# 81 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 82 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exp_true_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (true)) None FStar_Absyn_Syntax.dummyRange)

# 85 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exp_false_bool : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant (FStar_Const.Const_bool (false)) None FStar_Absyn_Syntax.dummyRange)

# 86 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let exp_unit : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None FStar_Absyn_Syntax.dummyRange)

# 87 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 88 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 89 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 90 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 91 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 92 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 93 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 94 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 97 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 98 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 99 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 100 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 101 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 102 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 103 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 104 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 105 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 106 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 107 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 108 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 109 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 110 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 111 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 114 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 115 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 118 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 119 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 120 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 121 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 122 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 125 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 126 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let set_lid : FStar_Ident.lident = (p2l (("FStar")::("Set")::[]))

# 127 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 128 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 129 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 130 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 133 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 134 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 135 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 136 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 137 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 138 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 139 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 142 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 143 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 144 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 145 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 146 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 147 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 148 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 150 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 151 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\absyn\\const.fs"

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





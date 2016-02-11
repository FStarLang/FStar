
open Prims
# 24 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

# 25 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

# 26 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 27 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 28 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 31 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let bool_lid : FStar_Ident.lident = (pconst "bool")

# 32 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let unit_lid : FStar_Ident.lident = (pconst "unit")

# 33 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let string_lid : FStar_Ident.lident = (pconst "string")

# 34 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 35 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let char_lid : FStar_Ident.lident = (pconst "char")

# 36 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let int_lid : FStar_Ident.lident = (pconst "int")

# 37 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 38 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let int64_lid : FStar_Ident.lident = (pconst "int64")

# 39 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let float_lid : FStar_Ident.lident = (pconst "float")

# 40 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let exn_lid : FStar_Ident.lident = (pconst "exn")

# 41 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let list_lid : FStar_Ident.lident = (pconst "list")

# 42 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 43 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 44 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 45 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 46 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 47 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 48 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 49 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 51 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 52 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 53 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 56 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _135_13 = (let _135_12 = (let _135_11 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k))::[], _135_11))
in FStar_Syntax_Syntax.Tm_arrow (_135_12))
in (mk _135_13)))

# 57 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _135_22 = (let _135_21 = (let _135_20 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::[], _135_20))
in FStar_Syntax_Syntax.Tm_arrow (_135_21))
in (mk _135_22)))

# 58 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _135_33 = (let _135_32 = (let _135_31 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::((FStar_Syntax_Syntax.null_binder k3))::[], _135_31))
in FStar_Syntax_Syntax.Tm_arrow (_135_32))
in (mk _135_33)))

# 61 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let true_lid : FStar_Ident.lident = (pconst "True")

# 62 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let false_lid : FStar_Ident.lident = (pconst "False")

# 63 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let and_lid : FStar_Ident.lident = (pconst "l_and")

# 64 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let or_lid : FStar_Ident.lident = (pconst "l_or")

# 65 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let not_lid : FStar_Ident.lident = (pconst "l_not")

# 66 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 67 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 68 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 69 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 70 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 71 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 72 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 73 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let admit_lid : FStar_Ident.lident = (pconst "admit")

# 74 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let magic_lid : FStar_Ident.lident = (pconst "magic")

# 77 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 78 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let neq_lid : FStar_Ident.lident = (pconst "neq")

# 79 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 82 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 83 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 84 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 85 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 86 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 87 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 88 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 89 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 90 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 91 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 94 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 95 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 96 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 97 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 98 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 99 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 100 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 101 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 102 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 103 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 104 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 105 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 106 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 107 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 108 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 111 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 112 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 115 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 116 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 117 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 118 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 119 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 122 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 123 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 124 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 125 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 126 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 129 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 130 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 131 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 132 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 133 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 134 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 135 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 138 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 139 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 140 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 141 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 142 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 143 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 144 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 146 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 147 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 148 "C:\\Users\\nswamy\\workspace\\FStar\\src\\syntax\\const.fs"

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





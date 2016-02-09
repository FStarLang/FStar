
open Prims
# 24 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

# 25 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

# 26 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 27 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 28 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 31 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let bool_lid : FStar_Ident.lident = (pconst "bool")

# 32 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let unit_lid : FStar_Ident.lident = (pconst "unit")

# 33 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let string_lid : FStar_Ident.lident = (pconst "string")

# 34 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 35 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let char_lid : FStar_Ident.lident = (pconst "char")

# 36 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let int_lid : FStar_Ident.lident = (pconst "int")

# 37 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 38 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let int64_lid : FStar_Ident.lident = (pconst "int64")

# 39 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let float_lid : FStar_Ident.lident = (pconst "float")

# 40 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let exn_lid : FStar_Ident.lident = (pconst "exn")

# 41 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let list_lid : FStar_Ident.lident = (pconst "list")

# 42 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 43 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 44 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 45 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 46 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 47 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 48 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 49 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 51 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 52 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 53 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 56 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _135_13 = (let _135_12 = (let _135_11 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k))::[], _135_11))
in FStar_Syntax_Syntax.Tm_arrow (_135_12))
in (mk _135_13)))

# 57 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _135_22 = (let _135_21 = (let _135_20 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::[], _135_20))
in FStar_Syntax_Syntax.Tm_arrow (_135_21))
in (mk _135_22)))

# 58 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _135_33 = (let _135_32 = (let _135_31 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::((FStar_Syntax_Syntax.null_binder k3))::[], _135_31))
in FStar_Syntax_Syntax.Tm_arrow (_135_32))
in (mk _135_33)))

# 61 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let true_lid : FStar_Ident.lident = (pconst "True")

# 62 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let false_lid : FStar_Ident.lident = (pconst "False")

# 63 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let and_lid : FStar_Ident.lident = (pconst "l_and")

# 64 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let or_lid : FStar_Ident.lident = (pconst "l_or")

# 65 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let not_lid : FStar_Ident.lident = (pconst "l_not")

# 66 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 67 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 68 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 69 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 70 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 71 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 72 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 73 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let admit_lid : FStar_Ident.lident = (pconst "admit")

# 74 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let magic_lid : FStar_Ident.lident = (pconst "magic")

# 77 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 78 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let neq_lid : FStar_Ident.lident = (pconst "neq")

# 79 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 82 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 83 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 84 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 85 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 86 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 87 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 88 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 89 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 90 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 91 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 94 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 95 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 96 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 97 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 98 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 99 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 100 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 101 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 102 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 103 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 104 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 105 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 106 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 107 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 108 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 111 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 112 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 115 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 116 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 117 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 118 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 119 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 122 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 123 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 124 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 125 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 126 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 129 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 130 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 131 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 132 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 133 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 134 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 135 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 138 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 139 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 140 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 141 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 142 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 143 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 144 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 146 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 147 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 148 "D:\\workspace\\universes\\FStar\\src\\syntax\\const.fs"

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





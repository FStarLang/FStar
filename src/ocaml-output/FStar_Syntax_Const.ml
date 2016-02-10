
open Prims
# 22 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))

# 24 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))

# 25 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))

# 26 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))

# 27 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))

# 28 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let bool_lid : FStar_Ident.lident = (pconst "bool")

# 31 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let unit_lid : FStar_Ident.lident = (pconst "unit")

# 32 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let string_lid : FStar_Ident.lident = (pconst "string")

# 33 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let bytes_lid : FStar_Ident.lident = (pconst "bytes")

# 34 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let char_lid : FStar_Ident.lident = (pconst "char")

# 35 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let int_lid : FStar_Ident.lident = (pconst "int")

# 36 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let uint8_lid : FStar_Ident.lident = (pconst "uint8")

# 37 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let int64_lid : FStar_Ident.lident = (pconst "int64")

# 38 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let float_lid : FStar_Ident.lident = (pconst "float")

# 39 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let exn_lid : FStar_Ident.lident = (pconst "exn")

# 40 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let list_lid : FStar_Ident.lident = (pconst "list")

# 41 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let pattern_lid : FStar_Ident.lident = (pconst "pattern")

# 42 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let precedes_lid : FStar_Ident.lident = (pconst "precedes")

# 43 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")

# 44 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")

# 45 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let lextop_lid : FStar_Ident.lident = (pconst "LexTop")

# 46 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")

# 47 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")

# 48 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")

# 49 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))

# 51 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let int31_lid : FStar_Ident.lident = (p2l (("FStar")::("Int31")::("int31")::[]))

# 52 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))

# 53 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _135_13 = (let _135_12 = (let _135_11 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k))::[], _135_11))
in FStar_Syntax_Syntax.Tm_arrow (_135_12))
in (mk _135_13)))

# 56 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _135_22 = (let _135_21 = (let _135_20 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::[], _135_20))
in FStar_Syntax_Syntax.Tm_arrow (_135_21))
in (mk _135_22)))

# 57 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _135_33 = (let _135_32 = (let _135_31 = (FStar_Syntax_Syntax.mk_Total k')
in (((FStar_Syntax_Syntax.null_binder k1))::((FStar_Syntax_Syntax.null_binder k2))::((FStar_Syntax_Syntax.null_binder k3))::[], _135_31))
in FStar_Syntax_Syntax.Tm_arrow (_135_32))
in (mk _135_33)))

# 60 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let true_lid : FStar_Ident.lident = (pconst "True")

# 61 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let false_lid : FStar_Ident.lident = (pconst "False")

# 62 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let and_lid : FStar_Ident.lident = (pconst "l_and")

# 63 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let or_lid : FStar_Ident.lident = (pconst "l_or")

# 64 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let not_lid : FStar_Ident.lident = (pconst "l_not")

# 65 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let imp_lid : FStar_Ident.lident = (pconst "l_imp")

# 66 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let iff_lid : FStar_Ident.lident = (pconst "l_iff")

# 67 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let ite_lid : FStar_Ident.lident = (pconst "ITE")

# 68 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let exists_lid : FStar_Ident.lident = (pconst "Exists")

# 69 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let forall_lid : FStar_Ident.lident = (pconst "Forall")

# 70 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let b2t_lid : FStar_Ident.lident = (pconst "b2t")

# 71 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let using_IH : FStar_Ident.lident = (pconst "InductionHyp")

# 72 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let admit_lid : FStar_Ident.lident = (pconst "admit")

# 73 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let magic_lid : FStar_Ident.lident = (pconst "magic")

# 74 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let eq2_lid : FStar_Ident.lident = (pconst "Eq2")

# 77 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let neq_lid : FStar_Ident.lident = (pconst "neq")

# 78 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let neq2_lid : FStar_Ident.lident = (pconst "neq2")

# 79 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))

# 82 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))

# 83 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))

# 84 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let cons_lid : FStar_Ident.lident = (pconst "Cons")

# 85 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let nil_lid : FStar_Ident.lident = (pconst "Nil")

# 86 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let assume_lid : FStar_Ident.lident = (pconst "_assume")

# 87 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let assert_lid : FStar_Ident.lident = (pconst "_assert")

# 88 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let list_append_lid : FStar_Ident.lident = (p2l (("FStar")::("List")::("append")::[]))

# 89 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let strcat_lid : FStar_Ident.lident = (p2l (("Prims")::("strcat")::[]))

# 90 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let let_in_typ : FStar_Ident.lident = (p2l (("Prims")::("Let")::[]))

# 91 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Eq : FStar_Ident.lident = (pconst "op_Equality")

# 94 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_notEq : FStar_Ident.lident = (pconst "op_disEquality")

# 95 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_LT : FStar_Ident.lident = (pconst "op_LessThan")

# 96 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_LTE : FStar_Ident.lident = (pconst "op_LessThanOrEqual")

# 97 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_GT : FStar_Ident.lident = (pconst "op_GreaterThan")

# 98 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_GTE : FStar_Ident.lident = (pconst "op_GreaterThanOrEqual")

# 99 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Subtraction : FStar_Ident.lident = (pconst "op_Subtraction")

# 100 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Minus : FStar_Ident.lident = (pconst "op_Minus")

# 101 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Addition : FStar_Ident.lident = (pconst "op_Addition")

# 102 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Multiply : FStar_Ident.lident = (pconst "op_Multiply")

# 103 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Division : FStar_Ident.lident = (pconst "op_Division")

# 104 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Modulus : FStar_Ident.lident = (pconst "op_Modulus")

# 105 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_And : FStar_Ident.lident = (pconst "op_AmpAmp")

# 106 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Or : FStar_Ident.lident = (pconst "op_BarBar")

# 107 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_Negation : FStar_Ident.lident = (pconst "op_Negation")

# 108 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("array")::[]))

# 111 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let array_mk_array_lid : FStar_Ident.lident = (p2l (("FStar")::("Array")::("mk_array")::[]))

# 112 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let st_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::[]))

# 115 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let write_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("write")::[]))

# 116 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let read_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("read")::[]))

# 117 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let alloc_lid : FStar_Ident.lident = (p2l (("FStar")::("ST")::("alloc")::[]))

# 118 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let op_ColonEq : FStar_Ident.lident = (p2l (("FStar")::("ST")::("op_Colon_Equals")::[]))

# 119 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let ref_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("ref")::[]))

# 122 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let heap_ref : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("Ref")::[]))

# 123 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))

# 124 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))

# 125 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))

# 126 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_PURE_lid : FStar_Ident.lident = (pconst "PURE")

# 129 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_Pure_lid : FStar_Ident.lident = (pconst "Pure")

# 130 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_Tot_lid : FStar_Ident.lident = (pconst "Tot")

# 131 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_Lemma_lid : FStar_Ident.lident = (pconst "Lemma")

# 132 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_GTot_lid : FStar_Ident.lident = (pconst "GTot")

# 133 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_GHOST_lid : FStar_Ident.lident = (pconst "GHOST")

# 134 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_Ghost_lid : FStar_Ident.lident = (pconst "Ghost")

# 135 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let all_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::[]))

# 138 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_ALL_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ALL")::[]))

# 139 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let effect_ML_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("ML")::[]))

# 140 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let failwith_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("failwith")::[]))

# 141 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let pipe_right_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_right")::[]))

# 142 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let pipe_left_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("pipe_left")::[]))

# 143 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let try_with_lid : FStar_Ident.lident = (p2l (("FStar")::("All")::("try_with")::[]))

# 144 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let as_requires : FStar_Ident.lident = (pconst "as_requires")

# 146 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let as_ensures : FStar_Ident.lident = (pconst "as_ensures")

# 147 "D:\\cygwin\\home\\protz\\Code\\fstar\\src\\syntax\\const.fs"

let decreases_lid : FStar_Ident.lident = (pconst "decreases")





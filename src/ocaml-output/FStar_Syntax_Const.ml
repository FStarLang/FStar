
open Prims

let mk : FStar_Syntax_Syntax.term'  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (FStar_Syntax_Syntax.mk t None FStar_Range.dummyRange))


let p2l : Prims.string Prims.list  ->  FStar_Ident.lident = (fun l -> (FStar_Ident.lid_of_path l FStar_Range.dummyRange))


let pconst : Prims.string  ->  FStar_Ident.lident = (fun s -> (p2l (("Prims")::(s)::[])))


let prims_lid : FStar_Ident.lident = (p2l (("Prims")::[]))


let fstar_ns_lid : FStar_Ident.lident = (p2l (("FStar")::[]))


let bool_lid : FStar_Ident.lident = (pconst "bool")


let unit_lid : FStar_Ident.lident = (pconst "unit")


let string_lid : FStar_Ident.lident = (pconst "string")


let bytes_lid : FStar_Ident.lident = (pconst "bytes")


let int_lid : FStar_Ident.lident = (pconst "int")


let exn_lid : FStar_Ident.lident = (pconst "exn")


let list_lid : FStar_Ident.lident = (pconst "list")


let pattern_lid : FStar_Ident.lident = (pconst "pattern")


let precedes_lid : FStar_Ident.lident = (pconst "precedes")


let lex_t_lid : FStar_Ident.lident = (pconst "lex_t")


let lexcons_lid : FStar_Ident.lident = (pconst "LexCons")


let lextop_lid : FStar_Ident.lident = (pconst "LexTop")


let smtpat_lid : FStar_Ident.lident = (pconst "SMTPat")


let smtpatT_lid : FStar_Ident.lident = (pconst "SMTPatT")


let smtpatOr_lid : FStar_Ident.lident = (pconst "SMTPatOr")


let int8_lid : FStar_Ident.lident = (p2l (("FStar")::("Int8")::("int8")::[]))


let uint8_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt8")::("uint8")::[]))


let int16_lid : FStar_Ident.lident = (p2l (("FStar")::("Int16")::("int16")::[]))


let uint16_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt16")::("uint16")::[]))


let int32_lid : FStar_Ident.lident = (p2l (("FStar")::("Int32")::("int32")::[]))


let uint32_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt32")::("uint32")::[]))


let int64_lid : FStar_Ident.lident = (p2l (("FStar")::("Int64")::("int64")::[]))


let uint64_lid : FStar_Ident.lident = (p2l (("FStar")::("UInt64")::("uint64")::[]))


let float_lid : FStar_Ident.lident = (p2l (("FStar")::("Float")::("float")::[]))


let char_lid : FStar_Ident.lident = (p2l (("FStar")::("Char")::("char")::[]))


let heap_lid : FStar_Ident.lident = (p2l (("FStar")::("Heap")::("heap")::[]))


let kunary : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k k' -> (let _123_15 = (let _123_14 = (let _123_13 = (let _123_11 = (FStar_Syntax_Syntax.null_binder k)
in (_123_11)::[])
in (let _123_12 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_13, _123_12)))
in FStar_Syntax_Syntax.Tm_arrow (_123_14))
in (mk _123_15)))


let kbin : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k' -> (let _123_28 = (let _123_27 = (let _123_26 = (let _123_24 = (FStar_Syntax_Syntax.null_binder k1)
in (let _123_23 = (let _123_22 = (FStar_Syntax_Syntax.null_binder k2)
in (_123_22)::[])
in (_123_24)::_123_23))
in (let _123_25 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_26, _123_25)))
in FStar_Syntax_Syntax.Tm_arrow (_123_27))
in (mk _123_28)))


let ktern : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun k1 k2 k3 k' -> (let _123_45 = (let _123_44 = (let _123_43 = (let _123_41 = (FStar_Syntax_Syntax.null_binder k1)
in (let _123_40 = (let _123_39 = (FStar_Syntax_Syntax.null_binder k2)
in (let _123_38 = (let _123_37 = (FStar_Syntax_Syntax.null_binder k3)
in (_123_37)::[])
in (_123_39)::_123_38))
in (_123_41)::_123_40))
in (let _123_42 = (FStar_Syntax_Syntax.mk_Total k')
in (_123_43, _123_42)))
in FStar_Syntax_Syntax.Tm_arrow (_123_44))
in (mk _123_45)))


let true_lid : FStar_Ident.lident = (pconst "l_True")


let false_lid : FStar_Ident.lident = (pconst "l_False")


let and_lid : FStar_Ident.lident = (pconst "l_and")


let or_lid : FStar_Ident.lident = (pconst "l_or")


let not_lid : FStar_Ident.lident = (pconst "l_not")


let imp_lid : FStar_Ident.lident = (pconst "l_imp")


let iff_lid : FStar_Ident.lident = (pconst "l_iff")


let ite_lid : FStar_Ident.lident = (pconst "l_ITE")


let exists_lid : FStar_Ident.lident = (pconst "l_Exists")


let forall_lid : FStar_Ident.lident = (pconst "l_Forall")


let b2t_lid : FStar_Ident.lident = (pconst "b2t")


let admit_lid : FStar_Ident.lident = (pconst "admit")


let magic_lid : FStar_Ident.lident = (pconst "magic")


let has_type_lid : FStar_Ident.lident = (pconst "has_type")


let eq2_lid : FStar_Ident.lident = (pconst "eq2")


let exp_true_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (true))))


let exp_false_bool : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool (false))))


let exp_unit : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))


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


let set_empty : FStar_Ident.lident = (p2l (("FStar")::("Set")::("empty")::[]))


let set_singleton : FStar_Ident.lident = (p2l (("FStar")::("Set")::("singleton")::[]))


let set_union : FStar_Ident.lident = (p2l (("FStar")::("Set")::("union")::[]))


let fstar_hyperheap_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::[]))


let rref_lid : FStar_Ident.lident = (p2l (("FStar")::("HyperHeap")::("rref")::[]))


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


let range_of_lid : FStar_Ident.lident = (pconst "range_of")


let labeled_lid : FStar_Ident.lident = (pconst "labeled")





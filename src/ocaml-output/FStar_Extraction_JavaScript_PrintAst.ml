
open Prims

let semi : FStar_Format.doc = (FStar_Format.text ";")


let comma : FStar_Format.doc = (FStar_Format.text ",")


let dot : FStar_Format.doc = (FStar_Format.text ".")


let colon : FStar_Format.doc = (FStar_Format.text ":")


let ws : FStar_Format.doc = FStar_Format.break1


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___96_9 -> (match (uu___96_9) with
| c when (c = '\\') -> begin
"\\\\"
end
| c when (c = ' ') -> begin
" "
end
| c when (c = '\b') -> begin
"\\b"
end
| c when (c = '\t') -> begin
"\\t"
end
| c when (c = '\r') -> begin
"\\r"
end
| c when (c = '\n') -> begin
"\\n"
end
| c when (c = '\'') -> begin
"\\\'"
end
| c when (c = '\"') -> begin
"\\\""
end
| c when (FStar_Util.is_letter_or_digit c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_punctuation c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_symbol c) -> begin
(FStar_Util.string_of_char c)
end
| c -> begin
(fallback c)
end))


let jstr_escape : Prims.string  ->  Prims.string = (fun s -> (FStar_String.collect (escape_or FStar_Util.string_of_char) s))


let escape_char : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback uu___97_35 -> (match (uu___97_35) with
| c when (c = '\'') -> begin
"_"
end
| c when (FStar_Util.is_letter_or_digit c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_punctuation c) -> begin
(FStar_Util.string_of_char c)
end
| c when (FStar_Util.is_symbol c) -> begin
(FStar_Util.string_of_char c)
end
| c -> begin
(fallback c)
end))


let remove_chars_t : Prims.string  ->  Prims.string = (fun s -> (FStar_String.collect (escape_char FStar_Util.string_of_char) s))


let print_op_un : FStar_Extraction_JavaScript_Ast.op_un  ->  FStar_Format.doc = (fun uu___98_48 -> (match (uu___98_48) with
| FStar_Extraction_JavaScript_Ast.JSU_Minus -> begin
(FStar_Format.text "-")
end
| FStar_Extraction_JavaScript_Ast.JSU_Not -> begin
(FStar_Format.text "!")
end))


let print_op_bin : FStar_Extraction_JavaScript_Ast.op_bin  ->  FStar_Format.doc = (fun uu___99_51 -> (match (uu___99_51) with
| FStar_Extraction_JavaScript_Ast.JSB_Equal -> begin
(FStar_Format.text "==")
end
| FStar_Extraction_JavaScript_Ast.JSB_NotEqual -> begin
(FStar_Format.text "!=")
end
| FStar_Extraction_JavaScript_Ast.JSB_LessThan -> begin
(FStar_Format.text "<")
end
| FStar_Extraction_JavaScript_Ast.JSB_LessThanEqual -> begin
(FStar_Format.text "<=")
end
| FStar_Extraction_JavaScript_Ast.JSB_GreaterThan -> begin
(FStar_Format.text ">")
end
| FStar_Extraction_JavaScript_Ast.JSB_GreaterThanEqual -> begin
(FStar_Format.text ">=")
end
| FStar_Extraction_JavaScript_Ast.JSB_Plus -> begin
(FStar_Format.text "+")
end
| FStar_Extraction_JavaScript_Ast.JSB_Minus -> begin
(FStar_Format.text "-")
end
| FStar_Extraction_JavaScript_Ast.JSB_Mult -> begin
(FStar_Format.text "*")
end
| FStar_Extraction_JavaScript_Ast.JSB_Div -> begin
(FStar_Format.text "/")
end
| FStar_Extraction_JavaScript_Ast.JSB_Mod -> begin
(FStar_Format.text "%")
end
| FStar_Extraction_JavaScript_Ast.JSB_StrictEqual -> begin
(FStar_Format.text "===")
end))


let print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun uu___100_54 -> (match (uu___100_54) with
| FStar_Extraction_JavaScript_Ast.JSL_Or -> begin
(FStar_Format.text "||")
end
| FStar_Extraction_JavaScript_Ast.JSL_And -> begin
(FStar_Format.text "&&")
end))


let keywords_js : Prims.string Prims.list = ("abstract")::("arguments")::("boolean")::("break")::("byte")::("case")::("catch")::("char")::("class")::("const")::("continue")::("debugger")::("default")::("delete")::("do")::("double")::("else")::("enum")::("eval")::("export")::("extends")::("false")::("final")::("finally")::("float")::("for")::("function")::("goto")::("if")::("implements")::("import")::("in")::("instanceof")::("int")::("interface")::("let")::("long")::("native")::("new")::("null")::("package")::("private")::("protected")::("public")::("return")::("short")::("static")::("super")::("switch")::("synchronized")::("this")::("throw")::("throws")::("transient")::("true")::("try")::("typeof")::("var")::("void")::("volatile")::("while")::("with")::("yield")::[]


let remove_chars : Prims.string  ->  FStar_Format.doc = (fun s -> (match ((FStar_List.existsb (fun x -> (s = x)) keywords_js)) with
| true -> begin
(

let v = (FStar_List.tryFind (fun x -> (s = x)) keywords_js)
in ((let _0_32 = (FStar_Util.must v)
in (FStar_Util.print1 "Warning: this name is a keyword in JavaScript: %s \n" _0_32));
(FStar_Format.reduce (let _0_34 = (let _0_33 = (FStar_Format.text (remove_chars_t s))
in (_0_33)::[])
in ((FStar_Format.text "_"))::_0_34));
))
end
| uu____64 -> begin
(FStar_Format.text (remove_chars_t s))
end))


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (FStar_Format.reduce (let _0_35 = (FStar_List.map (fun uu___101_128 -> (match (uu___101_128) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| uu____132 -> begin
(pretty_print_statement s)
end)
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _0_35))))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| uu____140 -> begin
(pretty_print_statement s)
end))
in (match (p) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(FStar_Format.reduce (let _0_38 = (let _0_37 = (let _0_36 = (pretty_print_statements l)
in (_0_36)::((FStar_Format.text "}"))::(FStar_Format.hardline)::[])
in ((FStar_Format.text "{"))::_0_37)
in (ws)::_0_38))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(FStar_Format.reduce (let _0_40 = (let _0_39 = (pretty_print_exp e)
in (_0_39)::(semi)::(FStar_Format.hardline)::[])
in (ws)::_0_40))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(FStar_Format.reduce (let _0_54 = (let _0_53 = (let _0_52 = (FStar_Format.parens (pretty_print_exp c))
in (let _0_51 = (let _0_50 = (let _0_49 = (let _0_48 = (optws t)
in (let _0_47 = (let _0_46 = (let _0_45 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(FStar_Format.reduce (let _0_44 = (let _0_43 = (let _0_42 = (let _0_41 = (optws s)
in (_0_41)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_0_42)
in ((FStar_Format.text "else"))::_0_43)
in (ws)::_0_44))
end)
in (_0_45)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "}"))::_0_46)
in (_0_48)::_0_47))
in (FStar_Format.hardline)::_0_49)
in ((FStar_Format.text "{"))::_0_50)
in (_0_52)::_0_51))
in ((FStar_Format.text "if"))::_0_53)
in (ws)::_0_54))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, uu____151), lt, t) -> begin
(FStar_Format.reduce (let _0_62 = (let _0_61 = (let _0_60 = (remove_chars id)
in (let _0_59 = (let _0_58 = (print_decl_t lt)
in (let _0_57 = (let _0_56 = (let _0_55 = (print_typ t)
in (_0_55)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "="))::_0_56)
in (_0_58)::_0_57))
in (_0_60)::_0_59))
in ((FStar_Format.text "type "))::_0_61)
in (ws)::_0_62))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(FStar_Format.reduce (let _0_67 = (let _0_66 = (let _0_65 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(FStar_Format.reduce (let _0_64 = (let _0_63 = (pretty_print_exp v)
in (_0_63)::[])
in (ws)::_0_64))
end)
in (_0_65)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "return"))::_0_66)
in (ws)::_0_67))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(FStar_Format.reduce (let _0_70 = (let _0_69 = (let _0_68 = (pretty_print_exp e)
in (_0_68)::(semi)::[])
in ((FStar_Format.text "throw "))::_0_69)
in (ws)::_0_70))
end
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, uu____176) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(FStar_Format.reduce (let _0_71 = (pretty_print_exp v)
in (_0_71)::(semi)::(FStar_Format.hardline)::[]))
end
| None -> begin
FStar_Format.empty
end)
end
| uu____180 -> begin
(FStar_Format.reduce (let _0_78 = (print_kind_var k)
in (let _0_77 = (let _0_76 = (print_pattern p true)
in (let _0_75 = (let _0_74 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(FStar_Format.reduce (let _0_73 = (let _0_72 = (pretty_print_exp v)
in (_0_72)::[])
in ((FStar_Format.text "="))::_0_73))
end)
in (_0_74)::(semi)::(FStar_Format.hardline)::[])
in (_0_76)::_0_75))
in (_0_78)::_0_77)))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(match (d) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(FStar_Format.reduce (FStar_List.map (fun x -> (print_export_stmt x)) l))
end
| uu____188 -> begin
(FStar_Format.reduce (let _0_80 = (let _0_79 = (optws s)
in (_0_79)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_0_80))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(FStar_Format.reduce (let _0_82 = (let _0_81 = (pretty_print_exp e)
in (_0_81)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_0_82))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(FStar_Format.reduce (let _0_88 = (let _0_87 = (FStar_Format.text (jstr_escape (Prims.fst d)))
in (let _0_86 = (let _0_85 = (let _0_84 = (let _0_83 = (FStar_Format.text (jstr_escape (Prims.fst d)))
in (_0_83)::((FStar_Format.text "\""))::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "\"./"))::_0_84)
in ((FStar_Format.text " from "))::_0_85)
in (_0_87)::_0_86))
in ((FStar_Format.text "import * as "))::_0_88))
end
| FStar_Extraction_JavaScript_Ast.JSS_Seq (l) -> begin
(pretty_print_statements l)
end)))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (FStar_Format.reduce (FStar_List.map pretty_print_statement l)))
and print_export_stmt : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, uu____210) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(FStar_Format.reduce (let _0_89 = (pretty_print_exp v)
in (_0_89)::(semi)::(FStar_Format.hardline)::[]))
end
| None -> begin
FStar_Format.empty
end)
end
| uu____214 -> begin
(FStar_Format.reduce (let _0_91 = (let _0_90 = (pretty_print_statement s)
in (_0_90)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_0_91))
end)
end
| uu____215 -> begin
(FStar_Format.reduce (let _0_93 = (let _0_92 = (pretty_print_statement s)
in (_0_92)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_0_93))
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun uu___102_216 -> (match (uu___102_216) with
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(FStar_Format.reduce (let _0_96 = (let _0_95 = (let _0_94 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _0_94 (FStar_Format.combine comma)))
in (_0_95)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_0_96))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(FStar_Format.reduce (let _0_99 = (let _0_98 = (let _0_97 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _0_97 (FStar_Format.combine comma)))
in (_0_98)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_0_99))
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (uu____228, args, body, ret_t, decl_vars) -> begin
(FStar_Format.reduce (let _0_103 = (print_decl_t decl_vars)
in (let _0_102 = (let _0_101 = (let _0_100 = (print_body body)
in (print_arrow_fun args _0_100 ret_t))
in (_0_101)::[])
in (_0_103)::_0_102)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(FStar_Format.reduce (let _0_105 = (let _0_104 = (pretty_print_exp e)
in (_0_104)::[])
in ((print_op_un o))::_0_105))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(FStar_Format.reduce (let _0_110 = (let _0_109 = (pretty_print_exp e1)
in (let _0_108 = (let _0_107 = (let _0_106 = (pretty_print_exp e2)
in (_0_106)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_0_107)
in (_0_109)::_0_108))
in ((FStar_Format.text "("))::_0_110))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, uu____257) when (n = "_") -> begin
(pretty_print_exp e)
end
| uu____260 -> begin
(FStar_Format.reduce (let _0_114 = (print_pattern p false)
in (let _0_113 = (let _0_112 = (let _0_111 = (pretty_print_exp e)
in (_0_111)::[])
in ((FStar_Format.text "="))::_0_112)
in (_0_114)::_0_113)))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(FStar_Format.reduce (let _0_118 = (pretty_print_exp e1)
in (let _0_117 = (let _0_116 = (let _0_115 = (pretty_print_exp e2)
in (_0_115)::[])
in ((print_op_log o))::_0_116)
in (_0_118)::_0_117)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _0_119 = (FStar_List.map (fun x -> (FStar_Format.parens (pretty_print_exp x))) l)
in (FStar_All.pipe_right _0_119 (FStar_Format.combine FStar_Format.empty)))
in (FStar_Format.reduce (let _0_120 = (pretty_print_exp e)
in (_0_120)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| uu____271 -> begin
le
end))::[])))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(FStar_Format.reduce (let _0_123 = (pretty_print_exp o)
in (let _0_122 = (let _0_121 = (pretty_print_propmem p)
in (_0_121)::[])
in (_0_123)::_0_122)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (id, t) -> begin
(remove_chars id)
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(FStar_Format.reduce (let _0_128 = (let _0_127 = (pretty_print_exp e)
in (let _0_126 = (let _0_125 = (let _0_124 = (print_typ t)
in (_0_124)::((FStar_Format.text ")"))::[])
in (colon)::_0_125)
in (_0_127)::_0_126))
in ((FStar_Format.text "("))::_0_128))
end))
and print_decl_t : Prims.string Prims.list Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(FStar_Format.reduce (let _0_131 = (let _0_130 = (let _0_129 = (FStar_List.map (fun s -> (remove_chars s)) l)
in (FStar_All.pipe_right _0_129 (FStar_Format.combine comma)))
in (_0_130)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_0_131))
end
| None -> begin
FStar_Format.empty
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option  ->  FStar_Format.doc = (fun args body ret_t -> (

let ret_t = (match (ret_t) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(FStar_Format.reduce (let _0_133 = (let _0_132 = (FStar_Format.parens (print_typ v))
in (_0_132)::[])
in (colon)::_0_133))
end)
in (print_arrow_fun_p args body ret_t true)))
and print_arrow_fun_p : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Format.doc  ->  Prims.bool  ->  FStar_Format.doc = (fun args body ret_t print_ret_t -> (

let ret_t = (match (print_ret_t) with
| true -> begin
ret_t
end
| uu____306 -> begin
FStar_Format.empty
end)
in (match (args) with
| [] -> begin
(FStar_Format.reduce (((FStar_Format.text "()"))::((FStar_Format.text "=>"))::(body)::[]))
end
| (x)::[] -> begin
(FStar_Format.reduce (let _0_134 = (FStar_Format.parens (print_pattern x true))
in (_0_134)::(ret_t)::((FStar_Format.text "=>"))::(body)::[]))
end
| (hd)::tl -> begin
(FStar_Format.reduce (let _0_139 = (FStar_Format.parens (print_pattern hd true))
in (let _0_138 = (let _0_137 = (let _0_136 = (let _0_135 = (FStar_Format.parens (print_arrow_fun_p tl body ret_t false))
in (_0_135)::[])
in ((FStar_Format.text "=>"))::_0_136)
in (ret_t)::_0_137)
in (_0_139)::_0_138)))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, uu____314) -> begin
(FStar_Format.reduce (let _0_143 = (pretty_print_prop_key k)
in (let _0_142 = (let _0_141 = (let _0_140 = (pretty_print_exp e)
in (_0_140)::[])
in ((FStar_Format.text ":"))::_0_141)
in (_0_143)::_0_142)))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(FStar_Format.text (jstr_escape id))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(FStar_Format.reduce (let _0_145 = (let _0_144 = (FStar_Format.text (jstr_escape i))
in (_0_144)::[])
in ((FStar_Format.text "."))::_0_145))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(FStar_Format.reduce (let _0_147 = (let _0_146 = (pretty_print_exp e)
in (_0_146)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_0_147))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun uu___103_331 -> (match (uu___103_331) with
| FStar_Extraction_JavaScript_Ast.JST_Any -> begin
(FStar_Format.text "any")
end
| FStar_Extraction_JavaScript_Ast.JST_Void -> begin
(FStar_Format.text "void")
end
| FStar_Extraction_JavaScript_Ast.JST_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JST_Number -> begin
(FStar_Format.text "number")
end
| FStar_Extraction_JavaScript_Ast.JST_String -> begin
(FStar_Format.text "string")
end
| FStar_Extraction_JavaScript_Ast.JST_Boolean -> begin
(FStar_Format.text "boolean")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(FStar_Format.reduce (let _0_150 = (print_decl_t decl_vars)
in (let _0_149 = (let _0_148 = (print_fun_typ args ret_t)
in (_0_148)::[])
in (_0_150)::_0_149)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp) -> begin
(FStar_Format.reduce (let _0_157 = (let _0_156 = (let _0_155 = (FStar_List.map (fun uu____358 -> (match (uu____358) with
| (k, t) -> begin
(FStar_Format.reduce (let _0_154 = (pretty_print_prop_key k)
in (let _0_153 = (let _0_152 = (let _0_151 = (print_typ t)
in (_0_151)::[])
in ((FStar_Format.text ":"))::_0_152)
in (_0_154)::_0_153)))
end)) lp)
in (FStar_All.pipe_right _0_155 (FStar_Format.combine comma)))
in (_0_156)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_0_157))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(FStar_Format.reduce (let _0_160 = (let _0_159 = (let _0_158 = (print_typ t)
in (_0_158)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_0_159)
in ((FStar_Format.text "Array"))::_0_160))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(FStar_Format.reduce (let _0_162 = (let _0_161 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _0_161 (FStar_Format.combine (FStar_Format.text "|"))))
in (_0_162)::[]))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(FStar_Format.reduce (let _0_164 = (let _0_163 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _0_163 (FStar_Format.combine (FStar_Format.text "&"))))
in (_0_164)::[]))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(FStar_Format.reduce (let _0_167 = (let _0_166 = (let _0_165 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _0_165 (FStar_Format.combine comma)))
in (_0_166)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_0_167))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, uu____374) -> begin
(FStar_Format.text (let _0_169 = (let _0_168 = (jstr_escape s)
in (Prims.strcat _0_168 "\""))
in (Prims.strcat "\"" _0_169)))
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (n, lt) -> begin
(

let print_lt = (match (lt) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(FStar_Format.reduce (let _0_172 = (let _0_171 = (let _0_170 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _0_170 (FStar_Format.combine comma)))
in (_0_171)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_0_172))
end)
in (FStar_Format.reduce (let _0_173 = (remove_chars n)
in (_0_173)::(print_lt)::[])))
end))
and print_fun_typ : ((Prims.string * FStar_Extraction_JavaScript_Ast.typ Prims.option) * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun args ret_t -> (

let print_arg = (fun uu____403 -> (match (uu____403) with
| ((id, uu____410), t) -> begin
(FStar_Format.reduce (let _0_177 = (FStar_Format.text (jstr_escape id))
in (let _0_176 = (let _0_175 = (let _0_174 = (print_typ t)
in (_0_174)::[])
in (colon)::_0_175)
in (_0_177)::_0_176)))
end))
in (match (args) with
| [] -> begin
(FStar_Format.reduce (let _0_180 = (let _0_179 = (let _0_178 = (print_typ ret_t)
in (_0_178)::[])
in ((FStar_Format.text "=>"))::_0_179)
in ((FStar_Format.text "()"))::_0_180))
end
| (x)::[] -> begin
(FStar_Format.reduce (let _0_184 = (FStar_Format.parens (print_arg x))
in (let _0_183 = (let _0_182 = (let _0_181 = (FStar_Format.parens (print_typ ret_t))
in (_0_181)::[])
in ((FStar_Format.text "=>"))::_0_182)
in (_0_184)::_0_183)))
end
| (hd)::tl -> begin
(FStar_Format.reduce (let _0_188 = (FStar_Format.parens (print_arg hd))
in (let _0_187 = (let _0_186 = (let _0_185 = (FStar_Format.parens (print_fun_typ tl ret_t))
in (_0_185)::[])
in ((FStar_Format.text "=>"))::_0_186)
in (_0_188)::_0_187)))
end)))
and print_literal : (FStar_Extraction_JavaScript_Ast.value_t * Prims.string)  ->  FStar_Format.doc = (fun uu____456 -> (match (uu____456) with
| (v, s) -> begin
(match (((v), (s))) with
| (FStar_Extraction_JavaScript_Ast.JSV_String (s), uu____462) -> begin
(FStar_Format.text (let _0_190 = (let _0_189 = (jstr_escape s)
in (Prims.strcat _0_189 "\""))
in (Prims.strcat "\"" _0_190)))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Boolean (b), uu____464) -> begin
(FStar_Format.text (FStar_Util.string_of_bool b))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Null, uu____465) -> begin
(FStar_Format.text "null")
end
| (FStar_Extraction_JavaScript_Ast.JSV_Number (f), s) -> begin
(FStar_Format.text s)
end)
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun uu___104_468 -> (match (uu___104_468) with
| FStar_Extraction_JavaScript_Ast.JSV_Var -> begin
(FStar_Format.text "var ")
end
| FStar_Extraction_JavaScript_Ast.JSV_Let -> begin
(FStar_Format.text "let ")
end
| FStar_Extraction_JavaScript_Ast.JSV_Const -> begin
(FStar_Format.text "const ")
end))
and print_pattern : FStar_Extraction_JavaScript_Ast.pattern_t  ->  Prims.bool  ->  FStar_Format.doc = (fun p print_t -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(FStar_Format.reduce (let _0_192 = (let _0_191 = (print_typ v)
in (_0_191)::[])
in (colon)::_0_192))
end
| None -> begin
FStar_Format.empty
end)
in (FStar_Format.reduce (let _0_193 = (remove_chars id)
in (_0_193)::((match (print_t) with
| true -> begin
r
end
| uu____478 -> begin
FStar_Format.empty
end))::[])))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun uu___105_479 -> (match (uu___105_479) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(FStar_Format.reduce (let _0_196 = (let _0_195 = (let _0_194 = (pretty_print_statements l)
in (_0_194)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_0_195)
in ((FStar_Format.text "{"))::_0_196))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(FStar_Format.parens (pretty_print_exp e))
end))





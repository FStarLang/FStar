
open Prims

let semi : FStar_Format.doc = (FStar_Format.text ";")


let comma : FStar_Format.doc = (FStar_Format.text ",")


let dot : FStar_Format.doc = (FStar_Format.text ".")


let colon : FStar_Format.doc = (FStar_Format.text ":")


let ws : FStar_Format.doc = FStar_Format.break1


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _83_1 -> (match (_83_1) with
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


let escape_char : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _83_2 -> (match (_83_2) with
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


let print_op_un : FStar_Extraction_JavaScript_Ast.op_un  ->  FStar_Format.doc = (fun _83_3 -> (match (_83_3) with
| FStar_Extraction_JavaScript_Ast.JSU_Minus -> begin
(FStar_Format.text "-")
end
| FStar_Extraction_JavaScript_Ast.JSU_Plus -> begin
(FStar_Format.text "+")
end
| FStar_Extraction_JavaScript_Ast.JSU_Not -> begin
(FStar_Format.text "!")
end
| FStar_Extraction_JavaScript_Ast.JSU_BitNot -> begin
(FStar_Format.text "~")
end
| FStar_Extraction_JavaScript_Ast.JSU_Typeof -> begin
(FStar_Format.text "typeof")
end
| FStar_Extraction_JavaScript_Ast.JSU_Void -> begin
(FStar_Format.text "void")
end
| FStar_Extraction_JavaScript_Ast.JSU_Delete -> begin
(FStar_Format.text "delete")
end
| FStar_Extraction_JavaScript_Ast.JSU_Await -> begin
(FStar_Format.text "await")
end))


let print_op_bin : FStar_Extraction_JavaScript_Ast.op_bin  ->  FStar_Format.doc = (fun _83_4 -> (match (_83_4) with
| FStar_Extraction_JavaScript_Ast.JSB_Equal -> begin
(FStar_Format.text "==")
end
| FStar_Extraction_JavaScript_Ast.JSB_NotEqual -> begin
(FStar_Format.text "!=")
end
| FStar_Extraction_JavaScript_Ast.JSB_StrictEqual -> begin
(FStar_Format.text "===")
end
| FStar_Extraction_JavaScript_Ast.JSB_StrictNotEqual -> begin
(FStar_Format.text "!==")
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
| FStar_Extraction_JavaScript_Ast.JSB_LShift -> begin
(FStar_Format.text "<<")
end
| FStar_Extraction_JavaScript_Ast.JSB_RShift -> begin
(FStar_Format.text ">>")
end
| FStar_Extraction_JavaScript_Ast.JSB_RShift3 -> begin
(FStar_Format.text ">>>")
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
| FStar_Extraction_JavaScript_Ast.JSB_Exp -> begin
(FStar_Format.text "**")
end
| FStar_Extraction_JavaScript_Ast.JSB_Div -> begin
(FStar_Format.text "/")
end
| FStar_Extraction_JavaScript_Ast.JSB_Mod -> begin
(FStar_Format.text "%")
end
| FStar_Extraction_JavaScript_Ast.JSB_BitOr -> begin
(FStar_Format.text "|")
end
| FStar_Extraction_JavaScript_Ast.JSB_Xor -> begin
(FStar_Format.text "^")
end
| FStar_Extraction_JavaScript_Ast.JSB_BitAnd -> begin
(FStar_Format.text "&")
end
| FStar_Extraction_JavaScript_Ast.JSB_In -> begin
(FStar_Format.text "in")
end
| FStar_Extraction_JavaScript_Ast.JSB_Instanceof -> begin
(FStar_Format.text "instanceof")
end))


let print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun _83_5 -> (match (_83_5) with
| FStar_Extraction_JavaScript_Ast.JSL_Or -> begin
(FStar_Format.text "||")
end
| FStar_Extraction_JavaScript_Ast.JSL_And -> begin
(FStar_Format.text "&&")
end))


let f_print_arrow_fun_t : Prims.bool FStar_ST.ref = (FStar_ST.alloc true)


let f_print_arrow_fun : Prims.bool FStar_ST.ref = (FStar_ST.alloc true)


let keywords_js : Prims.string Prims.list = ("abstract")::("arguments")::("boolean")::("break")::("byte")::("case")::("catch")::("char")::("class")::("const")::("continue")::("debugger")::("default")::("delete")::("do")::("double")::("else")::("enum")::("eval")::("export")::("extends")::("false")::("final")::("finally")::("float")::("for")::("function")::("goto")::("if")::("implements")::("import")::("in")::("instanceof")::("int")::("interface")::("let")::("long")::("native")::("new")::("null")::("package")::("private")::("protected")::("public")::("return")::("short")::("static")::("super")::("switch")::("synchronized")::("this")::("throw")::("throws")::("transient")::("true")::("try")::("typeof")::("var")::("void")::("volatile")::("while")::("with")::("yield")::[]


let remove_chars : Prims.string  ->  FStar_Format.doc = (fun s -> if (FStar_List.existsb (fun x -> (s = x)) keywords_js) then begin
(

let v = (FStar_List.tryFind (fun x -> (s = x)) keywords_js)
in (

let _83_75 = (let _180_33 = (FStar_Util.must v)
in (FStar_Util.print1 "Warning: this name is a keyword in JavaScript: %s \n" _180_33))
in (let _180_37 = (let _180_36 = (let _180_35 = (let _180_34 = (remove_chars_t s)
in (FStar_Format.text _180_34))
in (_180_35)::[])
in ((FStar_Format.text "_"))::_180_36)
in (FStar_Format.reduce _180_37))))
end else begin
(let _180_38 = (remove_chars_t s)
in (FStar_Format.text _180_38))
end)


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_69 = (let _180_68 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(

let _83_81 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t true)
in (

let _83_83 = (FStar_ST.op_Colon_Equals f_print_arrow_fun true)
in (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_88 -> begin
(pretty_print_statement s)
end)))
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_68))
in (FStar_Format.reduce _180_69)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_95 -> begin
(pretty_print_statement s)
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_78 = (let _180_77 = (let _180_76 = (let _180_75 = (pretty_print_statements l)
in (_180_75)::((FStar_Format.text "}"))::(FStar_Format.hardline)::[])
in ((FStar_Format.text "{"))::_180_76)
in (ws)::_180_77)
in (FStar_Format.reduce _180_78))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_81 = (let _180_80 = (let _180_79 = (pretty_print_exp e)
in (_180_79)::(semi)::(FStar_Format.hardline)::[])
in (ws)::_180_80)
in (FStar_Format.reduce _180_81))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_98 = (let _180_97 = (let _180_96 = (let _180_95 = (let _180_82 = (pretty_print_exp c)
in (FStar_Format.parens _180_82))
in (let _180_94 = (let _180_93 = (let _180_92 = (let _180_91 = (optws t)
in (let _180_90 = (let _180_89 = (let _180_88 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_87 = (let _180_86 = (let _180_85 = (let _180_84 = (let _180_83 = (optws s)
in (_180_83)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_84)
in ((FStar_Format.text "else"))::_180_85)
in (ws)::_180_86)
in (FStar_Format.reduce _180_87))
end)
in (_180_88)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "}"))::_180_89)
in (_180_91)::_180_90))
in (FStar_Format.hardline)::_180_92)
in ((FStar_Format.text "{"))::_180_93)
in (_180_95)::_180_94))
in ((FStar_Format.text "if"))::_180_96)
in (ws)::_180_97)
in (FStar_Format.reduce _180_98))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_106 = (let _180_105 = (let _180_104 = (let _180_103 = (let _180_99 = (pretty_print_exp e)
in (FStar_Format.parens _180_99))
in (let _180_102 = (let _180_101 = (let _180_100 = (optws s)
in (_180_100)::[])
in (FStar_Format.hardline)::_180_101)
in (_180_103)::_180_102))
in ((FStar_Format.text "with"))::_180_104)
in (ws)::_180_105)
in (FStar_Format.reduce _180_106))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_116), lt, t) -> begin
(let _180_115 = (let _180_114 = (let _180_113 = (let _180_112 = (remove_chars id)
in (let _180_111 = (let _180_110 = (print_decl_t lt)
in (let _180_109 = (let _180_108 = (let _180_107 = (print_typ t)
in (_180_107)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "="))::_180_108)
in (_180_110)::_180_109))
in (_180_112)::_180_111))
in ((FStar_Format.text "type "))::_180_113)
in (ws)::_180_114)
in (FStar_Format.reduce _180_115))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_135 = (let _180_134 = (let _180_133 = (let _180_132 = (let _180_116 = (pretty_print_exp e)
in (FStar_Format.parens _180_116))
in (let _180_131 = (let _180_130 = (let _180_129 = (let _180_128 = (let _180_127 = (let _180_126 = (FStar_List.map (fun _83_128 -> (match (_83_128) with
| (e, l) -> begin
(let _180_125 = (let _180_124 = (let _180_123 = (let _180_122 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_121 = (let _180_120 = (let _180_119 = (let _180_118 = (pretty_print_statements l)
in (_180_118)::[])
in (FStar_Format.hardline)::_180_119)
in (colon)::_180_120)
in (_180_122)::_180_121))
in ((FStar_Format.text "case "))::_180_123)
in (ws)::_180_124)
in (FStar_Format.reduce _180_125))
end)) lcase)
in (FStar_All.pipe_right _180_126 (FStar_Format.combine FStar_Format.hardline)))
in (_180_127)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_128)
in ((FStar_Format.text "{"))::_180_129)
in (ws)::_180_130)
in (_180_132)::_180_131))
in ((FStar_Format.text "switch "))::_180_133)
in (ws)::_180_134)
in (FStar_Format.reduce _180_135))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_142 = (let _180_141 = (let _180_140 = (let _180_139 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_138 = (let _180_137 = (let _180_136 = (pretty_print_exp v)
in (_180_136)::[])
in (ws)::_180_137)
in (FStar_Format.reduce _180_138))
end)
in (_180_139)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "return"))::_180_140)
in (ws)::_180_141)
in (FStar_Format.reduce _180_142))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_146 = (let _180_145 = (let _180_144 = (let _180_143 = (pretty_print_exp e)
in (_180_143)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_144)
in (ws)::_180_145)
in (FStar_Format.reduce _180_146))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (pretty_print_statements b)
in (_180_147)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_148)
in ((FStar_Format.text "try"))::_180_149)
in (FStar_Format.reduce _180_150))
end
| FStar_Extraction_JavaScript_Ast.JSS_FunctionDeclaration (f) -> begin
(let _180_152 = (let _180_151 = (pretty_print_fun f)
in (_180_151)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_152))
end
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(

let isNull = (fun v -> (match (v) with
| FStar_Extraction_JavaScript_Ast.JSE_Literal (FStar_Extraction_JavaScript_Ast.JSV_Null, "") -> begin
true
end
| _83_158 -> begin
false
end))
in (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_161) when (n = "_") -> begin
(match (e) with
| Some (v) when (isNull v) -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_156 = (let _180_155 = (pretty_print_exp v)
in (_180_155)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_156))
end
| None -> begin
FStar_Format.empty
end)
end
| _83_170 -> begin
(let _180_165 = (let _180_164 = (print_kind_var k)
in (let _180_163 = (let _180_162 = (print_pattern p true)
in (let _180_161 = (let _180_160 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_159 = (let _180_158 = (let _180_157 = (pretty_print_exp v)
in (_180_157)::[])
in ((FStar_Format.text "="))::_180_158)
in (FStar_Format.reduce _180_159))
end)
in (_180_160)::(semi)::(FStar_Format.hardline)::[])
in (_180_162)::_180_161))
in (_180_164)::_180_163))
in (FStar_Format.reduce _180_165))
end))
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(match (d) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_167 = (FStar_List.map (fun x -> (print_export_stmt x)) l)
in (FStar_Format.reduce _180_167))
end
| _83_184 -> begin
(let _180_170 = (let _180_169 = (let _180_168 = (optws s)
in (_180_168)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_169)
in (FStar_Format.reduce _180_170))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(let _180_173 = (let _180_172 = (let _180_171 = (pretty_print_exp e)
in (_180_171)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_172)
in (FStar_Format.reduce _180_173))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _180_182 = (let _180_181 = (let _180_180 = (let _180_174 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_174))
in (let _180_179 = (let _180_178 = (let _180_177 = (let _180_176 = (let _180_175 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_175))
in (_180_176)::((FStar_Format.text "\""))::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "\"./"))::_180_177)
in ((FStar_Format.text " from "))::_180_178)
in (_180_180)::_180_179))
in ((FStar_Format.text "import * as "))::_180_181)
in (FStar_Format.reduce _180_182))
end
| FStar_Extraction_JavaScript_Ast.JSS_Seq (l) -> begin
(pretty_print_statements l)
end))
in (f p))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_184 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_184)))
and print_export_stmt : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_202) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(let _180_187 = (let _180_186 = (pretty_print_exp v)
in (_180_186)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_187))
end
| None -> begin
FStar_Format.empty
end)
end
| _83_209 -> begin
(let _180_190 = (let _180_189 = (let _180_188 = (pretty_print_statement s)
in (_180_188)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_189)
in (FStar_Format.reduce _180_190))
end)
end
| _83_211 -> begin
(let _180_193 = (let _180_192 = (let _180_191 = (pretty_print_statement s)
in (_180_191)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_192)
in (FStar_Format.reduce _180_193))
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_198 = (let _180_197 = (let _180_196 = (let _180_195 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_195 (FStar_Format.combine comma)))
in (_180_196)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_197)
in (FStar_Format.reduce _180_198))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_202 = (let _180_201 = (let _180_200 = (let _180_199 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_199 (FStar_Format.combine comma)))
in (_180_200)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_201)
in (FStar_Format.reduce _180_202))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_223, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_231 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_206 = (let _180_205 = (let _180_204 = (let _180_203 = (print_body body)
in (print_arrow_fun args _180_203 ret_t))
in (_180_204)::[])
in (decl_t)::_180_205)
in (FStar_Format.reduce _180_206))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_209 = (let _180_208 = (let _180_207 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_207 (FStar_Format.combine semi)))
in (_180_208)::[])
in (FStar_Format.reduce _180_209))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_212 = (let _180_211 = (let _180_210 = (pretty_print_exp e)
in (_180_210)::[])
in ((print_op_un o))::_180_211)
in (FStar_Format.reduce _180_212))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_218 = (let _180_217 = (let _180_216 = (pretty_print_exp e1)
in (let _180_215 = (let _180_214 = (let _180_213 = (pretty_print_exp e2)
in (_180_213)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_214)
in (_180_216)::_180_215))
in ((FStar_Format.text "("))::_180_217)
in (FStar_Format.reduce _180_218))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_250) when (n = "_") -> begin
(pretty_print_exp e)
end
| _83_254 -> begin
(let _180_223 = (let _180_222 = (print_pattern p false)
in (let _180_221 = (let _180_220 = (let _180_219 = (pretty_print_exp e)
in (_180_219)::[])
in ((FStar_Format.text "="))::_180_220)
in (_180_222)::_180_221))
in (FStar_Format.reduce _180_223))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_228 = (let _180_227 = (pretty_print_exp e1)
in (let _180_226 = (let _180_225 = (let _180_224 = (pretty_print_exp e2)
in (_180_224)::[])
in ((print_op_log o))::_180_225)
in (_180_227)::_180_226))
in (FStar_Format.reduce _180_228))
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _180_231 = (FStar_List.map (fun x -> (let _180_230 = (pretty_print_exp x)
in (FStar_Format.parens _180_230))) l)
in (FStar_All.pipe_right _180_231 (FStar_Format.combine FStar_Format.empty)))
in (let _180_233 = (let _180_232 = (pretty_print_exp e)
in (_180_232)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_268 -> begin
le
end))::[])
in (FStar_Format.reduce _180_233)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_237 = (let _180_236 = (pretty_print_exp o)
in (let _180_235 = (let _180_234 = (pretty_print_propmem p)
in (_180_234)::[])
in (_180_236)::_180_235))
in (FStar_Format.reduce _180_237))
end
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (id, t) -> begin
(remove_chars id)
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_243 = (let _180_242 = (let _180_241 = (pretty_print_exp e)
in (let _180_240 = (let _180_239 = (let _180_238 = (print_typ t)
in (_180_238)::((FStar_Format.text ")"))::[])
in (colon)::_180_239)
in (_180_241)::_180_240))
in ((FStar_Format.text "("))::_180_242)
in (FStar_Format.reduce _180_243))
end))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_249 = (let _180_248 = (let _180_247 = (let _180_246 = (FStar_List.map (fun s -> (remove_chars s)) l)
in (FStar_All.pipe_right _180_246 (FStar_Format.combine comma)))
in (_180_247)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_248)
in (FStar_Format.reduce _180_249))
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
(let _180_256 = (let _180_255 = (let _180_254 = (let _180_253 = (print_typ v)
in (FStar_Format.parens _180_253))
in (_180_254)::[])
in (colon)::_180_255)
in (FStar_Format.reduce _180_256))
end)
in (print_arrow_fun_p args body ret_t true)))
and print_arrow_fun_p : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Format.doc  ->  Prims.bool  ->  FStar_Format.doc = (fun args body ret_t print_ret_t -> (

let ret_t = if print_ret_t then begin
ret_t
end else begin
FStar_Format.empty
end
in (match (args) with
| [] -> begin
(FStar_Format.reduce (((FStar_Format.text "()"))::((FStar_Format.text "=>"))::(body)::[]))
end
| (x)::[] -> begin
(let _180_263 = (let _180_262 = (let _180_261 = (print_pattern x true)
in (FStar_Format.parens _180_261))
in (_180_262)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_263))
end
| (hd)::tl -> begin
(let _180_271 = (let _180_270 = (let _180_264 = (print_pattern hd true)
in (FStar_Format.parens _180_264))
in (let _180_269 = (let _180_268 = (let _180_267 = (let _180_266 = (let _180_265 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_265))
in (_180_266)::[])
in ((FStar_Format.text "=>"))::_180_267)
in (ret_t)::_180_268)
in (_180_270)::_180_269))
in (FStar_Format.reduce _180_271))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_310) -> begin
(let _180_277 = (let _180_276 = (pretty_print_prop_key k)
in (let _180_275 = (let _180_274 = (let _180_273 = (pretty_print_exp e)
in (_180_273)::[])
in ((FStar_Format.text ":"))::_180_274)
in (_180_276)::_180_275))
in (FStar_Format.reduce _180_277))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_279 = (jstr_escape id)
in (FStar_Format.text _180_279))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_284 = (let _180_283 = (let _180_282 = (let _180_281 = (jstr_escape i)
in (FStar_Format.text _180_281))
in (_180_282)::[])
in ((FStar_Format.text "."))::_180_283)
in (FStar_Format.reduce _180_284))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_287 = (let _180_286 = (let _180_285 = (pretty_print_exp e)
in (_180_285)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_286)
in (FStar_Format.reduce _180_287))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
| FStar_Extraction_JavaScript_Ast.JST_Any -> begin
(FStar_Format.text "any")
end
| FStar_Extraction_JavaScript_Ast.JST_Mixed -> begin
(FStar_Format.text "mixed")
end
| FStar_Extraction_JavaScript_Ast.JST_Empty -> begin
(FStar_All.failwith "todo: pretty-print [JST_Empty]")
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_341) -> begin
(FStar_All.failwith "todo: pretty-print [JST_Nullable]")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(

let decl_vars = if (FStar_ST.read f_print_arrow_fun_t) then begin
decl_vars
end else begin
None
end
in (

let _83_349 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_353, _83_355) -> begin
(let _180_298 = (let _180_297 = (let _180_296 = (let _180_295 = (FStar_List.map (fun _83_360 -> (match (_83_360) with
| (k, t) -> begin
(let _180_294 = (let _180_293 = (pretty_print_prop_key k)
in (let _180_292 = (let _180_291 = (let _180_290 = (print_typ t)
in (_180_290)::[])
in ((FStar_Format.text ":"))::_180_291)
in (_180_293)::_180_292))
in (FStar_Format.reduce _180_294))
end)) lp)
in (FStar_All.pipe_right _180_295 (FStar_Format.combine comma)))
in (_180_296)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_297)
in (FStar_Format.reduce _180_298))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_302 = (let _180_301 = (let _180_300 = (let _180_299 = (print_typ t)
in (_180_299)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_300)
in ((FStar_Format.text "Array"))::_180_301)
in (FStar_Format.reduce _180_302))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_305 = (let _180_304 = (let _180_303 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_303 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_304)::[])
in (FStar_Format.reduce _180_305))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_308 = (let _180_307 = (let _180_306 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_306 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_307)::[])
in (FStar_Format.reduce _180_308))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_311 = (let _180_310 = (let _180_309 = (print_typ t)
in (_180_309)::[])
in ((FStar_Format.text "typeof"))::_180_310)
in (FStar_Format.reduce _180_311))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_315 = (let _180_314 = (let _180_313 = (let _180_312 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_312 (FStar_Format.combine comma)))
in (_180_313)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_314)
in (FStar_Format.reduce _180_315))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_373) -> begin
(let _180_318 = (let _180_317 = (let _180_316 = (jstr_escape s)
in (Prims.strcat _180_316 "\""))
in (Prims.strcat "\"" _180_317))
in (FStar_Format.text _180_318))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_378) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_383) -> begin
(let _180_319 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_319))
end
| FStar_Extraction_JavaScript_Ast.JST_Exists -> begin
(FStar_All.failwith "todo: pretty-print [JST_Exists]")
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (n, lt) -> begin
(

let print_lt = (match (lt) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_323 = (let _180_322 = (let _180_321 = (let _180_320 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_320 (FStar_Format.combine comma)))
in (_180_321)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_322)
in (FStar_Format.reduce _180_323))
end)
in (let _180_325 = (let _180_324 = (print_gen_t n)
in (_180_324)::(print_lt)::[])
in (FStar_Format.reduce _180_325)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_404 -> (match (_83_404) with
| ((id, _83_401), t) -> begin
(let _180_336 = (let _180_335 = (let _180_331 = (jstr_escape id)
in (FStar_Format.text _180_331))
in (let _180_334 = (let _180_333 = (let _180_332 = (print_typ t)
in (_180_332)::[])
in (colon)::_180_333)
in (_180_335)::_180_334))
in (FStar_Format.reduce _180_336))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_340 = (let _180_339 = (let _180_338 = (let _180_337 = (print_typ ret_t)
in (_180_337)::[])
in ((FStar_Format.text "=>"))::_180_338)
in ((FStar_Format.text "()"))::_180_339)
in (FStar_Format.reduce _180_340))
end
| (x)::[] -> begin
(let _180_347 = (let _180_346 = (let _180_341 = (print_arg x)
in (FStar_Format.parens _180_341))
in (let _180_345 = (let _180_344 = (let _180_343 = (let _180_342 = (print_typ ret_t)
in (FStar_Format.parens _180_342))
in (_180_343)::[])
in ((FStar_Format.text "=>"))::_180_344)
in (_180_346)::_180_345))
in (FStar_Format.reduce _180_347))
end
| (hd)::tl -> begin
(let _180_354 = (let _180_353 = (let _180_348 = (print_arg hd)
in (FStar_Format.parens _180_348))
in (let _180_352 = (let _180_351 = (let _180_350 = (let _180_349 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_349))
in (_180_350)::[])
in ((FStar_Format.text "=>"))::_180_351)
in (_180_353)::_180_352))
in (FStar_Format.reduce _180_354))
end)
in (let _180_356 = (let _180_355 = (print_decl_t decl_vars)
in (_180_355)::(args_t)::[])
in (FStar_Format.reduce _180_356)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_415) -> begin
(remove_chars id)
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_421)) -> begin
(let _180_362 = (let _180_361 = (print_gen_t g)
in (let _180_360 = (let _180_359 = (let _180_358 = (remove_chars id)
in (_180_358)::[])
in (comma)::_180_359)
in (_180_361)::_180_360))
in (FStar_Format.reduce _180_362))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.literal_t  ->  FStar_Format.doc = (fun _83_427 -> (match (_83_427) with
| (v, s) -> begin
(match (((v), (s))) with
| (FStar_Extraction_JavaScript_Ast.JSV_String (s), _83_431) -> begin
(let _180_366 = (let _180_365 = (let _180_364 = (jstr_escape s)
in (Prims.strcat _180_364 "\""))
in (Prims.strcat "\"" _180_365))
in (FStar_Format.text _180_366))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Boolean (b), _83_436) -> begin
(let _180_367 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_367))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Null, _83_440) -> begin
(FStar_Format.text "null")
end
| (FStar_Extraction_JavaScript_Ast.JSV_Number (f), s) -> begin
(FStar_Format.text s)
end)
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_453) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Object]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_456) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Array]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_459) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Assignment]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_373 = (let _180_372 = (let _180_371 = (print_typ v)
in (_180_371)::[])
in (colon)::_180_372)
in (FStar_Format.reduce _180_373))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_375 = (let _180_374 = (remove_chars id)
in (_180_374)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_375)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_380 = (let _180_379 = (let _180_378 = (let _180_377 = (pretty_print_statements l)
in (_180_377)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_378)
in ((FStar_Format.text "{"))::_180_379)
in (FStar_Format.reduce _180_380))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_381 = (pretty_print_exp e)
in (FStar_Format.parens _180_381))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_481 -> (match (_83_481) with
| (n, pars, body, t, typePars) -> begin
(

let name = (match (n) with
| Some (v) -> begin
(FStar_Format.text (Prims.fst v))
end
| None -> begin
FStar_Format.empty
end)
in (

let returnT = (match (t) with
| Some (v) -> begin
(let _180_386 = (let _180_385 = (let _180_384 = (let _180_383 = (print_typ v)
in (_180_383)::[])
in (ws)::_180_384)
in ((FStar_Format.text ":"))::_180_385)
in (FStar_Format.reduce _180_386))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_401 = (let _180_400 = (let _180_399 = (let _180_398 = (let _180_397 = (print_decl_t typePars)
in (let _180_396 = (let _180_395 = (let _180_389 = (let _180_388 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_388 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_389))
in (let _180_394 = (let _180_393 = (let _180_392 = (let _180_391 = (let _180_390 = (print_body body)
in (_180_390)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_391)
in ((FStar_Format.text "{"))::_180_392)
in (returnT)::_180_393)
in (_180_395)::_180_394))
in (_180_397)::_180_396))
in (name)::_180_398)
in (ws)::_180_399)
in ((FStar_Format.text "function"))::_180_400)
in (FStar_Format.reduce _180_401))))
end))





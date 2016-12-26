
open Prims

let semi : FStar_Format.doc = (FStar_Format.text ";")


let comma : FStar_Format.doc = (FStar_Format.text ",")


let dot : FStar_Format.doc = (FStar_Format.text ".")


let colon : FStar_Format.doc = (FStar_Format.text ":")


let ws : FStar_Format.doc = FStar_Format.break1


let escape_or : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _85_1 -> (match (_85_1) with
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


let escape_char : (FStar_Char.char  ->  Prims.string)  ->  FStar_Char.char  ->  Prims.string = (fun fallback _85_2 -> (match (_85_2) with
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


let print_op_un : FStar_Extraction_JavaScript_Ast.op_un  ->  FStar_Format.doc = (fun _85_3 -> (match (_85_3) with
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


let print_op_bin : FStar_Extraction_JavaScript_Ast.op_bin  ->  FStar_Format.doc = (fun _85_4 -> (match (_85_4) with
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


let print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun _85_5 -> (match (_85_5) with
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

let _85_75 = (let _185_33 = (FStar_Util.must v)
in (FStar_Util.print1 "Warning: this name is a keyword in JavaScript: %s \n" _185_33))
in (let _185_37 = (let _185_36 = (let _185_35 = (let _185_34 = (remove_chars_t s)
in (FStar_Format.text _185_34))
in (_185_35)::[])
in ((FStar_Format.text "_"))::_185_36)
in (FStar_Format.reduce _185_37))))
end else begin
(let _185_38 = (remove_chars_t s)
in (FStar_Format.text _185_38))
end)


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _185_69 = (let _185_68 = (FStar_List.map (fun _85_6 -> (match (_85_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(

let _85_81 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t true)
in (

let _85_83 = (FStar_ST.op_Colon_Equals f_print_arrow_fun true)
in (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _85_88 -> begin
(pretty_print_statement s)
end)))
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _185_68))
in (FStar_Format.reduce _185_69)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _85_95 -> begin
(pretty_print_statement s)
end))
in (

let f = (fun _85_7 -> (match (_85_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _185_78 = (let _185_77 = (let _185_76 = (let _185_75 = (pretty_print_statements l)
in (_185_75)::((FStar_Format.text "}"))::(FStar_Format.hardline)::[])
in ((FStar_Format.text "{"))::_185_76)
in (ws)::_185_77)
in (FStar_Format.reduce _185_78))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _185_81 = (let _185_80 = (let _185_79 = (pretty_print_exp e)
in (_185_79)::(semi)::(FStar_Format.hardline)::[])
in (ws)::_185_80)
in (FStar_Format.reduce _185_81))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _185_98 = (let _185_97 = (let _185_96 = (let _185_95 = (let _185_82 = (pretty_print_exp c)
in (FStar_Format.parens _185_82))
in (let _185_94 = (let _185_93 = (let _185_92 = (let _185_91 = (optws t)
in (let _185_90 = (let _185_89 = (let _185_88 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _185_87 = (let _185_86 = (let _185_85 = (let _185_84 = (let _185_83 = (optws s)
in (_185_83)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_185_84)
in ((FStar_Format.text "else"))::_185_85)
in (ws)::_185_86)
in (FStar_Format.reduce _185_87))
end)
in (_185_88)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "}"))::_185_89)
in (_185_91)::_185_90))
in (FStar_Format.hardline)::_185_92)
in ((FStar_Format.text "{"))::_185_93)
in (_185_95)::_185_94))
in ((FStar_Format.text "if"))::_185_96)
in (ws)::_185_97)
in (FStar_Format.reduce _185_98))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _185_106 = (let _185_105 = (let _185_104 = (let _185_103 = (let _185_99 = (pretty_print_exp e)
in (FStar_Format.parens _185_99))
in (let _185_102 = (let _185_101 = (let _185_100 = (optws s)
in (_185_100)::[])
in (FStar_Format.hardline)::_185_101)
in (_185_103)::_185_102))
in ((FStar_Format.text "with"))::_185_104)
in (ws)::_185_105)
in (FStar_Format.reduce _185_106))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _85_116), lt, t) -> begin
(let _185_115 = (let _185_114 = (let _185_113 = (let _185_112 = (remove_chars id)
in (let _185_111 = (let _185_110 = (print_decl_t lt)
in (let _185_109 = (let _185_108 = (let _185_107 = (print_typ t)
in (_185_107)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "="))::_185_108)
in (_185_110)::_185_109))
in (_185_112)::_185_111))
in ((FStar_Format.text "type "))::_185_113)
in (ws)::_185_114)
in (FStar_Format.reduce _185_115))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _185_135 = (let _185_134 = (let _185_133 = (let _185_132 = (let _185_116 = (pretty_print_exp e)
in (FStar_Format.parens _185_116))
in (let _185_131 = (let _185_130 = (let _185_129 = (let _185_128 = (let _185_127 = (let _185_126 = (FStar_List.map (fun _85_128 -> (match (_85_128) with
| (e, l) -> begin
(let _185_125 = (let _185_124 = (let _185_123 = (let _185_122 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _185_121 = (let _185_120 = (let _185_119 = (let _185_118 = (pretty_print_statements l)
in (_185_118)::[])
in (FStar_Format.hardline)::_185_119)
in (colon)::_185_120)
in (_185_122)::_185_121))
in ((FStar_Format.text "case "))::_185_123)
in (ws)::_185_124)
in (FStar_Format.reduce _185_125))
end)) lcase)
in (FStar_All.pipe_right _185_126 (FStar_Format.combine FStar_Format.hardline)))
in (_185_127)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_185_128)
in ((FStar_Format.text "{"))::_185_129)
in (ws)::_185_130)
in (_185_132)::_185_131))
in ((FStar_Format.text "switch "))::_185_133)
in (ws)::_185_134)
in (FStar_Format.reduce _185_135))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _185_142 = (let _185_141 = (let _185_140 = (let _185_139 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _185_138 = (let _185_137 = (let _185_136 = (pretty_print_exp v)
in (_185_136)::[])
in (ws)::_185_137)
in (FStar_Format.reduce _185_138))
end)
in (_185_139)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "return"))::_185_140)
in (ws)::_185_141)
in (FStar_Format.reduce _185_142))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _185_146 = (let _185_145 = (let _185_144 = (let _185_143 = (pretty_print_exp e)
in (_185_143)::(semi)::[])
in ((FStar_Format.text "throw "))::_185_144)
in (ws)::_185_145)
in (FStar_Format.reduce _185_146))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _185_150 = (let _185_149 = (let _185_148 = (let _185_147 = (pretty_print_statements b)
in (_185_147)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_185_148)
in ((FStar_Format.text "try"))::_185_149)
in (FStar_Format.reduce _185_150))
end
| FStar_Extraction_JavaScript_Ast.JSS_FunctionDeclaration (f) -> begin
(let _185_152 = (let _185_151 = (pretty_print_fun f)
in (_185_151)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _185_152))
end
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(

let isNull = (fun v -> (match (v) with
| FStar_Extraction_JavaScript_Ast.JSE_Literal (FStar_Extraction_JavaScript_Ast.JSV_Null, "") -> begin
true
end
| _85_158 -> begin
false
end))
in (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _85_161) when (n = "_") -> begin
(match (e) with
| Some (v) when (isNull v) -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _185_156 = (let _185_155 = (pretty_print_exp v)
in (_185_155)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _185_156))
end
| None -> begin
FStar_Format.empty
end)
end
| _85_170 -> begin
(let _185_165 = (let _185_164 = (print_kind_var k)
in (let _185_163 = (let _185_162 = (print_pattern p true)
in (let _185_161 = (let _185_160 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _185_159 = (let _185_158 = (let _185_157 = (pretty_print_exp v)
in (_185_157)::[])
in ((FStar_Format.text "="))::_185_158)
in (FStar_Format.reduce _185_159))
end)
in (_185_160)::(semi)::(FStar_Format.hardline)::[])
in (_185_162)::_185_161))
in (_185_164)::_185_163))
in (FStar_Format.reduce _185_165))
end))
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(match (d) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _185_167 = (FStar_List.map (fun x -> (print_export_stmt x)) l)
in (FStar_Format.reduce _185_167))
end
| _85_184 -> begin
(let _185_170 = (let _185_169 = (let _185_168 = (optws s)
in (_185_168)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_185_169)
in (FStar_Format.reduce _185_170))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(let _185_173 = (let _185_172 = (let _185_171 = (pretty_print_exp e)
in (_185_171)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_185_172)
in (FStar_Format.reduce _185_173))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _185_182 = (let _185_181 = (let _185_180 = (let _185_174 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _185_174))
in (let _185_179 = (let _185_178 = (let _185_177 = (let _185_176 = (let _185_175 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _185_175))
in (_185_176)::((FStar_Format.text "\""))::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "\"./"))::_185_177)
in ((FStar_Format.text " from "))::_185_178)
in (_185_180)::_185_179))
in ((FStar_Format.text "import * as "))::_185_181)
in (FStar_Format.reduce _185_182))
end
| FStar_Extraction_JavaScript_Ast.JSS_Seq (l) -> begin
(pretty_print_statements l)
end))
in (f p))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _185_184 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _185_184)))
and print_export_stmt : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _85_202) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(let _185_187 = (let _185_186 = (pretty_print_exp v)
in (_185_186)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _185_187))
end
| None -> begin
FStar_Format.empty
end)
end
| _85_209 -> begin
(let _185_190 = (let _185_189 = (let _185_188 = (pretty_print_statement s)
in (_185_188)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_185_189)
in (FStar_Format.reduce _185_190))
end)
end
| _85_211 -> begin
(let _185_193 = (let _185_192 = (let _185_191 = (pretty_print_statement s)
in (_185_191)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_185_192)
in (FStar_Format.reduce _185_193))
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _85_8 -> (match (_85_8) with
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _185_198 = (let _185_197 = (let _185_196 = (let _185_195 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _185_195 (FStar_Format.combine comma)))
in (_185_196)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_185_197)
in (FStar_Format.reduce _185_198))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _185_202 = (let _185_201 = (let _185_200 = (let _185_199 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _185_199 (FStar_Format.combine comma)))
in (_185_200)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_185_201)
in (FStar_Format.reduce _185_202))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_85_223, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _85_231 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _185_206 = (let _185_205 = (let _185_204 = (let _185_203 = (print_body body)
in (print_arrow_fun args _185_203 ret_t))
in (_185_204)::[])
in (decl_t)::_185_205)
in (FStar_Format.reduce _185_206))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _185_209 = (let _185_208 = (let _185_207 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _185_207 (FStar_Format.combine semi)))
in (_185_208)::[])
in (FStar_Format.reduce _185_209))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _185_212 = (let _185_211 = (let _185_210 = (pretty_print_exp e)
in (_185_210)::[])
in ((print_op_un o))::_185_211)
in (FStar_Format.reduce _185_212))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _185_218 = (let _185_217 = (let _185_216 = (pretty_print_exp e1)
in (let _185_215 = (let _185_214 = (let _185_213 = (pretty_print_exp e2)
in (_185_213)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_185_214)
in (_185_216)::_185_215))
in ((FStar_Format.text "("))::_185_217)
in (FStar_Format.reduce _185_218))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _85_250) when (n = "_") -> begin
(pretty_print_exp e)
end
| _85_254 -> begin
(let _185_223 = (let _185_222 = (print_pattern p false)
in (let _185_221 = (let _185_220 = (let _185_219 = (pretty_print_exp e)
in (_185_219)::[])
in ((FStar_Format.text "="))::_185_220)
in (_185_222)::_185_221))
in (FStar_Format.reduce _185_223))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _185_228 = (let _185_227 = (pretty_print_exp e1)
in (let _185_226 = (let _185_225 = (let _185_224 = (pretty_print_exp e2)
in (_185_224)::[])
in ((print_op_log o))::_185_225)
in (_185_227)::_185_226))
in (FStar_Format.reduce _185_228))
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _185_231 = (FStar_List.map (fun x -> (let _185_230 = (pretty_print_exp x)
in (FStar_Format.parens _185_230))) l)
in (FStar_All.pipe_right _185_231 (FStar_Format.combine FStar_Format.empty)))
in (let _185_233 = (let _185_232 = (pretty_print_exp e)
in (_185_232)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _85_268 -> begin
le
end))::[])
in (FStar_Format.reduce _185_233)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _185_237 = (let _185_236 = (pretty_print_exp o)
in (let _185_235 = (let _185_234 = (pretty_print_propmem p)
in (_185_234)::[])
in (_185_236)::_185_235))
in (FStar_Format.reduce _185_237))
end
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (id, t) -> begin
(remove_chars id)
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _185_243 = (let _185_242 = (let _185_241 = (pretty_print_exp e)
in (let _185_240 = (let _185_239 = (let _185_238 = (print_typ t)
in (_185_238)::((FStar_Format.text ")"))::[])
in (colon)::_185_239)
in (_185_241)::_185_240))
in ((FStar_Format.text "("))::_185_242)
in (FStar_Format.reduce _185_243))
end))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _185_249 = (let _185_248 = (let _185_247 = (let _185_246 = (FStar_List.map (fun s -> (remove_chars s)) l)
in (FStar_All.pipe_right _185_246 (FStar_Format.combine comma)))
in (_185_247)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_185_248)
in (FStar_Format.reduce _185_249))
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
(let _185_256 = (let _185_255 = (let _185_254 = (let _185_253 = (print_typ v)
in (FStar_Format.parens _185_253))
in (_185_254)::[])
in (colon)::_185_255)
in (FStar_Format.reduce _185_256))
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
(let _185_263 = (let _185_262 = (let _185_261 = (print_pattern x true)
in (FStar_Format.parens _185_261))
in (_185_262)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _185_263))
end
| (hd)::tl -> begin
(let _185_271 = (let _185_270 = (let _185_264 = (print_pattern hd true)
in (FStar_Format.parens _185_264))
in (let _185_269 = (let _185_268 = (let _185_267 = (let _185_266 = (let _185_265 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _185_265))
in (_185_266)::[])
in ((FStar_Format.text "=>"))::_185_267)
in (ret_t)::_185_268)
in (_185_270)::_185_269))
in (FStar_Format.reduce _185_271))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _85_310) -> begin
(let _185_277 = (let _185_276 = (pretty_print_prop_key k)
in (let _185_275 = (let _185_274 = (let _185_273 = (pretty_print_exp e)
in (_185_273)::[])
in ((FStar_Format.text ":"))::_185_274)
in (_185_276)::_185_275))
in (FStar_Format.reduce _185_277))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal l)
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _185_279 = (jstr_escape id)
in (FStar_Format.text _185_279))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _185_284 = (let _185_283 = (let _185_282 = (let _185_281 = (jstr_escape i)
in (FStar_Format.text _185_281))
in (_185_282)::[])
in ((FStar_Format.text "."))::_185_283)
in (FStar_Format.reduce _185_284))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _185_287 = (let _185_286 = (let _185_285 = (pretty_print_exp e)
in (_185_285)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_185_286)
in (FStar_Format.reduce _185_287))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _85_9 -> (match (_85_9) with
| FStar_Extraction_JavaScript_Ast.JST_Any -> begin
(FStar_Format.text "any")
end
| FStar_Extraction_JavaScript_Ast.JST_Mixed -> begin
(FStar_Format.text "mixed")
end
| FStar_Extraction_JavaScript_Ast.JST_Empty -> begin
(failwith "todo: pretty-print [JST_Empty]")
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_85_341) -> begin
(failwith "todo: pretty-print [JST_Nullable]")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(

let decl_vars = if (FStar_ST.read f_print_arrow_fun_t) then begin
decl_vars
end else begin
None
end
in (

let _85_349 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _85_353, _85_355) -> begin
(let _185_298 = (let _185_297 = (let _185_296 = (let _185_295 = (FStar_List.map (fun _85_360 -> (match (_85_360) with
| (k, t) -> begin
(let _185_294 = (let _185_293 = (pretty_print_prop_key k)
in (let _185_292 = (let _185_291 = (let _185_290 = (print_typ t)
in (_185_290)::[])
in ((FStar_Format.text ":"))::_185_291)
in (_185_293)::_185_292))
in (FStar_Format.reduce _185_294))
end)) lp)
in (FStar_All.pipe_right _185_295 (FStar_Format.combine comma)))
in (_185_296)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_185_297)
in (FStar_Format.reduce _185_298))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _185_302 = (let _185_301 = (let _185_300 = (let _185_299 = (print_typ t)
in (_185_299)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_185_300)
in ((FStar_Format.text "Array"))::_185_301)
in (FStar_Format.reduce _185_302))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _185_305 = (let _185_304 = (let _185_303 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _185_303 (FStar_Format.combine (FStar_Format.text "|"))))
in (_185_304)::[])
in (FStar_Format.reduce _185_305))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _185_308 = (let _185_307 = (let _185_306 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _185_306 (FStar_Format.combine (FStar_Format.text "&"))))
in (_185_307)::[])
in (FStar_Format.reduce _185_308))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _185_311 = (let _185_310 = (let _185_309 = (print_typ t)
in (_185_309)::[])
in ((FStar_Format.text "typeof"))::_185_310)
in (FStar_Format.reduce _185_311))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _185_315 = (let _185_314 = (let _185_313 = (let _185_312 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _185_312 (FStar_Format.combine comma)))
in (_185_313)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_185_314)
in (FStar_Format.reduce _185_315))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _85_373) -> begin
(let _185_318 = (let _185_317 = (let _185_316 = (jstr_escape s)
in (Prims.strcat _185_316 "\""))
in (Prims.strcat "\"" _185_317))
in (FStar_Format.text _185_318))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _85_378) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _85_383) -> begin
(let _185_319 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _185_319))
end
| FStar_Extraction_JavaScript_Ast.JST_Exists -> begin
(failwith "todo: pretty-print [JST_Exists]")
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (n, lt) -> begin
(

let print_lt = (match (lt) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _185_323 = (let _185_322 = (let _185_321 = (let _185_320 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _185_320 (FStar_Format.combine comma)))
in (_185_321)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_185_322)
in (FStar_Format.reduce _185_323))
end)
in (let _185_325 = (let _185_324 = (print_gen_t n)
in (_185_324)::(print_lt)::[])
in (FStar_Format.reduce _185_325)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _85_404 -> (match (_85_404) with
| ((id, _85_401), t) -> begin
(let _185_336 = (let _185_335 = (let _185_331 = (jstr_escape id)
in (FStar_Format.text _185_331))
in (let _185_334 = (let _185_333 = (let _185_332 = (print_typ t)
in (_185_332)::[])
in (colon)::_185_333)
in (_185_335)::_185_334))
in (FStar_Format.reduce _185_336))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _185_340 = (let _185_339 = (let _185_338 = (let _185_337 = (print_typ ret_t)
in (_185_337)::[])
in ((FStar_Format.text "=>"))::_185_338)
in ((FStar_Format.text "()"))::_185_339)
in (FStar_Format.reduce _185_340))
end
| (x)::[] -> begin
(let _185_347 = (let _185_346 = (let _185_341 = (print_arg x)
in (FStar_Format.parens _185_341))
in (let _185_345 = (let _185_344 = (let _185_343 = (let _185_342 = (print_typ ret_t)
in (FStar_Format.parens _185_342))
in (_185_343)::[])
in ((FStar_Format.text "=>"))::_185_344)
in (_185_346)::_185_345))
in (FStar_Format.reduce _185_347))
end
| (hd)::tl -> begin
(let _185_354 = (let _185_353 = (let _185_348 = (print_arg hd)
in (FStar_Format.parens _185_348))
in (let _185_352 = (let _185_351 = (let _185_350 = (let _185_349 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _185_349))
in (_185_350)::[])
in ((FStar_Format.text "=>"))::_185_351)
in (_185_353)::_185_352))
in (FStar_Format.reduce _185_354))
end)
in (let _185_356 = (let _185_355 = (print_decl_t decl_vars)
in (_185_355)::(args_t)::[])
in (FStar_Format.reduce _185_356)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _85_10 -> (match (_85_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _85_415) -> begin
(remove_chars id)
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _85_421)) -> begin
(let _185_362 = (let _185_361 = (print_gen_t g)
in (let _185_360 = (let _185_359 = (let _185_358 = (remove_chars id)
in (_185_358)::[])
in (comma)::_185_359)
in (_185_361)::_185_360))
in (FStar_Format.reduce _185_362))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.literal_t  ->  FStar_Format.doc = (fun _85_427 -> (match (_85_427) with
| (v, s) -> begin
(match (((v), (s))) with
| (FStar_Extraction_JavaScript_Ast.JSV_String (s), _85_431) -> begin
(let _185_366 = (let _185_365 = (let _185_364 = (jstr_escape s)
in (Prims.strcat _185_364 "\""))
in (Prims.strcat "\"" _185_365))
in (FStar_Format.text _185_366))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Boolean (b), _85_436) -> begin
(let _185_367 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _185_367))
end
| (FStar_Extraction_JavaScript_Ast.JSV_Null, _85_440) -> begin
(FStar_Format.text "null")
end
| (FStar_Extraction_JavaScript_Ast.JSV_Number (f), s) -> begin
(FStar_Format.text s)
end)
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _85_11 -> (match (_85_11) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_85_453) -> begin
(failwith "todo: pretty-print [JGP_Object]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_85_456) -> begin
(failwith "todo: pretty-print [JGP_Array]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_85_459) -> begin
(failwith "todo: pretty-print [JGP_Assignment]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _185_373 = (let _185_372 = (let _185_371 = (print_typ v)
in (_185_371)::[])
in (colon)::_185_372)
in (FStar_Format.reduce _185_373))
end
| None -> begin
FStar_Format.empty
end)
in (let _185_375 = (let _185_374 = (remove_chars id)
in (_185_374)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _185_375)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _85_12 -> (match (_85_12) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _185_380 = (let _185_379 = (let _185_378 = (let _185_377 = (pretty_print_statements l)
in (_185_377)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_185_378)
in ((FStar_Format.text "{"))::_185_379)
in (FStar_Format.reduce _185_380))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _185_381 = (pretty_print_exp e)
in (FStar_Format.parens _185_381))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _85_481 -> (match (_85_481) with
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
(let _185_386 = (let _185_385 = (let _185_384 = (let _185_383 = (print_typ v)
in (_185_383)::[])
in (ws)::_185_384)
in ((FStar_Format.text ":"))::_185_385)
in (FStar_Format.reduce _185_386))
end
| None -> begin
FStar_Format.empty
end)
in (let _185_401 = (let _185_400 = (let _185_399 = (let _185_398 = (let _185_397 = (print_decl_t typePars)
in (let _185_396 = (let _185_395 = (let _185_389 = (let _185_388 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _185_388 (FStar_Format.combine comma)))
in (FStar_Format.parens _185_389))
in (let _185_394 = (let _185_393 = (let _185_392 = (let _185_391 = (let _185_390 = (print_body body)
in (_185_390)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_185_391)
in ((FStar_Format.text "{"))::_185_392)
in (returnT)::_185_393)
in (_185_395)::_185_394))
in (_185_397)::_185_396))
in (name)::_185_398)
in (ws)::_185_399)
in ((FStar_Format.text "function"))::_185_400)
in (FStar_Format.reduce _185_401))))
end))





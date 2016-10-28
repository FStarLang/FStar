
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_62 = (let _180_61 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(

let _83_78 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t true)
in (

let _83_80 = (FStar_ST.op_Colon_Equals f_print_arrow_fun true)
in (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_85 -> begin
(pretty_print_statement s)
end)))
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_61))
in (FStar_Format.reduce _180_62)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_92 -> begin
(let _180_69 = (let _180_68 = (let _180_67 = (let _180_66 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_66))
in (_180_67)::[])
in (ws)::_180_68)
in (FStar_Format.reduce _180_69))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_74 = (let _180_73 = (let _180_72 = (pretty_print_statements l)
in (_180_72)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_73)
in (FStar_Format.reduce _180_74))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_77 = (let _180_76 = (let _180_75 = (pretty_print_exp e)
in (_180_75)::(semi)::[])
in (ws)::_180_76)
in (FStar_Format.reduce _180_77))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_94 = (let _180_93 = (let _180_92 = (let _180_91 = (let _180_78 = (pretty_print_exp c)
in (FStar_Format.parens _180_78))
in (let _180_90 = (let _180_89 = (let _180_88 = (let _180_87 = (optws t)
in (let _180_86 = (let _180_85 = (let _180_84 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_83 = (let _180_82 = (let _180_81 = (let _180_80 = (let _180_79 = (optws s)
in (_180_79)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_80)
in ((FStar_Format.text "else"))::_180_81)
in (ws)::_180_82)
in (FStar_Format.reduce _180_83))
end)
in (_180_84)::[])
in ((FStar_Format.text "}"))::_180_85)
in (_180_87)::_180_86))
in (FStar_Format.hardline)::_180_88)
in ((FStar_Format.text "{"))::_180_89)
in (_180_91)::_180_90))
in ((FStar_Format.text "if"))::_180_92)
in (ws)::_180_93)
in (FStar_Format.reduce _180_94))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_102 = (let _180_101 = (let _180_100 = (let _180_95 = (jstr_escape l)
in (FStar_Format.text _180_95))
in (let _180_99 = (let _180_98 = (let _180_97 = (let _180_96 = (optws s)
in (_180_96)::[])
in (FStar_Format.hardline)::_180_97)
in (colon)::_180_98)
in (_180_100)::_180_99))
in (ws)::_180_101)
in (FStar_Format.reduce _180_102))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(let _180_110 = (let _180_109 = (let _180_108 = (let _180_107 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_106 = (let _180_105 = (let _180_104 = (let _180_103 = (jstr_escape v)
in (FStar_Format.text _180_103))
in (_180_104)::[])
in (ws)::_180_105)
in (FStar_Format.reduce _180_106))
end)
in (_180_107)::(semi)::[])
in ((FStar_Format.text "break"))::_180_108)
in (ws)::_180_109)
in (FStar_Format.reduce _180_110))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_118 = (let _180_117 = (let _180_116 = (let _180_115 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_114 = (let _180_113 = (let _180_112 = (let _180_111 = (jstr_escape v)
in (FStar_Format.text _180_111))
in (_180_112)::[])
in (ws)::_180_113)
in (FStar_Format.reduce _180_114))
end)
in (_180_115)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_116)
in (ws)::_180_117)
in (FStar_Format.reduce _180_118))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_126 = (let _180_125 = (let _180_124 = (let _180_123 = (let _180_119 = (pretty_print_exp e)
in (FStar_Format.parens _180_119))
in (let _180_122 = (let _180_121 = (let _180_120 = (optws s)
in (_180_120)::[])
in (FStar_Format.hardline)::_180_121)
in (_180_123)::_180_122))
in ((FStar_Format.text "with"))::_180_124)
in (ws)::_180_125)
in (FStar_Format.reduce _180_126))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_133), lt, t) -> begin
(let _180_135 = (let _180_134 = (let _180_133 = (let _180_127 = (jstr_escape id)
in (FStar_Format.text _180_127))
in (let _180_132 = (let _180_131 = (print_decl_t lt)
in (let _180_130 = (let _180_129 = (let _180_128 = (print_typ t)
in (_180_128)::(semi)::[])
in ((FStar_Format.text "="))::_180_129)
in (_180_131)::_180_130))
in (_180_133)::_180_132))
in ((FStar_Format.text "type "))::_180_134)
in (FStar_Format.reduce _180_135))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_157 = (let _180_156 = (let _180_155 = (let _180_154 = (let _180_136 = (pretty_print_exp e)
in (FStar_Format.parens _180_136))
in (let _180_153 = (let _180_152 = (let _180_151 = (let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (FStar_List.map (fun _83_145 -> (match (_83_145) with
| (e, l) -> begin
(let _180_146 = (let _180_145 = (let _180_144 = (let _180_143 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_142 = (let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_138))
in (_180_139)::[])
in (FStar_Format.hardline)::_180_140)
in (colon)::_180_141)
in (_180_143)::_180_142))
in ((FStar_Format.text "case "))::_180_144)
in (ws)::_180_145)
in (FStar_Format.reduce _180_146))
end)) lcase)
in (FStar_All.pipe_right _180_147 (FStar_Format.combine FStar_Format.hardline)))
in (_180_148)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_149)
in ((FStar_Format.text "{"))::_180_150)
in (ws)::_180_151)
in (FStar_Format.hardline)::_180_152)
in (_180_154)::_180_153))
in ((FStar_Format.text "switch"))::_180_155)
in (ws)::_180_156)
in (FStar_Format.reduce _180_157))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_164 = (let _180_163 = (let _180_162 = (let _180_161 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_160 = (let _180_159 = (let _180_158 = (pretty_print_exp v)
in (_180_158)::[])
in (ws)::_180_159)
in (FStar_Format.reduce _180_160))
end)
in (_180_161)::(semi)::[])
in ((FStar_Format.text "return"))::_180_162)
in (ws)::_180_163)
in (FStar_Format.reduce _180_164))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_168 = (let _180_167 = (let _180_166 = (let _180_165 = (pretty_print_exp e)
in (_180_165)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_166)
in (ws)::_180_167)
in (FStar_Format.reduce _180_168))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_172 = (let _180_171 = (let _180_170 = (let _180_169 = (pretty_print_statements b)
in (_180_169)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_170)
in ((FStar_Format.text "try"))::_180_171)
in (FStar_Format.reduce _180_172))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_180 = (let _180_179 = (let _180_178 = (let _180_177 = (let _180_173 = (pretty_print_exp e)
in (FStar_Format.parens _180_173))
in (let _180_176 = (let _180_175 = (let _180_174 = (optws s)
in (_180_174)::[])
in (FStar_Format.hardline)::_180_175)
in (_180_177)::_180_176))
in ((FStar_Format.text "while"))::_180_178)
in (ws)::_180_179)
in (FStar_Format.reduce _180_180))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_192 = (let _180_191 = (let _180_190 = (let _180_189 = (let _180_188 = (optws s)
in (let _180_187 = (let _180_186 = (pretty_print_statement s)
in (let _180_185 = (let _180_184 = (let _180_183 = (let _180_182 = (let _180_181 = (pretty_print_exp e)
in (FStar_Format.parens _180_181))
in (_180_182)::(semi)::[])
in ((FStar_Format.text "while"))::_180_183)
in (ws)::_180_184)
in (_180_186)::_180_185))
in (_180_188)::_180_187))
in (FStar_Format.hardline)::_180_189)
in ((FStar_Format.text "do"))::_180_190)
in (ws)::_180_191)
in (FStar_Format.reduce _180_192))
end
| FStar_Extraction_JavaScript_Ast.JSS_For (i, c, l, s) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Forin (i, e, s) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_ForOf (i, e, s) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Let (l, s) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Debugger -> begin
(FStar_Format.reduce ((ws)::((FStar_Format.text "debugger;"))::[]))
end
| FStar_Extraction_JavaScript_Ast.JSS_FunctionDeclaration (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration (l, k) -> begin
(let _180_209 = (let _180_208 = (let _180_207 = (print_kind_var k)
in (let _180_206 = (let _180_205 = (let _180_204 = (let _180_203 = (FStar_List.map (fun _83_197 -> (match (_83_197) with
| (p, e) -> begin
(let _180_202 = (let _180_201 = (print_pattern1 p true)
in (let _180_200 = (let _180_199 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_198 = (let _180_197 = (let _180_196 = (let _180_195 = (let _180_194 = (pretty_print_exp v)
in (_180_194)::[])
in (ws)::_180_195)
in ((FStar_Format.text "="))::_180_196)
in (ws)::_180_197)
in (FStar_Format.reduce _180_198))
end)
in (_180_199)::[])
in (_180_201)::_180_200))
in (FStar_Format.reduce _180_202))
end)) l)
in (FStar_All.pipe_right _180_203 (FStar_Format.combine comma)))
in (_180_204)::(semi)::[])
in (ws)::_180_205)
in (_180_207)::_180_206))
in (ws)::_180_208)
in (FStar_Format.reduce _180_209))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_202) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_205) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(let _180_213 = (let _180_212 = (print_exp_kind k)
in (let _180_211 = (let _180_210 = (print_declaration d)
in (_180_210)::[])
in (_180_212)::_180_211))
in (FStar_Format.reduce _180_213))
end))
in (let _180_215 = (let _180_214 = (f p)
in (_180_214)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_215)))))
and print_declaration : FStar_Extraction_JavaScript_Ast.declaration  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(pretty_print_statement s)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(pretty_print_exp e)
end))
and print_exp_kind : FStar_Extraction_JavaScript_Ast.export_kind  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
| FStar_Extraction_JavaScript_Ast.ExportType -> begin
(FStar_Format.text "declare ")
end
| FStar_Extraction_JavaScript_Ast.ExportValue -> begin
(FStar_Format.text "export ")
end))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_219 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_219)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_226 = (let _180_225 = (let _180_224 = (let _180_223 = (FStar_List.map (fun s -> (let _180_222 = (remove_chars_t s)
in (FStar_Format.text _180_222))) l)
in (FStar_All.pipe_right _180_223 (FStar_Format.combine comma)))
in (_180_224)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_225)
in (FStar_Format.reduce _180_226))
end
| None -> begin
FStar_Format.empty
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_231 = (let _180_230 = (let _180_229 = (let _180_228 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_228 (FStar_Format.combine comma)))
in (_180_229)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_230)
in (FStar_Format.reduce _180_231))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_235 = (let _180_234 = (let _180_233 = (let _180_232 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_232 (FStar_Format.combine comma)))
in (_180_233)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_234)
in (FStar_Format.reduce _180_235))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_238, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_246 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_239 = (let _180_238 = (let _180_237 = (let _180_236 = (print_body body)
in (print_arrow_fun args _180_236 ret_t))
in (_180_237)::[])
in (decl_t)::_180_238)
in (FStar_Format.reduce _180_239))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_242 = (let _180_241 = (let _180_240 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_240 (FStar_Format.combine semi)))
in (_180_241)::[])
in (FStar_Format.reduce _180_242))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_246 = (let _180_245 = (print_op_un o)
in (let _180_244 = (let _180_243 = (pretty_print_exp e)
in (_180_243)::[])
in (_180_245)::_180_244))
in (FStar_Format.reduce _180_246))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_252 = (let _180_251 = (let _180_250 = (pretty_print_exp e1)
in (let _180_249 = (let _180_248 = (let _180_247 = (pretty_print_exp e2)
in (_180_247)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_248)
in (_180_250)::_180_249))
in ((FStar_Format.text "("))::_180_251)
in (FStar_Format.reduce _180_252))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(let _180_257 = (let _180_256 = (print_pattern p false)
in (let _180_255 = (let _180_254 = (let _180_253 = (pretty_print_exp e)
in (_180_253)::[])
in ((FStar_Format.text "="))::_180_254)
in (_180_256)::_180_255))
in (FStar_Format.reduce _180_257))
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_262 = (let _180_261 = (pretty_print_exp e1)
in (let _180_260 = (let _180_259 = (let _180_258 = (pretty_print_exp e2)
in (_180_258)::[])
in ((print_op_log o))::_180_259)
in (_180_261)::_180_260))
in (FStar_Format.reduce _180_262))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _180_265 = (FStar_List.map (fun x -> (let _180_264 = (pretty_print_exp x)
in (FStar_Format.parens _180_264))) l)
in (FStar_All.pipe_right _180_265 (FStar_Format.combine FStar_Format.empty)))
in (let _180_267 = (let _180_266 = (pretty_print_exp e)
in (_180_266)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_290 -> begin
le
end))::[])
in (FStar_Format.reduce _180_267)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_271 = (let _180_270 = (pretty_print_exp o)
in (let _180_269 = (let _180_268 = (pretty_print_propmem p)
in (_180_268)::[])
in (_180_270)::_180_269))
in (FStar_Format.reduce _180_271))
end
| FStar_Extraction_JavaScript_Ast.JSE_Yield (e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Comprehension (l, e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Generator (l, e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Let (l, e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (id, t) -> begin
(let _180_272 = (remove_chars_t id)
in (FStar_Format.text _180_272))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_278 = (let _180_277 = (let _180_276 = (pretty_print_exp e)
in (let _180_275 = (let _180_274 = (let _180_273 = (print_typ t)
in (_180_273)::((FStar_Format.text ")"))::[])
in (colon)::_180_274)
in (_180_276)::_180_275))
in ((FStar_Format.text "("))::_180_277)
in (FStar_Format.reduce _180_278))
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option  ->  FStar_Format.doc = (fun args body ret_t -> (

let ret_t = (match (ret_t) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_285 = (let _180_284 = (let _180_283 = (let _180_282 = (print_typ v)
in (FStar_Format.parens _180_282))
in (_180_283)::[])
in (colon)::_180_284)
in (FStar_Format.reduce _180_285))
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
(let _180_292 = (let _180_291 = (let _180_290 = (print_pattern x true)
in (FStar_Format.parens _180_290))
in (_180_291)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_292))
end
| (hd)::tl -> begin
(let _180_300 = (let _180_299 = (let _180_293 = (print_pattern hd true)
in (FStar_Format.parens _180_293))
in (let _180_298 = (let _180_297 = (let _180_296 = (let _180_295 = (let _180_294 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_294))
in (_180_295)::[])
in ((FStar_Format.text "=>"))::_180_296)
in (ret_t)::_180_297)
in (_180_299)::_180_298))
in (FStar_Format.reduce _180_300))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_343) -> begin
(let _180_306 = (let _180_305 = (pretty_print_prop_key k)
in (let _180_304 = (let _180_303 = (let _180_302 = (pretty_print_exp e)
in (_180_302)::[])
in ((FStar_Format.text ":"))::_180_303)
in (_180_305)::_180_304))
in (FStar_Format.reduce _180_306))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_308 = (jstr_escape id)
in (FStar_Format.text _180_308))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_313 = (let _180_312 = (let _180_311 = (let _180_310 = (jstr_escape i)
in (FStar_Format.text _180_310))
in (_180_311)::[])
in ((FStar_Format.text "."))::_180_312)
in (FStar_Format.reduce _180_313))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_316 = (let _180_315 = (let _180_314 = (pretty_print_exp e)
in (_180_314)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_315)
in (FStar_Format.reduce _180_316))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JST_Any -> begin
(FStar_Format.text "any")
end
| FStar_Extraction_JavaScript_Ast.JST_Mixed -> begin
(FStar_Format.text "mixed")
end
| FStar_Extraction_JavaScript_Ast.JST_Empty -> begin
(FStar_Format.text "!!!")
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_374) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(

let decl_vars = if (FStar_ST.read f_print_arrow_fun_t) then begin
decl_vars
end else begin
None
end
in (

let _83_382 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_386, _83_388) -> begin
(let _180_327 = (let _180_326 = (let _180_325 = (let _180_324 = (FStar_List.map (fun _83_393 -> (match (_83_393) with
| (k, t) -> begin
(let _180_323 = (let _180_322 = (pretty_print_prop_key k)
in (let _180_321 = (let _180_320 = (let _180_319 = (print_typ t)
in (_180_319)::[])
in ((FStar_Format.text ":"))::_180_320)
in (_180_322)::_180_321))
in (FStar_Format.reduce _180_323))
end)) lp)
in (FStar_All.pipe_right _180_324 (FStar_Format.combine comma)))
in (_180_325)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_326)
in (FStar_Format.reduce _180_327))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_331 = (let _180_330 = (let _180_329 = (let _180_328 = (print_typ t)
in (_180_328)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_329)
in ((FStar_Format.text "Array"))::_180_330)
in (FStar_Format.reduce _180_331))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_334 = (let _180_333 = (let _180_332 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_332 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_333)::[])
in (FStar_Format.reduce _180_334))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_337 = (let _180_336 = (let _180_335 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_335 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_336)::[])
in (FStar_Format.reduce _180_337))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_340 = (let _180_339 = (let _180_338 = (print_typ t)
in (_180_338)::[])
in ((FStar_Format.text "typeof"))::_180_339)
in (FStar_Format.reduce _180_340))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_344 = (let _180_343 = (let _180_342 = (let _180_341 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_341 (FStar_Format.combine comma)))
in (_180_342)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_343)
in (FStar_Format.reduce _180_344))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_406) -> begin
(let _180_347 = (let _180_346 = (let _180_345 = (jstr_escape s)
in (Prims.strcat _180_345 "\""))
in (Prims.strcat "\"" _180_346))
in (FStar_Format.text _180_347))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_411) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_416) -> begin
(let _180_348 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_348))
end
| FStar_Extraction_JavaScript_Ast.JST_Exists -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (n, lt) -> begin
(

let print_lt = (match (lt) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_352 = (let _180_351 = (let _180_350 = (let _180_349 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_349 (FStar_Format.combine comma)))
in (_180_350)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_351)
in (FStar_Format.reduce _180_352))
end)
in (let _180_354 = (let _180_353 = (print_gen_t n)
in (_180_353)::(print_lt)::[])
in (FStar_Format.reduce _180_354)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_437 -> (match (_83_437) with
| ((id, _83_434), t) -> begin
(let _180_365 = (let _180_364 = (let _180_360 = (jstr_escape id)
in (FStar_Format.text _180_360))
in (let _180_363 = (let _180_362 = (let _180_361 = (print_typ t)
in (_180_361)::[])
in (colon)::_180_362)
in (_180_364)::_180_363))
in (FStar_Format.reduce _180_365))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_369 = (let _180_368 = (let _180_367 = (let _180_366 = (print_typ ret_t)
in (_180_366)::[])
in ((FStar_Format.text "=>"))::_180_367)
in ((FStar_Format.text "()"))::_180_368)
in (FStar_Format.reduce _180_369))
end
| (x)::[] -> begin
(let _180_376 = (let _180_375 = (let _180_370 = (print_arg x)
in (FStar_Format.parens _180_370))
in (let _180_374 = (let _180_373 = (let _180_372 = (let _180_371 = (print_typ ret_t)
in (FStar_Format.parens _180_371))
in (_180_372)::[])
in ((FStar_Format.text "=>"))::_180_373)
in (_180_375)::_180_374))
in (FStar_Format.reduce _180_376))
end
| (hd)::tl -> begin
(let _180_383 = (let _180_382 = (let _180_377 = (print_arg hd)
in (FStar_Format.parens _180_377))
in (let _180_381 = (let _180_380 = (let _180_379 = (let _180_378 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_378))
in (_180_379)::[])
in ((FStar_Format.text "=>"))::_180_380)
in (_180_382)::_180_381))
in (FStar_Format.reduce _180_383))
end)
in (let _180_385 = (let _180_384 = (print_decl_t decl_vars)
in (_180_384)::(args_t)::[])
in (FStar_Format.reduce _180_385)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_448) -> begin
(let _180_387 = (remove_chars_t id)
in (FStar_Format.text _180_387))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_454)) -> begin
(let _180_393 = (let _180_392 = (print_gen_t g)
in (let _180_391 = (let _180_390 = (let _180_389 = (let _180_388 = (remove_chars_t id)
in (FStar_Format.text _180_388))
in (_180_389)::[])
in (comma)::_180_390)
in (_180_392)::_180_391))
in (FStar_Format.reduce _180_393))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_397 = (let _180_396 = (let _180_395 = (jstr_escape s)
in (Prims.strcat _180_395 "\""))
in (Prims.strcat "\"" _180_396))
in (FStar_Format.text _180_397))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_398 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_398))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_467) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
| FStar_Extraction_JavaScript_Ast.JSV_Var -> begin
(FStar_Format.text "var")
end
| FStar_Extraction_JavaScript_Ast.JSV_Let -> begin
(FStar_Format.text "let")
end
| FStar_Extraction_JavaScript_Ast.JSV_Const -> begin
(FStar_Format.text "const")
end))
and print_pattern : FStar_Extraction_JavaScript_Ast.pattern_t  ->  Prims.bool  ->  FStar_Format.doc = (fun p print_t -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_476) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_479) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_482) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_485) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_404 = (let _180_403 = (let _180_402 = (print_typ v)
in (_180_402)::[])
in (colon)::_180_403)
in (FStar_Format.reduce _180_404))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_407 = (let _180_406 = (let _180_405 = (remove_chars_t id)
in (FStar_Format.text _180_405))
in (_180_406)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_407)))
end))
and print_pattern1 : FStar_Extraction_JavaScript_Ast.pattern_t  ->  Prims.bool  ->  FStar_Format.doc = (fun p print_t -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_412 = (let _180_411 = (let _180_410 = (print_typ v)
in (_180_410)::[])
in (colon)::_180_411)
in (FStar_Format.reduce _180_412))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_415 = (let _180_414 = (let _180_413 = (remove_chars_t id)
in (FStar_Format.text _180_413))
in (_180_414)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_415)))
end
| _83_506 -> begin
(FStar_Format.text "!!!")
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_15 -> (match (_83_15) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_419 = (let _180_418 = (let _180_417 = (pretty_print_statements l)
in (_180_417)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_418)
in (FStar_Format.reduce _180_419))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_420 = (pretty_print_exp e)
in (FStar_Format.parens _180_420))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_517 -> (match (_83_517) with
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
(let _180_425 = (let _180_424 = (let _180_423 = (let _180_422 = (print_typ v)
in (_180_422)::[])
in (ws)::_180_423)
in ((FStar_Format.text ":"))::_180_424)
in (FStar_Format.reduce _180_425))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_440 = (let _180_439 = (let _180_438 = (let _180_437 = (let _180_436 = (print_decl_t typePars)
in (let _180_435 = (let _180_434 = (let _180_428 = (let _180_427 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_427 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_428))
in (let _180_433 = (let _180_432 = (let _180_431 = (let _180_430 = (let _180_429 = (print_body body)
in (_180_429)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_430)
in ((FStar_Format.text "{"))::_180_431)
in (returnT)::_180_432)
in (_180_434)::_180_433))
in (_180_436)::_180_435))
in (name)::_180_437)
in (ws)::_180_438)
in ((FStar_Format.text "function"))::_180_439)
in (FStar_Format.reduce _180_440))))
end))





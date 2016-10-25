
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_61 = (let _180_60 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_79 -> begin
(pretty_print_statement s)
end)
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_60))
in (FStar_Format.reduce _180_61)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_86 -> begin
(let _180_68 = (let _180_67 = (let _180_66 = (let _180_65 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_65))
in (_180_66)::[])
in (ws)::_180_67)
in (FStar_Format.reduce _180_68))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_73 = (let _180_72 = (let _180_71 = (pretty_print_statements l)
in (_180_71)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_72)
in (FStar_Format.reduce _180_73))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_76 = (let _180_75 = (let _180_74 = (pretty_print_exp e)
in (_180_74)::(semi)::[])
in (ws)::_180_75)
in (FStar_Format.reduce _180_76))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_93 = (let _180_92 = (let _180_91 = (let _180_90 = (let _180_77 = (pretty_print_exp c)
in (FStar_Format.parens _180_77))
in (let _180_89 = (let _180_88 = (let _180_87 = (let _180_86 = (optws t)
in (let _180_85 = (let _180_84 = (let _180_83 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_82 = (let _180_81 = (let _180_80 = (let _180_79 = (let _180_78 = (optws s)
in (_180_78)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_79)
in ((FStar_Format.text "else"))::_180_80)
in (ws)::_180_81)
in (FStar_Format.reduce _180_82))
end)
in (_180_83)::[])
in ((FStar_Format.text "}"))::_180_84)
in (_180_86)::_180_85))
in (FStar_Format.hardline)::_180_87)
in ((FStar_Format.text "{"))::_180_88)
in (_180_90)::_180_89))
in ((FStar_Format.text "if"))::_180_91)
in (ws)::_180_92)
in (FStar_Format.reduce _180_93))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_101 = (let _180_100 = (let _180_99 = (let _180_94 = (jstr_escape l)
in (FStar_Format.text _180_94))
in (let _180_98 = (let _180_97 = (let _180_96 = (let _180_95 = (optws s)
in (_180_95)::[])
in (FStar_Format.hardline)::_180_96)
in (colon)::_180_97)
in (_180_99)::_180_98))
in (ws)::_180_100)
in (FStar_Format.reduce _180_101))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(let _180_109 = (let _180_108 = (let _180_107 = (let _180_106 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_105 = (let _180_104 = (let _180_103 = (let _180_102 = (jstr_escape v)
in (FStar_Format.text _180_102))
in (_180_103)::[])
in (ws)::_180_104)
in (FStar_Format.reduce _180_105))
end)
in (_180_106)::(semi)::[])
in ((FStar_Format.text "break"))::_180_107)
in (ws)::_180_108)
in (FStar_Format.reduce _180_109))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_117 = (let _180_116 = (let _180_115 = (let _180_114 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_113 = (let _180_112 = (let _180_111 = (let _180_110 = (jstr_escape v)
in (FStar_Format.text _180_110))
in (_180_111)::[])
in (ws)::_180_112)
in (FStar_Format.reduce _180_113))
end)
in (_180_114)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_115)
in (ws)::_180_116)
in (FStar_Format.reduce _180_117))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_125 = (let _180_124 = (let _180_123 = (let _180_122 = (let _180_118 = (pretty_print_exp e)
in (FStar_Format.parens _180_118))
in (let _180_121 = (let _180_120 = (let _180_119 = (optws s)
in (_180_119)::[])
in (FStar_Format.hardline)::_180_120)
in (_180_122)::_180_121))
in ((FStar_Format.text "with"))::_180_123)
in (ws)::_180_124)
in (FStar_Format.reduce _180_125))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_127), lt, t) -> begin
(let _180_134 = (let _180_133 = (let _180_132 = (let _180_126 = (jstr_escape id)
in (FStar_Format.text _180_126))
in (let _180_131 = (let _180_130 = (print_decl_t lt)
in (let _180_129 = (let _180_128 = (let _180_127 = (print_typ t)
in (_180_127)::(semi)::[])
in ((FStar_Format.text "="))::_180_128)
in (_180_130)::_180_129))
in (_180_132)::_180_131))
in ((FStar_Format.text "type "))::_180_133)
in (FStar_Format.reduce _180_134))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_156 = (let _180_155 = (let _180_154 = (let _180_153 = (let _180_135 = (pretty_print_exp e)
in (FStar_Format.parens _180_135))
in (let _180_152 = (let _180_151 = (let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (let _180_146 = (FStar_List.map (fun _83_139 -> (match (_83_139) with
| (e, l) -> begin
(let _180_145 = (let _180_144 = (let _180_143 = (let _180_142 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (let _180_137 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_137))
in (_180_138)::[])
in (FStar_Format.hardline)::_180_139)
in (colon)::_180_140)
in (_180_142)::_180_141))
in ((FStar_Format.text "case "))::_180_143)
in (ws)::_180_144)
in (FStar_Format.reduce _180_145))
end)) lcase)
in (FStar_All.pipe_right _180_146 (FStar_Format.combine FStar_Format.hardline)))
in (_180_147)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_148)
in ((FStar_Format.text "{"))::_180_149)
in (ws)::_180_150)
in (FStar_Format.hardline)::_180_151)
in (_180_153)::_180_152))
in ((FStar_Format.text "switch"))::_180_154)
in (ws)::_180_155)
in (FStar_Format.reduce _180_156))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_163 = (let _180_162 = (let _180_161 = (let _180_160 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_159 = (let _180_158 = (let _180_157 = (pretty_print_exp v)
in (_180_157)::[])
in (ws)::_180_158)
in (FStar_Format.reduce _180_159))
end)
in (_180_160)::(semi)::[])
in ((FStar_Format.text "return"))::_180_161)
in (ws)::_180_162)
in (FStar_Format.reduce _180_163))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_167 = (let _180_166 = (let _180_165 = (let _180_164 = (pretty_print_exp e)
in (_180_164)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_165)
in (ws)::_180_166)
in (FStar_Format.reduce _180_167))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_171 = (let _180_170 = (let _180_169 = (let _180_168 = (pretty_print_statements b)
in (_180_168)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_169)
in ((FStar_Format.text "try"))::_180_170)
in (FStar_Format.reduce _180_171))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_179 = (let _180_178 = (let _180_177 = (let _180_176 = (let _180_172 = (pretty_print_exp e)
in (FStar_Format.parens _180_172))
in (let _180_175 = (let _180_174 = (let _180_173 = (optws s)
in (_180_173)::[])
in (FStar_Format.hardline)::_180_174)
in (_180_176)::_180_175))
in ((FStar_Format.text "while"))::_180_177)
in (ws)::_180_178)
in (FStar_Format.reduce _180_179))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_191 = (let _180_190 = (let _180_189 = (let _180_188 = (let _180_187 = (optws s)
in (let _180_186 = (let _180_185 = (pretty_print_statement s)
in (let _180_184 = (let _180_183 = (let _180_182 = (let _180_181 = (let _180_180 = (pretty_print_exp e)
in (FStar_Format.parens _180_180))
in (_180_181)::(semi)::[])
in ((FStar_Format.text "while"))::_180_182)
in (ws)::_180_183)
in (_180_185)::_180_184))
in (_180_187)::_180_186))
in (FStar_Format.hardline)::_180_188)
in ((FStar_Format.text "do"))::_180_189)
in (ws)::_180_190)
in (FStar_Format.reduce _180_191))
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
(let _180_208 = (let _180_207 = (let _180_206 = (print_kind_var k)
in (let _180_205 = (let _180_204 = (let _180_203 = (let _180_202 = (FStar_List.map (fun _83_191 -> (match (_83_191) with
| (p, e) -> begin
(let _180_201 = (let _180_200 = (print_pattern1 p true)
in (let _180_199 = (let _180_198 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_197 = (let _180_196 = (let _180_195 = (let _180_194 = (let _180_193 = (pretty_print_exp v)
in (_180_193)::[])
in (ws)::_180_194)
in ((FStar_Format.text "="))::_180_195)
in (ws)::_180_196)
in (FStar_Format.reduce _180_197))
end)
in (_180_198)::[])
in (_180_200)::_180_199))
in (FStar_Format.reduce _180_201))
end)) l)
in (FStar_All.pipe_right _180_202 (FStar_Format.combine comma)))
in (_180_203)::(semi)::[])
in (ws)::_180_204)
in (_180_206)::_180_205))
in (ws)::_180_207)
in (FStar_Format.reduce _180_208))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_196) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_199) -> begin
semi
end))
in (let _180_210 = (let _180_209 = (f p)
in (_180_209)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_210)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_212 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_212)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_219 = (let _180_218 = (let _180_217 = (let _180_216 = (FStar_List.map (fun s -> (let _180_215 = (remove_chars_t s)
in (FStar_Format.text _180_215))) l)
in (FStar_All.pipe_right _180_216 (FStar_Format.combine comma)))
in (_180_217)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_218)
in (FStar_Format.reduce _180_219))
end
| None -> begin
FStar_Format.empty
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_224 = (let _180_223 = (let _180_222 = (let _180_221 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_221 (FStar_Format.combine comma)))
in (_180_222)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_223)
in (FStar_Format.reduce _180_224))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_228 = (let _180_227 = (let _180_226 = (let _180_225 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_225 (FStar_Format.combine comma)))
in (_180_226)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_227)
in (FStar_Format.reduce _180_228))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_220, args, body, ret_t, decl_vars) -> begin
(let _180_233 = (let _180_232 = (print_decl_t decl_vars)
in (let _180_231 = (let _180_230 = (let _180_229 = (print_body body)
in (print_arrow_fun args _180_229 ret_t))
in (_180_230)::[])
in (_180_232)::_180_231))
in (FStar_Format.reduce _180_233))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_236 = (let _180_235 = (let _180_234 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_234 (FStar_Format.combine semi)))
in (_180_235)::[])
in (FStar_Format.reduce _180_236))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_240 = (let _180_239 = (print_op_un o)
in (let _180_238 = (let _180_237 = (pretty_print_exp e)
in (_180_237)::[])
in (_180_239)::_180_238))
in (FStar_Format.reduce _180_240))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_246 = (let _180_245 = (let _180_244 = (pretty_print_exp e1)
in (let _180_243 = (let _180_242 = (let _180_241 = (pretty_print_exp e2)
in (_180_241)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_242)
in (_180_244)::_180_243))
in ((FStar_Format.text "("))::_180_245)
in (FStar_Format.reduce _180_246))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(let _180_251 = (let _180_250 = (print_pattern p false)
in (let _180_249 = (let _180_248 = (let _180_247 = (pretty_print_exp e)
in (_180_247)::[])
in ((FStar_Format.text "="))::_180_248)
in (_180_250)::_180_249))
in (FStar_Format.reduce _180_251))
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_256 = (let _180_255 = (pretty_print_exp e1)
in (let _180_254 = (let _180_253 = (let _180_252 = (pretty_print_exp e2)
in (_180_252)::[])
in ((print_op_log o))::_180_253)
in (_180_255)::_180_254))
in (FStar_Format.reduce _180_256))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_263 = (let _180_262 = (pretty_print_exp e)
in (let _180_261 = (let _180_260 = (let _180_259 = (FStar_List.map (fun x -> (let _180_258 = (pretty_print_exp x)
in (FStar_Format.parens _180_258))) l)
in (FStar_All.pipe_right _180_259 (FStar_Format.combine FStar_Format.empty)))
in (_180_260)::[])
in (_180_262)::_180_261))
in (FStar_Format.reduce _180_263))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_267 = (let _180_266 = (pretty_print_exp o)
in (let _180_265 = (let _180_264 = (pretty_print_propmem p)
in (_180_264)::[])
in (_180_266)::_180_265))
in (FStar_Format.reduce _180_267))
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
(let _180_268 = (remove_chars_t id)
in (FStar_Format.text _180_268))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_274 = (let _180_273 = (let _180_272 = (pretty_print_exp e)
in (let _180_271 = (let _180_270 = (let _180_269 = (print_typ t)
in (_180_269)::((FStar_Format.text ")"))::[])
in (colon)::_180_270)
in (_180_272)::_180_271))
in ((FStar_Format.text "("))::_180_273)
in (FStar_Format.reduce _180_274))
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option  ->  FStar_Format.doc = (fun args body ret_t -> (

let ret_t = (match (ret_t) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_281 = (let _180_280 = (let _180_279 = (let _180_278 = (print_typ_f v)
in (FStar_Format.parens _180_278))
in (_180_279)::[])
in (colon)::_180_280)
in (FStar_Format.reduce _180_281))
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
(let _180_288 = (let _180_287 = (let _180_286 = (print_pattern x true)
in (FStar_Format.parens _180_286))
in (_180_287)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_288))
end
| (hd)::tl -> begin
(let _180_296 = (let _180_295 = (let _180_289 = (print_pattern hd true)
in (FStar_Format.parens _180_289))
in (let _180_294 = (let _180_293 = (let _180_292 = (let _180_291 = (let _180_290 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_290))
in (_180_291)::[])
in ((FStar_Format.text "=>"))::_180_292)
in (ret_t)::_180_293)
in (_180_295)::_180_294))
in (FStar_Format.reduce _180_296))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_318) -> begin
(let _180_302 = (let _180_301 = (pretty_print_prop_key k)
in (let _180_300 = (let _180_299 = (let _180_298 = (pretty_print_exp e)
in (_180_298)::[])
in ((FStar_Format.text ":"))::_180_299)
in (_180_301)::_180_300))
in (FStar_Format.reduce _180_302))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_304 = (jstr_escape id)
in (FStar_Format.text _180_304))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_309 = (let _180_308 = (let _180_307 = (let _180_306 = (jstr_escape i)
in (FStar_Format.text _180_306))
in (_180_307)::[])
in ((FStar_Format.text "."))::_180_308)
in (FStar_Format.reduce _180_309))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_312 = (let _180_311 = (let _180_310 = (pretty_print_exp e)
in (_180_310)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_311)
in (FStar_Format.reduce _180_312))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_349) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(print_fun_typ args ret_t decl_vars)
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_358, _83_360) -> begin
(let _180_323 = (let _180_322 = (let _180_321 = (let _180_320 = (FStar_List.map (fun _83_365 -> (match (_83_365) with
| (k, t) -> begin
(let _180_319 = (let _180_318 = (pretty_print_prop_key k)
in (let _180_317 = (let _180_316 = (let _180_315 = (print_typ t)
in (_180_315)::[])
in ((FStar_Format.text ":"))::_180_316)
in (_180_318)::_180_317))
in (FStar_Format.reduce _180_319))
end)) lp)
in (FStar_All.pipe_right _180_320 (FStar_Format.combine comma)))
in (_180_321)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_322)
in (FStar_Format.reduce _180_323))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_327 = (let _180_326 = (let _180_325 = (let _180_324 = (print_typ t)
in (_180_324)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_325)
in ((FStar_Format.text "Array"))::_180_326)
in (FStar_Format.reduce _180_327))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_330 = (let _180_329 = (let _180_328 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_328 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_329)::[])
in (FStar_Format.reduce _180_330))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_333 = (let _180_332 = (let _180_331 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_331 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_332)::[])
in (FStar_Format.reduce _180_333))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_336 = (let _180_335 = (let _180_334 = (print_typ t)
in (_180_334)::[])
in ((FStar_Format.text "typeof"))::_180_335)
in (FStar_Format.reduce _180_336))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_340 = (let _180_339 = (let _180_338 = (let _180_337 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_337 (FStar_Format.combine comma)))
in (_180_338)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_339)
in (FStar_Format.reduce _180_340))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_378) -> begin
(let _180_343 = (let _180_342 = (let _180_341 = (jstr_escape s)
in (Prims.strcat _180_341 "\""))
in (Prims.strcat "\"" _180_342))
in (FStar_Format.text _180_343))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_383) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_388) -> begin
(let _180_344 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_344))
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
(let _180_348 = (let _180_347 = (let _180_346 = (let _180_345 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_345 (FStar_Format.combine comma)))
in (_180_346)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_347)
in (FStar_Format.reduce _180_348))
end)
in (let _180_350 = (let _180_349 = (print_gen_t n)
in (_180_349)::(print_lt)::[])
in (FStar_Format.reduce _180_350)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_409 -> (match (_83_409) with
| ((id, _83_406), t) -> begin
(let _180_361 = (let _180_360 = (let _180_356 = (jstr_escape id)
in (FStar_Format.text _180_356))
in (let _180_359 = (let _180_358 = (let _180_357 = (print_typ_f t)
in (_180_357)::[])
in (colon)::_180_358)
in (_180_360)::_180_359))
in (FStar_Format.reduce _180_361))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_365 = (let _180_364 = (let _180_363 = (let _180_362 = (print_typ_f ret_t)
in (_180_362)::[])
in ((FStar_Format.text "=>"))::_180_363)
in ((FStar_Format.text "()"))::_180_364)
in (FStar_Format.reduce _180_365))
end
| (x)::[] -> begin
(let _180_372 = (let _180_371 = (let _180_366 = (print_arg x)
in (FStar_Format.parens _180_366))
in (let _180_370 = (let _180_369 = (let _180_368 = (let _180_367 = (print_typ_f ret_t)
in (FStar_Format.parens _180_367))
in (_180_368)::[])
in ((FStar_Format.text "=>"))::_180_369)
in (_180_371)::_180_370))
in (FStar_Format.reduce _180_372))
end
| (hd)::tl -> begin
(let _180_379 = (let _180_378 = (let _180_373 = (print_arg hd)
in (FStar_Format.parens _180_373))
in (let _180_377 = (let _180_376 = (let _180_375 = (let _180_374 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_374))
in (_180_375)::[])
in ((FStar_Format.text "=>"))::_180_376)
in (_180_378)::_180_377))
in (FStar_Format.reduce _180_379))
end)
in (let _180_381 = (let _180_380 = (print_decl_t decl_vars)
in (_180_380)::(args_t)::[])
in (FStar_Format.reduce _180_381)))))
and print_typ_f : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun t -> (match (t) with
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(print_fun_typ args ret_t None)
end
| _83_424 -> begin
(print_typ t)
end))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_428) -> begin
(let _180_384 = (remove_chars_t id)
in (FStar_Format.text _180_384))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_434)) -> begin
(let _180_390 = (let _180_389 = (print_gen_t g)
in (let _180_388 = (let _180_387 = (let _180_386 = (let _180_385 = (remove_chars_t id)
in (FStar_Format.text _180_385))
in (_180_386)::[])
in (comma)::_180_387)
in (_180_389)::_180_388))
in (FStar_Format.reduce _180_390))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_394 = (let _180_393 = (let _180_392 = (jstr_escape s)
in (Prims.strcat _180_392 "\""))
in (Prims.strcat "\"" _180_393))
in (FStar_Format.text _180_394))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_395 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_395))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_447) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_456) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_459) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_462) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_465) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_401 = (let _180_400 = (let _180_399 = (print_typ_f v)
in (_180_399)::[])
in (colon)::_180_400)
in (FStar_Format.reduce _180_401))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_404 = (let _180_403 = (let _180_402 = (remove_chars_t id)
in (FStar_Format.text _180_402))
in (_180_403)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_404)))
end))
and print_pattern1 : FStar_Extraction_JavaScript_Ast.pattern_t  ->  Prims.bool  ->  FStar_Format.doc = (fun p print_t -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_409 = (let _180_408 = (let _180_407 = (print_typ v)
in (_180_407)::[])
in (colon)::_180_408)
in (FStar_Format.reduce _180_409))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_412 = (let _180_411 = (let _180_410 = (remove_chars_t id)
in (FStar_Format.text _180_410))
in (_180_411)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_412)))
end
| _83_486 -> begin
(FStar_Format.text "!!!")
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_416 = (let _180_415 = (let _180_414 = (pretty_print_statements l)
in (_180_414)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_415)
in (FStar_Format.reduce _180_416))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_417 = (pretty_print_exp e)
in (FStar_Format.parens _180_417))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_497 -> (match (_83_497) with
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
(let _180_422 = (let _180_421 = (let _180_420 = (let _180_419 = (print_typ v)
in (_180_419)::[])
in (ws)::_180_420)
in ((FStar_Format.text ":"))::_180_421)
in (FStar_Format.reduce _180_422))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_437 = (let _180_436 = (let _180_435 = (let _180_434 = (let _180_433 = (print_decl_t typePars)
in (let _180_432 = (let _180_431 = (let _180_425 = (let _180_424 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_424 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_425))
in (let _180_430 = (let _180_429 = (let _180_428 = (let _180_427 = (let _180_426 = (print_body body)
in (_180_426)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_427)
in ((FStar_Format.text "{"))::_180_428)
in (returnT)::_180_429)
in (_180_431)::_180_430))
in (_180_433)::_180_432))
in (name)::_180_434)
in (ws)::_180_435)
in ((FStar_Format.text "function"))::_180_436)
in (FStar_Format.reduce _180_437))))
end))





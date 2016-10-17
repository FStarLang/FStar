
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
""
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_51 = (let _180_50 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_80 -> begin
(pretty_print_statement s)
end)
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_50))
in (FStar_Format.reduce _180_51)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_87 -> begin
(let _180_58 = (let _180_57 = (let _180_56 = (let _180_55 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_55))
in (_180_56)::[])
in (ws)::_180_57)
in (FStar_Format.reduce _180_58))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_63 = (let _180_62 = (let _180_61 = (pretty_print_statements l)
in (_180_61)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_62)
in (FStar_Format.reduce _180_63))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_66 = (let _180_65 = (let _180_64 = (pretty_print_exp e)
in (_180_64)::(semi)::[])
in (ws)::_180_65)
in (FStar_Format.reduce _180_66))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_83 = (let _180_82 = (let _180_81 = (let _180_80 = (let _180_67 = (pretty_print_exp c)
in (FStar_Format.parens _180_67))
in (let _180_79 = (let _180_78 = (let _180_77 = (let _180_76 = (optws t)
in (let _180_75 = (let _180_74 = (let _180_73 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_72 = (let _180_71 = (let _180_70 = (let _180_69 = (let _180_68 = (optws s)
in (_180_68)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_69)
in ((FStar_Format.text "else"))::_180_70)
in (ws)::_180_71)
in (FStar_Format.reduce _180_72))
end)
in (_180_73)::[])
in ((FStar_Format.text "}"))::_180_74)
in (_180_76)::_180_75))
in (FStar_Format.hardline)::_180_77)
in ((FStar_Format.text "{"))::_180_78)
in (_180_80)::_180_79))
in ((FStar_Format.text "if"))::_180_81)
in (ws)::_180_82)
in (FStar_Format.reduce _180_83))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_91 = (let _180_90 = (let _180_89 = (let _180_84 = (jstr_escape l)
in (FStar_Format.text _180_84))
in (let _180_88 = (let _180_87 = (let _180_86 = (let _180_85 = (optws s)
in (_180_85)::[])
in (FStar_Format.hardline)::_180_86)
in (colon)::_180_87)
in (_180_89)::_180_88))
in (ws)::_180_90)
in (FStar_Format.reduce _180_91))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(let _180_99 = (let _180_98 = (let _180_97 = (let _180_96 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_95 = (let _180_94 = (let _180_93 = (let _180_92 = (jstr_escape v)
in (FStar_Format.text _180_92))
in (_180_93)::[])
in (ws)::_180_94)
in (FStar_Format.reduce _180_95))
end)
in (_180_96)::(semi)::[])
in ((FStar_Format.text "break"))::_180_97)
in (ws)::_180_98)
in (FStar_Format.reduce _180_99))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_107 = (let _180_106 = (let _180_105 = (let _180_104 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_103 = (let _180_102 = (let _180_101 = (let _180_100 = (jstr_escape v)
in (FStar_Format.text _180_100))
in (_180_101)::[])
in (ws)::_180_102)
in (FStar_Format.reduce _180_103))
end)
in (_180_104)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_105)
in (ws)::_180_106)
in (FStar_Format.reduce _180_107))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_115 = (let _180_114 = (let _180_113 = (let _180_112 = (let _180_108 = (pretty_print_exp e)
in (FStar_Format.parens _180_108))
in (let _180_111 = (let _180_110 = (let _180_109 = (optws s)
in (_180_109)::[])
in (FStar_Format.hardline)::_180_110)
in (_180_112)::_180_111))
in ((FStar_Format.text "with"))::_180_113)
in (ws)::_180_114)
in (FStar_Format.reduce _180_115))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_128), lt, t) -> begin
(let _180_124 = (let _180_123 = (let _180_122 = (let _180_116 = (jstr_escape id)
in (FStar_Format.text _180_116))
in (let _180_121 = (let _180_120 = (print_decl_t lt)
in (let _180_119 = (let _180_118 = (let _180_117 = (print_typ t)
in (_180_117)::(semi)::[])
in ((FStar_Format.text "="))::_180_118)
in (_180_120)::_180_119))
in (_180_122)::_180_121))
in ((FStar_Format.text "type "))::_180_123)
in (FStar_Format.reduce _180_124))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_146 = (let _180_145 = (let _180_144 = (let _180_143 = (let _180_125 = (pretty_print_exp e)
in (FStar_Format.parens _180_125))
in (let _180_142 = (let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (let _180_137 = (let _180_136 = (FStar_List.map (fun _83_140 -> (match (_83_140) with
| (e, l) -> begin
(let _180_135 = (let _180_134 = (let _180_133 = (let _180_132 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_131 = (let _180_130 = (let _180_129 = (let _180_128 = (let _180_127 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_127))
in (_180_128)::[])
in (FStar_Format.hardline)::_180_129)
in (colon)::_180_130)
in (_180_132)::_180_131))
in ((FStar_Format.text "case "))::_180_133)
in (ws)::_180_134)
in (FStar_Format.reduce _180_135))
end)) lcase)
in (FStar_All.pipe_right _180_136 (FStar_Format.combine FStar_Format.hardline)))
in (_180_137)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_138)
in ((FStar_Format.text "{"))::_180_139)
in (ws)::_180_140)
in (FStar_Format.hardline)::_180_141)
in (_180_143)::_180_142))
in ((FStar_Format.text "switch"))::_180_144)
in (ws)::_180_145)
in (FStar_Format.reduce _180_146))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_153 = (let _180_152 = (let _180_151 = (let _180_150 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_149 = (let _180_148 = (let _180_147 = (pretty_print_exp v)
in (_180_147)::[])
in (ws)::_180_148)
in (FStar_Format.reduce _180_149))
end)
in (_180_150)::(semi)::[])
in ((FStar_Format.text "return"))::_180_151)
in (ws)::_180_152)
in (FStar_Format.reduce _180_153))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_157 = (let _180_156 = (let _180_155 = (let _180_154 = (pretty_print_exp e)
in (_180_154)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_155)
in (ws)::_180_156)
in (FStar_Format.reduce _180_157))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_161 = (let _180_160 = (let _180_159 = (let _180_158 = (pretty_print_statements b)
in (_180_158)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_159)
in ((FStar_Format.text "try"))::_180_160)
in (FStar_Format.reduce _180_161))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_169 = (let _180_168 = (let _180_167 = (let _180_166 = (let _180_162 = (pretty_print_exp e)
in (FStar_Format.parens _180_162))
in (let _180_165 = (let _180_164 = (let _180_163 = (optws s)
in (_180_163)::[])
in (FStar_Format.hardline)::_180_164)
in (_180_166)::_180_165))
in ((FStar_Format.text "while"))::_180_167)
in (ws)::_180_168)
in (FStar_Format.reduce _180_169))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_181 = (let _180_180 = (let _180_179 = (let _180_178 = (let _180_177 = (optws s)
in (let _180_176 = (let _180_175 = (pretty_print_statement s)
in (let _180_174 = (let _180_173 = (let _180_172 = (let _180_171 = (let _180_170 = (pretty_print_exp e)
in (FStar_Format.parens _180_170))
in (_180_171)::(semi)::[])
in ((FStar_Format.text "while"))::_180_172)
in (ws)::_180_173)
in (_180_175)::_180_174))
in (_180_177)::_180_176))
in (FStar_Format.hardline)::_180_178)
in ((FStar_Format.text "do"))::_180_179)
in (ws)::_180_180)
in (FStar_Format.reduce _180_181))
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
(let _180_198 = (let _180_197 = (let _180_196 = (print_kind_var k)
in (let _180_195 = (let _180_194 = (let _180_193 = (let _180_192 = (FStar_List.map (fun _83_192 -> (match (_83_192) with
| (p, e) -> begin
(let _180_191 = (let _180_190 = (print_pattern p)
in (let _180_189 = (let _180_188 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_187 = (let _180_186 = (let _180_185 = (let _180_184 = (let _180_183 = (pretty_print_exp v)
in (_180_183)::[])
in (ws)::_180_184)
in ((FStar_Format.text "="))::_180_185)
in (ws)::_180_186)
in (FStar_Format.reduce _180_187))
end)
in (_180_188)::[])
in (_180_190)::_180_189))
in (FStar_Format.reduce _180_191))
end)) l)
in (FStar_All.pipe_right _180_192 (FStar_Format.combine comma)))
in (_180_193)::(semi)::[])
in (ws)::_180_194)
in (_180_196)::_180_195))
in (ws)::_180_197)
in (FStar_Format.reduce _180_198))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_197) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_200) -> begin
semi
end))
in (let _180_200 = (let _180_199 = (f p)
in (_180_199)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_200)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_202 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_202)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_209 = (let _180_208 = (let _180_207 = (let _180_206 = (FStar_List.map (fun s -> (let _180_205 = (remove_chars_t s)
in (FStar_Format.text _180_205))) l)
in (FStar_All.pipe_right _180_206 (FStar_Format.combine comma)))
in (_180_207)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_208)
in (FStar_Format.reduce _180_209))
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
(let _180_214 = (let _180_213 = (let _180_212 = (let _180_211 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_211 (FStar_Format.combine comma)))
in (_180_212)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_213)
in (FStar_Format.reduce _180_214))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_218 = (let _180_217 = (let _180_216 = (let _180_215 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_215 (FStar_Format.combine comma)))
in (_180_216)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_217)
in (FStar_Format.reduce _180_218))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_221, args, body, ret_t, decl_vars) -> begin
(let _180_219 = (print_body body)
in (print_arrow_fun args _180_219))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_222 = (let _180_221 = (let _180_220 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_220 (FStar_Format.combine semi)))
in (_180_221)::[])
in (FStar_Format.reduce _180_222))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_226 = (let _180_225 = (print_op_un o)
in (let _180_224 = (let _180_223 = (pretty_print_exp e)
in (_180_223)::[])
in (_180_225)::_180_224))
in (FStar_Format.reduce _180_226))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_232 = (let _180_231 = (let _180_230 = (pretty_print_exp e1)
in (let _180_229 = (let _180_228 = (let _180_227 = (pretty_print_exp e2)
in (_180_227)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_228)
in (_180_230)::_180_229))
in ((FStar_Format.text "("))::_180_231)
in (FStar_Format.reduce _180_232))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(let _180_237 = (let _180_236 = (print_pattern p)
in (let _180_235 = (let _180_234 = (let _180_233 = (pretty_print_exp e)
in (_180_233)::[])
in ((FStar_Format.text "="))::_180_234)
in (_180_236)::_180_235))
in (FStar_Format.reduce _180_237))
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_242 = (let _180_241 = (pretty_print_exp e1)
in (let _180_240 = (let _180_239 = (let _180_238 = (pretty_print_exp e2)
in (_180_238)::[])
in ((print_op_log o))::_180_239)
in (_180_241)::_180_240))
in (FStar_Format.reduce _180_242))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_249 = (let _180_248 = (pretty_print_exp e)
in (let _180_247 = (let _180_246 = (let _180_245 = (FStar_List.map (fun x -> (let _180_244 = (pretty_print_exp x)
in (FStar_Format.parens _180_244))) l)
in (FStar_All.pipe_right _180_245 (FStar_Format.combine FStar_Format.empty)))
in (_180_246)::[])
in (_180_248)::_180_247))
in (FStar_Format.reduce _180_249))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_253 = (let _180_252 = (pretty_print_exp o)
in (let _180_251 = (let _180_250 = (pretty_print_propmem p)
in (_180_250)::[])
in (_180_252)::_180_251))
in (FStar_Format.reduce _180_253))
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
(let _180_254 = (jstr_escape id)
in (FStar_Format.text _180_254))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
semi
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Format.doc = (fun args body -> (match (args) with
| [] -> begin
(FStar_Format.reduce (((FStar_Format.text "()"))::((FStar_Format.text "=>"))::(body)::[]))
end
| (x)::[] -> begin
(let _180_259 = (let _180_258 = (let _180_257 = (print_pattern x)
in (FStar_Format.parens _180_257))
in (_180_258)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_259))
end
| (hd)::tl -> begin
(let _180_266 = (let _180_265 = (let _180_260 = (print_pattern hd)
in (FStar_Format.parens _180_260))
in (let _180_264 = (let _180_263 = (let _180_262 = (let _180_261 = (print_arrow_fun tl body)
in (FStar_Format.parens _180_261))
in (_180_262)::[])
in ((FStar_Format.text "=>"))::_180_263)
in (_180_265)::_180_264))
in (FStar_Format.reduce _180_266))
end))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_309) -> begin
(let _180_272 = (let _180_271 = (pretty_print_prop_key k)
in (let _180_270 = (let _180_269 = (let _180_268 = (pretty_print_exp e)
in (_180_268)::[])
in ((FStar_Format.text ":"))::_180_269)
in (_180_271)::_180_270))
in (FStar_Format.reduce _180_272))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_274 = (jstr_escape id)
in (FStar_Format.text _180_274))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_279 = (let _180_278 = (let _180_277 = (let _180_276 = (jstr_escape i)
in (FStar_Format.text _180_276))
in (_180_277)::[])
in ((FStar_Format.text "."))::_180_278)
in (FStar_Format.reduce _180_279))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_282 = (let _180_281 = (let _180_280 = (pretty_print_exp e)
in (_180_280)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_281)
in (FStar_Format.reduce _180_282))
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_340) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(let _180_287 = (let _180_286 = (print_decl_t decl_vars)
in (let _180_285 = (let _180_284 = (print_fun_typ args ret_t)
in (_180_284)::[])
in (_180_286)::_180_285))
in (FStar_Format.reduce _180_287))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_349, _83_351) -> begin
(let _180_297 = (let _180_296 = (let _180_295 = (let _180_294 = (FStar_List.map (fun _83_356 -> (match (_83_356) with
| (k, t) -> begin
(let _180_293 = (let _180_292 = (pretty_print_prop_key k)
in (let _180_291 = (let _180_290 = (let _180_289 = (print_typ t)
in (_180_289)::[])
in ((FStar_Format.text ":"))::_180_290)
in (_180_292)::_180_291))
in (FStar_Format.reduce _180_293))
end)) lp)
in (FStar_All.pipe_right _180_294 (FStar_Format.combine comma)))
in (_180_295)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_296)
in (FStar_Format.reduce _180_297))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_301 = (let _180_300 = (let _180_299 = (let _180_298 = (print_typ t)
in (_180_298)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_299)
in ((FStar_Format.text "Array"))::_180_300)
in (FStar_Format.reduce _180_301))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_304 = (let _180_303 = (let _180_302 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_302 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_303)::[])
in (FStar_Format.reduce _180_304))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_307 = (let _180_306 = (let _180_305 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_305 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_306)::[])
in (FStar_Format.reduce _180_307))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_310 = (let _180_309 = (let _180_308 = (print_typ t)
in (_180_308)::[])
in ((FStar_Format.text "typeof"))::_180_309)
in (FStar_Format.reduce _180_310))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_314 = (let _180_313 = (let _180_312 = (let _180_311 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_311 (FStar_Format.combine comma)))
in (_180_312)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_313)
in (FStar_Format.reduce _180_314))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_369) -> begin
(let _180_317 = (let _180_316 = (let _180_315 = (jstr_escape s)
in (Prims.strcat _180_315 "\""))
in (Prims.strcat "\"" _180_316))
in (FStar_Format.text _180_317))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_374) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_379) -> begin
(let _180_318 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_318))
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
(let _180_322 = (let _180_321 = (let _180_320 = (let _180_319 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_319 (FStar_Format.combine comma)))
in (_180_320)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_321)
in (FStar_Format.reduce _180_322))
end)
in (let _180_324 = (let _180_323 = (print_gen_t n)
in (_180_323)::(print_lt)::[])
in (FStar_Format.reduce _180_324)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun args ret_t -> (

let print_arg = (fun _83_399 -> (match (_83_399) with
| ((id, _83_396), t) -> begin
(let _180_334 = (let _180_333 = (let _180_329 = (jstr_escape id)
in (FStar_Format.text _180_329))
in (let _180_332 = (let _180_331 = (let _180_330 = (print_typ t)
in (_180_330)::[])
in (colon)::_180_331)
in (_180_333)::_180_332))
in (FStar_Format.reduce _180_334))
end))
in (match (args) with
| [] -> begin
(let _180_338 = (let _180_337 = (let _180_336 = (let _180_335 = (print_typ ret_t)
in (_180_335)::[])
in ((FStar_Format.text "=>"))::_180_336)
in ((FStar_Format.text "()"))::_180_337)
in (FStar_Format.reduce _180_338))
end
| (x)::[] -> begin
(let _180_345 = (let _180_344 = (let _180_339 = (print_arg x)
in (FStar_Format.parens _180_339))
in (let _180_343 = (let _180_342 = (let _180_341 = (let _180_340 = (print_typ ret_t)
in (FStar_Format.parens _180_340))
in (_180_341)::[])
in ((FStar_Format.text "=>"))::_180_342)
in (_180_344)::_180_343))
in (FStar_Format.reduce _180_345))
end
| (hd)::tl -> begin
(let _180_352 = (let _180_351 = (let _180_346 = (print_arg hd)
in (FStar_Format.parens _180_346))
in (let _180_350 = (let _180_349 = (let _180_348 = (let _180_347 = (print_fun_typ tl ret_t)
in (FStar_Format.parens _180_347))
in (_180_348)::[])
in ((FStar_Format.text "=>"))::_180_349)
in (_180_351)::_180_350))
in (FStar_Format.reduce _180_352))
end)))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_409) -> begin
(let _180_354 = (remove_chars_t id)
in (FStar_Format.text _180_354))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_415)) -> begin
(let _180_360 = (let _180_359 = (print_gen_t g)
in (let _180_358 = (let _180_357 = (let _180_356 = (let _180_355 = (remove_chars_t id)
in (FStar_Format.text _180_355))
in (_180_356)::[])
in (comma)::_180_357)
in (_180_359)::_180_358))
in (FStar_Format.reduce _180_360))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_364 = (let _180_363 = (let _180_362 = (jstr_escape s)
in (Prims.strcat _180_362 "\""))
in (Prims.strcat "\"" _180_363))
in (FStar_Format.text _180_364))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_365 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_365))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_428) -> begin
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
and print_pattern : FStar_Extraction_JavaScript_Ast.pattern_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_436) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_439) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_442) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_445) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_370 = (let _180_369 = (let _180_368 = (print_typ v)
in (_180_368)::[])
in (colon)::_180_369)
in (FStar_Format.reduce _180_370))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_373 = (let _180_372 = (let _180_371 = (jstr_escape id)
in (FStar_Format.text _180_371))
in (_180_372)::(r)::[])
in (FStar_Format.reduce _180_373)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_377 = (let _180_376 = (let _180_375 = (pretty_print_statements l)
in (_180_375)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_376)
in (FStar_Format.reduce _180_377))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_465 -> (match (_83_465) with
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
(let _180_382 = (let _180_381 = (let _180_380 = (let _180_379 = (print_typ v)
in (_180_379)::[])
in (ws)::_180_380)
in ((FStar_Format.text ":"))::_180_381)
in (FStar_Format.reduce _180_382))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_396 = (let _180_395 = (let _180_394 = (let _180_393 = (let _180_392 = (print_decl_t typePars)
in (let _180_391 = (let _180_390 = (let _180_384 = (let _180_383 = (FStar_List.map print_pattern pars)
in (FStar_All.pipe_right _180_383 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_384))
in (let _180_389 = (let _180_388 = (let _180_387 = (let _180_386 = (let _180_385 = (print_body body)
in (_180_385)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_386)
in ((FStar_Format.text "{"))::_180_387)
in (returnT)::_180_388)
in (_180_390)::_180_389))
in (_180_392)::_180_391))
in (name)::_180_393)
in (ws)::_180_394)
in ((FStar_Format.text "function"))::_180_395)
in (FStar_Format.reduce _180_396))))
end))





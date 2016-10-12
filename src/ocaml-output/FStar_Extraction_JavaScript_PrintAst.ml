
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_49 = (let _180_48 = (let _180_47 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(pretty_print_statement s)
end)) program)
in (FStar_List.append (((FStar_Format.text "import * as Prims from \"./Prims.js\""))::(semi)::(FStar_Format.hardline)::[]) _180_47))
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_48))
in (FStar_Format.reduce _180_49)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (_83_81) -> begin
(pretty_print_statement s)
end
| _83_84 -> begin
(let _180_56 = (let _180_55 = (let _180_54 = (let _180_53 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_53))
in (_180_54)::[])
in (ws)::_180_55)
in (FStar_Format.reduce _180_56))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_61 = (let _180_60 = (let _180_59 = (pretty_print_exp e)
in (_180_59)::(semi)::[])
in (ws)::_180_60)
in (FStar_Format.reduce _180_61))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_78 = (let _180_77 = (let _180_76 = (let _180_75 = (let _180_62 = (pretty_print_exp c)
in (FStar_Format.parens _180_62))
in (let _180_74 = (let _180_73 = (let _180_72 = (let _180_71 = (optws t)
in (let _180_70 = (let _180_69 = (let _180_68 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_67 = (let _180_66 = (let _180_65 = (let _180_64 = (let _180_63 = (optws s)
in (_180_63)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_64)
in ((FStar_Format.text "else"))::_180_65)
in (ws)::_180_66)
in (FStar_Format.reduce _180_67))
end)
in (_180_68)::[])
in ((FStar_Format.text "}"))::_180_69)
in (_180_71)::_180_70))
in (FStar_Format.hardline)::_180_72)
in ((FStar_Format.text "{"))::_180_73)
in (_180_75)::_180_74))
in ((FStar_Format.text "if"))::_180_76)
in (ws)::_180_77)
in (FStar_Format.reduce _180_78))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_86 = (let _180_85 = (let _180_84 = (let _180_79 = (jstr_escape l)
in (FStar_Format.text _180_79))
in (let _180_83 = (let _180_82 = (let _180_81 = (let _180_80 = (optws s)
in (_180_80)::[])
in (FStar_Format.hardline)::_180_81)
in (colon)::_180_82)
in (_180_84)::_180_83))
in (ws)::_180_85)
in (FStar_Format.reduce _180_86))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(let _180_94 = (let _180_93 = (let _180_92 = (let _180_91 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_90 = (let _180_89 = (let _180_88 = (let _180_87 = (jstr_escape v)
in (FStar_Format.text _180_87))
in (_180_88)::[])
in (ws)::_180_89)
in (FStar_Format.reduce _180_90))
end)
in (_180_91)::(semi)::[])
in ((FStar_Format.text "break"))::_180_92)
in (ws)::_180_93)
in (FStar_Format.reduce _180_94))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_102 = (let _180_101 = (let _180_100 = (let _180_99 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_98 = (let _180_97 = (let _180_96 = (let _180_95 = (jstr_escape v)
in (FStar_Format.text _180_95))
in (_180_96)::[])
in (ws)::_180_97)
in (FStar_Format.reduce _180_98))
end)
in (_180_99)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_100)
in (ws)::_180_101)
in (FStar_Format.reduce _180_102))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_110 = (let _180_109 = (let _180_108 = (let _180_107 = (let _180_103 = (pretty_print_exp e)
in (FStar_Format.parens _180_103))
in (let _180_106 = (let _180_105 = (let _180_104 = (optws s)
in (_180_104)::[])
in (FStar_Format.hardline)::_180_105)
in (_180_107)::_180_106))
in ((FStar_Format.text "with"))::_180_108)
in (ws)::_180_109)
in (FStar_Format.reduce _180_110))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_125), lt, t) -> begin
(let _180_119 = (let _180_118 = (let _180_117 = (let _180_111 = (jstr_escape id)
in (FStar_Format.text _180_111))
in (let _180_116 = (let _180_115 = (print_decl_t lt)
in (let _180_114 = (let _180_113 = (let _180_112 = (print_typ t)
in (_180_112)::(semi)::[])
in ((FStar_Format.text "="))::_180_113)
in (_180_115)::_180_114))
in (_180_117)::_180_116))
in ((FStar_Format.text "type "))::_180_118)
in (FStar_Format.reduce _180_119))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (let _180_120 = (pretty_print_exp e)
in (FStar_Format.parens _180_120))
in (let _180_137 = (let _180_136 = (let _180_135 = (let _180_134 = (let _180_133 = (let _180_132 = (let _180_131 = (FStar_List.map (fun _83_137 -> (match (_83_137) with
| (e, l) -> begin
(let _180_130 = (let _180_129 = (let _180_128 = (let _180_127 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_126 = (let _180_125 = (let _180_124 = (let _180_123 = (let _180_122 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_122))
in (_180_123)::[])
in (FStar_Format.hardline)::_180_124)
in (colon)::_180_125)
in (_180_127)::_180_126))
in ((FStar_Format.text "case "))::_180_128)
in (ws)::_180_129)
in (FStar_Format.reduce _180_130))
end)) lcase)
in (FStar_All.pipe_right _180_131 (FStar_Format.combine FStar_Format.hardline)))
in (_180_132)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_133)
in ((FStar_Format.text "{"))::_180_134)
in (ws)::_180_135)
in (FStar_Format.hardline)::_180_136)
in (_180_138)::_180_137))
in ((FStar_Format.text "switch"))::_180_139)
in (ws)::_180_140)
in (FStar_Format.reduce _180_141))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_148 = (let _180_147 = (let _180_146 = (let _180_145 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_144 = (let _180_143 = (let _180_142 = (pretty_print_exp v)
in (_180_142)::[])
in (ws)::_180_143)
in (FStar_Format.reduce _180_144))
end)
in (_180_145)::(semi)::[])
in ((FStar_Format.text "return"))::_180_146)
in (ws)::_180_147)
in (FStar_Format.reduce _180_148))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_152 = (let _180_151 = (let _180_150 = (let _180_149 = (pretty_print_exp e)
in (_180_149)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_150)
in (ws)::_180_151)
in (FStar_Format.reduce _180_152))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_156 = (let _180_155 = (let _180_154 = (let _180_153 = (pretty_print_statements b)
in (_180_153)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_154)
in ((FStar_Format.text "try"))::_180_155)
in (FStar_Format.reduce _180_156))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_164 = (let _180_163 = (let _180_162 = (let _180_161 = (let _180_157 = (pretty_print_exp e)
in (FStar_Format.parens _180_157))
in (let _180_160 = (let _180_159 = (let _180_158 = (optws s)
in (_180_158)::[])
in (FStar_Format.hardline)::_180_159)
in (_180_161)::_180_160))
in ((FStar_Format.text "while"))::_180_162)
in (ws)::_180_163)
in (FStar_Format.reduce _180_164))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_176 = (let _180_175 = (let _180_174 = (let _180_173 = (let _180_172 = (optws s)
in (let _180_171 = (let _180_170 = (pretty_print_statement s)
in (let _180_169 = (let _180_168 = (let _180_167 = (let _180_166 = (let _180_165 = (pretty_print_exp e)
in (FStar_Format.parens _180_165))
in (_180_166)::(semi)::[])
in ((FStar_Format.text "while"))::_180_167)
in (ws)::_180_168)
in (_180_170)::_180_169))
in (_180_172)::_180_171))
in (FStar_Format.hardline)::_180_173)
in ((FStar_Format.text "do"))::_180_174)
in (ws)::_180_175)
in (FStar_Format.reduce _180_176))
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
(let _180_193 = (let _180_192 = (let _180_191 = (print_kind_var k)
in (let _180_190 = (let _180_189 = (let _180_188 = (let _180_187 = (FStar_List.map (fun _83_189 -> (match (_83_189) with
| (p, e) -> begin
(let _180_186 = (let _180_185 = (print_pattern p)
in (let _180_184 = (let _180_183 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_182 = (let _180_181 = (let _180_180 = (let _180_179 = (let _180_178 = (pretty_print_exp v)
in (_180_178)::[])
in (ws)::_180_179)
in ((FStar_Format.text "="))::_180_180)
in (ws)::_180_181)
in (FStar_Format.reduce _180_182))
end)
in (_180_183)::[])
in (_180_185)::_180_184))
in (FStar_Format.reduce _180_186))
end)) l)
in (FStar_All.pipe_right _180_187 (FStar_Format.combine comma)))
in (_180_188)::(semi)::[])
in (ws)::_180_189)
in (_180_191)::_180_190))
in (ws)::_180_192)
in (FStar_Format.reduce _180_193))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_194) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_197) -> begin
semi
end))
in (let _180_195 = (let _180_194 = (f p)
in (_180_194)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_195)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_197 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_197)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_204 = (let _180_203 = (let _180_202 = (let _180_201 = (FStar_List.map (fun s -> (let _180_200 = (remove_chars_t s)
in (FStar_Format.text _180_200))) l)
in (FStar_All.pipe_right _180_201 (FStar_Format.combine comma)))
in (_180_202)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_203)
in (FStar_Format.reduce _180_204))
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
(let _180_209 = (let _180_208 = (let _180_207 = (let _180_206 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_206 (FStar_Format.combine comma)))
in (_180_207)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_208)
in (FStar_Format.reduce _180_209))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_213 = (let _180_212 = (let _180_211 = (let _180_210 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_210 (FStar_Format.combine comma)))
in (_180_211)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_212)
in (FStar_Format.reduce _180_213))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_216 = (let _180_215 = (let _180_214 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_214 (FStar_Format.combine semi)))
in (_180_215)::[])
in (FStar_Format.reduce _180_216))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_220 = (let _180_219 = (print_op_un o)
in (let _180_218 = (let _180_217 = (pretty_print_exp e)
in (_180_217)::[])
in (_180_219)::_180_218))
in (FStar_Format.reduce _180_220))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_225 = (let _180_224 = (pretty_print_exp e1)
in (let _180_223 = (let _180_222 = (let _180_221 = (pretty_print_exp e2)
in (_180_221)::[])
in ((print_op_bin o))::_180_222)
in (_180_224)::_180_223))
in (FStar_Format.reduce _180_225))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(let _180_230 = (let _180_229 = (print_pattern p)
in (let _180_228 = (let _180_227 = (let _180_226 = (pretty_print_exp e)
in (_180_226)::[])
in ((FStar_Format.text "="))::_180_227)
in (_180_229)::_180_228))
in (FStar_Format.reduce _180_230))
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_235 = (let _180_234 = (pretty_print_exp e1)
in (let _180_233 = (let _180_232 = (let _180_231 = (pretty_print_exp e2)
in (_180_231)::[])
in ((print_op_log o))::_180_232)
in (_180_234)::_180_233))
in (FStar_Format.reduce _180_235))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_241 = (let _180_240 = (pretty_print_exp e)
in (let _180_239 = (let _180_238 = (let _180_237 = (let _180_236 = (FStar_List.map pretty_print_exp l)
in (FStar_All.pipe_right _180_236 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_237))
in (_180_238)::[])
in (_180_240)::_180_239))
in (FStar_Format.reduce _180_241))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_245 = (let _180_244 = (pretty_print_exp o)
in (let _180_243 = (let _180_242 = (pretty_print_propmem p)
in (_180_242)::[])
in (_180_244)::_180_243))
in (FStar_Format.reduce _180_245))
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
(let _180_246 = (jstr_escape id)
in (FStar_Format.text _180_246))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
semi
end))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_291) -> begin
(let _180_252 = (let _180_251 = (pretty_print_prop_key k)
in (let _180_250 = (let _180_249 = (let _180_248 = (pretty_print_exp e)
in (_180_248)::[])
in ((FStar_Format.text ":"))::_180_249)
in (_180_251)::_180_250))
in (FStar_Format.reduce _180_252))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_254 = (jstr_escape id)
in (FStar_Format.text _180_254))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_259 = (let _180_258 = (let _180_257 = (let _180_256 = (jstr_escape i)
in (FStar_Format.text _180_256))
in (_180_257)::[])
in ((FStar_Format.text "."))::_180_258)
in (FStar_Format.reduce _180_259))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_262 = (let _180_261 = (let _180_260 = (pretty_print_exp e)
in (_180_260)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_261)
in (FStar_Format.reduce _180_262))
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_322) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(let _180_271 = (let _180_270 = (print_decl_t decl_vars)
in (let _180_269 = (let _180_268 = (let _180_264 = (print_args args)
in (FStar_Format.parens _180_264))
in (let _180_267 = (let _180_266 = (let _180_265 = (print_typ ret_t)
in (_180_265)::[])
in ((FStar_Format.text "=>"))::_180_266)
in (_180_268)::_180_267))
in (_180_270)::_180_269))
in (FStar_Format.reduce _180_271))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_331, _83_333) -> begin
(let _180_281 = (let _180_280 = (let _180_279 = (let _180_278 = (FStar_List.map (fun _83_338 -> (match (_83_338) with
| (k, t) -> begin
(let _180_277 = (let _180_276 = (pretty_print_prop_key k)
in (let _180_275 = (let _180_274 = (let _180_273 = (print_typ t)
in (_180_273)::[])
in ((FStar_Format.text ":"))::_180_274)
in (_180_276)::_180_275))
in (FStar_Format.reduce _180_277))
end)) lp)
in (FStar_All.pipe_right _180_278 (FStar_Format.combine comma)))
in (_180_279)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_280)
in (FStar_Format.reduce _180_281))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_285 = (let _180_284 = (let _180_283 = (let _180_282 = (print_typ t)
in (_180_282)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_283)
in ((FStar_Format.text "Array"))::_180_284)
in (FStar_Format.reduce _180_285))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_288 = (let _180_287 = (let _180_286 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_286 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_287)::[])
in (FStar_Format.reduce _180_288))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_291 = (let _180_290 = (let _180_289 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_289 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_290)::[])
in (FStar_Format.reduce _180_291))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_294 = (let _180_293 = (let _180_292 = (print_typ t)
in (_180_292)::[])
in ((FStar_Format.text "typeof"))::_180_293)
in (FStar_Format.reduce _180_294))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_298 = (let _180_297 = (let _180_296 = (let _180_295 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_295 (FStar_Format.combine comma)))
in (_180_296)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_297)
in (FStar_Format.reduce _180_298))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_351) -> begin
(let _180_301 = (let _180_300 = (let _180_299 = (jstr_escape s)
in (Prims.strcat _180_299 "\""))
in (Prims.strcat "\"" _180_300))
in (FStar_Format.text _180_301))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_356) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_361) -> begin
(let _180_302 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_302))
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
(let _180_306 = (let _180_305 = (let _180_304 = (let _180_303 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_303 (FStar_Format.combine comma)))
in (_180_304)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_305)
in (FStar_Format.reduce _180_306))
end)
in (let _180_308 = (let _180_307 = (print_gen_t n)
in (_180_307)::(print_lt)::[])
in (FStar_Format.reduce _180_308)))
end))
and print_args : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Format.doc = (fun args -> (let _180_319 = (let _180_318 = (let _180_317 = (FStar_List.map (fun _83_379 -> (match (_83_379) with
| ((id, _83_376), t) -> begin
(let _180_316 = (let _180_315 = (let _180_311 = (jstr_escape id)
in (FStar_Format.text _180_311))
in (let _180_314 = (let _180_313 = (let _180_312 = (print_typ t)
in (_180_312)::[])
in (colon)::_180_313)
in (_180_315)::_180_314))
in (FStar_Format.reduce _180_316))
end)) args)
in (FStar_All.pipe_right _180_317 (FStar_Format.combine comma)))
in (_180_318)::[])
in (FStar_Format.reduce _180_319)))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_383) -> begin
(let _180_321 = (remove_chars_t id)
in (FStar_Format.text _180_321))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_389)) -> begin
(let _180_327 = (let _180_326 = (print_gen_t g)
in (let _180_325 = (let _180_324 = (let _180_323 = (let _180_322 = (remove_chars_t id)
in (FStar_Format.text _180_322))
in (_180_323)::[])
in (comma)::_180_324)
in (_180_326)::_180_325))
in (FStar_Format.reduce _180_327))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_331 = (let _180_330 = (let _180_329 = (jstr_escape s)
in (Prims.strcat _180_329 "\""))
in (Prims.strcat "\"" _180_330))
in (FStar_Format.text _180_331))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_332 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_332))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_402) -> begin
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_410) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_413) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_416) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_419) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_337 = (let _180_336 = (let _180_335 = (print_typ v)
in (_180_335)::[])
in (colon)::_180_336)
in (FStar_Format.reduce _180_337))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_340 = (let _180_339 = (let _180_338 = (jstr_escape id)
in (FStar_Format.text _180_338))
in (_180_339)::(r)::[])
in (FStar_Format.reduce _180_340)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_439 -> (match (_83_439) with
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
(let _180_346 = (let _180_345 = (let _180_344 = (let _180_343 = (print_typ v)
in (_180_343)::[])
in (ws)::_180_344)
in ((FStar_Format.text ":"))::_180_345)
in (FStar_Format.reduce _180_346))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_360 = (let _180_359 = (let _180_358 = (let _180_357 = (let _180_356 = (print_decl_t typePars)
in (let _180_355 = (let _180_354 = (let _180_348 = (let _180_347 = (FStar_List.map print_pattern pars)
in (FStar_All.pipe_right _180_347 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_348))
in (let _180_353 = (let _180_352 = (let _180_351 = (let _180_350 = (let _180_349 = (print_body body)
in (_180_349)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_350)
in ((FStar_Format.text "{"))::_180_351)
in (returnT)::_180_352)
in (_180_354)::_180_353))
in (_180_356)::_180_355))
in (name)::_180_357)
in (ws)::_180_358)
in ((FStar_Format.text "function"))::_180_359)
in (FStar_Format.reduce _180_360))))
end))





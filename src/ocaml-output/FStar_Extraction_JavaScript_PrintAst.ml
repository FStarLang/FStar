
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_60 = (let _180_59 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
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
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_59))
in (FStar_Format.reduce _180_60)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_92 -> begin
(let _180_67 = (let _180_66 = (let _180_65 = (let _180_64 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_64))
in (_180_65)::[])
in (ws)::_180_66)
in (FStar_Format.reduce _180_67))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_72 = (let _180_71 = (let _180_70 = (pretty_print_statements l)
in (_180_70)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_71)
in (FStar_Format.reduce _180_72))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_75 = (let _180_74 = (let _180_73 = (pretty_print_exp e)
in (_180_73)::(semi)::[])
in (ws)::_180_74)
in (FStar_Format.reduce _180_75))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_92 = (let _180_91 = (let _180_90 = (let _180_89 = (let _180_76 = (pretty_print_exp c)
in (FStar_Format.parens _180_76))
in (let _180_88 = (let _180_87 = (let _180_86 = (let _180_85 = (optws t)
in (let _180_84 = (let _180_83 = (let _180_82 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_81 = (let _180_80 = (let _180_79 = (let _180_78 = (let _180_77 = (optws s)
in (_180_77)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_78)
in ((FStar_Format.text "else"))::_180_79)
in (ws)::_180_80)
in (FStar_Format.reduce _180_81))
end)
in (_180_82)::[])
in ((FStar_Format.text "}"))::_180_83)
in (_180_85)::_180_84))
in (FStar_Format.hardline)::_180_86)
in ((FStar_Format.text "{"))::_180_87)
in (_180_89)::_180_88))
in ((FStar_Format.text "if"))::_180_90)
in (ws)::_180_91)
in (FStar_Format.reduce _180_92))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_100 = (let _180_99 = (let _180_98 = (let _180_93 = (jstr_escape l)
in (FStar_Format.text _180_93))
in (let _180_97 = (let _180_96 = (let _180_95 = (let _180_94 = (optws s)
in (_180_94)::[])
in (FStar_Format.hardline)::_180_95)
in (colon)::_180_96)
in (_180_98)::_180_97))
in (ws)::_180_99)
in (FStar_Format.reduce _180_100))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(let _180_108 = (let _180_107 = (let _180_106 = (let _180_105 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_104 = (let _180_103 = (let _180_102 = (let _180_101 = (jstr_escape v)
in (FStar_Format.text _180_101))
in (_180_102)::[])
in (ws)::_180_103)
in (FStar_Format.reduce _180_104))
end)
in (_180_105)::(semi)::[])
in ((FStar_Format.text "break"))::_180_106)
in (ws)::_180_107)
in (FStar_Format.reduce _180_108))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_116 = (let _180_115 = (let _180_114 = (let _180_113 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_112 = (let _180_111 = (let _180_110 = (let _180_109 = (jstr_escape v)
in (FStar_Format.text _180_109))
in (_180_110)::[])
in (ws)::_180_111)
in (FStar_Format.reduce _180_112))
end)
in (_180_113)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_114)
in (ws)::_180_115)
in (FStar_Format.reduce _180_116))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_124 = (let _180_123 = (let _180_122 = (let _180_121 = (let _180_117 = (pretty_print_exp e)
in (FStar_Format.parens _180_117))
in (let _180_120 = (let _180_119 = (let _180_118 = (optws s)
in (_180_118)::[])
in (FStar_Format.hardline)::_180_119)
in (_180_121)::_180_120))
in ((FStar_Format.text "with"))::_180_122)
in (ws)::_180_123)
in (FStar_Format.reduce _180_124))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_133), lt, t) -> begin
(let _180_133 = (let _180_132 = (let _180_131 = (let _180_125 = (jstr_escape id)
in (FStar_Format.text _180_125))
in (let _180_130 = (let _180_129 = (print_decl_t lt)
in (let _180_128 = (let _180_127 = (let _180_126 = (print_typ t)
in (_180_126)::(semi)::[])
in ((FStar_Format.text "="))::_180_127)
in (_180_129)::_180_128))
in (_180_131)::_180_130))
in ((FStar_Format.text "type "))::_180_132)
in (FStar_Format.reduce _180_133))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_155 = (let _180_154 = (let _180_153 = (let _180_152 = (let _180_134 = (pretty_print_exp e)
in (FStar_Format.parens _180_134))
in (let _180_151 = (let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (let _180_146 = (let _180_145 = (FStar_List.map (fun _83_145 -> (match (_83_145) with
| (e, l) -> begin
(let _180_144 = (let _180_143 = (let _180_142 = (let _180_141 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_140 = (let _180_139 = (let _180_138 = (let _180_137 = (let _180_136 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_136))
in (_180_137)::[])
in (FStar_Format.hardline)::_180_138)
in (colon)::_180_139)
in (_180_141)::_180_140))
in ((FStar_Format.text "case "))::_180_142)
in (ws)::_180_143)
in (FStar_Format.reduce _180_144))
end)) lcase)
in (FStar_All.pipe_right _180_145 (FStar_Format.combine FStar_Format.hardline)))
in (_180_146)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_147)
in ((FStar_Format.text "{"))::_180_148)
in (ws)::_180_149)
in (FStar_Format.hardline)::_180_150)
in (_180_152)::_180_151))
in ((FStar_Format.text "switch"))::_180_153)
in (ws)::_180_154)
in (FStar_Format.reduce _180_155))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_162 = (let _180_161 = (let _180_160 = (let _180_159 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_158 = (let _180_157 = (let _180_156 = (pretty_print_exp v)
in (_180_156)::[])
in (ws)::_180_157)
in (FStar_Format.reduce _180_158))
end)
in (_180_159)::(semi)::[])
in ((FStar_Format.text "return"))::_180_160)
in (ws)::_180_161)
in (FStar_Format.reduce _180_162))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_166 = (let _180_165 = (let _180_164 = (let _180_163 = (pretty_print_exp e)
in (_180_163)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_164)
in (ws)::_180_165)
in (FStar_Format.reduce _180_166))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_170 = (let _180_169 = (let _180_168 = (let _180_167 = (pretty_print_statements b)
in (_180_167)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_168)
in ((FStar_Format.text "try"))::_180_169)
in (FStar_Format.reduce _180_170))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_178 = (let _180_177 = (let _180_176 = (let _180_175 = (let _180_171 = (pretty_print_exp e)
in (FStar_Format.parens _180_171))
in (let _180_174 = (let _180_173 = (let _180_172 = (optws s)
in (_180_172)::[])
in (FStar_Format.hardline)::_180_173)
in (_180_175)::_180_174))
in ((FStar_Format.text "while"))::_180_176)
in (ws)::_180_177)
in (FStar_Format.reduce _180_178))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_190 = (let _180_189 = (let _180_188 = (let _180_187 = (let _180_186 = (optws s)
in (let _180_185 = (let _180_184 = (pretty_print_statement s)
in (let _180_183 = (let _180_182 = (let _180_181 = (let _180_180 = (let _180_179 = (pretty_print_exp e)
in (FStar_Format.parens _180_179))
in (_180_180)::(semi)::[])
in ((FStar_Format.text "while"))::_180_181)
in (ws)::_180_182)
in (_180_184)::_180_183))
in (_180_186)::_180_185))
in (FStar_Format.hardline)::_180_187)
in ((FStar_Format.text "do"))::_180_188)
in (ws)::_180_189)
in (FStar_Format.reduce _180_190))
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
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_199) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
FStar_Format.empty
end)
end
| _83_206 -> begin
(let _180_199 = (let _180_198 = (print_kind_var k)
in (let _180_197 = (let _180_196 = (print_pattern p true)
in (let _180_195 = (let _180_194 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_193 = (let _180_192 = (let _180_191 = (pretty_print_exp v)
in (_180_191)::[])
in ((FStar_Format.text "="))::_180_192)
in (FStar_Format.reduce _180_193))
end)
in (_180_194)::(semi)::[])
in (_180_196)::_180_195))
in (_180_198)::_180_197))
in (FStar_Format.reduce _180_199))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_211) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_214) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(let _180_203 = (let _180_202 = (print_exp_kind k)
in (let _180_201 = (let _180_200 = (print_declaration d)
in (_180_200)::[])
in (_180_202)::_180_201))
in (FStar_Format.reduce _180_203))
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _180_212 = (let _180_211 = (let _180_210 = (let _180_204 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_204))
in (let _180_209 = (let _180_208 = (let _180_207 = (let _180_206 = (let _180_205 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_205))
in (_180_206)::((FStar_Format.text "\""))::((FStar_Format.text ";"))::[])
in ((FStar_Format.text "\"./"))::_180_207)
in ((FStar_Format.text " from "))::_180_208)
in (_180_210)::_180_209))
in ((FStar_Format.text "import * as "))::_180_211)
in (FStar_Format.reduce _180_212))
end))
in (let _180_214 = (let _180_213 = (f p)
in (_180_213)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_214)))))
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
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_218 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_218)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_225 = (let _180_224 = (let _180_223 = (let _180_222 = (FStar_List.map (fun s -> (let _180_221 = (remove_chars_t s)
in (FStar_Format.text _180_221))) l)
in (FStar_All.pipe_right _180_222 (FStar_Format.combine comma)))
in (_180_223)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_224)
in (FStar_Format.reduce _180_225))
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
(let _180_230 = (let _180_229 = (let _180_228 = (let _180_227 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_227 (FStar_Format.combine comma)))
in (_180_228)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_229)
in (FStar_Format.reduce _180_230))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_234 = (let _180_233 = (let _180_232 = (let _180_231 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_231 (FStar_Format.combine comma)))
in (_180_232)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_233)
in (FStar_Format.reduce _180_234))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_249, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_257 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_238 = (let _180_237 = (let _180_236 = (let _180_235 = (print_body body)
in (print_arrow_fun args _180_235 ret_t))
in (_180_236)::[])
in (decl_t)::_180_237)
in (FStar_Format.reduce _180_238))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_241 = (let _180_240 = (let _180_239 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_239 (FStar_Format.combine semi)))
in (_180_240)::[])
in (FStar_Format.reduce _180_241))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_244 = (let _180_243 = (let _180_242 = (pretty_print_exp e)
in (_180_242)::[])
in ((print_op_un o))::_180_243)
in (FStar_Format.reduce _180_244))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_250 = (let _180_249 = (let _180_248 = (pretty_print_exp e1)
in (let _180_247 = (let _180_246 = (let _180_245 = (pretty_print_exp e2)
in (_180_245)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_246)
in (_180_248)::_180_247))
in ((FStar_Format.text "("))::_180_249)
in (FStar_Format.reduce _180_250))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_276) when (n = "_") -> begin
(pretty_print_exp e)
end
| _83_280 -> begin
(let _180_255 = (let _180_254 = (print_pattern p false)
in (let _180_253 = (let _180_252 = (let _180_251 = (pretty_print_exp e)
in (_180_251)::[])
in ((FStar_Format.text "="))::_180_252)
in (_180_254)::_180_253))
in (FStar_Format.reduce _180_255))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_260 = (let _180_259 = (pretty_print_exp e1)
in (let _180_258 = (let _180_257 = (let _180_256 = (pretty_print_exp e2)
in (_180_256)::[])
in ((print_op_log o))::_180_257)
in (_180_259)::_180_258))
in (FStar_Format.reduce _180_260))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _180_263 = (FStar_List.map (fun x -> (let _180_262 = (pretty_print_exp x)
in (FStar_Format.parens _180_262))) l)
in (FStar_All.pipe_right _180_263 (FStar_Format.combine FStar_Format.empty)))
in (let _180_265 = (let _180_264 = (pretty_print_exp e)
in (_180_264)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_308 -> begin
le
end))::[])
in (FStar_Format.reduce _180_265)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_269 = (let _180_268 = (pretty_print_exp o)
in (let _180_267 = (let _180_266 = (pretty_print_propmem p)
in (_180_266)::[])
in (_180_268)::_180_267))
in (FStar_Format.reduce _180_269))
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
(let _180_270 = (remove_chars_t id)
in (FStar_Format.text _180_270))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_276 = (let _180_275 = (let _180_274 = (pretty_print_exp e)
in (let _180_273 = (let _180_272 = (let _180_271 = (print_typ t)
in (_180_271)::((FStar_Format.text ")"))::[])
in (colon)::_180_272)
in (_180_274)::_180_273))
in ((FStar_Format.text "("))::_180_275)
in (FStar_Format.reduce _180_276))
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option  ->  FStar_Format.doc = (fun args body ret_t -> (

let ret_t = (match (ret_t) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_283 = (let _180_282 = (let _180_281 = (let _180_280 = (print_typ v)
in (FStar_Format.parens _180_280))
in (_180_281)::[])
in (colon)::_180_282)
in (FStar_Format.reduce _180_283))
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
(let _180_290 = (let _180_289 = (let _180_288 = (print_pattern x true)
in (FStar_Format.parens _180_288))
in (_180_289)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_290))
end
| (hd)::tl -> begin
(let _180_298 = (let _180_297 = (let _180_291 = (print_pattern hd true)
in (FStar_Format.parens _180_291))
in (let _180_296 = (let _180_295 = (let _180_294 = (let _180_293 = (let _180_292 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_292))
in (_180_293)::[])
in ((FStar_Format.text "=>"))::_180_294)
in (ret_t)::_180_295)
in (_180_297)::_180_296))
in (FStar_Format.reduce _180_298))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_361) -> begin
(let _180_304 = (let _180_303 = (pretty_print_prop_key k)
in (let _180_302 = (let _180_301 = (let _180_300 = (pretty_print_exp e)
in (_180_300)::[])
in ((FStar_Format.text ":"))::_180_301)
in (_180_303)::_180_302))
in (FStar_Format.reduce _180_304))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_306 = (jstr_escape id)
in (FStar_Format.text _180_306))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_311 = (let _180_310 = (let _180_309 = (let _180_308 = (jstr_escape i)
in (FStar_Format.text _180_308))
in (_180_309)::[])
in ((FStar_Format.text "."))::_180_310)
in (FStar_Format.reduce _180_311))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_314 = (let _180_313 = (let _180_312 = (pretty_print_exp e)
in (_180_312)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_313)
in (FStar_Format.reduce _180_314))
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_392) -> begin
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

let _83_400 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_404, _83_406) -> begin
(let _180_325 = (let _180_324 = (let _180_323 = (let _180_322 = (FStar_List.map (fun _83_411 -> (match (_83_411) with
| (k, t) -> begin
(let _180_321 = (let _180_320 = (pretty_print_prop_key k)
in (let _180_319 = (let _180_318 = (let _180_317 = (print_typ t)
in (_180_317)::[])
in ((FStar_Format.text ":"))::_180_318)
in (_180_320)::_180_319))
in (FStar_Format.reduce _180_321))
end)) lp)
in (FStar_All.pipe_right _180_322 (FStar_Format.combine comma)))
in (_180_323)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_324)
in (FStar_Format.reduce _180_325))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_329 = (let _180_328 = (let _180_327 = (let _180_326 = (print_typ t)
in (_180_326)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_327)
in ((FStar_Format.text "Array"))::_180_328)
in (FStar_Format.reduce _180_329))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_332 = (let _180_331 = (let _180_330 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_330 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_331)::[])
in (FStar_Format.reduce _180_332))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_335 = (let _180_334 = (let _180_333 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_333 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_334)::[])
in (FStar_Format.reduce _180_335))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_338 = (let _180_337 = (let _180_336 = (print_typ t)
in (_180_336)::[])
in ((FStar_Format.text "typeof"))::_180_337)
in (FStar_Format.reduce _180_338))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_342 = (let _180_341 = (let _180_340 = (let _180_339 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_339 (FStar_Format.combine comma)))
in (_180_340)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_341)
in (FStar_Format.reduce _180_342))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_424) -> begin
(let _180_345 = (let _180_344 = (let _180_343 = (jstr_escape s)
in (Prims.strcat _180_343 "\""))
in (Prims.strcat "\"" _180_344))
in (FStar_Format.text _180_345))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_429) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_434) -> begin
(let _180_346 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_346))
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
(let _180_350 = (let _180_349 = (let _180_348 = (let _180_347 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_347 (FStar_Format.combine comma)))
in (_180_348)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_349)
in (FStar_Format.reduce _180_350))
end)
in (let _180_352 = (let _180_351 = (print_gen_t n)
in (_180_351)::(print_lt)::[])
in (FStar_Format.reduce _180_352)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_455 -> (match (_83_455) with
| ((id, _83_452), t) -> begin
(let _180_363 = (let _180_362 = (let _180_358 = (jstr_escape id)
in (FStar_Format.text _180_358))
in (let _180_361 = (let _180_360 = (let _180_359 = (print_typ t)
in (_180_359)::[])
in (colon)::_180_360)
in (_180_362)::_180_361))
in (FStar_Format.reduce _180_363))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_367 = (let _180_366 = (let _180_365 = (let _180_364 = (print_typ ret_t)
in (_180_364)::[])
in ((FStar_Format.text "=>"))::_180_365)
in ((FStar_Format.text "()"))::_180_366)
in (FStar_Format.reduce _180_367))
end
| (x)::[] -> begin
(let _180_374 = (let _180_373 = (let _180_368 = (print_arg x)
in (FStar_Format.parens _180_368))
in (let _180_372 = (let _180_371 = (let _180_370 = (let _180_369 = (print_typ ret_t)
in (FStar_Format.parens _180_369))
in (_180_370)::[])
in ((FStar_Format.text "=>"))::_180_371)
in (_180_373)::_180_372))
in (FStar_Format.reduce _180_374))
end
| (hd)::tl -> begin
(let _180_381 = (let _180_380 = (let _180_375 = (print_arg hd)
in (FStar_Format.parens _180_375))
in (let _180_379 = (let _180_378 = (let _180_377 = (let _180_376 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_376))
in (_180_377)::[])
in ((FStar_Format.text "=>"))::_180_378)
in (_180_380)::_180_379))
in (FStar_Format.reduce _180_381))
end)
in (let _180_383 = (let _180_382 = (print_decl_t decl_vars)
in (_180_382)::(args_t)::[])
in (FStar_Format.reduce _180_383)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_466) -> begin
(let _180_385 = (remove_chars_t id)
in (FStar_Format.text _180_385))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_472)) -> begin
(let _180_391 = (let _180_390 = (print_gen_t g)
in (let _180_389 = (let _180_388 = (let _180_387 = (let _180_386 = (remove_chars_t id)
in (FStar_Format.text _180_386))
in (_180_387)::[])
in (comma)::_180_388)
in (_180_390)::_180_389))
in (FStar_Format.reduce _180_391))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_395 = (let _180_394 = (let _180_393 = (jstr_escape s)
in (Prims.strcat _180_393 "\""))
in (Prims.strcat "\"" _180_394))
in (FStar_Format.text _180_395))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_396 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_396))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_485) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_494) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_497) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_500) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_402 = (let _180_401 = (let _180_400 = (print_typ v)
in (_180_400)::[])
in (colon)::_180_401)
in (FStar_Format.reduce _180_402))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_405 = (let _180_404 = (let _180_403 = (remove_chars_t id)
in (FStar_Format.text _180_403))
in (_180_404)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_405)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_15 -> (match (_83_15) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_409 = (let _180_408 = (let _180_407 = (pretty_print_statements l)
in (_180_407)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_408)
in (FStar_Format.reduce _180_409))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_410 = (pretty_print_exp e)
in (FStar_Format.parens _180_410))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_522 -> (match (_83_522) with
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
(let _180_415 = (let _180_414 = (let _180_413 = (let _180_412 = (print_typ v)
in (_180_412)::[])
in (ws)::_180_413)
in ((FStar_Format.text ":"))::_180_414)
in (FStar_Format.reduce _180_415))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_430 = (let _180_429 = (let _180_428 = (let _180_427 = (let _180_426 = (print_decl_t typePars)
in (let _180_425 = (let _180_424 = (let _180_418 = (let _180_417 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_417 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_418))
in (let _180_423 = (let _180_422 = (let _180_421 = (let _180_420 = (let _180_419 = (print_body body)
in (_180_419)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_420)
in ((FStar_Format.text "{"))::_180_421)
in (returnT)::_180_422)
in (_180_424)::_180_423))
in (_180_426)::_180_425))
in (name)::_180_427)
in (ws)::_180_428)
in ((FStar_Format.text "function"))::_180_429)
in (FStar_Format.reduce _180_430))))
end))





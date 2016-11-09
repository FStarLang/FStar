
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_59 = (let _180_58 = (FStar_List.map (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(

let _83_77 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t true)
in (

let _83_79 = (FStar_ST.op_Colon_Equals f_print_arrow_fun true)
in (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_84 -> begin
(pretty_print_statement s)
end)))
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_58))
in (FStar_Format.reduce _180_59)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (b) -> begin
(pretty_print_statements b)
end
| _83_91 -> begin
(let _180_66 = (let _180_65 = (let _180_64 = (let _180_63 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_63))
in (_180_64)::[])
in (ws)::_180_65)
in (FStar_Format.reduce _180_66))
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_71 = (let _180_70 = (let _180_69 = (pretty_print_statements l)
in (_180_69)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_70)
in (FStar_Format.reduce _180_71))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_74 = (let _180_73 = (let _180_72 = (pretty_print_exp e)
in (_180_72)::(semi)::[])
in (ws)::_180_73)
in (FStar_Format.reduce _180_74))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_91 = (let _180_90 = (let _180_89 = (let _180_88 = (let _180_75 = (pretty_print_exp c)
in (FStar_Format.parens _180_75))
in (let _180_87 = (let _180_86 = (let _180_85 = (let _180_84 = (optws t)
in (let _180_83 = (let _180_82 = (let _180_81 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_80 = (let _180_79 = (let _180_78 = (let _180_77 = (let _180_76 = (optws s)
in (_180_76)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_77)
in ((FStar_Format.text "else"))::_180_78)
in (ws)::_180_79)
in (FStar_Format.reduce _180_80))
end)
in (_180_81)::[])
in ((FStar_Format.text "}"))::_180_82)
in (_180_84)::_180_83))
in (FStar_Format.hardline)::_180_85)
in ((FStar_Format.text "{"))::_180_86)
in (_180_88)::_180_87))
in ((FStar_Format.text "if"))::_180_89)
in (ws)::_180_90)
in (FStar_Format.reduce _180_91))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_99 = (let _180_98 = (let _180_97 = (let _180_92 = (jstr_escape l)
in (FStar_Format.text _180_92))
in (let _180_96 = (let _180_95 = (let _180_94 = (let _180_93 = (optws s)
in (_180_93)::[])
in (FStar_Format.hardline)::_180_94)
in (colon)::_180_95)
in (_180_97)::_180_96))
in (ws)::_180_98)
in (FStar_Format.reduce _180_99))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
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
in ((FStar_Format.text "break"))::_180_105)
in (ws)::_180_106)
in (FStar_Format.reduce _180_107))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_115 = (let _180_114 = (let _180_113 = (let _180_112 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_111 = (let _180_110 = (let _180_109 = (let _180_108 = (jstr_escape v)
in (FStar_Format.text _180_108))
in (_180_109)::[])
in (ws)::_180_110)
in (FStar_Format.reduce _180_111))
end)
in (_180_112)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_113)
in (ws)::_180_114)
in (FStar_Format.reduce _180_115))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_123 = (let _180_122 = (let _180_121 = (let _180_120 = (let _180_116 = (pretty_print_exp e)
in (FStar_Format.parens _180_116))
in (let _180_119 = (let _180_118 = (let _180_117 = (optws s)
in (_180_117)::[])
in (FStar_Format.hardline)::_180_118)
in (_180_120)::_180_119))
in ((FStar_Format.text "with"))::_180_121)
in (ws)::_180_122)
in (FStar_Format.reduce _180_123))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_132), lt, t) -> begin
(let _180_132 = (let _180_131 = (let _180_130 = (let _180_124 = (jstr_escape id)
in (FStar_Format.text _180_124))
in (let _180_129 = (let _180_128 = (print_decl_t lt)
in (let _180_127 = (let _180_126 = (let _180_125 = (print_typ t)
in (_180_125)::(semi)::[])
in ((FStar_Format.text "="))::_180_126)
in (_180_128)::_180_127))
in (_180_130)::_180_129))
in ((FStar_Format.text "type "))::_180_131)
in (FStar_Format.reduce _180_132))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_154 = (let _180_153 = (let _180_152 = (let _180_151 = (let _180_133 = (pretty_print_exp e)
in (FStar_Format.parens _180_133))
in (let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (let _180_146 = (let _180_145 = (let _180_144 = (FStar_List.map (fun _83_144 -> (match (_83_144) with
| (e, l) -> begin
(let _180_143 = (let _180_142 = (let _180_141 = (let _180_140 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_139 = (let _180_138 = (let _180_137 = (let _180_136 = (let _180_135 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_135))
in (_180_136)::[])
in (FStar_Format.hardline)::_180_137)
in (colon)::_180_138)
in (_180_140)::_180_139))
in ((FStar_Format.text "case "))::_180_141)
in (ws)::_180_142)
in (FStar_Format.reduce _180_143))
end)) lcase)
in (FStar_All.pipe_right _180_144 (FStar_Format.combine FStar_Format.hardline)))
in (_180_145)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_146)
in ((FStar_Format.text "{"))::_180_147)
in (ws)::_180_148)
in (FStar_Format.hardline)::_180_149)
in (_180_151)::_180_150))
in ((FStar_Format.text "switch"))::_180_152)
in (ws)::_180_153)
in (FStar_Format.reduce _180_154))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_161 = (let _180_160 = (let _180_159 = (let _180_158 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_157 = (let _180_156 = (let _180_155 = (pretty_print_exp v)
in (_180_155)::[])
in (ws)::_180_156)
in (FStar_Format.reduce _180_157))
end)
in (_180_158)::(semi)::[])
in ((FStar_Format.text "return"))::_180_159)
in (ws)::_180_160)
in (FStar_Format.reduce _180_161))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_165 = (let _180_164 = (let _180_163 = (let _180_162 = (pretty_print_exp e)
in (_180_162)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_163)
in (ws)::_180_164)
in (FStar_Format.reduce _180_165))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_169 = (let _180_168 = (let _180_167 = (let _180_166 = (pretty_print_statements b)
in (_180_166)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_167)
in ((FStar_Format.text "try"))::_180_168)
in (FStar_Format.reduce _180_169))
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_177 = (let _180_176 = (let _180_175 = (let _180_174 = (let _180_170 = (pretty_print_exp e)
in (FStar_Format.parens _180_170))
in (let _180_173 = (let _180_172 = (let _180_171 = (optws s)
in (_180_171)::[])
in (FStar_Format.hardline)::_180_172)
in (_180_174)::_180_173))
in ((FStar_Format.text "while"))::_180_175)
in (ws)::_180_176)
in (FStar_Format.reduce _180_177))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_189 = (let _180_188 = (let _180_187 = (let _180_186 = (let _180_185 = (optws s)
in (let _180_184 = (let _180_183 = (pretty_print_statement s)
in (let _180_182 = (let _180_181 = (let _180_180 = (let _180_179 = (let _180_178 = (pretty_print_exp e)
in (FStar_Format.parens _180_178))
in (_180_179)::(semi)::[])
in ((FStar_Format.text "while"))::_180_180)
in (ws)::_180_181)
in (_180_183)::_180_182))
in (_180_185)::_180_184))
in (FStar_Format.hardline)::_180_186)
in ((FStar_Format.text "do"))::_180_187)
in (ws)::_180_188)
in (FStar_Format.reduce _180_189))
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
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_198) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
FStar_Format.empty
end)
end
| _83_205 -> begin
(let _180_198 = (let _180_197 = (print_kind_var k)
in (let _180_196 = (let _180_195 = (print_pattern p true)
in (let _180_194 = (let _180_193 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_192 = (let _180_191 = (let _180_190 = (pretty_print_exp v)
in (_180_190)::[])
in ((FStar_Format.text "="))::_180_191)
in (FStar_Format.reduce _180_192))
end)
in (_180_193)::(semi)::[])
in (_180_195)::_180_194))
in (_180_197)::_180_196))
in (FStar_Format.reduce _180_198))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_210) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_213) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(

let print_declaration = (match (d) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(optws s)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(pretty_print_exp e)
end)
in (let _180_200 = (let _180_199 = (print_exp_kind k)
in (_180_199)::(print_declaration)::[])
in (FStar_Format.reduce _180_200)))
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _180_209 = (let _180_208 = (let _180_207 = (let _180_201 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_201))
in (let _180_206 = (let _180_205 = (let _180_204 = (let _180_203 = (let _180_202 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_202))
in (_180_203)::((FStar_Format.text "\""))::((FStar_Format.text ";"))::[])
in ((FStar_Format.text "\"./"))::_180_204)
in ((FStar_Format.text " from "))::_180_205)
in (_180_207)::_180_206))
in ((FStar_Format.text "import * as "))::_180_208)
in (FStar_Format.reduce _180_209))
end))
in (let _180_211 = (let _180_210 = (f p)
in (_180_210)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_211)))))
and print_exp_kind : FStar_Extraction_JavaScript_Ast.export_kind  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.ExportType -> begin
(FStar_Format.text "declare ")
end
| FStar_Extraction_JavaScript_Ast.ExportValue -> begin
(FStar_Format.text "export ")
end))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_214 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_214)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_221 = (let _180_220 = (let _180_219 = (let _180_218 = (FStar_List.map (fun s -> (let _180_217 = (remove_chars_t s)
in (FStar_Format.text _180_217))) l)
in (FStar_All.pipe_right _180_218 (FStar_Format.combine comma)))
in (_180_219)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_220)
in (FStar_Format.reduce _180_221))
end
| None -> begin
FStar_Format.empty
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_226 = (let _180_225 = (let _180_224 = (let _180_223 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_223 (FStar_Format.combine comma)))
in (_180_224)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_225)
in (FStar_Format.reduce _180_226))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_230 = (let _180_229 = (let _180_228 = (let _180_227 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_227 (FStar_Format.combine comma)))
in (_180_228)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_229)
in (FStar_Format.reduce _180_230))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_248, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_256 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_234 = (let _180_233 = (let _180_232 = (let _180_231 = (print_body body)
in (print_arrow_fun args _180_231 ret_t))
in (_180_232)::[])
in (decl_t)::_180_233)
in (FStar_Format.reduce _180_234))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_237 = (let _180_236 = (let _180_235 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_235 (FStar_Format.combine semi)))
in (_180_236)::[])
in (FStar_Format.reduce _180_237))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_240 = (let _180_239 = (let _180_238 = (pretty_print_exp e)
in (_180_238)::[])
in ((print_op_un o))::_180_239)
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
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_275) when (n = "_") -> begin
(pretty_print_exp e)
end
| _83_279 -> begin
(let _180_251 = (let _180_250 = (print_pattern p false)
in (let _180_249 = (let _180_248 = (let _180_247 = (pretty_print_exp e)
in (_180_247)::[])
in ((FStar_Format.text "="))::_180_248)
in (_180_250)::_180_249))
in (FStar_Format.reduce _180_251))
end)
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
(

let le = (let _180_259 = (FStar_List.map (fun x -> (let _180_258 = (pretty_print_exp x)
in (FStar_Format.parens _180_258))) l)
in (FStar_All.pipe_right _180_259 (FStar_Format.combine FStar_Format.empty)))
in (let _180_261 = (let _180_260 = (pretty_print_exp e)
in (_180_260)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_307 -> begin
le
end))::[])
in (FStar_Format.reduce _180_261)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_265 = (let _180_264 = (pretty_print_exp o)
in (let _180_263 = (let _180_262 = (pretty_print_propmem p)
in (_180_262)::[])
in (_180_264)::_180_263))
in (FStar_Format.reduce _180_265))
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
(let _180_266 = (remove_chars_t id)
in (FStar_Format.text _180_266))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_272 = (let _180_271 = (let _180_270 = (pretty_print_exp e)
in (let _180_269 = (let _180_268 = (let _180_267 = (print_typ t)
in (_180_267)::((FStar_Format.text ")"))::[])
in (colon)::_180_268)
in (_180_270)::_180_269))
in ((FStar_Format.text "("))::_180_271)
in (FStar_Format.reduce _180_272))
end))
and print_arrow_fun : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc  ->  FStar_Extraction_JavaScript_Ast.typ Prims.option  ->  FStar_Format.doc = (fun args body ret_t -> (

let ret_t = (match (ret_t) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_279 = (let _180_278 = (let _180_277 = (let _180_276 = (print_typ v)
in (FStar_Format.parens _180_276))
in (_180_277)::[])
in (colon)::_180_278)
in (FStar_Format.reduce _180_279))
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
(let _180_286 = (let _180_285 = (let _180_284 = (print_pattern x true)
in (FStar_Format.parens _180_284))
in (_180_285)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_286))
end
| (hd)::tl -> begin
(let _180_294 = (let _180_293 = (let _180_287 = (print_pattern hd true)
in (FStar_Format.parens _180_287))
in (let _180_292 = (let _180_291 = (let _180_290 = (let _180_289 = (let _180_288 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_288))
in (_180_289)::[])
in ((FStar_Format.text "=>"))::_180_290)
in (ret_t)::_180_291)
in (_180_293)::_180_292))
in (FStar_Format.reduce _180_294))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_360) -> begin
(let _180_300 = (let _180_299 = (pretty_print_prop_key k)
in (let _180_298 = (let _180_297 = (let _180_296 = (pretty_print_exp e)
in (_180_296)::[])
in ((FStar_Format.text ":"))::_180_297)
in (_180_299)::_180_298))
in (FStar_Format.reduce _180_300))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_302 = (jstr_escape id)
in (FStar_Format.text _180_302))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_307 = (let _180_306 = (let _180_305 = (let _180_304 = (jstr_escape i)
in (FStar_Format.text _180_304))
in (_180_305)::[])
in ((FStar_Format.text "."))::_180_306)
in (FStar_Format.reduce _180_307))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_310 = (let _180_309 = (let _180_308 = (pretty_print_exp e)
in (_180_308)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_309)
in (FStar_Format.reduce _180_310))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_391) -> begin
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

let _83_399 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_403, _83_405) -> begin
(let _180_321 = (let _180_320 = (let _180_319 = (let _180_318 = (FStar_List.map (fun _83_410 -> (match (_83_410) with
| (k, t) -> begin
(let _180_317 = (let _180_316 = (pretty_print_prop_key k)
in (let _180_315 = (let _180_314 = (let _180_313 = (print_typ t)
in (_180_313)::[])
in ((FStar_Format.text ":"))::_180_314)
in (_180_316)::_180_315))
in (FStar_Format.reduce _180_317))
end)) lp)
in (FStar_All.pipe_right _180_318 (FStar_Format.combine comma)))
in (_180_319)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_320)
in (FStar_Format.reduce _180_321))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_325 = (let _180_324 = (let _180_323 = (let _180_322 = (print_typ t)
in (_180_322)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_323)
in ((FStar_Format.text "Array"))::_180_324)
in (FStar_Format.reduce _180_325))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_328 = (let _180_327 = (let _180_326 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_326 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_327)::[])
in (FStar_Format.reduce _180_328))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_331 = (let _180_330 = (let _180_329 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_329 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_330)::[])
in (FStar_Format.reduce _180_331))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_334 = (let _180_333 = (let _180_332 = (print_typ t)
in (_180_332)::[])
in ((FStar_Format.text "typeof"))::_180_333)
in (FStar_Format.reduce _180_334))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_338 = (let _180_337 = (let _180_336 = (let _180_335 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_335 (FStar_Format.combine comma)))
in (_180_336)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_337)
in (FStar_Format.reduce _180_338))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_423) -> begin
(let _180_341 = (let _180_340 = (let _180_339 = (jstr_escape s)
in (Prims.strcat _180_339 "\""))
in (Prims.strcat "\"" _180_340))
in (FStar_Format.text _180_341))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_428) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_433) -> begin
(let _180_342 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_342))
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
(let _180_346 = (let _180_345 = (let _180_344 = (let _180_343 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_343 (FStar_Format.combine comma)))
in (_180_344)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_345)
in (FStar_Format.reduce _180_346))
end)
in (let _180_348 = (let _180_347 = (print_gen_t n)
in (_180_347)::(print_lt)::[])
in (FStar_Format.reduce _180_348)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_454 -> (match (_83_454) with
| ((id, _83_451), t) -> begin
(let _180_359 = (let _180_358 = (let _180_354 = (jstr_escape id)
in (FStar_Format.text _180_354))
in (let _180_357 = (let _180_356 = (let _180_355 = (print_typ t)
in (_180_355)::[])
in (colon)::_180_356)
in (_180_358)::_180_357))
in (FStar_Format.reduce _180_359))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_363 = (let _180_362 = (let _180_361 = (let _180_360 = (print_typ ret_t)
in (_180_360)::[])
in ((FStar_Format.text "=>"))::_180_361)
in ((FStar_Format.text "()"))::_180_362)
in (FStar_Format.reduce _180_363))
end
| (x)::[] -> begin
(let _180_370 = (let _180_369 = (let _180_364 = (print_arg x)
in (FStar_Format.parens _180_364))
in (let _180_368 = (let _180_367 = (let _180_366 = (let _180_365 = (print_typ ret_t)
in (FStar_Format.parens _180_365))
in (_180_366)::[])
in ((FStar_Format.text "=>"))::_180_367)
in (_180_369)::_180_368))
in (FStar_Format.reduce _180_370))
end
| (hd)::tl -> begin
(let _180_377 = (let _180_376 = (let _180_371 = (print_arg hd)
in (FStar_Format.parens _180_371))
in (let _180_375 = (let _180_374 = (let _180_373 = (let _180_372 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_372))
in (_180_373)::[])
in ((FStar_Format.text "=>"))::_180_374)
in (_180_376)::_180_375))
in (FStar_Format.reduce _180_377))
end)
in (let _180_379 = (let _180_378 = (print_decl_t decl_vars)
in (_180_378)::(args_t)::[])
in (FStar_Format.reduce _180_379)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_465) -> begin
(let _180_381 = (remove_chars_t id)
in (FStar_Format.text _180_381))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_471)) -> begin
(let _180_387 = (let _180_386 = (print_gen_t g)
in (let _180_385 = (let _180_384 = (let _180_383 = (let _180_382 = (remove_chars_t id)
in (FStar_Format.text _180_382))
in (_180_383)::[])
in (comma)::_180_384)
in (_180_386)::_180_385))
in (FStar_Format.reduce _180_387))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_391 = (let _180_390 = (let _180_389 = (jstr_escape s)
in (Prims.strcat _180_389 "\""))
in (Prims.strcat "\"" _180_390))
in (FStar_Format.text _180_391))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_392 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_392))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_484) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_493) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_496) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_499) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_398 = (let _180_397 = (let _180_396 = (print_typ v)
in (_180_396)::[])
in (colon)::_180_397)
in (FStar_Format.reduce _180_398))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_401 = (let _180_400 = (let _180_399 = (remove_chars_t id)
in (FStar_Format.text _180_399))
in (_180_400)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_401)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_405 = (let _180_404 = (let _180_403 = (pretty_print_statements l)
in (_180_403)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_404)
in (FStar_Format.reduce _180_405))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_406 = (pretty_print_exp e)
in (FStar_Format.parens _180_406))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_521 -> (match (_83_521) with
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
(let _180_411 = (let _180_410 = (let _180_409 = (let _180_408 = (print_typ v)
in (_180_408)::[])
in (ws)::_180_409)
in ((FStar_Format.text ":"))::_180_410)
in (FStar_Format.reduce _180_411))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_426 = (let _180_425 = (let _180_424 = (let _180_423 = (let _180_422 = (print_decl_t typePars)
in (let _180_421 = (let _180_420 = (let _180_414 = (let _180_413 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_413 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_414))
in (let _180_419 = (let _180_418 = (let _180_417 = (let _180_416 = (let _180_415 = (print_body body)
in (_180_415)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_416)
in ((FStar_Format.text "{"))::_180_417)
in (returnT)::_180_418)
in (_180_420)::_180_419))
in (_180_422)::_180_421))
in (name)::_180_423)
in (ws)::_180_424)
in ((FStar_Format.text "function"))::_180_425)
in (FStar_Format.reduce _180_426))))
end))





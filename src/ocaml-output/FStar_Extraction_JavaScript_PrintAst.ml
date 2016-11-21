
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
(let _180_132 = (let _180_131 = (let _180_130 = (let _180_124 = (remove_chars_t id)
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
(FStar_All.failwith "todo: pretty-print [JSS_For]")
end
| FStar_Extraction_JavaScript_Ast.JSS_Forin (i, e, s) -> begin
(FStar_All.failwith "todo: pretty-print [JSS_Forin]")
end
| FStar_Extraction_JavaScript_Ast.JSS_ForOf (i, e, s) -> begin
(FStar_All.failwith "todo: pretty-print [JSS_ForOf]")
end
| FStar_Extraction_JavaScript_Ast.JSS_Let (l, s) -> begin
(FStar_All.failwith "todo: pretty-print [JSS_Let]")
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
(let _180_191 = (let _180_190 = (pretty_print_exp v)
in (_180_190)::(semi)::[])
in (FStar_Format.reduce _180_191))
end
| None -> begin
FStar_Format.empty
end)
end
| _83_205 -> begin
(let _180_200 = (let _180_199 = (print_kind_var k)
in (let _180_198 = (let _180_197 = (print_pattern p true)
in (let _180_196 = (let _180_195 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_194 = (let _180_193 = (let _180_192 = (pretty_print_exp v)
in (_180_192)::[])
in ((FStar_Format.text "="))::_180_193)
in (FStar_Format.reduce _180_194))
end)
in (_180_195)::(semi)::[])
in (_180_197)::_180_196))
in (_180_199)::_180_198))
in (FStar_Format.reduce _180_200))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_210) -> begin
(FStar_All.failwith "todo: pretty-print [JSS_DeclareVariable]")
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_213) -> begin
(FStar_All.failwith "todo: pretty-print [JSS_DeclareFunction]")
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
in (let _180_202 = (let _180_201 = (print_exp_kind k)
in (_180_201)::(print_declaration)::[])
in (FStar_Format.reduce _180_202)))
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _180_211 = (let _180_210 = (let _180_209 = (let _180_203 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_203))
in (let _180_208 = (let _180_207 = (let _180_206 = (let _180_205 = (let _180_204 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_204))
in (_180_205)::((FStar_Format.text "\""))::(semi)::[])
in ((FStar_Format.text "\"./"))::_180_206)
in ((FStar_Format.text " from "))::_180_207)
in (_180_209)::_180_208))
in ((FStar_Format.text "import * as "))::_180_210)
in (FStar_Format.reduce _180_211))
end
| FStar_Extraction_JavaScript_Ast.JSS_Seq (l) -> begin
(pretty_print_statements l)
end))
in (match (p) with
| FStar_Extraction_JavaScript_Ast.JSS_Seq (_83_230) -> begin
(f p)
end
| _83_233 -> begin
(let _180_213 = (let _180_212 = (f p)
in (_180_212)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_213))
end))))
and print_exp_kind : FStar_Extraction_JavaScript_Ast.export_kind  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.ExportType -> begin
(FStar_Format.text "export ")
end
| FStar_Extraction_JavaScript_Ast.ExportValue -> begin
(FStar_Format.text "export ")
end))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_216 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_216)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_223 = (let _180_222 = (let _180_221 = (let _180_220 = (FStar_List.map (fun s -> (let _180_219 = (remove_chars_t s)
in (FStar_Format.text _180_219))) l)
in (FStar_All.pipe_right _180_220 (FStar_Format.combine comma)))
in (_180_221)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_222)
in (FStar_Format.reduce _180_223))
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
(let _180_228 = (let _180_227 = (let _180_226 = (let _180_225 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_225 (FStar_Format.combine comma)))
in (_180_226)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_227)
in (FStar_Format.reduce _180_228))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_232 = (let _180_231 = (let _180_230 = (let _180_229 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_229 (FStar_Format.combine comma)))
in (_180_230)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_231)
in (FStar_Format.reduce _180_232))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_255, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_263 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_236 = (let _180_235 = (let _180_234 = (let _180_233 = (print_body body)
in (print_arrow_fun args _180_233 ret_t))
in (_180_234)::[])
in (decl_t)::_180_235)
in (FStar_Format.reduce _180_236))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_239 = (let _180_238 = (let _180_237 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_237 (FStar_Format.combine semi)))
in (_180_238)::[])
in (FStar_Format.reduce _180_239))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_242 = (let _180_241 = (let _180_240 = (pretty_print_exp e)
in (_180_240)::[])
in ((print_op_un o))::_180_241)
in (FStar_Format.reduce _180_242))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_248 = (let _180_247 = (let _180_246 = (pretty_print_exp e1)
in (let _180_245 = (let _180_244 = (let _180_243 = (pretty_print_exp e2)
in (_180_243)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_244)
in (_180_246)::_180_245))
in ((FStar_Format.text "("))::_180_247)
in (FStar_Format.reduce _180_248))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_282) when (n = "_") -> begin
(pretty_print_exp e)
end
| _83_286 -> begin
(let _180_253 = (let _180_252 = (print_pattern p false)
in (let _180_251 = (let _180_250 = (let _180_249 = (pretty_print_exp e)
in (_180_249)::[])
in ((FStar_Format.text "="))::_180_250)
in (_180_252)::_180_251))
in (FStar_Format.reduce _180_253))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_258 = (let _180_257 = (pretty_print_exp e1)
in (let _180_256 = (let _180_255 = (let _180_254 = (pretty_print_exp e2)
in (_180_254)::[])
in ((print_op_log o))::_180_255)
in (_180_257)::_180_256))
in (FStar_Format.reduce _180_258))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_Conditional]")
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_New]")
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _180_261 = (FStar_List.map (fun x -> (let _180_260 = (pretty_print_exp x)
in (FStar_Format.parens _180_260))) l)
in (FStar_All.pipe_right _180_261 (FStar_Format.combine FStar_Format.empty)))
in (let _180_263 = (let _180_262 = (pretty_print_exp e)
in (_180_262)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_309 -> begin
le
end))::[])
in (FStar_Format.reduce _180_263)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_267 = (let _180_266 = (pretty_print_exp o)
in (let _180_265 = (let _180_264 = (pretty_print_propmem p)
in (_180_264)::[])
in (_180_266)::_180_265))
in (FStar_Format.reduce _180_267))
end
| FStar_Extraction_JavaScript_Ast.JSE_Yield (e, b) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_Yield]")
end
| FStar_Extraction_JavaScript_Ast.JSE_Comprehension (l, e) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_Comprehension]")
end
| FStar_Extraction_JavaScript_Ast.JSE_Generator (l, e) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_Generator]")
end
| FStar_Extraction_JavaScript_Ast.JSE_Let (l, e) -> begin
(FStar_All.failwith "todo: pretty-print [JSE_Let]")
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
(let _180_281 = (let _180_280 = (let _180_279 = (let _180_278 = (print_typ v)
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
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_362) -> begin
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
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_393) -> begin
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

let _83_401 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_405, _83_407) -> begin
(let _180_323 = (let _180_322 = (let _180_321 = (let _180_320 = (FStar_List.map (fun _83_412 -> (match (_83_412) with
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
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_425) -> begin
(let _180_343 = (let _180_342 = (let _180_341 = (jstr_escape s)
in (Prims.strcat _180_341 "\""))
in (Prims.strcat "\"" _180_342))
in (FStar_Format.text _180_343))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_430) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_435) -> begin
(let _180_344 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_344))
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

let print_arg = (fun _83_456 -> (match (_83_456) with
| ((id, _83_453), t) -> begin
(let _180_361 = (let _180_360 = (let _180_356 = (jstr_escape id)
in (FStar_Format.text _180_356))
in (let _180_359 = (let _180_358 = (let _180_357 = (print_typ t)
in (_180_357)::[])
in (colon)::_180_358)
in (_180_360)::_180_359))
in (FStar_Format.reduce _180_361))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_365 = (let _180_364 = (let _180_363 = (let _180_362 = (print_typ ret_t)
in (_180_362)::[])
in ((FStar_Format.text "=>"))::_180_363)
in ((FStar_Format.text "()"))::_180_364)
in (FStar_Format.reduce _180_365))
end
| (x)::[] -> begin
(let _180_372 = (let _180_371 = (let _180_366 = (print_arg x)
in (FStar_Format.parens _180_366))
in (let _180_370 = (let _180_369 = (let _180_368 = (let _180_367 = (print_typ ret_t)
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
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_467) -> begin
(let _180_383 = (remove_chars_t id)
in (FStar_Format.text _180_383))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_473)) -> begin
(let _180_389 = (let _180_388 = (print_gen_t g)
in (let _180_387 = (let _180_386 = (let _180_385 = (let _180_384 = (remove_chars_t id)
in (FStar_Format.text _180_384))
in (_180_385)::[])
in (comma)::_180_386)
in (_180_388)::_180_387))
in (FStar_Format.reduce _180_389))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_393 = (let _180_392 = (let _180_391 = (jstr_escape s)
in (Prims.strcat _180_391 "\""))
in (Prims.strcat "\"" _180_392))
in (FStar_Format.text _180_393))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_394 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_394))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_486) -> begin
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_495) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Object]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_498) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Array]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_501) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Assignment]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_400 = (let _180_399 = (let _180_398 = (print_typ v)
in (_180_398)::[])
in (colon)::_180_399)
in (FStar_Format.reduce _180_400))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_403 = (let _180_402 = (let _180_401 = (remove_chars_t id)
in (FStar_Format.text _180_401))
in (_180_402)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_403)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_14 -> (match (_83_14) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_408 = (let _180_407 = (let _180_406 = (let _180_405 = (pretty_print_statements l)
in (_180_405)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_406)
in ((FStar_Format.text "{"))::_180_407)
in (FStar_Format.reduce _180_408))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_409 = (pretty_print_exp e)
in (FStar_Format.parens _180_409))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_523 -> (match (_83_523) with
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
(let _180_414 = (let _180_413 = (let _180_412 = (let _180_411 = (print_typ v)
in (_180_411)::[])
in (ws)::_180_412)
in ((FStar_Format.text ":"))::_180_413)
in (FStar_Format.reduce _180_414))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_429 = (let _180_428 = (let _180_427 = (let _180_426 = (let _180_425 = (print_decl_t typePars)
in (let _180_424 = (let _180_423 = (let _180_417 = (let _180_416 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_416 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_417))
in (let _180_422 = (let _180_421 = (let _180_420 = (let _180_419 = (let _180_418 = (print_body body)
in (_180_418)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_419)
in ((FStar_Format.text "{"))::_180_420)
in (returnT)::_180_421)
in (_180_423)::_180_422))
in (_180_425)::_180_424))
in (name)::_180_426)
in (ws)::_180_427)
in ((FStar_Format.text "function"))::_180_428)
in (FStar_Format.reduce _180_429))))
end))





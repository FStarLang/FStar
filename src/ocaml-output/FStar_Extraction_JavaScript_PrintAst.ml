
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

let _83_76 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t true)
in (

let _83_78 = (FStar_ST.op_Colon_Equals f_print_arrow_fun true)
in (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| _83_83 -> begin
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
| _83_90 -> begin
(pretty_print_statement s)
end))
in (

let f = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_68 = (let _180_67 = (let _180_66 = (let _180_65 = (pretty_print_statements l)
in (_180_65)::((FStar_Format.text "}"))::(FStar_Format.hardline)::[])
in ((FStar_Format.text "{"))::_180_66)
in (ws)::_180_67)
in (FStar_Format.reduce _180_68))
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_71 = (let _180_70 = (let _180_69 = (pretty_print_exp e)
in (_180_69)::(semi)::(FStar_Format.hardline)::[])
in (ws)::_180_70)
in (FStar_Format.reduce _180_71))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_88 = (let _180_87 = (let _180_86 = (let _180_85 = (let _180_72 = (pretty_print_exp c)
in (FStar_Format.parens _180_72))
in (let _180_84 = (let _180_83 = (let _180_82 = (let _180_81 = (optws t)
in (let _180_80 = (let _180_79 = (let _180_78 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_77 = (let _180_76 = (let _180_75 = (let _180_74 = (let _180_73 = (optws s)
in (_180_73)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_74)
in ((FStar_Format.text "else"))::_180_75)
in (ws)::_180_76)
in (FStar_Format.reduce _180_77))
end)
in (_180_78)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "}"))::_180_79)
in (_180_81)::_180_80))
in (FStar_Format.hardline)::_180_82)
in ((FStar_Format.text "{"))::_180_83)
in (_180_85)::_180_84))
in ((FStar_Format.text "if"))::_180_86)
in (ws)::_180_87)
in (FStar_Format.reduce _180_88))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_96 = (let _180_95 = (let _180_94 = (let _180_93 = (let _180_89 = (pretty_print_exp e)
in (FStar_Format.parens _180_89))
in (let _180_92 = (let _180_91 = (let _180_90 = (optws s)
in (_180_90)::[])
in (FStar_Format.hardline)::_180_91)
in (_180_93)::_180_92))
in ((FStar_Format.text "with"))::_180_94)
in (ws)::_180_95)
in (FStar_Format.reduce _180_96))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_111), lt, t) -> begin
(let _180_106 = (let _180_105 = (let _180_104 = (let _180_103 = (let _180_97 = (remove_chars_t id)
in (FStar_Format.text _180_97))
in (let _180_102 = (let _180_101 = (print_decl_t lt)
in (let _180_100 = (let _180_99 = (let _180_98 = (print_typ t)
in (_180_98)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "="))::_180_99)
in (_180_101)::_180_100))
in (_180_103)::_180_102))
in ((FStar_Format.text "type "))::_180_104)
in (ws)::_180_105)
in (FStar_Format.reduce _180_106))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_126 = (let _180_125 = (let _180_124 = (let _180_123 = (let _180_107 = (pretty_print_exp e)
in (FStar_Format.parens _180_107))
in (let _180_122 = (let _180_121 = (let _180_120 = (let _180_119 = (let _180_118 = (let _180_117 = (FStar_List.map (fun _83_123 -> (match (_83_123) with
| (e, l) -> begin
(let _180_116 = (let _180_115 = (let _180_114 = (let _180_113 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_112 = (let _180_111 = (let _180_110 = (let _180_109 = (pretty_print_statements l)
in (_180_109)::[])
in (FStar_Format.hardline)::_180_110)
in (colon)::_180_111)
in (_180_113)::_180_112))
in ((FStar_Format.text "case "))::_180_114)
in (ws)::_180_115)
in (FStar_Format.reduce _180_116))
end)) lcase)
in (FStar_All.pipe_right _180_117 (FStar_Format.combine FStar_Format.hardline)))
in (_180_118)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_119)
in ((FStar_Format.text "{"))::_180_120)
in (ws)::_180_121)
in (_180_123)::_180_122))
in ((FStar_Format.text "switch "))::_180_124)
in (ws)::_180_125)
in (FStar_Format.reduce _180_126))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_133 = (let _180_132 = (let _180_131 = (let _180_130 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_129 = (let _180_128 = (let _180_127 = (pretty_print_exp v)
in (_180_127)::[])
in (ws)::_180_128)
in (FStar_Format.reduce _180_129))
end)
in (_180_130)::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "return"))::_180_131)
in (ws)::_180_132)
in (FStar_Format.reduce _180_133))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_137 = (let _180_136 = (let _180_135 = (let _180_134 = (pretty_print_exp e)
in (_180_134)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_135)
in (ws)::_180_136)
in (FStar_Format.reduce _180_137))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (b, h) -> begin
(let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (pretty_print_statements b)
in (_180_138)::((FStar_Format.text "}"))::((FStar_Format.text "TODO:catch"))::[])
in ((FStar_Format.text "{"))::_180_139)
in ((FStar_Format.text "try"))::_180_140)
in (FStar_Format.reduce _180_141))
end
| FStar_Extraction_JavaScript_Ast.JSS_FunctionDeclaration (f) -> begin
(let _180_143 = (let _180_142 = (pretty_print_fun f)
in (_180_142)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_143))
end
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(

let isNull = (fun v -> (match (v) with
| FStar_Extraction_JavaScript_Ast.JSE_Literal (FStar_Extraction_JavaScript_Ast.JSV_Null, "") -> begin
true
end
| _83_153 -> begin
false
end))
in (match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_156) when (n = "_") -> begin
(match (e) with
| Some (v) when (isNull v) -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_147 = (let _180_146 = (pretty_print_exp v)
in (_180_146)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_147))
end
| None -> begin
FStar_Format.empty
end)
end
| _83_165 -> begin
(let _180_156 = (let _180_155 = (print_kind_var k)
in (let _180_154 = (let _180_153 = (print_pattern p true)
in (let _180_152 = (let _180_151 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_150 = (let _180_149 = (let _180_148 = (pretty_print_exp v)
in (_180_148)::[])
in ((FStar_Format.text "="))::_180_149)
in (FStar_Format.reduce _180_150))
end)
in (_180_151)::(semi)::(FStar_Format.hardline)::[])
in (_180_153)::_180_152))
in (_180_155)::_180_154))
in (FStar_Format.reduce _180_156))
end))
end
| FStar_Extraction_JavaScript_Ast.JSS_ExportDefaultDeclaration (d, k) -> begin
(match (d) with
| FStar_Extraction_JavaScript_Ast.JSE_Declaration (s) -> begin
(match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(let _180_158 = (FStar_List.map (fun x -> (print_export_stmt x)) l)
in (FStar_Format.reduce _180_158))
end
| _83_179 -> begin
(let _180_161 = (let _180_160 = (let _180_159 = (optws s)
in (_180_159)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_160)
in (FStar_Format.reduce _180_161))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Expression (e) -> begin
(let _180_164 = (let _180_163 = (let _180_162 = (pretty_print_exp e)
in (_180_162)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_163)
in (FStar_Format.reduce _180_164))
end)
end
| FStar_Extraction_JavaScript_Ast.JSS_ImportDeclaration (d) -> begin
(let _180_173 = (let _180_172 = (let _180_171 = (let _180_165 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_165))
in (let _180_170 = (let _180_169 = (let _180_168 = (let _180_167 = (let _180_166 = (jstr_escape (Prims.fst d))
in (FStar_Format.text _180_166))
in (_180_167)::((FStar_Format.text "\""))::(semi)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "\"./"))::_180_168)
in ((FStar_Format.text " from "))::_180_169)
in (_180_171)::_180_170))
in ((FStar_Format.text "import * as "))::_180_172)
in (FStar_Format.reduce _180_173))
end
| FStar_Extraction_JavaScript_Ast.JSS_Seq (l) -> begin
(pretty_print_statements l)
end))
in (f p))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_175 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_175)))
and print_export_stmt : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_VariableDeclaration ((p, e), k) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_197) when (n = "_") -> begin
(match (e) with
| Some (v) -> begin
(let _180_178 = (let _180_177 = (pretty_print_exp v)
in (_180_177)::(semi)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_178))
end
| None -> begin
FStar_Format.empty
end)
end
| _83_204 -> begin
(let _180_181 = (let _180_180 = (let _180_179 = (pretty_print_statement s)
in (_180_179)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_180)
in (FStar_Format.reduce _180_181))
end)
end
| _83_206 -> begin
(let _180_184 = (let _180_183 = (let _180_182 = (pretty_print_statement s)
in (_180_182)::(FStar_Format.hardline)::[])
in ((FStar_Format.text "export "))::_180_183)
in (FStar_Format.reduce _180_184))
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_189 = (let _180_188 = (let _180_187 = (let _180_186 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_186 (FStar_Format.combine comma)))
in (_180_187)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_188)
in (FStar_Format.reduce _180_189))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_193 = (let _180_192 = (let _180_191 = (let _180_190 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_190 (FStar_Format.combine comma)))
in (_180_191)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_192)
in (FStar_Format.reduce _180_193))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (_83_218, args, body, ret_t, decl_vars) -> begin
(

let decl_t = if (FStar_ST.read f_print_arrow_fun) then begin
(print_decl_t decl_vars)
end else begin
FStar_Format.empty
end
in (

let _83_226 = (FStar_ST.op_Colon_Equals f_print_arrow_fun false)
in (let _180_197 = (let _180_196 = (let _180_195 = (let _180_194 = (print_body body)
in (print_arrow_fun args _180_194 ret_t))
in (_180_195)::[])
in (decl_t)::_180_196)
in (FStar_Format.reduce _180_197))))
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_200 = (let _180_199 = (let _180_198 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_198 (FStar_Format.combine semi)))
in (_180_199)::[])
in (FStar_Format.reduce _180_200))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_203 = (let _180_202 = (let _180_201 = (pretty_print_exp e)
in (_180_201)::[])
in ((print_op_un o))::_180_202)
in (FStar_Format.reduce _180_203))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_209 = (let _180_208 = (let _180_207 = (pretty_print_exp e1)
in (let _180_206 = (let _180_205 = (let _180_204 = (pretty_print_exp e2)
in (_180_204)::((FStar_Format.text ")"))::[])
in ((print_op_bin o))::_180_205)
in (_180_207)::_180_206))
in ((FStar_Format.text "("))::_180_208)
in (FStar_Format.reduce _180_209))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(match (p) with
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (n, _83_245) when (n = "_") -> begin
(pretty_print_exp e)
end
| _83_249 -> begin
(let _180_214 = (let _180_213 = (print_pattern p false)
in (let _180_212 = (let _180_211 = (let _180_210 = (pretty_print_exp e)
in (_180_210)::[])
in ((FStar_Format.text "="))::_180_211)
in (_180_213)::_180_212))
in (FStar_Format.reduce _180_214))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_219 = (let _180_218 = (pretty_print_exp e1)
in (let _180_217 = (let _180_216 = (let _180_215 = (pretty_print_exp e2)
in (_180_215)::[])
in ((print_op_log o))::_180_216)
in (_180_218)::_180_217))
in (FStar_Format.reduce _180_219))
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(

let le = (let _180_222 = (FStar_List.map (fun x -> (let _180_221 = (pretty_print_exp x)
in (FStar_Format.parens _180_221))) l)
in (FStar_All.pipe_right _180_222 (FStar_Format.combine FStar_Format.empty)))
in (let _180_224 = (let _180_223 = (pretty_print_exp e)
in (_180_223)::((match (l) with
| [] -> begin
(FStar_Format.text "()")
end
| _83_263 -> begin
le
end))::[])
in (FStar_Format.reduce _180_224)))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_228 = (let _180_227 = (pretty_print_exp o)
in (let _180_226 = (let _180_225 = (pretty_print_propmem p)
in (_180_225)::[])
in (_180_227)::_180_226))
in (FStar_Format.reduce _180_228))
end
| FStar_Extraction_JavaScript_Ast.JSE_Identifier (id, t) -> begin
(let _180_229 = (remove_chars_t id)
in (FStar_Format.text _180_229))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
(let _180_235 = (let _180_234 = (let _180_233 = (pretty_print_exp e)
in (let _180_232 = (let _180_231 = (let _180_230 = (print_typ t)
in (_180_230)::((FStar_Format.text ")"))::[])
in (colon)::_180_231)
in (_180_233)::_180_232))
in ((FStar_Format.text "("))::_180_234)
in (FStar_Format.reduce _180_235))
end))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_242 = (let _180_241 = (let _180_240 = (let _180_239 = (FStar_List.map (fun s -> (let _180_238 = (remove_chars_t s)
in (FStar_Format.text _180_238))) l)
in (FStar_All.pipe_right _180_239 (FStar_Format.combine comma)))
in (_180_240)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_241)
in (FStar_Format.reduce _180_242))
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
(let _180_249 = (let _180_248 = (let _180_247 = (let _180_246 = (print_typ v)
in (FStar_Format.parens _180_246))
in (_180_247)::[])
in (colon)::_180_248)
in (FStar_Format.reduce _180_249))
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
(let _180_256 = (let _180_255 = (let _180_254 = (print_pattern x true)
in (FStar_Format.parens _180_254))
in (_180_255)::(ret_t)::((FStar_Format.text "=>"))::(body)::[])
in (FStar_Format.reduce _180_256))
end
| (hd)::tl -> begin
(let _180_264 = (let _180_263 = (let _180_257 = (print_pattern hd true)
in (FStar_Format.parens _180_257))
in (let _180_262 = (let _180_261 = (let _180_260 = (let _180_259 = (let _180_258 = (print_arrow_fun_p tl body ret_t false)
in (FStar_Format.parens _180_258))
in (_180_259)::[])
in ((FStar_Format.text "=>"))::_180_260)
in (ret_t)::_180_261)
in (_180_263)::_180_262))
in (FStar_Format.reduce _180_264))
end)))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_305) -> begin
(let _180_270 = (let _180_269 = (pretty_print_prop_key k)
in (let _180_268 = (let _180_267 = (let _180_266 = (pretty_print_exp e)
in (_180_266)::[])
in ((FStar_Format.text ":"))::_180_267)
in (_180_269)::_180_268))
in (FStar_Format.reduce _180_270))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_272 = (jstr_escape id)
in (FStar_Format.text _180_272))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_277 = (let _180_276 = (let _180_275 = (let _180_274 = (jstr_escape i)
in (FStar_Format.text _180_274))
in (_180_275)::[])
in ((FStar_Format.text "."))::_180_276)
in (FStar_Format.reduce _180_277))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_280 = (let _180_279 = (let _180_278 = (pretty_print_exp e)
in (_180_278)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_279)
in (FStar_Format.reduce _180_280))
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_336) -> begin
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

let _83_344 = (FStar_ST.op_Colon_Equals f_print_arrow_fun_t false)
in (print_fun_typ args ret_t decl_vars)))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_348, _83_350) -> begin
(let _180_291 = (let _180_290 = (let _180_289 = (let _180_288 = (FStar_List.map (fun _83_355 -> (match (_83_355) with
| (k, t) -> begin
(let _180_287 = (let _180_286 = (pretty_print_prop_key k)
in (let _180_285 = (let _180_284 = (let _180_283 = (print_typ t)
in (_180_283)::[])
in ((FStar_Format.text ":"))::_180_284)
in (_180_286)::_180_285))
in (FStar_Format.reduce _180_287))
end)) lp)
in (FStar_All.pipe_right _180_288 (FStar_Format.combine comma)))
in (_180_289)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_290)
in (FStar_Format.reduce _180_291))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_295 = (let _180_294 = (let _180_293 = (let _180_292 = (print_typ t)
in (_180_292)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_293)
in ((FStar_Format.text "Array"))::_180_294)
in (FStar_Format.reduce _180_295))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_298 = (let _180_297 = (let _180_296 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_296 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_297)::[])
in (FStar_Format.reduce _180_298))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_301 = (let _180_300 = (let _180_299 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_299 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_300)::[])
in (FStar_Format.reduce _180_301))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_304 = (let _180_303 = (let _180_302 = (print_typ t)
in (_180_302)::[])
in ((FStar_Format.text "typeof"))::_180_303)
in (FStar_Format.reduce _180_304))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_308 = (let _180_307 = (let _180_306 = (let _180_305 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_305 (FStar_Format.combine comma)))
in (_180_306)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_307)
in (FStar_Format.reduce _180_308))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_368) -> begin
(let _180_311 = (let _180_310 = (let _180_309 = (jstr_escape s)
in (Prims.strcat _180_309 "\""))
in (Prims.strcat "\"" _180_310))
in (FStar_Format.text _180_311))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_373) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_378) -> begin
(let _180_312 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_312))
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
(let _180_316 = (let _180_315 = (let _180_314 = (let _180_313 = (FStar_List.map print_typ v)
in (FStar_All.pipe_right _180_313 (FStar_Format.combine comma)))
in (_180_314)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_315)
in (FStar_Format.reduce _180_316))
end)
in (let _180_318 = (let _180_317 = (print_gen_t n)
in (_180_317)::(print_lt)::[])
in (FStar_Format.reduce _180_318)))
end))
and print_fun_typ : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun args ret_t decl_vars -> (

let print_arg = (fun _83_399 -> (match (_83_399) with
| ((id, _83_396), t) -> begin
(let _180_329 = (let _180_328 = (let _180_324 = (jstr_escape id)
in (FStar_Format.text _180_324))
in (let _180_327 = (let _180_326 = (let _180_325 = (print_typ t)
in (_180_325)::[])
in (colon)::_180_326)
in (_180_328)::_180_327))
in (FStar_Format.reduce _180_329))
end))
in (

let args_t = (match (args) with
| [] -> begin
(let _180_333 = (let _180_332 = (let _180_331 = (let _180_330 = (print_typ ret_t)
in (_180_330)::[])
in ((FStar_Format.text "=>"))::_180_331)
in ((FStar_Format.text "()"))::_180_332)
in (FStar_Format.reduce _180_333))
end
| (x)::[] -> begin
(let _180_340 = (let _180_339 = (let _180_334 = (print_arg x)
in (FStar_Format.parens _180_334))
in (let _180_338 = (let _180_337 = (let _180_336 = (let _180_335 = (print_typ ret_t)
in (FStar_Format.parens _180_335))
in (_180_336)::[])
in ((FStar_Format.text "=>"))::_180_337)
in (_180_339)::_180_338))
in (FStar_Format.reduce _180_340))
end
| (hd)::tl -> begin
(let _180_347 = (let _180_346 = (let _180_341 = (print_arg hd)
in (FStar_Format.parens _180_341))
in (let _180_345 = (let _180_344 = (let _180_343 = (let _180_342 = (print_fun_typ tl ret_t None)
in (FStar_Format.parens _180_342))
in (_180_343)::[])
in ((FStar_Format.text "=>"))::_180_344)
in (_180_346)::_180_345))
in (FStar_Format.reduce _180_347))
end)
in (let _180_349 = (let _180_348 = (print_decl_t decl_vars)
in (_180_348)::(args_t)::[])
in (FStar_Format.reduce _180_349)))))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_410) -> begin
(let _180_351 = (remove_chars_t id)
in (FStar_Format.text _180_351))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_416)) -> begin
(let _180_357 = (let _180_356 = (print_gen_t g)
in (let _180_355 = (let _180_354 = (let _180_353 = (let _180_352 = (remove_chars_t id)
in (FStar_Format.text _180_352))
in (_180_353)::[])
in (comma)::_180_354)
in (_180_356)::_180_355))
in (FStar_Format.reduce _180_357))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_361 = (let _180_360 = (let _180_359 = (jstr_escape s)
in (Prims.strcat _180_359 "\""))
in (Prims.strcat "\"" _180_360))
in (FStar_Format.text _180_361))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_362 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_362))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
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
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_435) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Object]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_438) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Array]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_441) -> begin
(FStar_All.failwith "todo: pretty-print [JGP_Assignment]")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (e) -> begin
(pretty_print_exp e)
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_368 = (let _180_367 = (let _180_366 = (print_typ v)
in (_180_366)::[])
in (colon)::_180_367)
in (FStar_Format.reduce _180_368))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_371 = (let _180_370 = (let _180_369 = (remove_chars_t id)
in (FStar_Format.text _180_369))
in (_180_370)::(if print_t then begin
r
end else begin
FStar_Format.empty
end)::[])
in (FStar_Format.reduce _180_371)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(let _180_376 = (let _180_375 = (let _180_374 = (let _180_373 = (pretty_print_statements l)
in (_180_373)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_374)
in ((FStar_Format.text "{"))::_180_375)
in (FStar_Format.reduce _180_376))
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(let _180_377 = (pretty_print_exp e)
in (FStar_Format.parens _180_377))
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_463 -> (match (_83_463) with
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
in (let _180_397 = (let _180_396 = (let _180_395 = (let _180_394 = (let _180_393 = (print_decl_t typePars)
in (let _180_392 = (let _180_391 = (let _180_385 = (let _180_384 = (FStar_List.map (fun p -> (print_pattern p true)) pars)
in (FStar_All.pipe_right _180_384 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_385))
in (let _180_390 = (let _180_389 = (let _180_388 = (let _180_387 = (let _180_386 = (print_body body)
in (_180_386)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_387)
in ((FStar_Format.text "{"))::_180_388)
in (returnT)::_180_389)
in (_180_391)::_180_390))
in (_180_393)::_180_392))
in (name)::_180_394)
in (ws)::_180_395)
in ((FStar_Format.text "function"))::_180_396)
in (FStar_Format.reduce _180_397))))
end))





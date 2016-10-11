
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


let print_op_un : FStar_Extraction_JavaScript_Ast.op_un  ->  FStar_Format.doc = (fun _83_2 -> (match (_83_2) with
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


let print_op_bin : FStar_Extraction_JavaScript_Ast.op_bin  ->  FStar_Format.doc = (fun _83_3 -> (match (_83_3) with
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


let print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun _83_4 -> (match (_83_4) with
| FStar_Extraction_JavaScript_Ast.JSL_Or -> begin
(FStar_Format.text "||")
end
| FStar_Extraction_JavaScript_Ast.JSL_And -> begin
(FStar_Format.text "&&")
end))


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_37 = (let _180_36 = (FStar_List.map (fun _83_5 -> (match (_83_5) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(pretty_print_statement s)
end)) program)
in (FStar_List.append (((FStar_Format.text "/* @flow */"))::(FStar_Format.hardline)::[]) _180_36))
in (FStar_Format.reduce _180_37)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (_83_72) -> begin
(pretty_print_statement s)
end
| _83_75 -> begin
(let _180_44 = (let _180_43 = (let _180_42 = (let _180_41 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_41))
in (_180_42)::[])
in (ws)::_180_43)
in (FStar_Format.reduce _180_44))
end))
in (

let f = (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_49 = (let _180_48 = (let _180_47 = (pretty_print_exp e)
in (_180_47)::(semi)::[])
in (ws)::_180_48)
in (FStar_Format.reduce _180_49))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_66 = (let _180_65 = (let _180_64 = (let _180_63 = (let _180_50 = (pretty_print_exp c)
in (FStar_Format.parens _180_50))
in (let _180_62 = (let _180_61 = (let _180_60 = (let _180_59 = (optws t)
in (let _180_58 = (let _180_57 = (let _180_56 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_55 = (let _180_54 = (let _180_53 = (let _180_52 = (let _180_51 = (optws s)
in (_180_51)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_52)
in ((FStar_Format.text "else"))::_180_53)
in (ws)::_180_54)
in (FStar_Format.reduce _180_55))
end)
in (_180_56)::[])
in ((FStar_Format.text "}"))::_180_57)
in (_180_59)::_180_58))
in (FStar_Format.hardline)::_180_60)
in ((FStar_Format.text "{"))::_180_61)
in (_180_63)::_180_62))
in ((FStar_Format.text "if"))::_180_64)
in (ws)::_180_65)
in (FStar_Format.reduce _180_66))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_74 = (let _180_73 = (let _180_72 = (let _180_67 = (jstr_escape l)
in (FStar_Format.text _180_67))
in (let _180_71 = (let _180_70 = (let _180_69 = (let _180_68 = (optws s)
in (_180_68)::[])
in (FStar_Format.hardline)::_180_69)
in (colon)::_180_70)
in (_180_72)::_180_71))
in (ws)::_180_73)
in (FStar_Format.reduce _180_74))
end
| FStar_Extraction_JavaScript_Ast.JSS_Break (i) -> begin
(FStar_Format.reduce ((ws)::((FStar_Format.text "break"))::((match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(FStar_Format.cat ws (FStar_Format.text v))
end))::(semi)::[]))
end
| FStar_Extraction_JavaScript_Ast.JSS_Continue (i) -> begin
(let _180_82 = (let _180_81 = (let _180_80 = (let _180_79 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_78 = (let _180_77 = (let _180_76 = (let _180_75 = (jstr_escape v)
in (FStar_Format.text _180_75))
in (_180_76)::[])
in (ws)::_180_77)
in (FStar_Format.reduce _180_78))
end)
in (_180_79)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_80)
in (ws)::_180_81)
in (FStar_Format.reduce _180_82))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_90 = (let _180_89 = (let _180_88 = (let _180_87 = (let _180_83 = (pretty_print_exp e)
in (FStar_Format.parens _180_83))
in (let _180_86 = (let _180_85 = (let _180_84 = (optws s)
in (_180_84)::[])
in (FStar_Format.hardline)::_180_85)
in (_180_87)::_180_86))
in ((FStar_Format.text "with"))::_180_88)
in (ws)::_180_89)
in (FStar_Format.reduce _180_90))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_116), lt, t) -> begin
(let _180_99 = (let _180_98 = (let _180_97 = (let _180_91 = (jstr_escape id)
in (FStar_Format.text _180_91))
in (let _180_96 = (let _180_95 = (print_decl_t lt)
in (let _180_94 = (let _180_93 = (let _180_92 = (print_typ t)
in (_180_92)::(semi)::[])
in ((FStar_Format.text "="))::_180_93)
in (_180_95)::_180_94))
in (_180_97)::_180_96))
in ((FStar_Format.text "type "))::_180_98)
in (FStar_Format.reduce _180_99))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_121 = (let _180_120 = (let _180_119 = (let _180_118 = (let _180_100 = (pretty_print_exp e)
in (FStar_Format.parens _180_100))
in (let _180_117 = (let _180_116 = (let _180_115 = (let _180_114 = (let _180_113 = (let _180_112 = (let _180_111 = (FStar_List.map (fun _83_128 -> (match (_83_128) with
| (e, l) -> begin
(let _180_110 = (let _180_109 = (let _180_108 = (let _180_107 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_106 = (let _180_105 = (let _180_104 = (let _180_103 = (let _180_102 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_102))
in (_180_103)::[])
in (FStar_Format.hardline)::_180_104)
in (colon)::_180_105)
in (_180_107)::_180_106))
in ((FStar_Format.text "case "))::_180_108)
in (ws)::_180_109)
in (FStar_Format.reduce _180_110))
end)) lcase)
in (FStar_Format.combine FStar_Format.hardline _180_111))
in (_180_112)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_113)
in ((FStar_Format.text "{"))::_180_114)
in (ws)::_180_115)
in (FStar_Format.hardline)::_180_116)
in (_180_118)::_180_117))
in ((FStar_Format.text "switch"))::_180_119)
in (ws)::_180_120)
in (FStar_Format.reduce _180_121))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_128 = (let _180_127 = (let _180_126 = (let _180_125 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_124 = (let _180_123 = (let _180_122 = (pretty_print_exp v)
in (_180_122)::[])
in (ws)::_180_123)
in (FStar_Format.reduce _180_124))
end)
in (_180_125)::(semi)::[])
in ((FStar_Format.text "return"))::_180_126)
in (ws)::_180_127)
in (FStar_Format.reduce _180_128))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_132 = (let _180_131 = (let _180_130 = (let _180_129 = (pretty_print_exp e)
in (_180_129)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_130)
in (ws)::_180_131)
in (FStar_Format.reduce _180_132))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (_83_140) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_140 = (let _180_139 = (let _180_138 = (let _180_137 = (let _180_133 = (pretty_print_exp e)
in (FStar_Format.parens _180_133))
in (let _180_136 = (let _180_135 = (let _180_134 = (optws s)
in (_180_134)::[])
in (FStar_Format.hardline)::_180_135)
in (_180_137)::_180_136))
in ((FStar_Format.text "while"))::_180_138)
in (ws)::_180_139)
in (FStar_Format.reduce _180_140))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_152 = (let _180_151 = (let _180_150 = (let _180_149 = (let _180_148 = (optws s)
in (let _180_147 = (let _180_146 = (pretty_print_statement s)
in (let _180_145 = (let _180_144 = (let _180_143 = (let _180_142 = (let _180_141 = (pretty_print_exp e)
in (FStar_Format.parens _180_141))
in (_180_142)::(semi)::[])
in ((FStar_Format.text "while"))::_180_143)
in (ws)::_180_144)
in (_180_146)::_180_145))
in (_180_148)::_180_147))
in (FStar_Format.hardline)::_180_149)
in ((FStar_Format.text "do"))::_180_150)
in (ws)::_180_151)
in (FStar_Format.reduce _180_152))
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
(let _180_169 = (let _180_168 = (let _180_167 = (print_kind_var k)
in (let _180_166 = (let _180_165 = (let _180_164 = (let _180_163 = (FStar_List.map (fun _83_179 -> (match (_83_179) with
| (p, e) -> begin
(let _180_162 = (let _180_161 = (print_pattern p)
in (let _180_160 = (let _180_159 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_158 = (let _180_157 = (let _180_156 = (let _180_155 = (let _180_154 = (pretty_print_exp v)
in (_180_154)::[])
in (ws)::_180_155)
in ((FStar_Format.text "="))::_180_156)
in (ws)::_180_157)
in (FStar_Format.reduce _180_158))
end)
in (_180_159)::[])
in (_180_161)::_180_160))
in (FStar_Format.reduce _180_162))
end)) l)
in (FStar_Format.combine comma _180_163))
in (_180_164)::(semi)::[])
in (ws)::_180_165)
in (_180_167)::_180_166))
in (ws)::_180_168)
in (FStar_Format.reduce _180_169))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_184) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_187) -> begin
semi
end))
in (let _180_171 = (let _180_170 = (f p)
in (_180_170)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_171)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_173 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_173)))
and print_decl_t : FStar_Extraction_JavaScript_Ast.param_decl_t Prims.option  ->  FStar_Format.doc = (fun lt -> (match (lt) with
| Some (l) -> begin
(let _180_180 = (let _180_179 = (let _180_178 = (let _180_177 = (FStar_List.map (fun s -> (let _180_176 = (jstr_escape s)
in (FStar_Format.text _180_176))) l)
in (FStar_All.pipe_right _180_177 (FStar_Format.combine comma)))
in (_180_178)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_179)
in (FStar_Format.reduce _180_180))
end
| None -> begin
FStar_Format.empty
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_185 = (let _180_184 = (let _180_183 = (let _180_182 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_182 (FStar_Format.combine comma)))
in (_180_183)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_184)
in (FStar_Format.reduce _180_185))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_189 = (let _180_188 = (let _180_187 = (let _180_186 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_186 (FStar_Format.combine comma)))
in (_180_187)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_188)
in (FStar_Format.reduce _180_189))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
(let _180_192 = (let _180_191 = (let _180_190 = (FStar_List.map pretty_print_exp e)
in (FStar_All.pipe_right _180_190 (FStar_Format.combine semi)))
in (_180_191)::[])
in (FStar_Format.reduce _180_192))
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_196 = (let _180_195 = (print_op_un o)
in (let _180_194 = (let _180_193 = (pretty_print_exp e)
in (_180_193)::[])
in (_180_195)::_180_194))
in (FStar_Format.reduce _180_196))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_201 = (let _180_200 = (pretty_print_exp e1)
in (let _180_199 = (let _180_198 = (let _180_197 = (pretty_print_exp e2)
in (_180_197)::[])
in ((print_op_bin o))::_180_198)
in (_180_200)::_180_199))
in (FStar_Format.reduce _180_201))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
(let _180_206 = (let _180_205 = (print_pattern p)
in (let _180_204 = (let _180_203 = (let _180_202 = (pretty_print_exp e)
in (_180_202)::[])
in ((FStar_Format.text "="))::_180_203)
in (_180_205)::_180_204))
in (FStar_Format.reduce _180_206))
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_211 = (let _180_210 = (pretty_print_exp e1)
in (let _180_209 = (let _180_208 = (let _180_207 = (pretty_print_exp e2)
in (_180_207)::[])
in ((print_op_log o))::_180_208)
in (_180_210)::_180_209))
in (FStar_Format.reduce _180_211))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_217 = (let _180_216 = (pretty_print_exp e)
in (let _180_215 = (let _180_214 = (let _180_213 = (let _180_212 = (FStar_List.map pretty_print_exp l)
in (FStar_All.pipe_right _180_212 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_213))
in (_180_214)::[])
in (_180_216)::_180_215))
in (FStar_Format.reduce _180_217))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_221 = (let _180_220 = (pretty_print_exp o)
in (let _180_219 = (let _180_218 = (pretty_print_propmem p)
in (_180_218)::[])
in (_180_220)::_180_219))
in (FStar_Format.reduce _180_221))
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
(let _180_229 = (let _180_228 = (let _180_222 = (jstr_escape id)
in (FStar_Format.text _180_222))
in (let _180_227 = (let _180_226 = (match (t) with
| Some (v) -> begin
(let _180_225 = (let _180_224 = (let _180_223 = (print_typ v)
in (_180_223)::[])
in ((FStar_Format.text ":"))::_180_224)
in (FStar_Format.reduce _180_225))
end
| None -> begin
(FStar_Format.text "")
end)
in (_180_226)::[])
in (_180_228)::_180_227))
in (FStar_Format.reduce _180_229))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
semi
end))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_284) -> begin
(let _180_235 = (let _180_234 = (pretty_print_prop_key k)
in (let _180_233 = (let _180_232 = (let _180_231 = (pretty_print_exp e)
in (_180_231)::[])
in ((FStar_Format.text ":"))::_180_232)
in (_180_234)::_180_233))
in (FStar_Format.reduce _180_235))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_237 = (jstr_escape id)
in (FStar_Format.text _180_237))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_242 = (let _180_241 = (let _180_240 = (let _180_239 = (jstr_escape i)
in (FStar_Format.text _180_239))
in (_180_240)::[])
in ((FStar_Format.text "."))::_180_241)
in (FStar_Format.reduce _180_242))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(let _180_245 = (let _180_244 = (let _180_243 = (pretty_print_exp e)
in (_180_243)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_244)
in (FStar_Format.reduce _180_245))
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
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
(FStar_Format.text "bool")
end
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_315) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (args, ret_t, decl_vars) -> begin
(let _180_254 = (let _180_253 = (print_decl_t decl_vars)
in (let _180_252 = (let _180_251 = (let _180_247 = (print_args args)
in (FStar_Format.parens _180_247))
in (let _180_250 = (let _180_249 = (let _180_248 = (print_typ ret_t)
in (_180_248)::[])
in ((FStar_Format.text "=>"))::_180_249)
in (_180_251)::_180_250))
in (_180_253)::_180_252))
in (FStar_Format.reduce _180_254))
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_324, _83_326) -> begin
(let _180_264 = (let _180_263 = (let _180_262 = (let _180_261 = (FStar_List.map (fun _83_331 -> (match (_83_331) with
| (k, t) -> begin
(let _180_260 = (let _180_259 = (pretty_print_prop_key k)
in (let _180_258 = (let _180_257 = (let _180_256 = (print_typ t)
in (_180_256)::[])
in ((FStar_Format.text ":"))::_180_257)
in (_180_259)::_180_258))
in (FStar_Format.reduce _180_260))
end)) lp)
in (FStar_All.pipe_right _180_261 (FStar_Format.combine comma)))
in (_180_262)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_263)
in (FStar_Format.reduce _180_264))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (t) -> begin
(let _180_268 = (let _180_267 = (let _180_266 = (let _180_265 = (print_typ t)
in (_180_265)::((FStar_Format.text ">"))::[])
in ((FStar_Format.text "<"))::_180_266)
in ((FStar_Format.text "Array"))::_180_267)
in (FStar_Format.reduce _180_268))
end
| FStar_Extraction_JavaScript_Ast.JST_Union (l) -> begin
(let _180_271 = (let _180_270 = (let _180_269 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_269 (FStar_Format.combine (FStar_Format.text "|"))))
in (_180_270)::[])
in (FStar_Format.reduce _180_271))
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (l) -> begin
(let _180_274 = (let _180_273 = (let _180_272 = (FStar_List.map print_typ l)
in (FStar_All.pipe_right _180_272 (FStar_Format.combine (FStar_Format.text "&"))))
in (_180_273)::[])
in (FStar_Format.reduce _180_274))
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (t) -> begin
(let _180_277 = (let _180_276 = (let _180_275 = (print_typ t)
in (_180_275)::[])
in ((FStar_Format.text "typeof"))::_180_276)
in (FStar_Format.reduce _180_277))
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (lt) -> begin
(let _180_281 = (let _180_280 = (let _180_279 = (let _180_278 = (FStar_List.map print_typ lt)
in (FStar_All.pipe_right _180_278 (FStar_Format.combine comma)))
in (_180_279)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_280)
in (FStar_Format.reduce _180_281))
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (s, _83_344) -> begin
(let _180_284 = (let _180_283 = (let _180_282 = (jstr_escape s)
in (Prims.strcat _180_282 "\""))
in (Prims.strcat "\"" _180_283))
in (FStar_Format.text _180_284))
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (n, _83_349) -> begin
(FStar_Format.text (FStar_Util.string_of_float n))
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (b, _83_354) -> begin
(let _180_285 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_285))
end
| FStar_Extraction_JavaScript_Ast.JST_Exists -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (n, _83_360) -> begin
(print_gen_t n)
end))
and print_args : (FStar_Extraction_JavaScript_Ast.identifier_t * FStar_Extraction_JavaScript_Ast.typ) Prims.list  ->  FStar_Format.doc = (fun args -> (let _180_296 = (let _180_295 = (let _180_294 = (FStar_List.map (fun _83_369 -> (match (_83_369) with
| ((id, _83_366), t) -> begin
(let _180_293 = (let _180_292 = (let _180_288 = (jstr_escape id)
in (FStar_Format.text _180_288))
in (let _180_291 = (let _180_290 = (let _180_289 = (print_typ t)
in (_180_289)::[])
in ((FStar_Format.text ":"))::_180_290)
in (_180_292)::_180_291))
in (FStar_Format.reduce _180_293))
end)) args)
in (FStar_All.pipe_right _180_294 (FStar_Format.combine comma)))
in (_180_295)::[])
in (FStar_Format.reduce _180_296)))
and print_gen_t : FStar_Extraction_JavaScript_Ast.generic_t  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
| FStar_Extraction_JavaScript_Ast.Unqualified (id, _83_373) -> begin
(let _180_298 = (jstr_escape id)
in (FStar_Format.text _180_298))
end
| FStar_Extraction_JavaScript_Ast.Qualified (g, (id, _83_379)) -> begin
(let _180_304 = (let _180_303 = (print_gen_t g)
in (let _180_302 = (let _180_301 = (let _180_300 = (let _180_299 = (jstr_escape id)
in (FStar_Format.text _180_299))
in (_180_300)::[])
in ((FStar_Format.text ","))::_180_301)
in (_180_303)::_180_302))
in (FStar_Format.reduce _180_304))
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_308 = (let _180_307 = (let _180_306 = (jstr_escape s)
in (Prims.strcat _180_306 "\""))
in (Prims.strcat "\"" _180_307))
in (FStar_Format.text _180_308))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_309 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_309))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_392) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JSV_Var -> begin
(FStar_Format.text "var")
end
| FStar_Extraction_JavaScript_Ast.JSV_Let -> begin
(FStar_Format.text "let")
end
| FStar_Extraction_JavaScript_Ast.JSV_Const -> begin
(FStar_Format.text "const")
end))
and print_pattern : FStar_Extraction_JavaScript_Ast.pattern_t  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_400) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_403) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_406) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_409) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_314 = (let _180_313 = (let _180_312 = (print_typ v)
in (_180_312)::[])
in (colon)::_180_313)
in (FStar_Format.reduce _180_314))
end
| None -> begin
(FStar_Format.text "")
end)
in (let _180_317 = (let _180_316 = (let _180_315 = (jstr_escape id)
in (FStar_Format.text _180_315))
in (_180_316)::(r)::[])
in (FStar_Format.reduce _180_317)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_13 -> (match (_83_13) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_429 -> (match (_83_429) with
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
(let _180_323 = (let _180_322 = (let _180_321 = (let _180_320 = (print_typ v)
in (_180_320)::[])
in (ws)::_180_321)
in ((FStar_Format.text ":"))::_180_322)
in (FStar_Format.reduce _180_323))
end
| None -> begin
FStar_Format.empty
end)
in (let _180_337 = (let _180_336 = (let _180_335 = (let _180_334 = (let _180_333 = (print_decl_t typePars)
in (let _180_332 = (let _180_331 = (let _180_325 = (let _180_324 = (FStar_List.map print_pattern pars)
in (FStar_All.pipe_right _180_324 (FStar_Format.combine comma)))
in (FStar_Format.parens _180_325))
in (let _180_330 = (let _180_329 = (let _180_328 = (let _180_327 = (let _180_326 = (print_body body)
in (_180_326)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_327)
in ((FStar_Format.text "{"))::_180_328)
in (returnT)::_180_329)
in (_180_331)::_180_330))
in (_180_333)::_180_332))
in (name)::_180_334)
in (ws)::_180_335)
in ((FStar_Format.text "function"))::_180_336)
in (FStar_Format.reduce _180_337))))
end))





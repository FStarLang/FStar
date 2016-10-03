
open Prims

let semi : FStar_Format.doc = (FStar_Format.text ";")


let comma : FStar_Format.doc = (FStar_Format.text ",")


let dot : FStar_Format.doc = (FStar_Format.text ".")


let colon : FStar_Format.doc = (FStar_Format.text ":")


let lbr : FStar_Format.doc = (FStar_Format.text "[")


let rbr : FStar_Format.doc = (FStar_Format.text "]")


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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_35 = (FStar_All.pipe_right program (FStar_List.map (fun _83_4 -> (match (_83_4) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(pretty_print_statement s)
end))))
in (FStar_All.pipe_right _180_35 FStar_Format.reduce)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (_83_68) -> begin
(pretty_print_statement s)
end
| _83_71 -> begin
(let _180_42 = (let _180_41 = (let _180_40 = (let _180_39 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_39))
in (_180_40)::[])
in (ws)::_180_41)
in (FStar_Format.reduce _180_42))
end))
in (

let f = (fun _83_5 -> (match (_83_5) with
| FStar_Extraction_JavaScript_Ast.JSS_Empty -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_Block (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JSS_Expression (e) -> begin
(let _180_47 = (let _180_46 = (let _180_45 = (pretty_print_exp e)
in (_180_45)::(semi)::[])
in (ws)::_180_46)
in (FStar_Format.reduce _180_47))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_65 = (let _180_64 = (let _180_63 = (let _180_62 = (let _180_48 = (pretty_print_exp c)
in (FStar_Format.parens _180_48))
in (let _180_61 = (let _180_60 = (let _180_59 = (let _180_58 = (optws t)
in (let _180_57 = (let _180_56 = (let _180_55 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_54 = (let _180_53 = (let _180_52 = (let _180_51 = (let _180_50 = (let _180_49 = (optws s)
in (_180_49)::((FStar_Format.text "}"))::[])
in ((match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_If (_83_87) -> begin
ws
end
| _83_90 -> begin
FStar_Format.hardline
end))::_180_50)
in ((FStar_Format.text "{"))::_180_51)
in ((FStar_Format.text "else"))::_180_52)
in (ws)::_180_53)
in (FStar_Format.reduce _180_54))
end)
in (_180_55)::[])
in ((FStar_Format.text "}"))::_180_56)
in (_180_58)::_180_57))
in (FStar_Format.hardline)::_180_59)
in ((FStar_Format.text "{"))::_180_60)
in (_180_62)::_180_61))
in ((FStar_Format.text "if"))::_180_63)
in (ws)::_180_64)
in (FStar_Format.reduce _180_65))
end
| FStar_Extraction_JavaScript_Ast.JSS_Labeled ((l, t), s) -> begin
(let _180_73 = (let _180_72 = (let _180_71 = (let _180_66 = (jstr_escape l)
in (FStar_Format.text _180_66))
in (let _180_70 = (let _180_69 = (let _180_68 = (let _180_67 = (optws s)
in (_180_67)::[])
in (FStar_Format.hardline)::_180_68)
in ((FStar_Format.text ":"))::_180_69)
in (_180_71)::_180_70))
in (ws)::_180_72)
in (FStar_Format.reduce _180_73))
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
(let _180_81 = (let _180_80 = (let _180_79 = (let _180_78 = (match (i) with
| None -> begin
FStar_Format.empty
end
| Some (v, t) -> begin
(let _180_77 = (let _180_76 = (let _180_75 = (let _180_74 = (jstr_escape v)
in (FStar_Format.text _180_74))
in (_180_75)::[])
in (ws)::_180_76)
in (FStar_Format.reduce _180_77))
end)
in (_180_78)::(semi)::[])
in ((FStar_Format.text "continue"))::_180_79)
in (ws)::_180_80)
in (FStar_Format.reduce _180_81))
end
| FStar_Extraction_JavaScript_Ast.JSS_With (e, s) -> begin
(let _180_89 = (let _180_88 = (let _180_87 = (let _180_86 = (let _180_82 = (pretty_print_exp e)
in (FStar_Format.parens _180_82))
in (let _180_85 = (let _180_84 = (let _180_83 = (optws s)
in (_180_83)::[])
in (FStar_Format.hardline)::_180_84)
in (_180_86)::_180_85))
in ((FStar_Format.text "with"))::_180_87)
in (ws)::_180_88)
in (FStar_Format.reduce _180_89))
end
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_117), _83_120, t) -> begin
(let _180_96 = (let _180_95 = (let _180_94 = (let _180_90 = (jstr_escape id)
in (FStar_Format.text _180_90))
in (let _180_93 = (let _180_92 = (let _180_91 = (print_typ t)
in (_180_91)::((FStar_Format.text ";"))::[])
in ((FStar_Format.text "="))::_180_92)
in (_180_94)::_180_93))
in ((FStar_Format.text "type "))::_180_95)
in (FStar_Format.reduce _180_96))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_118 = (let _180_117 = (let _180_116 = (let _180_115 = (let _180_97 = (pretty_print_exp e)
in (FStar_Format.parens _180_97))
in (let _180_114 = (let _180_113 = (let _180_112 = (let _180_111 = (let _180_110 = (let _180_109 = (let _180_108 = (FStar_List.map (fun _83_130 -> (match (_83_130) with
| (e, l) -> begin
(let _180_107 = (let _180_106 = (let _180_105 = (let _180_104 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_103 = (let _180_102 = (let _180_101 = (let _180_100 = (let _180_99 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_99))
in (_180_100)::[])
in (FStar_Format.hardline)::_180_101)
in (colon)::_180_102)
in (_180_104)::_180_103))
in ((FStar_Format.text "case "))::_180_105)
in (ws)::_180_106)
in (FStar_Format.reduce _180_107))
end)) lcase)
in (FStar_Format.combine FStar_Format.hardline _180_108))
in (_180_109)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_110)
in ((FStar_Format.text "{"))::_180_111)
in (ws)::_180_112)
in (FStar_Format.hardline)::_180_113)
in (_180_115)::_180_114))
in ((FStar_Format.text "switch"))::_180_116)
in (ws)::_180_117)
in (FStar_Format.reduce _180_118))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_125 = (let _180_124 = (let _180_123 = (let _180_122 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_121 = (let _180_120 = (let _180_119 = (pretty_print_exp v)
in (_180_119)::[])
in (ws)::_180_120)
in (FStar_Format.reduce _180_121))
end)
in (_180_122)::(semi)::[])
in ((FStar_Format.text "return"))::_180_123)
in (ws)::_180_124)
in (FStar_Format.reduce _180_125))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_129 = (let _180_128 = (let _180_127 = (let _180_126 = (pretty_print_exp e)
in (_180_126)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_127)
in (ws)::_180_128)
in (FStar_Format.reduce _180_129))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (_83_142) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_137 = (let _180_136 = (let _180_135 = (let _180_134 = (let _180_130 = (pretty_print_exp e)
in (FStar_Format.parens _180_130))
in (let _180_133 = (let _180_132 = (let _180_131 = (optws s)
in (_180_131)::[])
in (FStar_Format.hardline)::_180_132)
in (_180_134)::_180_133))
in ((FStar_Format.text "while"))::_180_135)
in (ws)::_180_136)
in (FStar_Format.reduce _180_137))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_149 = (let _180_148 = (let _180_147 = (let _180_146 = (let _180_145 = (optws s)
in (let _180_144 = (let _180_143 = (pretty_print_statement s)
in (let _180_142 = (let _180_141 = (let _180_140 = (let _180_139 = (let _180_138 = (pretty_print_exp e)
in (FStar_Format.parens _180_138))
in (_180_139)::(semi)::[])
in ((FStar_Format.text "while"))::_180_140)
in (ws)::_180_141)
in (_180_143)::_180_142))
in (_180_145)::_180_144))
in (FStar_Format.hardline)::_180_146)
in ((FStar_Format.text "do"))::_180_147)
in (ws)::_180_148)
in (FStar_Format.reduce _180_149))
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
(let _180_166 = (let _180_165 = (let _180_164 = (print_kind_var k)
in (let _180_163 = (let _180_162 = (let _180_161 = (let _180_160 = (FStar_List.map (fun _83_181 -> (match (_83_181) with
| (p, e) -> begin
(let _180_159 = (let _180_158 = (print_pattern p)
in (let _180_157 = (let _180_156 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_155 = (let _180_154 = (let _180_153 = (let _180_152 = (let _180_151 = (pretty_print_exp v)
in (_180_151)::[])
in (ws)::_180_152)
in ((FStar_Format.text "="))::_180_153)
in (ws)::_180_154)
in (FStar_Format.reduce _180_155))
end)
in (_180_156)::[])
in (_180_158)::_180_157))
in (FStar_Format.reduce _180_159))
end)) l)
in (FStar_Format.combine comma _180_160))
in (_180_161)::(semi)::[])
in (ws)::_180_162)
in (_180_164)::_180_163))
in (ws)::_180_165)
in (FStar_Format.reduce _180_166))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_186) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_189) -> begin
semi
end))
in (let _180_168 = (let _180_167 = (f p)
in (_180_167)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_168)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_170 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_170)))
and pretty_print_elist : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_172 = (FStar_List.map print_pattern l)
in (FStar_All.pipe_right _180_172 (FStar_Format.combine comma))))
and pt : FStar_Format.doc  ->  Prims.bool  ->  FStar_Format.doc = (fun s b -> if b then begin
(FStar_Format.parens s)
end else begin
s
end)
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_179 = (let _180_178 = (let _180_177 = (let _180_176 = (FStar_List.map pretty_print_exp v)
in (FStar_All.pipe_right _180_176 (FStar_Format.combine comma)))
in (_180_177)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_178)
in (FStar_Format.reduce _180_179))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_183 = (let _180_182 = (let _180_181 = (let _180_180 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_180 (FStar_Format.combine comma)))
in (_180_181)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_182)
in (FStar_Format.reduce _180_183))
end
| FStar_Extraction_JavaScript_Ast.JSE_Function (f) -> begin
(pretty_print_fun f)
end
| FStar_Extraction_JavaScript_Ast.JSE_ArrowFunction (f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Sequence (e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Unary (o, e) -> begin
(let _180_187 = (let _180_186 = (print_op_un o)
in (let _180_185 = (let _180_184 = (pretty_print_exp e)
in (_180_184)::[])
in (_180_186)::_180_185))
in (FStar_Format.reduce _180_187))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_192 = (let _180_191 = (pretty_print_exp e1)
in (let _180_190 = (let _180_189 = (let _180_188 = (pretty_print_exp e2)
in (_180_188)::[])
in ((print_op_bin o))::_180_189)
in (_180_191)::_180_190))
in (FStar_Format.reduce _180_192))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_198 = (let _180_197 = (pretty_print_exp e1)
in (let _180_196 = (let _180_195 = (print_op_log o)
in (let _180_194 = (let _180_193 = (pretty_print_exp e2)
in (_180_193)::[])
in (_180_195)::_180_194))
in (_180_197)::_180_196))
in (FStar_Format.reduce _180_198))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_204 = (let _180_203 = (pretty_print_exp e)
in (let _180_202 = (let _180_201 = (let _180_200 = (let _180_199 = (FStar_List.map pretty_print_exp l)
in (FStar_All.pipe_right _180_199 (FStar_Format.combine comma)))
in (_180_200)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text "("))::_180_201)
in (_180_203)::_180_202))
in (FStar_Format.reduce _180_204))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_209 = (let _180_208 = (pretty_print_exp o)
in (let _180_207 = (let _180_206 = (let _180_205 = (pretty_print_propmem p)
in (_180_205)::[])
in ((FStar_Format.text "."))::_180_206)
in (_180_208)::_180_207))
in (FStar_Format.reduce _180_209))
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
(let _180_217 = (let _180_216 = (let _180_210 = (jstr_escape id)
in (FStar_Format.text _180_210))
in (let _180_215 = (let _180_214 = (match (t) with
| Some (v) -> begin
(let _180_213 = (let _180_212 = (let _180_211 = (print_typ v)
in (_180_211)::[])
in ((FStar_Format.text ":"))::_180_212)
in (FStar_Format.reduce _180_213))
end
| None -> begin
(FStar_Format.text "")
end)
in (_180_214)::[])
in (_180_216)::_180_215))
in (FStar_Format.reduce _180_217))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
semi
end))
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_284) -> begin
(let _180_223 = (let _180_222 = (pretty_print_prop_key k)
in (let _180_221 = (let _180_220 = (let _180_219 = (pretty_print_exp e)
in (_180_219)::[])
in ((FStar_Format.text ":"))::_180_220)
in (_180_222)::_180_221))
in (FStar_Format.reduce _180_223))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_225 = (jstr_escape id)
in (FStar_Format.text _180_225))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_227 = (jstr_escape i)
in (FStar_Format.text _180_227))
end
| FStar_Extraction_JavaScript_Ast.JSPM_Expression (e) -> begin
(pretty_print_exp e)
end))
and print_typ : FStar_Extraction_JavaScript_Ast.typ  ->  FStar_Format.doc = (fun _83_7 -> (match (_83_7) with
| FStar_Extraction_JavaScript_Ast.JST_Any -> begin
(FStar_Format.text "any")
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
| FStar_Extraction_JavaScript_Ast.JST_Nullable (_83_313) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Function (_83_316) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Object (lp, _83_320, _83_322) -> begin
(let _180_238 = (let _180_237 = (let _180_236 = (let _180_235 = (FStar_List.map (fun _83_327 -> (match (_83_327) with
| (k, t) -> begin
(let _180_234 = (let _180_233 = (pretty_print_prop_key k)
in (let _180_232 = (let _180_231 = (let _180_230 = (print_typ t)
in (_180_230)::[])
in ((FStar_Format.text ":"))::_180_231)
in (_180_233)::_180_232))
in (FStar_Format.reduce _180_234))
end)) lp)
in (FStar_All.pipe_right _180_235 (FStar_Format.combine comma)))
in (_180_236)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_237)
in (FStar_Format.reduce _180_238))
end
| FStar_Extraction_JavaScript_Ast.JST_Array (_83_329) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Union (_83_332) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Intersection (_83_335) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Typeof (_83_338) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Tuple (_83_341) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_StringLiteral (_83_344) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_NumberLiteral (_83_347) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_BooleanLiteral (_83_350) -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Exists -> begin
(FStar_Format.text "!!!")
end
| FStar_Extraction_JavaScript_Ast.JST_Generic (_83_354) -> begin
(FStar_Format.text "!!!")
end))
and print_literal : FStar_Extraction_JavaScript_Ast.value_t  ->  FStar_Format.doc = (fun _83_8 -> (match (_83_8) with
| FStar_Extraction_JavaScript_Ast.JSV_String (s) -> begin
(let _180_242 = (let _180_241 = (let _180_240 = (jstr_escape s)
in (Prims.strcat _180_240 "\""))
in (Prims.strcat "\"" _180_241))
in (FStar_Format.text _180_242))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_243 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_243))
end
| FStar_Extraction_JavaScript_Ast.JSV_Null -> begin
(FStar_Format.text "null")
end
| FStar_Extraction_JavaScript_Ast.JSV_Number (f) -> begin
(FStar_Format.text (FStar_Util.string_of_float f))
end
| FStar_Extraction_JavaScript_Ast.JSV_RegExp (_83_365) -> begin
(FStar_Format.text "!!")
end))
and print_kind_var : FStar_Extraction_JavaScript_Ast.kind_var_t  ->  FStar_Format.doc = (fun _83_9 -> (match (_83_9) with
| FStar_Extraction_JavaScript_Ast.JSV_Var -> begin
(FStar_Format.text "var")
end
| FStar_Extraction_JavaScript_Ast.JSV_Let -> begin
(FStar_Format.text "let")
end
| FStar_Extraction_JavaScript_Ast.JSV_Const -> begin
(FStar_Format.text "const")
end))
and print_pattern : FStar_Extraction_JavaScript_Ast.pattern_t  ->  FStar_Format.doc = (fun _83_10 -> (match (_83_10) with
| FStar_Extraction_JavaScript_Ast.JGP_Object (_83_373) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Array (_83_376) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Assignment (_83_379) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Expression (_83_382) -> begin
(FStar_Format.text "!!")
end
| FStar_Extraction_JavaScript_Ast.JGP_Identifier (id, t) -> begin
(

let r = (match (t) with
| Some (v) -> begin
(let _180_248 = (let _180_247 = (let _180_246 = (print_typ v)
in (_180_246)::[])
in (colon)::_180_247)
in (FStar_Format.reduce _180_248))
end
| None -> begin
(FStar_Format.text "")
end)
in (let _180_251 = (let _180_250 = (let _180_249 = (jstr_escape id)
in (FStar_Format.text _180_249))
in (_180_250)::(r)::[])
in (FStar_Format.reduce _180_251)))
end))
and print_body : FStar_Extraction_JavaScript_Ast.body_t  ->  FStar_Format.doc = (fun _83_11 -> (match (_83_11) with
| FStar_Extraction_JavaScript_Ast.JS_BodyBlock (l) -> begin
(pretty_print_statements l)
end
| FStar_Extraction_JavaScript_Ast.JS_BodyExpression (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_fun : FStar_Extraction_JavaScript_Ast.function_t  ->  FStar_Format.doc = (fun _83_402 -> (match (_83_402) with
| (n, pars, body, t, typePars) -> begin
(

let name = (match (n) with
| Some (v) -> begin
(Prims.fst v)
end
| None -> begin
""
end)
in (

let reternT = (match (t) with
| Some (v) -> begin
(let _180_257 = (let _180_256 = (let _180_255 = (let _180_254 = (print_typ v)
in (_180_254)::[])
in (ws)::_180_255)
in ((FStar_Format.text ":"))::_180_256)
in (FStar_Format.reduce _180_257))
end
| None -> begin
(FStar_Format.text "")
end)
in (let _180_267 = (let _180_266 = (let _180_265 = (let _180_264 = (let _180_263 = (let _180_258 = (pretty_print_elist pars)
in (FStar_Format.parens _180_258))
in (let _180_262 = (let _180_261 = (let _180_260 = (let _180_259 = (print_body body)
in (_180_259)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_260)
in ((FStar_Format.text "{"))::_180_261)
in (_180_263)::_180_262))
in ((FStar_Format.text name))::_180_264)
in (ws)::_180_265)
in ((FStar_Format.text "function"))::_180_266)
in (FStar_Format.reduce _180_267))))
end))
and print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JSL_Or -> begin
(FStar_Format.text "||")
end
| FStar_Extraction_JavaScript_Ast.JSL_And -> begin
(FStar_Format.text "&&")
end))





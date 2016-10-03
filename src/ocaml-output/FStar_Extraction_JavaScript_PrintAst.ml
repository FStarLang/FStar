
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


let rec pretty_print : FStar_Extraction_JavaScript_Ast.t  ->  FStar_Format.doc = (fun program -> (let _180_36 = (FStar_All.pipe_right program (FStar_List.map (fun _83_4 -> (match (_83_4) with
| FStar_Extraction_JavaScript_Ast.JS_Statement (s) -> begin
(pretty_print_statement s)
end))))
in (FStar_All.pipe_right _180_36 FStar_Format.reduce)))
and pretty_print_statement : FStar_Extraction_JavaScript_Ast.statement_t  ->  FStar_Format.doc = (fun p -> (

let optws = (fun s -> (match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_Block (_83_68) -> begin
(pretty_print_statement s)
end
| _83_71 -> begin
(let _180_43 = (let _180_42 = (let _180_41 = (let _180_40 = (pretty_print_statement s)
in (FStar_Format.nest (Prims.parse_int "1") _180_40))
in (_180_41)::[])
in (ws)::_180_42)
in (FStar_Format.reduce _180_43))
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
(let _180_48 = (let _180_47 = (let _180_46 = (pretty_print_exp e)
in (_180_46)::(semi)::[])
in (ws)::_180_47)
in (FStar_Format.reduce _180_48))
end
| FStar_Extraction_JavaScript_Ast.JSS_If (c, t, f) -> begin
(let _180_66 = (let _180_65 = (let _180_64 = (let _180_63 = (let _180_49 = (pretty_print_exp c)
in (FStar_Format.parens _180_49))
in (let _180_62 = (let _180_61 = (let _180_60 = (let _180_59 = (optws t)
in (let _180_58 = (let _180_57 = (let _180_56 = (match (f) with
| None -> begin
FStar_Format.empty
end
| Some (s) -> begin
(let _180_55 = (let _180_54 = (let _180_53 = (let _180_52 = (let _180_51 = (let _180_50 = (optws s)
in (_180_50)::((FStar_Format.text "}"))::[])
in ((match (s) with
| FStar_Extraction_JavaScript_Ast.JSS_If (_83_87) -> begin
ws
end
| _83_90 -> begin
FStar_Format.hardline
end))::_180_51)
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
in ((FStar_Format.text ":"))::_180_70)
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
| FStar_Extraction_JavaScript_Ast.JSS_TypeAlias ((id, _83_117), _83_120, t) -> begin
(let _180_97 = (let _180_96 = (let _180_95 = (let _180_91 = (jstr_escape id)
in (FStar_Format.text _180_91))
in (let _180_94 = (let _180_93 = (let _180_92 = (print_typ t)
in (_180_92)::((FStar_Format.text ";"))::[])
in ((FStar_Format.text "="))::_180_93)
in (_180_95)::_180_94))
in ((FStar_Format.text "type "))::_180_96)
in (FStar_Format.reduce _180_97))
end
| FStar_Extraction_JavaScript_Ast.JSS_Switch (e, lcase) -> begin
(let _180_119 = (let _180_118 = (let _180_117 = (let _180_116 = (let _180_98 = (pretty_print_exp e)
in (FStar_Format.parens _180_98))
in (let _180_115 = (let _180_114 = (let _180_113 = (let _180_112 = (let _180_111 = (let _180_110 = (let _180_109 = (FStar_List.map (fun _83_130 -> (match (_83_130) with
| (e, l) -> begin
(let _180_108 = (let _180_107 = (let _180_106 = (let _180_105 = (match (e) with
| Some (v) -> begin
(pretty_print_exp v)
end
| None -> begin
(FStar_Format.text "default")
end)
in (let _180_104 = (let _180_103 = (let _180_102 = (let _180_101 = (let _180_100 = (pretty_print_statements l)
in (FStar_Format.nest (Prims.parse_int "1") _180_100))
in (_180_101)::[])
in (FStar_Format.hardline)::_180_102)
in (colon)::_180_103)
in (_180_105)::_180_104))
in ((FStar_Format.text "case "))::_180_106)
in (ws)::_180_107)
in (FStar_Format.reduce _180_108))
end)) lcase)
in (FStar_Format.combine FStar_Format.hardline _180_109))
in (_180_110)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_111)
in ((FStar_Format.text "{"))::_180_112)
in (ws)::_180_113)
in (FStar_Format.hardline)::_180_114)
in (_180_116)::_180_115))
in ((FStar_Format.text "switch"))::_180_117)
in (ws)::_180_118)
in (FStar_Format.reduce _180_119))
end
| FStar_Extraction_JavaScript_Ast.JSS_Return (e) -> begin
(let _180_126 = (let _180_125 = (let _180_124 = (let _180_123 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_122 = (let _180_121 = (let _180_120 = (pretty_print_exp v)
in (_180_120)::[])
in (ws)::_180_121)
in (FStar_Format.reduce _180_122))
end)
in (_180_123)::(semi)::[])
in ((FStar_Format.text "return"))::_180_124)
in (ws)::_180_125)
in (FStar_Format.reduce _180_126))
end
| FStar_Extraction_JavaScript_Ast.JSS_Throw (e) -> begin
(let _180_130 = (let _180_129 = (let _180_128 = (let _180_127 = (pretty_print_exp e)
in (_180_127)::(semi)::[])
in ((FStar_Format.text "throw "))::_180_128)
in (ws)::_180_129)
in (FStar_Format.reduce _180_130))
end
| FStar_Extraction_JavaScript_Ast.JSS_Try (_83_142) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_While (e, s) -> begin
(let _180_138 = (let _180_137 = (let _180_136 = (let _180_135 = (let _180_131 = (pretty_print_exp e)
in (FStar_Format.parens _180_131))
in (let _180_134 = (let _180_133 = (let _180_132 = (optws s)
in (_180_132)::[])
in (FStar_Format.hardline)::_180_133)
in (_180_135)::_180_134))
in ((FStar_Format.text "while"))::_180_136)
in (ws)::_180_137)
in (FStar_Format.reduce _180_138))
end
| FStar_Extraction_JavaScript_Ast.JSS_DoWhile (s, e) -> begin
(let _180_150 = (let _180_149 = (let _180_148 = (let _180_147 = (let _180_146 = (optws s)
in (let _180_145 = (let _180_144 = (pretty_print_statement s)
in (let _180_143 = (let _180_142 = (let _180_141 = (let _180_140 = (let _180_139 = (pretty_print_exp e)
in (FStar_Format.parens _180_139))
in (_180_140)::(semi)::[])
in ((FStar_Format.text "while"))::_180_141)
in (ws)::_180_142)
in (_180_144)::_180_143))
in (_180_146)::_180_145))
in (FStar_Format.hardline)::_180_147)
in ((FStar_Format.text "do"))::_180_148)
in (ws)::_180_149)
in (FStar_Format.reduce _180_150))
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
(let _180_167 = (let _180_166 = (let _180_165 = (print_kind_var k)
in (let _180_164 = (let _180_163 = (let _180_162 = (let _180_161 = (FStar_List.map (fun _83_181 -> (match (_83_181) with
| (p, e) -> begin
(let _180_160 = (let _180_159 = (print_pattern p)
in (let _180_158 = (let _180_157 = (match (e) with
| None -> begin
FStar_Format.empty
end
| Some (v) -> begin
(let _180_156 = (let _180_155 = (let _180_154 = (let _180_153 = (let _180_152 = (pretty_print_exp v)
in (_180_152)::[])
in (ws)::_180_153)
in ((FStar_Format.text "="))::_180_154)
in (ws)::_180_155)
in (FStar_Format.reduce _180_156))
end)
in (_180_157)::[])
in (_180_159)::_180_158))
in (FStar_Format.reduce _180_160))
end)) l)
in (FStar_Format.combine comma _180_161))
in (_180_162)::(semi)::[])
in (ws)::_180_163)
in (_180_165)::_180_164))
in (ws)::_180_166)
in (FStar_Format.reduce _180_167))
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareVariable (_83_186) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSS_DeclareFunction (_83_189) -> begin
semi
end))
in (let _180_169 = (let _180_168 = (f p)
in (_180_168)::(FStar_Format.hardline)::[])
in (FStar_Format.reduce _180_169)))))
and pretty_print_statements : FStar_Extraction_JavaScript_Ast.statement_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_171 = (FStar_List.map pretty_print_statement l)
in (FStar_Format.reduce _180_171)))
and pretty_print_elist : FStar_Extraction_JavaScript_Ast.pattern_t Prims.list  ->  FStar_Format.doc = (fun l -> (let _180_173 = (FStar_List.map print_pattern l)
in (FStar_All.pipe_right _180_173 (FStar_Format.combine comma))))
and pt : FStar_Format.doc  ->  Prims.bool  ->  FStar_Format.doc = (fun s b -> if b then begin
(FStar_Format.parens s)
end else begin
s
end)
and pretty_print_exp_gen : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = (fun _83_6 -> (match (_83_6) with
| FStar_Extraction_JavaScript_Ast.JSE_This -> begin
(FStar_Format.text "this")
end
| FStar_Extraction_JavaScript_Ast.JSE_Array (l) -> begin
(match (l) with
| Some (v) -> begin
(let _180_180 = (let _180_179 = (let _180_178 = (let _180_177 = (FStar_List.map pretty_print_exp_gen v)
in (FStar_All.pipe_right _180_177 (FStar_Format.combine comma)))
in (_180_178)::((FStar_Format.text "]"))::[])
in ((FStar_Format.text "["))::_180_179)
in (FStar_Format.reduce _180_180))
end
| None -> begin
(FStar_Format.reduce (((FStar_Format.text "["))::((FStar_Format.text "]"))::[]))
end)
end
| FStar_Extraction_JavaScript_Ast.JSE_Object (l) -> begin
(let _180_184 = (let _180_183 = (let _180_182 = (let _180_181 = (FStar_List.map pretty_print_obj l)
in (FStar_All.pipe_right _180_181 (FStar_Format.combine comma)))
in (_180_182)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_183)
in (FStar_Format.reduce _180_184))
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
(let _180_188 = (let _180_187 = (print_op_un o)
in (let _180_186 = (let _180_185 = (pretty_print_exp_gen e)
in (_180_185)::[])
in (_180_187)::_180_186))
in (FStar_Format.reduce _180_188))
end
| FStar_Extraction_JavaScript_Ast.JSE_Binary (o, e1, e2) -> begin
(let _180_193 = (let _180_192 = (pretty_print_exp_gen e1)
in (let _180_191 = (let _180_190 = (let _180_189 = (pretty_print_exp_gen e2)
in (_180_189)::[])
in ((print_op_bin o))::_180_190)
in (_180_192)::_180_191))
in (FStar_Format.reduce _180_193))
end
| FStar_Extraction_JavaScript_Ast.JSE_Assignment (p, e) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Update (o, e, b) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Logical (o, e1, e2) -> begin
(let _180_199 = (let _180_198 = (pretty_print_exp_gen e1)
in (let _180_197 = (let _180_196 = (print_op_log o)
in (let _180_195 = (let _180_194 = (pretty_print_exp_gen e2)
in (_180_194)::[])
in (_180_196)::_180_195))
in (_180_198)::_180_197))
in (FStar_Format.reduce _180_199))
end
| FStar_Extraction_JavaScript_Ast.JSE_Conditional (c, e, f) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_New (e, l) -> begin
semi
end
| FStar_Extraction_JavaScript_Ast.JSE_Call (e, l) -> begin
(let _180_205 = (let _180_204 = (pretty_print_exp_gen e)
in (let _180_203 = (let _180_202 = (let _180_201 = (let _180_200 = (FStar_List.map pretty_print_exp_gen l)
in (FStar_All.pipe_right _180_200 (FStar_Format.combine comma)))
in (_180_201)::((FStar_Format.text ")"))::[])
in ((FStar_Format.text "("))::_180_202)
in (_180_204)::_180_203))
in (FStar_Format.reduce _180_205))
end
| FStar_Extraction_JavaScript_Ast.JSE_Member (o, p) -> begin
(let _180_210 = (let _180_209 = (pretty_print_exp_gen o)
in (let _180_208 = (let _180_207 = (let _180_206 = (pretty_print_propmem p)
in (_180_206)::[])
in ((FStar_Format.text "."))::_180_207)
in (_180_209)::_180_208))
in (FStar_Format.reduce _180_210))
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
(let _180_218 = (let _180_217 = (let _180_211 = (jstr_escape id)
in (FStar_Format.text _180_211))
in (let _180_216 = (let _180_215 = (match (t) with
| Some (v) -> begin
(let _180_214 = (let _180_213 = (let _180_212 = (print_typ v)
in (_180_212)::[])
in ((FStar_Format.text ":"))::_180_213)
in (FStar_Format.reduce _180_214))
end
| None -> begin
(FStar_Format.text "")
end)
in (_180_215)::[])
in (_180_217)::_180_216))
in (FStar_Format.reduce _180_218))
end
| FStar_Extraction_JavaScript_Ast.JSE_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSE_TypeCast (e, t) -> begin
semi
end))
and pretty_print_exp : FStar_Extraction_JavaScript_Ast.expression_t  ->  FStar_Format.doc = pretty_print_exp_gen
and pretty_print_obj : FStar_Extraction_JavaScript_Ast.property_obj_t  ->  FStar_Format.doc = (fun el -> (match (el) with
| FStar_Extraction_JavaScript_Ast.JSPO_Property (k, e, _83_284) -> begin
(let _180_224 = (let _180_223 = (pretty_print_prop_key k)
in (let _180_222 = (let _180_221 = (let _180_220 = (pretty_print_exp e)
in (_180_220)::[])
in ((FStar_Format.text ":"))::_180_221)
in (_180_223)::_180_222))
in (FStar_Format.reduce _180_224))
end
| FStar_Extraction_JavaScript_Ast.JSPO_SpreadProperty (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_prop_key : FStar_Extraction_JavaScript_Ast.object_prop_key_t  ->  FStar_Format.doc = (fun k -> (match (k) with
| FStar_Extraction_JavaScript_Ast.JSO_Literal (l) -> begin
(print_literal (Prims.fst l))
end
| FStar_Extraction_JavaScript_Ast.JSO_Identifier (id, t) -> begin
(let _180_226 = (jstr_escape id)
in (FStar_Format.text _180_226))
end
| FStar_Extraction_JavaScript_Ast.JSO_Computed (e) -> begin
(pretty_print_exp e)
end))
and pretty_print_propmem : FStar_Extraction_JavaScript_Ast.propmem_t  ->  FStar_Format.doc = (fun p -> (match (p) with
| FStar_Extraction_JavaScript_Ast.JSPM_Identifier (i, t) -> begin
(let _180_228 = (jstr_escape i)
in (FStar_Format.text _180_228))
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
(let _180_239 = (let _180_238 = (let _180_237 = (let _180_236 = (FStar_List.map (fun _83_327 -> (match (_83_327) with
| (k, t) -> begin
(let _180_235 = (let _180_234 = (pretty_print_prop_key k)
in (let _180_233 = (let _180_232 = (let _180_231 = (print_typ t)
in (_180_231)::[])
in ((FStar_Format.text ":"))::_180_232)
in (_180_234)::_180_233))
in (FStar_Format.reduce _180_235))
end)) lp)
in (FStar_All.pipe_right _180_236 (FStar_Format.combine comma)))
in (_180_237)::((FStar_Format.text "}"))::[])
in ((FStar_Format.text "{"))::_180_238)
in (FStar_Format.reduce _180_239))
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
(let _180_243 = (let _180_242 = (let _180_241 = (jstr_escape s)
in (Prims.strcat _180_241 "\""))
in (Prims.strcat "\"" _180_242))
in (FStar_Format.text _180_243))
end
| FStar_Extraction_JavaScript_Ast.JSV_Boolean (b) -> begin
(let _180_244 = (FStar_Util.string_of_bool b)
in (FStar_Format.text _180_244))
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
(let _180_249 = (let _180_248 = (let _180_247 = (print_typ v)
in (_180_247)::[])
in (colon)::_180_248)
in (FStar_Format.reduce _180_249))
end
| None -> begin
(FStar_Format.text "")
end)
in (let _180_252 = (let _180_251 = (let _180_250 = (jstr_escape id)
in (FStar_Format.text _180_250))
in (_180_251)::(r)::[])
in (FStar_Format.reduce _180_252)))
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
(let _180_258 = (let _180_257 = (let _180_256 = (let _180_255 = (print_typ v)
in (_180_255)::[])
in (ws)::_180_256)
in ((FStar_Format.text ":"))::_180_257)
in (FStar_Format.reduce _180_258))
end
| None -> begin
(FStar_Format.text "")
end)
in (let _180_268 = (let _180_267 = (let _180_266 = (let _180_265 = (let _180_264 = (let _180_259 = (pretty_print_elist pars)
in (FStar_Format.parens _180_259))
in (let _180_263 = (let _180_262 = (let _180_261 = (let _180_260 = (print_body body)
in (_180_260)::((FStar_Format.text "}"))::[])
in (FStar_Format.hardline)::_180_261)
in ((FStar_Format.text "{"))::_180_262)
in (_180_264)::_180_263))
in ((FStar_Format.text name))::_180_265)
in (ws)::_180_266)
in ((FStar_Format.text "function"))::_180_267)
in (FStar_Format.reduce _180_268))))
end))
and print_op_log : FStar_Extraction_JavaScript_Ast.op_log  ->  FStar_Format.doc = (fun _83_12 -> (match (_83_12) with
| FStar_Extraction_JavaScript_Ast.JSL_Or -> begin
(FStar_Format.text "||")
end
| FStar_Extraction_JavaScript_Ast.JSL_And -> begin
(FStar_Format.text "&&")
end))





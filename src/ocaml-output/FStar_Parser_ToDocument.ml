
open Prims

let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.document_of_string s))


let doc_of_option = (fun n f x -> (match (x) with
| None -> begin
n
end
| Some (x') -> begin
(f x')
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _67_14 -> (match (_67_14) with
| (comment, keywords) -> begin
(let _164_24 = (let _164_23 = (let _164_22 = (str comment)
in (let _164_21 = (let _164_20 = (let _164_19 = (let _164_18 = (str ",")
in (FStar_Pprint.separate_map _164_18 (fun _67_17 -> (match (_67_17) with
| (k, v) -> begin
(let _164_17 = (let _164_16 = (str k)
in (let _164_15 = (let _164_14 = (str "->")
in (let _164_13 = (let _164_12 = (str v)
in (_164_12)::[])
in (_164_14)::_164_13))
in (_164_16)::_164_15))
in (FStar_Pprint.concat _164_17))
end)) keywords))
in (_164_19)::[])
in (FStar_Pprint.space)::_164_20)
in (_164_22)::_164_21))
in (FStar_Pprint.concat _164_23))
in (FStar_Pprint.group _164_24))
end))


let doc_of_let_qualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _67_1 -> (match (_67_1) with
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.Rec -> begin
(str "rec")
end
| FStar_Parser_AST.Mutable -> begin
(str "mutable")
end))


let to_string_l = (fun sep f l -> (let _164_33 = (FStar_List.map f l)
in (FStar_String.concat sep _164_33)))


let doc_of_imp : FStar_Parser_AST.imp  ->  FStar_Pprint.document = (fun _67_2 -> (match (_67_2) with
| FStar_Parser_AST.Hash -> begin
(str "#")
end
| _67_28 -> begin
FStar_Pprint.empty
end))


let doc_of_const : FStar_Const.sconst  ->  FStar_Pprint.document = (fun x -> (match (x) with
| FStar_Const.Const_effect -> begin
(str "eff")
end
| FStar_Const.Const_unit -> begin
(str "()")
end
| FStar_Const.Const_bool (b) -> begin
(str (if b then begin
"true"
end else begin
"false"
end))
end
| FStar_Const.Const_float (x) -> begin
(str (FStar_Util.string_of_float x))
end
| FStar_Const.Const_char (x) -> begin
(let _164_38 = (FStar_Pprint.document_of_char x)
in (FStar_Pprint.squotes _164_38))
end
| FStar_Const.Const_string (bytes, _67_40) -> begin
(let _164_39 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _164_39))
end
| FStar_Const.Const_bytearray (_67_44) -> begin
(str "<bytearray>")
end
| FStar_Const.Const_int (x, _67_48) -> begin
(str x)
end
| FStar_Const.Const_range (r) -> begin
(let _164_40 = (FStar_Range.string_of_range r)
in (str _164_40))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(str "unsupported constant")
end))


let rec doc_of_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun x -> (match (x.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Requires (t, _67_61) -> begin
(let _164_52 = (let _164_51 = (let _164_50 = (let _164_49 = (str "requires")
in (let _164_48 = (let _164_47 = (let _164_46 = (doc_of_term t)
in (_164_46)::[])
in (FStar_Pprint.space)::_164_47)
in (_164_49)::_164_48))
in (FStar_Pprint.concat _164_50))
in (FStar_Pprint.brackets _164_51))
in (FStar_Pprint.group _164_52))
end
| FStar_Parser_AST.Ensures (t, _67_66) -> begin
(let _164_59 = (let _164_58 = (let _164_57 = (let _164_56 = (str "ensures")
in (let _164_55 = (let _164_54 = (let _164_53 = (doc_of_term t)
in (_164_53)::[])
in (FStar_Pprint.space)::_164_54)
in (_164_56)::_164_55))
in (FStar_Pprint.concat _164_57))
in (FStar_Pprint.brackets _164_58))
in (FStar_Pprint.group _164_59))
end
| FStar_Parser_AST.Labeled (t, l, _67_72) -> begin
(let _164_68 = (let _164_67 = (let _164_66 = (let _164_65 = (str "labeled")
in (let _164_64 = (let _164_63 = (let _164_62 = (str l)
in (let _164_61 = (let _164_60 = (doc_of_term t)
in (_164_60)::[])
in (_164_62)::_164_61))
in (FStar_Pprint.space)::_164_63)
in (_164_65)::_164_64))
in (FStar_Pprint.concat _164_66))
in (FStar_Pprint.brackets _164_67))
in (FStar_Pprint.group _164_68))
end
| FStar_Parser_AST.Const (c) -> begin
(let _164_69 = (doc_of_const c)
in (FStar_Pprint.group _164_69))
end
| FStar_Parser_AST.Op (s, xs) -> begin
(let _164_76 = (let _164_75 = (let _164_74 = (str s)
in (let _164_73 = (let _164_72 = (let _164_71 = (let _164_70 = (str ", ")
in (FStar_Pprint.separate_map _164_70 doc_of_term xs))
in (FStar_Pprint.brackets _164_71))
in (_164_72)::[])
in (_164_74)::_164_73))
in (FStar_Pprint.concat _164_75))
in (FStar_Pprint.group _164_76))
end
| FStar_Parser_AST.Tvar (id) -> begin
(let _164_77 = (str id.FStar_Ident.idText)
in (FStar_Pprint.group _164_77))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _164_78 = (str l.FStar_Ident.str)
in (FStar_Pprint.group _164_78))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let _164_90 = (let _164_89 = (let _164_88 = (let _164_87 = (str l.FStar_Ident.str)
in (let _164_86 = (let _164_85 = (let _164_84 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_92 -> (match (_67_92) with
| (a, imp) -> begin
(let _164_83 = (let _164_82 = (doc_of_imp imp)
in (let _164_81 = (let _164_80 = (doc_of_term a)
in (_164_80)::[])
in (_164_82)::_164_81))
in (FStar_Pprint.concat _164_83))
end)) args)
in (_164_84)::[])
in (FStar_Pprint.space)::_164_85)
in (_164_87)::_164_86))
in (FStar_Pprint.concat _164_88))
in (FStar_Pprint.brackets _164_89))
in (FStar_Pprint.group _164_90))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _164_103 = (let _164_102 = (let _164_101 = (let _164_100 = (str "fun")
in (let _164_99 = (let _164_98 = (let _164_97 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat pats)
in (let _164_96 = (let _164_95 = (let _164_94 = (str "->")
in (let _164_93 = (let _164_92 = (let _164_91 = (doc_of_term t)
in (_164_91)::[])
in (FStar_Pprint.space)::_164_92)
in (_164_94)::_164_93))
in (FStar_Pprint.space)::_164_95)
in (_164_97)::_164_96))
in (FStar_Pprint.space)::_164_98)
in (_164_100)::_164_99))
in (FStar_Pprint.concat _164_101))
in (FStar_Pprint.brackets _164_102))
in (FStar_Pprint.group _164_103))
end
| FStar_Parser_AST.App (t1, t2, imp) -> begin
(let _164_111 = (let _164_110 = (let _164_109 = (doc_of_term t1)
in (let _164_108 = (let _164_107 = (let _164_106 = (doc_of_imp imp)
in (let _164_105 = (let _164_104 = (doc_of_term t2)
in (_164_104)::[])
in (_164_106)::_164_105))
in (FStar_Pprint.space)::_164_107)
in (_164_109)::_164_108))
in (FStar_Pprint.concat _164_110))
in (FStar_Pprint.group _164_111))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.Rec, lbs, body) -> begin
(let _164_130 = (let _164_129 = (let _164_128 = (str "let rec")
in (let _164_127 = (let _164_126 = (let _164_125 = (let _164_118 = (str " and ")
in (FStar_Pprint.separate_map _164_118 (fun _67_109 -> (match (_67_109) with
| (p, b) -> begin
(let _164_117 = (let _164_116 = (doc_of_pat p)
in (let _164_115 = (let _164_114 = (let _164_113 = (doc_of_term b)
in (_164_113)::[])
in (FStar_Pprint.equals)::_164_114)
in (_164_116)::_164_115))
in (FStar_Pprint.concat _164_117))
end)) lbs))
in (let _164_124 = (let _164_123 = (let _164_122 = (str "in")
in (let _164_121 = (let _164_120 = (let _164_119 = (doc_of_term body)
in (_164_119)::[])
in (FStar_Pprint.space)::_164_120)
in (_164_122)::_164_121))
in (FStar_Pprint.space)::_164_123)
in (_164_125)::_164_124))
in (FStar_Pprint.space)::_164_126)
in (_164_128)::_164_127))
in (FStar_Pprint.concat _164_129))
in (FStar_Pprint.group _164_130))
end
| FStar_Parser_AST.Let (q, ((pat, tm))::[], body) -> begin
(let _164_150 = (let _164_149 = (let _164_148 = (str "let")
in (let _164_147 = (let _164_146 = (let _164_145 = (doc_of_let_qualifier q)
in (let _164_144 = (let _164_143 = (let _164_142 = (doc_of_pat pat)
in (let _164_141 = (let _164_140 = (let _164_139 = (let _164_138 = (let _164_137 = (doc_of_term tm)
in (let _164_136 = (let _164_135 = (let _164_134 = (str "in")
in (let _164_133 = (let _164_132 = (let _164_131 = (doc_of_term body)
in (_164_131)::[])
in (FStar_Pprint.space)::_164_132)
in (_164_134)::_164_133))
in (FStar_Pprint.space)::_164_135)
in (_164_137)::_164_136))
in (FStar_Pprint.space)::_164_138)
in (FStar_Pprint.equals)::_164_139)
in (FStar_Pprint.space)::_164_140)
in (_164_142)::_164_141))
in (FStar_Pprint.space)::_164_143)
in (_164_145)::_164_144))
in (FStar_Pprint.space)::_164_146)
in (_164_148)::_164_147))
in (FStar_Pprint.concat _164_149))
in (FStar_Pprint.group _164_150))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _164_157 = (let _164_156 = (let _164_155 = (doc_of_term t1)
in (let _164_154 = (let _164_153 = (let _164_152 = (let _164_151 = (doc_of_term t2)
in (_164_151)::[])
in (FStar_Pprint.space)::_164_152)
in (FStar_Pprint.semi)::_164_153)
in (_164_155)::_164_154))
in (FStar_Pprint.concat _164_156))
in (FStar_Pprint.group _164_157))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _164_176 = (let _164_175 = (let _164_174 = (str "if")
in (let _164_173 = (let _164_172 = (let _164_171 = (doc_of_term t1)
in (let _164_170 = (let _164_169 = (let _164_168 = (str "then")
in (let _164_167 = (let _164_166 = (let _164_165 = (let _164_158 = (doc_of_term t2)
in (FStar_Pprint.nest (Prims.parse_int "2") _164_158))
in (let _164_164 = (let _164_163 = (str "else")
in (let _164_162 = (let _164_161 = (let _164_160 = (let _164_159 = (doc_of_term t3)
in (FStar_Pprint.nest (Prims.parse_int "2") _164_159))
in (_164_160)::[])
in (FStar_Pprint.space)::_164_161)
in (_164_163)::_164_162))
in (_164_165)::_164_164))
in (FStar_Pprint.space)::_164_166)
in (_164_168)::_164_167))
in (FStar_Pprint.space)::_164_169)
in (_164_171)::_164_170))
in (FStar_Pprint.space)::_164_172)
in (_164_174)::_164_173))
in (FStar_Pprint.concat _164_175))
in (FStar_Pprint.group _164_176))
end
| FStar_Parser_AST.Match (t, branches) -> begin
(let _164_206 = (let _164_205 = (let _164_204 = (str "match")
in (let _164_203 = (let _164_202 = (let _164_201 = (doc_of_term t)
in (let _164_200 = (let _164_199 = (let _164_198 = (str "with")
in (let _164_197 = (let _164_196 = (let _164_195 = (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_134 -> (match (_67_134) with
| (p, w, e) -> begin
(let _164_194 = (let _164_193 = (str " | ")
in (let _164_192 = (let _164_191 = (doc_of_pat p)
in (let _164_190 = (let _164_189 = (let _164_188 = (match (w) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _164_181 = (let _164_180 = (str "when ")
in (let _164_179 = (let _164_178 = (doc_of_term e)
in (_164_178)::[])
in (_164_180)::_164_179))
in (FStar_Pprint.concat _164_181))
end)
in (let _164_187 = (let _164_186 = (let _164_185 = (str "->")
in (let _164_184 = (let _164_183 = (let _164_182 = (doc_of_term e)
in (_164_182)::[])
in (FStar_Pprint.space)::_164_183)
in (_164_185)::_164_184))
in (FStar_Pprint.space)::_164_186)
in (_164_188)::_164_187))
in (FStar_Pprint.space)::_164_189)
in (_164_191)::_164_190))
in (_164_193)::_164_192))
in (FStar_Pprint.concat _164_194))
end)) branches)
in (_164_195)::[])
in (FStar_Pprint.space)::_164_196)
in (_164_198)::_164_197))
in (FStar_Pprint.space)::_164_199)
in (_164_201)::_164_200))
in (FStar_Pprint.space)::_164_202)
in (_164_204)::_164_203))
in (FStar_Pprint.concat _164_205))
in (FStar_Pprint.group _164_206))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _164_214 = (let _164_213 = (let _164_212 = (doc_of_term t1)
in (let _164_211 = (let _164_210 = (let _164_209 = (let _164_208 = (let _164_207 = (doc_of_term t2)
in (_164_207)::[])
in (FStar_Pprint.space)::_164_208)
in (FStar_Pprint.colon)::_164_209)
in (FStar_Pprint.space)::_164_210)
in (_164_212)::_164_211))
in (FStar_Pprint.concat _164_213))
in (FStar_Pprint.group _164_214))
end
| FStar_Parser_AST.Record (Some (e), fields) -> begin
(let _164_230 = (let _164_229 = (let _164_228 = (let _164_227 = (doc_of_term e)
in (let _164_226 = (let _164_225 = (let _164_224 = (str "with")
in (let _164_223 = (let _164_222 = (let _164_221 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_149 -> (match (_67_149) with
| (l, e) -> begin
(let _164_220 = (let _164_219 = (str l.FStar_Ident.str)
in (let _164_218 = (let _164_217 = (let _164_216 = (doc_of_term e)
in (_164_216)::[])
in (FStar_Pprint.equals)::_164_217)
in (_164_219)::_164_218))
in (FStar_Pprint.concat _164_220))
end)) fields)
in (_164_221)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.space)::_164_222)
in (_164_224)::_164_223))
in (FStar_Pprint.space)::_164_225)
in (_164_227)::_164_226))
in (FStar_Pprint.lbrace)::_164_228)
in (FStar_Pprint.concat _164_229))
in (FStar_Pprint.group _164_230))
end
| FStar_Parser_AST.Record (None, fields) -> begin
(let _164_240 = (let _164_239 = (let _164_238 = (let _164_237 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_156 -> (match (_67_156) with
| (l, e) -> begin
(let _164_236 = (let _164_235 = (str l.FStar_Ident.str)
in (let _164_234 = (let _164_233 = (let _164_232 = (doc_of_term e)
in (_164_232)::[])
in (FStar_Pprint.equals)::_164_233)
in (_164_235)::_164_234))
in (FStar_Pprint.concat _164_236))
end)) fields)
in (_164_237)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_164_238)
in (FStar_Pprint.concat _164_239))
in (FStar_Pprint.group _164_240))
end
| FStar_Parser_AST.Project (e, l) -> begin
(let _164_246 = (let _164_245 = (let _164_244 = (doc_of_term e)
in (let _164_243 = (let _164_242 = (let _164_241 = (str l.FStar_Ident.str)
in (_164_241)::[])
in (FStar_Pprint.dot)::_164_242)
in (_164_244)::_164_243))
in (FStar_Pprint.concat _164_245))
in (FStar_Pprint.group _164_246))
end
| FStar_Parser_AST.Product ([], t) -> begin
(let _164_247 = (doc_of_term t)
in (FStar_Pprint.group _164_247))
end
| FStar_Parser_AST.Product ((b)::(hd)::tl, t) -> begin
(let _164_248 = (doc_of_term (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((b)::[]), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((hd)::tl), (t)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))
in (FStar_Pprint.group _164_248))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Type) -> begin
(let _164_257 = (let _164_256 = (let _164_255 = (doc_of_binder b)
in (let _164_254 = (let _164_253 = (let _164_252 = (str "->")
in (let _164_251 = (let _164_250 = (let _164_249 = (doc_of_term t)
in (_164_249)::[])
in (FStar_Pprint.space)::_164_250)
in (_164_252)::_164_251))
in (FStar_Pprint.space)::_164_253)
in (_164_255)::_164_254))
in (FStar_Pprint.concat _164_256))
in (FStar_Pprint.group _164_257))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Kind) -> begin
(let _164_266 = (let _164_265 = (let _164_264 = (doc_of_binder b)
in (let _164_263 = (let _164_262 = (let _164_261 = (str "=>")
in (let _164_260 = (let _164_259 = (let _164_258 = (doc_of_term t)
in (_164_258)::[])
in (FStar_Pprint.space)::_164_259)
in (_164_261)::_164_260))
in (FStar_Pprint.space)::_164_262)
in (_164_264)::_164_263))
in (FStar_Pprint.concat _164_265))
in (FStar_Pprint.group _164_266))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _164_276 = (let _164_275 = (let _164_274 = (let _164_267 = (str " * ")
in (FStar_Pprint.separate_map _164_267 doc_of_binder binders))
in (let _164_273 = (let _164_272 = (let _164_271 = (str "*")
in (let _164_270 = (let _164_269 = (let _164_268 = (doc_of_term t)
in (_164_268)::[])
in (FStar_Pprint.space)::_164_269)
in (_164_271)::_164_270))
in (FStar_Pprint.space)::_164_272)
in (_164_274)::_164_273))
in (FStar_Pprint.concat _164_275))
in (FStar_Pprint.group _164_276))
end
| FStar_Parser_AST.QForall (bs, pats, t) -> begin
(let _164_297 = (let _164_296 = (let _164_295 = (str "forall")
in (let _164_294 = (let _164_293 = (let _164_292 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _164_291 = (let _164_290 = (let _164_289 = (let _164_288 = (let _164_287 = (str "pattern")
in (let _164_286 = (let _164_285 = (let _164_284 = (let _164_279 = (str " \\/ ")
in (let _164_278 = (let _164_277 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_277 doc_of_term))
in (FStar_Pprint.separate_map _164_279 _164_278 pats)))
in (let _164_283 = (let _164_282 = (let _164_281 = (let _164_280 = (doc_of_term t)
in (_164_280)::[])
in (FStar_Pprint.space)::_164_281)
in (FStar_Pprint.rbrace)::_164_282)
in (_164_284)::_164_283))
in (FStar_Pprint.space)::_164_285)
in (_164_287)::_164_286))
in (FStar_Pprint.colon)::_164_288)
in (FStar_Pprint.lbrace)::_164_289)
in (FStar_Pprint.dot)::_164_290)
in (_164_292)::_164_291))
in (FStar_Pprint.space)::_164_293)
in (_164_295)::_164_294))
in (FStar_Pprint.concat _164_296))
in (FStar_Pprint.group _164_297))
end
| FStar_Parser_AST.QExists (bs, pats, t) -> begin
(let _164_318 = (let _164_317 = (let _164_316 = (str "exists")
in (let _164_315 = (let _164_314 = (let _164_313 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _164_312 = (let _164_311 = (let _164_310 = (let _164_309 = (let _164_308 = (str "pattern")
in (let _164_307 = (let _164_306 = (let _164_305 = (let _164_300 = (str " \\/ ")
in (let _164_299 = (let _164_298 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_298 doc_of_term))
in (FStar_Pprint.separate_map _164_300 _164_299 pats)))
in (let _164_304 = (let _164_303 = (let _164_302 = (let _164_301 = (doc_of_term t)
in (_164_301)::[])
in (FStar_Pprint.space)::_164_302)
in (FStar_Pprint.rbrace)::_164_303)
in (_164_305)::_164_304))
in (FStar_Pprint.space)::_164_306)
in (_164_308)::_164_307))
in (FStar_Pprint.colon)::_164_309)
in (FStar_Pprint.lbrace)::_164_310)
in (FStar_Pprint.dot)::_164_311)
in (_164_313)::_164_312))
in (FStar_Pprint.space)::_164_314)
in (_164_316)::_164_315))
in (FStar_Pprint.concat _164_317))
in (FStar_Pprint.group _164_318))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _164_325 = (let _164_324 = (let _164_323 = (doc_of_binder b)
in (let _164_322 = (let _164_321 = (let _164_320 = (let _164_319 = (doc_of_term t)
in (_164_319)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_164_320)
in (FStar_Pprint.colon)::_164_321)
in (_164_323)::_164_322))
in (FStar_Pprint.concat _164_324))
in (FStar_Pprint.group _164_325))
end
| FStar_Parser_AST.NamedTyp (x, t) -> begin
(let _164_331 = (let _164_330 = (let _164_329 = (str x.FStar_Ident.idText)
in (let _164_328 = (let _164_327 = (let _164_326 = (doc_of_term t)
in (_164_326)::[])
in (FStar_Pprint.colon)::_164_327)
in (_164_329)::_164_328))
in (FStar_Pprint.concat _164_330))
in (FStar_Pprint.group _164_331))
end
| FStar_Parser_AST.Paren (t) -> begin
(let _164_333 = (let _164_332 = (doc_of_term t)
in (FStar_Pprint.parens _164_332))
in (FStar_Pprint.group _164_333))
end
| FStar_Parser_AST.Product (bs, t) -> begin
(let _164_343 = (let _164_342 = (let _164_341 = (str "Unidentified product: [")
in (let _164_340 = (let _164_339 = (FStar_Pprint.separate_map FStar_Pprint.comma doc_of_binder bs)
in (let _164_338 = (let _164_337 = (str "]")
in (let _164_336 = (let _164_335 = (let _164_334 = (doc_of_term t)
in (_164_334)::[])
in (FStar_Pprint.space)::_164_335)
in (_164_337)::_164_336))
in (_164_339)::_164_338))
in (_164_341)::_164_340))
in (FStar_Pprint.concat _164_342))
in (FStar_Pprint.group _164_343))
end
| t -> begin
FStar_Pprint.underscore
end))
and doc_of_binder : FStar_Parser_AST.binder  ->  FStar_Pprint.document = (fun x -> (

let s = (match (x.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (i) -> begin
(str i.FStar_Ident.idText)
end
| FStar_Parser_AST.TVariable (i) -> begin
(let _164_346 = (let _164_345 = (str i.FStar_Ident.idText)
in (_164_345)::(FStar_Pprint.colon)::(FStar_Pprint.underscore)::[])
in (FStar_Pprint.concat _164_346))
end
| (FStar_Parser_AST.TAnnotated (i, t)) | (FStar_Parser_AST.Annotated (i, t)) -> begin
(let _164_351 = (let _164_350 = (str i.FStar_Ident.idText)
in (let _164_349 = (let _164_348 = (let _164_347 = (doc_of_term t)
in (_164_347)::[])
in (FStar_Pprint.colon)::_164_348)
in (_164_350)::_164_349))
in (FStar_Pprint.concat _164_351))
end
| FStar_Parser_AST.NoName (t) -> begin
(doc_of_term t)
end)
in (let _164_353 = (let _164_352 = (doc_of_aqual x.FStar_Parser_AST.aqual)
in (_164_352)::(s)::[])
in (FStar_Pprint.concat _164_353))))
and doc_of_aqual : FStar_Parser_AST.aqual  ->  FStar_Pprint.document = (fun _67_3 -> (match (_67_3) with
| Some (FStar_Parser_AST.Equality) -> begin
(str "$")
end
| Some (FStar_Parser_AST.Implicit) -> begin
(str "#")
end
| _67_232 -> begin
FStar_Pprint.empty
end))
and doc_of_pat : FStar_Parser_AST.pattern  ->  FStar_Pprint.document = (fun x -> (match (x.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.PatConst (c) -> begin
(doc_of_const c)
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(let _164_362 = (let _164_361 = (let _164_360 = (let _164_359 = (doc_of_pat p)
in (let _164_358 = (let _164_357 = (let _164_356 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat ps)
in (_164_356)::[])
in (FStar_Pprint.space)::_164_357)
in (_164_359)::_164_358))
in (FStar_Pprint.concat _164_360))
in (FStar_Pprint.parens _164_361))
in (FStar_Pprint.group _164_362))
end
| (FStar_Parser_AST.PatTvar (i, aq)) | (FStar_Parser_AST.PatVar (i, aq)) -> begin
(let _164_367 = (let _164_366 = (let _164_365 = (doc_of_aqual aq)
in (let _164_364 = (let _164_363 = (str i.FStar_Ident.idText)
in (_164_363)::[])
in (_164_365)::_164_364))
in (FStar_Pprint.concat _164_366))
in (FStar_Pprint.group _164_367))
end
| FStar_Parser_AST.PatName (l) -> begin
(str l.FStar_Ident.str)
end
| FStar_Parser_AST.PatList (l) -> begin
(let _164_370 = (let _164_369 = (let _164_368 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_368 doc_of_pat l))
in (FStar_Pprint.brackets _164_369))
in (FStar_Pprint.group _164_370))
end
| FStar_Parser_AST.PatTuple (l, false) -> begin
(let _164_373 = (let _164_372 = (let _164_371 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_371 doc_of_pat l))
in (FStar_Pprint.parens _164_372))
in (FStar_Pprint.group _164_373))
end
| FStar_Parser_AST.PatTuple (l, true) -> begin
(let _164_379 = (let _164_378 = (let _164_377 = (let _164_376 = (let _164_375 = (let _164_374 = (FStar_Pprint.concat ((FStar_Pprint.comma)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_374 doc_of_pat l))
in (_164_375)::(FStar_Pprint.bar)::[])
in (FStar_Pprint.bar)::_164_376)
in (FStar_Pprint.concat _164_377))
in (FStar_Pprint.parens _164_378))
in (FStar_Pprint.group _164_379))
end
| FStar_Parser_AST.PatRecord (l) -> begin
(let _164_388 = (let _164_387 = (let _164_386 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_386 (fun _67_263 -> (match (_67_263) with
| (f, e) -> begin
(let _164_385 = (let _164_384 = (str f.FStar_Ident.str)
in (let _164_383 = (let _164_382 = (let _164_381 = (doc_of_pat e)
in (_164_381)::[])
in (FStar_Pprint.equals)::_164_382)
in (_164_384)::_164_383))
in (FStar_Pprint.concat _164_385))
end)) l))
in (FStar_Pprint.braces _164_387))
in (FStar_Pprint.group _164_388))
end
| FStar_Parser_AST.PatOr (l) -> begin
(let _164_389 = (FStar_Pprint.concat ((FStar_Pprint.bar)::(FStar_Pprint.hardline)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_389 doc_of_pat l))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _164_390 = (str op)
in (FStar_Pprint.parens _164_390))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _164_397 = (let _164_396 = (let _164_395 = (let _164_394 = (doc_of_pat p)
in (let _164_393 = (let _164_392 = (let _164_391 = (doc_of_term t)
in (_164_391)::[])
in (FStar_Pprint.colon)::_164_392)
in (_164_394)::_164_393))
in (FStar_Pprint.concat _164_395))
in (FStar_Pprint.parens _164_396))
in (FStar_Pprint.group _164_397))
end))


let rec head_id_of_pat : FStar_Parser_AST.pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _67_277) -> begin
(let _164_400 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_164_400)::[])
end
| FStar_Parser_AST.PatApp (p, _67_282) -> begin
(head_id_of_pat p)
end
| FStar_Parser_AST.PatAscribed (p, _67_287) -> begin
(head_id_of_pat p)
end
| _67_291 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _67_296 -> (match (_67_296) with
| (p, _67_295) -> begin
(head_id_of_pat p)
end)))))


let doc_of_tycon : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _67_4 -> (match (_67_4) with
| FStar_Parser_AST.TyconAbstract (i, bb, k) -> begin
(let _164_413 = (let _164_412 = (let _164_411 = (str "abstract")
in (let _164_410 = (let _164_409 = (let _164_408 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _164_407 = (let _164_406 = (let _164_405 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (_164_405)::(FStar_Pprint.space)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_406)
in (_164_408)::_164_407))
in (FStar_Pprint.space)::_164_409)
in (_164_411)::_164_410))
in (FStar_Pprint.concat _164_412))
in (FStar_Pprint.group _164_413))
end
| FStar_Parser_AST.TyconAbbrev (i, bb, k, t) -> begin
(let _164_414 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _164_414))
end
| FStar_Parser_AST.TyconRecord (i, bb, k, flds) -> begin
(let _164_438 = (let _164_437 = (let _164_436 = (str i.FStar_Ident.idText)
in (let _164_435 = (let _164_434 = (let _164_433 = (let _164_432 = (let _164_431 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _164_430 = (let _164_429 = (let _164_428 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (let _164_427 = (let _164_426 = (let _164_425 = (let _164_424 = (let _164_423 = (FStar_Pprint.concat ((FStar_Pprint.space)::(FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _164_423 (fun _67_318 -> (match (_67_318) with
| (i, t, d) -> begin
(let _164_422 = (let _164_421 = (str i.FStar_Ident.idText)
in (let _164_420 = (let _164_419 = (let _164_418 = (let _164_417 = (let _164_416 = (doc_of_term t)
in (_164_416)::[])
in (FStar_Pprint.space)::_164_417)
in (FStar_Pprint.colon)::_164_418)
in (FStar_Pprint.space)::_164_419)
in (_164_421)::_164_420))
in (FStar_Pprint.concat _164_422))
end)) flds))
in (FStar_Pprint.braces _164_424))
in (_164_425)::[])
in (FStar_Pprint.space)::_164_426)
in (_164_428)::_164_427))
in (FStar_Pprint.space)::_164_429)
in (_164_431)::_164_430))
in (FStar_Pprint.space)::_164_432)
in (FStar_Pprint.equals)::_164_433)
in (FStar_Pprint.space)::_164_434)
in (_164_436)::_164_435))
in (FStar_Pprint.concat _164_437))
in (FStar_Pprint.group _164_438))
end
| FStar_Parser_AST.TyconVariant (i, bb, k, vars) -> begin
(let _164_439 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _164_439))
end))


let doc_of_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(let _164_447 = (let _164_446 = (let _164_445 = (str "module")
in (let _164_444 = (let _164_443 = (let _164_442 = (str l.FStar_Ident.str)
in (_164_442)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_443)
in (_164_445)::_164_444))
in (FStar_Pprint.concat _164_446))
in (FStar_Pprint.group _164_447))
end
| FStar_Parser_AST.Open (l) -> begin
(let _164_455 = (let _164_454 = (let _164_453 = (str "open")
in (let _164_452 = (let _164_451 = (let _164_450 = (let _164_449 = (let _164_448 = (str l.FStar_Ident.str)
in (_164_448)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_449)
in (FStar_Pprint.equals)::_164_450)
in (FStar_Pprint.space)::_164_451)
in (_164_453)::_164_452))
in (FStar_Pprint.concat _164_454))
in (FStar_Pprint.group _164_455))
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(let _164_466 = (let _164_465 = (let _164_464 = (str "module")
in (let _164_463 = (let _164_462 = (let _164_461 = (str i.FStar_Ident.idText)
in (let _164_460 = (let _164_459 = (let _164_458 = (let _164_457 = (let _164_456 = (str l.FStar_Ident.str)
in (_164_456)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_457)
in (FStar_Pprint.equals)::_164_458)
in (FStar_Pprint.space)::_164_459)
in (_164_461)::_164_460))
in (FStar_Pprint.space)::_164_462)
in (_164_464)::_164_463))
in (FStar_Pprint.concat _164_465))
in (FStar_Pprint.group _164_466))
end
| FStar_Parser_AST.KindAbbrev (i, bb, k) -> begin
(let _164_480 = (let _164_479 = (let _164_478 = (str "kind")
in (let _164_477 = (let _164_476 = (let _164_475 = (str i.FStar_Ident.idText)
in (let _164_474 = (let _164_473 = (FStar_Pprint.separate_map FStar_Pprint.space (fun b -> (doc_of_binder b)) bb)
in (let _164_472 = (let _164_471 = (let _164_470 = (let _164_469 = (let _164_468 = (doc_of_term k)
in (_164_468)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_469)
in (FStar_Pprint.equals)::_164_470)
in (FStar_Pprint.space)::_164_471)
in (_164_473)::_164_472))
in (_164_475)::_164_474))
in (FStar_Pprint.space)::_164_476)
in (_164_478)::_164_477))
in (FStar_Pprint.concat _164_479))
in (FStar_Pprint.group _164_480))
end
| FStar_Parser_AST.TopLevelLet (qq, lq, pats_terms) -> begin
(

let head_ids = (FStar_List.collect (fun _67_348 -> (match (_67_348) with
| (p, _67_347) -> begin
(head_id_of_pat p)
end)) pats_terms)
in (let _164_489 = (let _164_488 = (let _164_487 = (str "let")
in (let _164_486 = (let _164_485 = (let _164_484 = (let _164_483 = (str ", ")
in (FStar_Pprint.separate_map _164_483 (fun l -> (str l.FStar_Ident.str)) head_ids))
in (_164_484)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_485)
in (_164_487)::_164_486))
in (FStar_Pprint.concat _164_488))
in (FStar_Pprint.group _164_489)))
end
| FStar_Parser_AST.Main (e) -> begin
(let _164_495 = (let _164_494 = (let _164_493 = (str "main")
in (let _164_492 = (let _164_491 = (let _164_490 = (doc_of_term e)
in (_164_490)::[])
in (FStar_Pprint.space)::_164_491)
in (_164_493)::_164_492))
in (FStar_Pprint.concat _164_494))
in (FStar_Pprint.group _164_495))
end
| FStar_Parser_AST.Assume (q, i, t) -> begin
(let _164_501 = (let _164_500 = (let _164_499 = (str "assume")
in (let _164_498 = (let _164_497 = (let _164_496 = (str i.FStar_Ident.idText)
in (_164_496)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_497)
in (_164_499)::_164_498))
in (FStar_Pprint.concat _164_500))
in (FStar_Pprint.group _164_501))
end
| FStar_Parser_AST.Tycon (q, tys) -> begin
(let _164_509 = (let _164_508 = (let _164_507 = (str "type")
in (let _164_506 = (let _164_505 = (let _164_504 = (let _164_503 = (str ", ")
in (FStar_Pprint.separate_map _164_503 (fun _67_364 -> (match (_67_364) with
| (x, d) -> begin
(doc_of_tycon x)
end)) tys))
in (_164_504)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_164_505)
in (_164_507)::_164_506))
in (FStar_Pprint.concat _164_508))
in (FStar_Pprint.group _164_509))
end
| FStar_Parser_AST.Val (_67_366, i, _67_369) -> begin
(let _164_513 = (let _164_512 = (str "val ")
in (let _164_511 = (let _164_510 = (str i.FStar_Ident.idText)
in (_164_510)::(FStar_Pprint.hardline)::[])
in (_164_512)::_164_511))
in (FStar_Pprint.concat _164_513))
end
| FStar_Parser_AST.Exception (i, _67_374) -> begin
(let _164_517 = (let _164_516 = (str "exception ")
in (let _164_515 = (let _164_514 = (str i.FStar_Ident.idText)
in (_164_514)::(FStar_Pprint.hardline)::[])
in (_164_516)::_164_515))
in (FStar_Pprint.concat _164_517))
end
| (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _164_521 = (let _164_520 = (str "new_effect) ")
in (let _164_519 = (let _164_518 = (str i.FStar_Ident.idText)
in (_164_518)::(FStar_Pprint.hardline)::[])
in (_164_520)::_164_519))
in (FStar_Pprint.concat _164_521))
end
| (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (_, FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _164_525 = (let _164_524 = (str "new_effect_for_free ")
in (let _164_523 = (let _164_522 = (str i.FStar_Ident.idText)
in (_164_522)::(FStar_Pprint.hardline)::[])
in (_164_524)::_164_523))
in (FStar_Pprint.concat _164_525))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(str "sub_effect")
end
| FStar_Parser_AST.Pragma (p) -> begin
(str "pragma")
end
| FStar_Parser_AST.Fsdoc (d) -> begin
(let _164_528 = (let _164_527 = (let _164_526 = (doc_of_fsdoc d)
in (_164_526)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.concat _164_527))
in (FStar_Pprint.group _164_528))
end))


let doc_of_modul : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _164_531 = (FStar_All.pipe_right decls (FStar_List.map doc_of_decl))
in (FStar_All.pipe_right _164_531 FStar_Pprint.concat))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun t -> (doc_of_term t))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (doc_of_decl d))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (doc_of_modul m))





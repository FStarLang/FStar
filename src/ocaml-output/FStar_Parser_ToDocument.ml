
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
(let _167_24 = (let _167_23 = (let _167_22 = (str comment)
in (let _167_21 = (let _167_20 = (let _167_19 = (let _167_18 = (str ",")
in (FStar_Pprint.separate_map _167_18 (fun _67_17 -> (match (_67_17) with
| (k, v) -> begin
(let _167_17 = (let _167_16 = (str k)
in (let _167_15 = (let _167_14 = (str "->")
in (let _167_13 = (let _167_12 = (str v)
in (_167_12)::[])
in (_167_14)::_167_13))
in (_167_16)::_167_15))
in (FStar_Pprint.concat _167_17))
end)) keywords))
in (_167_19)::[])
in (FStar_Pprint.space)::_167_20)
in (_167_22)::_167_21))
in (FStar_Pprint.concat _167_23))
in (FStar_Pprint.group _167_24))
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


let to_string_l = (fun sep f l -> (let _167_33 = (FStar_List.map f l)
in (FStar_String.concat sep _167_33)))


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
(let _167_38 = (FStar_Pprint.document_of_char x)
in (FStar_Pprint.squotes _167_38))
end
| FStar_Const.Const_string (bytes, _67_40) -> begin
(let _167_39 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _167_39))
end
| FStar_Const.Const_bytearray (_67_44) -> begin
(str "<bytearray>")
end
| FStar_Const.Const_int (x, _67_48) -> begin
(str x)
end
| FStar_Const.Const_range (r) -> begin
(let _167_40 = (FStar_Range.string_of_range r)
in (str _167_40))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(str "unsupported constant")
end))


let rec doc_of_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun x -> (match (x.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Requires (t, _67_61) -> begin
(let _167_52 = (let _167_51 = (let _167_50 = (let _167_49 = (str "requires")
in (let _167_48 = (let _167_47 = (let _167_46 = (doc_of_term t)
in (_167_46)::[])
in (FStar_Pprint.space)::_167_47)
in (_167_49)::_167_48))
in (FStar_Pprint.concat _167_50))
in (FStar_Pprint.brackets _167_51))
in (FStar_Pprint.group _167_52))
end
| FStar_Parser_AST.Ensures (t, _67_66) -> begin
(let _167_59 = (let _167_58 = (let _167_57 = (let _167_56 = (str "ensures")
in (let _167_55 = (let _167_54 = (let _167_53 = (doc_of_term t)
in (_167_53)::[])
in (FStar_Pprint.space)::_167_54)
in (_167_56)::_167_55))
in (FStar_Pprint.concat _167_57))
in (FStar_Pprint.brackets _167_58))
in (FStar_Pprint.group _167_59))
end
| FStar_Parser_AST.Labeled (t, l, _67_72) -> begin
(let _167_68 = (let _167_67 = (let _167_66 = (let _167_65 = (str "labeled")
in (let _167_64 = (let _167_63 = (let _167_62 = (str l)
in (let _167_61 = (let _167_60 = (doc_of_term t)
in (_167_60)::[])
in (_167_62)::_167_61))
in (FStar_Pprint.space)::_167_63)
in (_167_65)::_167_64))
in (FStar_Pprint.concat _167_66))
in (FStar_Pprint.brackets _167_67))
in (FStar_Pprint.group _167_68))
end
| FStar_Parser_AST.Const (c) -> begin
(let _167_69 = (doc_of_const c)
in (FStar_Pprint.group _167_69))
end
| FStar_Parser_AST.Op (s, xs) -> begin
(let _167_76 = (let _167_75 = (let _167_74 = (str s)
in (let _167_73 = (let _167_72 = (let _167_71 = (let _167_70 = (str ", ")
in (FStar_Pprint.separate_map _167_70 doc_of_term xs))
in (FStar_Pprint.brackets _167_71))
in (_167_72)::[])
in (_167_74)::_167_73))
in (FStar_Pprint.concat _167_75))
in (FStar_Pprint.group _167_76))
end
| FStar_Parser_AST.Tvar (id) -> begin
(let _167_77 = (str id.FStar_Ident.idText)
in (FStar_Pprint.group _167_77))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _167_78 = (str l.FStar_Ident.str)
in (FStar_Pprint.group _167_78))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let _167_90 = (let _167_89 = (let _167_88 = (let _167_87 = (str l.FStar_Ident.str)
in (let _167_86 = (let _167_85 = (let _167_84 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_92 -> (match (_67_92) with
| (a, imp) -> begin
(let _167_83 = (let _167_82 = (doc_of_imp imp)
in (let _167_81 = (let _167_80 = (doc_of_term a)
in (_167_80)::[])
in (_167_82)::_167_81))
in (FStar_Pprint.concat _167_83))
end)) args)
in (_167_84)::[])
in (FStar_Pprint.space)::_167_85)
in (_167_87)::_167_86))
in (FStar_Pprint.concat _167_88))
in (FStar_Pprint.brackets _167_89))
in (FStar_Pprint.group _167_90))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _167_103 = (let _167_102 = (let _167_101 = (let _167_100 = (str "fun")
in (let _167_99 = (let _167_98 = (let _167_97 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat pats)
in (let _167_96 = (let _167_95 = (let _167_94 = (str "->")
in (let _167_93 = (let _167_92 = (let _167_91 = (doc_of_term t)
in (_167_91)::[])
in (FStar_Pprint.space)::_167_92)
in (_167_94)::_167_93))
in (FStar_Pprint.space)::_167_95)
in (_167_97)::_167_96))
in (FStar_Pprint.space)::_167_98)
in (_167_100)::_167_99))
in (FStar_Pprint.concat _167_101))
in (FStar_Pprint.brackets _167_102))
in (FStar_Pprint.group _167_103))
end
| FStar_Parser_AST.App (t1, t2, imp) -> begin
(let _167_111 = (let _167_110 = (let _167_109 = (doc_of_term t1)
in (let _167_108 = (let _167_107 = (let _167_106 = (doc_of_imp imp)
in (let _167_105 = (let _167_104 = (doc_of_term t2)
in (_167_104)::[])
in (_167_106)::_167_105))
in (FStar_Pprint.space)::_167_107)
in (_167_109)::_167_108))
in (FStar_Pprint.concat _167_110))
in (FStar_Pprint.group _167_111))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.Rec, lbs, body) -> begin
(let _167_130 = (let _167_129 = (let _167_128 = (str "let rec")
in (let _167_127 = (let _167_126 = (let _167_125 = (let _167_118 = (str " and ")
in (FStar_Pprint.separate_map _167_118 (fun _67_109 -> (match (_67_109) with
| (p, b) -> begin
(let _167_117 = (let _167_116 = (doc_of_pat p)
in (let _167_115 = (let _167_114 = (let _167_113 = (doc_of_term b)
in (_167_113)::[])
in (FStar_Pprint.equals)::_167_114)
in (_167_116)::_167_115))
in (FStar_Pprint.concat _167_117))
end)) lbs))
in (let _167_124 = (let _167_123 = (let _167_122 = (str "in")
in (let _167_121 = (let _167_120 = (let _167_119 = (doc_of_term body)
in (_167_119)::[])
in (FStar_Pprint.space)::_167_120)
in (_167_122)::_167_121))
in (FStar_Pprint.space)::_167_123)
in (_167_125)::_167_124))
in (FStar_Pprint.space)::_167_126)
in (_167_128)::_167_127))
in (FStar_Pprint.concat _167_129))
in (FStar_Pprint.group _167_130))
end
| FStar_Parser_AST.Let (q, ((pat, tm))::[], body) -> begin
(let _167_150 = (let _167_149 = (let _167_148 = (str "let")
in (let _167_147 = (let _167_146 = (let _167_145 = (doc_of_let_qualifier q)
in (let _167_144 = (let _167_143 = (let _167_142 = (doc_of_pat pat)
in (let _167_141 = (let _167_140 = (let _167_139 = (let _167_138 = (let _167_137 = (doc_of_term tm)
in (let _167_136 = (let _167_135 = (let _167_134 = (str "in")
in (let _167_133 = (let _167_132 = (let _167_131 = (doc_of_term body)
in (_167_131)::[])
in (FStar_Pprint.space)::_167_132)
in (_167_134)::_167_133))
in (FStar_Pprint.space)::_167_135)
in (_167_137)::_167_136))
in (FStar_Pprint.space)::_167_138)
in (FStar_Pprint.equals)::_167_139)
in (FStar_Pprint.space)::_167_140)
in (_167_142)::_167_141))
in (FStar_Pprint.space)::_167_143)
in (_167_145)::_167_144))
in (FStar_Pprint.space)::_167_146)
in (_167_148)::_167_147))
in (FStar_Pprint.concat _167_149))
in (FStar_Pprint.group _167_150))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _167_157 = (let _167_156 = (let _167_155 = (doc_of_term t1)
in (let _167_154 = (let _167_153 = (let _167_152 = (let _167_151 = (doc_of_term t2)
in (_167_151)::[])
in (FStar_Pprint.space)::_167_152)
in (FStar_Pprint.semi)::_167_153)
in (_167_155)::_167_154))
in (FStar_Pprint.concat _167_156))
in (FStar_Pprint.group _167_157))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _167_176 = (let _167_175 = (let _167_174 = (str "if")
in (let _167_173 = (let _167_172 = (let _167_171 = (doc_of_term t1)
in (let _167_170 = (let _167_169 = (let _167_168 = (str "then")
in (let _167_167 = (let _167_166 = (let _167_165 = (let _167_158 = (doc_of_term t2)
in (FStar_Pprint.nest (Prims.parse_int "2") _167_158))
in (let _167_164 = (let _167_163 = (str "else")
in (let _167_162 = (let _167_161 = (let _167_160 = (let _167_159 = (doc_of_term t3)
in (FStar_Pprint.nest (Prims.parse_int "2") _167_159))
in (_167_160)::[])
in (FStar_Pprint.space)::_167_161)
in (_167_163)::_167_162))
in (_167_165)::_167_164))
in (FStar_Pprint.space)::_167_166)
in (_167_168)::_167_167))
in (FStar_Pprint.space)::_167_169)
in (_167_171)::_167_170))
in (FStar_Pprint.space)::_167_172)
in (_167_174)::_167_173))
in (FStar_Pprint.concat _167_175))
in (FStar_Pprint.group _167_176))
end
| FStar_Parser_AST.Match (t, branches) -> begin
(let _167_206 = (let _167_205 = (let _167_204 = (str "match")
in (let _167_203 = (let _167_202 = (let _167_201 = (doc_of_term t)
in (let _167_200 = (let _167_199 = (let _167_198 = (str "with")
in (let _167_197 = (let _167_196 = (let _167_195 = (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _67_134 -> (match (_67_134) with
| (p, w, e) -> begin
(let _167_194 = (let _167_193 = (str " | ")
in (let _167_192 = (let _167_191 = (doc_of_pat p)
in (let _167_190 = (let _167_189 = (let _167_188 = (match (w) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _167_181 = (let _167_180 = (str "when ")
in (let _167_179 = (let _167_178 = (doc_of_term e)
in (_167_178)::[])
in (_167_180)::_167_179))
in (FStar_Pprint.concat _167_181))
end)
in (let _167_187 = (let _167_186 = (let _167_185 = (str "->")
in (let _167_184 = (let _167_183 = (let _167_182 = (doc_of_term e)
in (_167_182)::[])
in (FStar_Pprint.space)::_167_183)
in (_167_185)::_167_184))
in (FStar_Pprint.space)::_167_186)
in (_167_188)::_167_187))
in (FStar_Pprint.space)::_167_189)
in (_167_191)::_167_190))
in (_167_193)::_167_192))
in (FStar_Pprint.concat _167_194))
end)) branches)
in (_167_195)::[])
in (FStar_Pprint.space)::_167_196)
in (_167_198)::_167_197))
in (FStar_Pprint.space)::_167_199)
in (_167_201)::_167_200))
in (FStar_Pprint.space)::_167_202)
in (_167_204)::_167_203))
in (FStar_Pprint.concat _167_205))
in (FStar_Pprint.group _167_206))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _167_214 = (let _167_213 = (let _167_212 = (doc_of_term t1)
in (let _167_211 = (let _167_210 = (let _167_209 = (let _167_208 = (let _167_207 = (doc_of_term t2)
in (_167_207)::[])
in (FStar_Pprint.space)::_167_208)
in (FStar_Pprint.colon)::_167_209)
in (FStar_Pprint.space)::_167_210)
in (_167_212)::_167_211))
in (FStar_Pprint.concat _167_213))
in (FStar_Pprint.group _167_214))
end
| FStar_Parser_AST.Record (Some (e), fields) -> begin
(let _167_230 = (let _167_229 = (let _167_228 = (let _167_227 = (doc_of_term e)
in (let _167_226 = (let _167_225 = (let _167_224 = (str "with")
in (let _167_223 = (let _167_222 = (let _167_221 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_149 -> (match (_67_149) with
| (l, e) -> begin
(let _167_220 = (let _167_219 = (str l.FStar_Ident.str)
in (let _167_218 = (let _167_217 = (let _167_216 = (doc_of_term e)
in (_167_216)::[])
in (FStar_Pprint.equals)::_167_217)
in (_167_219)::_167_218))
in (FStar_Pprint.concat _167_220))
end)) fields)
in (_167_221)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.space)::_167_222)
in (_167_224)::_167_223))
in (FStar_Pprint.space)::_167_225)
in (_167_227)::_167_226))
in (FStar_Pprint.lbrace)::_167_228)
in (FStar_Pprint.concat _167_229))
in (FStar_Pprint.group _167_230))
end
| FStar_Parser_AST.Record (None, fields) -> begin
(let _167_240 = (let _167_239 = (let _167_238 = (let _167_237 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _67_156 -> (match (_67_156) with
| (l, e) -> begin
(let _167_236 = (let _167_235 = (str l.FStar_Ident.str)
in (let _167_234 = (let _167_233 = (let _167_232 = (doc_of_term e)
in (_167_232)::[])
in (FStar_Pprint.equals)::_167_233)
in (_167_235)::_167_234))
in (FStar_Pprint.concat _167_236))
end)) fields)
in (_167_237)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_167_238)
in (FStar_Pprint.concat _167_239))
in (FStar_Pprint.group _167_240))
end
| FStar_Parser_AST.Project (e, l) -> begin
(let _167_246 = (let _167_245 = (let _167_244 = (doc_of_term e)
in (let _167_243 = (let _167_242 = (let _167_241 = (str l.FStar_Ident.str)
in (_167_241)::[])
in (FStar_Pprint.dot)::_167_242)
in (_167_244)::_167_243))
in (FStar_Pprint.concat _167_245))
in (FStar_Pprint.group _167_246))
end
| FStar_Parser_AST.Product ([], t) -> begin
(let _167_247 = (doc_of_term t)
in (FStar_Pprint.group _167_247))
end
| FStar_Parser_AST.Product ((b)::(hd)::tl, t) -> begin
(let _167_248 = (doc_of_term (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((b)::[]), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((hd)::tl), (t)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))
in (FStar_Pprint.group _167_248))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Type) -> begin
(let _167_257 = (let _167_256 = (let _167_255 = (doc_of_binder b)
in (let _167_254 = (let _167_253 = (let _167_252 = (str "->")
in (let _167_251 = (let _167_250 = (let _167_249 = (doc_of_term t)
in (_167_249)::[])
in (FStar_Pprint.space)::_167_250)
in (_167_252)::_167_251))
in (FStar_Pprint.space)::_167_253)
in (_167_255)::_167_254))
in (FStar_Pprint.concat _167_256))
in (FStar_Pprint.group _167_257))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Kind) -> begin
(let _167_266 = (let _167_265 = (let _167_264 = (doc_of_binder b)
in (let _167_263 = (let _167_262 = (let _167_261 = (str "=>")
in (let _167_260 = (let _167_259 = (let _167_258 = (doc_of_term t)
in (_167_258)::[])
in (FStar_Pprint.space)::_167_259)
in (_167_261)::_167_260))
in (FStar_Pprint.space)::_167_262)
in (_167_264)::_167_263))
in (FStar_Pprint.concat _167_265))
in (FStar_Pprint.group _167_266))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _167_276 = (let _167_275 = (let _167_274 = (let _167_267 = (str " * ")
in (FStar_Pprint.separate_map _167_267 doc_of_binder binders))
in (let _167_273 = (let _167_272 = (let _167_271 = (str "*")
in (let _167_270 = (let _167_269 = (let _167_268 = (doc_of_term t)
in (_167_268)::[])
in (FStar_Pprint.space)::_167_269)
in (_167_271)::_167_270))
in (FStar_Pprint.space)::_167_272)
in (_167_274)::_167_273))
in (FStar_Pprint.concat _167_275))
in (FStar_Pprint.group _167_276))
end
| FStar_Parser_AST.QForall (bs, pats, t) -> begin
(let _167_297 = (let _167_296 = (let _167_295 = (str "forall")
in (let _167_294 = (let _167_293 = (let _167_292 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _167_291 = (let _167_290 = (let _167_289 = (let _167_288 = (let _167_287 = (str "pattern")
in (let _167_286 = (let _167_285 = (let _167_284 = (let _167_279 = (str " \\/ ")
in (let _167_278 = (let _167_277 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_277 doc_of_term))
in (FStar_Pprint.separate_map _167_279 _167_278 pats)))
in (let _167_283 = (let _167_282 = (let _167_281 = (let _167_280 = (doc_of_term t)
in (_167_280)::[])
in (FStar_Pprint.space)::_167_281)
in (FStar_Pprint.rbrace)::_167_282)
in (_167_284)::_167_283))
in (FStar_Pprint.space)::_167_285)
in (_167_287)::_167_286))
in (FStar_Pprint.colon)::_167_288)
in (FStar_Pprint.lbrace)::_167_289)
in (FStar_Pprint.dot)::_167_290)
in (_167_292)::_167_291))
in (FStar_Pprint.space)::_167_293)
in (_167_295)::_167_294))
in (FStar_Pprint.concat _167_296))
in (FStar_Pprint.group _167_297))
end
| FStar_Parser_AST.QExists (bs, pats, t) -> begin
(let _167_318 = (let _167_317 = (let _167_316 = (str "exists")
in (let _167_315 = (let _167_314 = (let _167_313 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _167_312 = (let _167_311 = (let _167_310 = (let _167_309 = (let _167_308 = (str "pattern")
in (let _167_307 = (let _167_306 = (let _167_305 = (let _167_300 = (str " \\/ ")
in (let _167_299 = (let _167_298 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_298 doc_of_term))
in (FStar_Pprint.separate_map _167_300 _167_299 pats)))
in (let _167_304 = (let _167_303 = (let _167_302 = (let _167_301 = (doc_of_term t)
in (_167_301)::[])
in (FStar_Pprint.space)::_167_302)
in (FStar_Pprint.rbrace)::_167_303)
in (_167_305)::_167_304))
in (FStar_Pprint.space)::_167_306)
in (_167_308)::_167_307))
in (FStar_Pprint.colon)::_167_309)
in (FStar_Pprint.lbrace)::_167_310)
in (FStar_Pprint.dot)::_167_311)
in (_167_313)::_167_312))
in (FStar_Pprint.space)::_167_314)
in (_167_316)::_167_315))
in (FStar_Pprint.concat _167_317))
in (FStar_Pprint.group _167_318))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _167_325 = (let _167_324 = (let _167_323 = (doc_of_binder b)
in (let _167_322 = (let _167_321 = (let _167_320 = (let _167_319 = (doc_of_term t)
in (_167_319)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_167_320)
in (FStar_Pprint.colon)::_167_321)
in (_167_323)::_167_322))
in (FStar_Pprint.concat _167_324))
in (FStar_Pprint.group _167_325))
end
| FStar_Parser_AST.NamedTyp (x, t) -> begin
(let _167_331 = (let _167_330 = (let _167_329 = (str x.FStar_Ident.idText)
in (let _167_328 = (let _167_327 = (let _167_326 = (doc_of_term t)
in (_167_326)::[])
in (FStar_Pprint.colon)::_167_327)
in (_167_329)::_167_328))
in (FStar_Pprint.concat _167_330))
in (FStar_Pprint.group _167_331))
end
| FStar_Parser_AST.Paren (t) -> begin
(let _167_333 = (let _167_332 = (doc_of_term t)
in (FStar_Pprint.parens _167_332))
in (FStar_Pprint.group _167_333))
end
| FStar_Parser_AST.Product (bs, t) -> begin
(let _167_343 = (let _167_342 = (let _167_341 = (str "Unidentified product: [")
in (let _167_340 = (let _167_339 = (FStar_Pprint.separate_map FStar_Pprint.comma doc_of_binder bs)
in (let _167_338 = (let _167_337 = (str "]")
in (let _167_336 = (let _167_335 = (let _167_334 = (doc_of_term t)
in (_167_334)::[])
in (FStar_Pprint.space)::_167_335)
in (_167_337)::_167_336))
in (_167_339)::_167_338))
in (_167_341)::_167_340))
in (FStar_Pprint.concat _167_342))
in (FStar_Pprint.group _167_343))
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
(let _167_346 = (let _167_345 = (str i.FStar_Ident.idText)
in (_167_345)::(FStar_Pprint.colon)::(FStar_Pprint.underscore)::[])
in (FStar_Pprint.concat _167_346))
end
| (FStar_Parser_AST.TAnnotated (i, t)) | (FStar_Parser_AST.Annotated (i, t)) -> begin
(let _167_351 = (let _167_350 = (str i.FStar_Ident.idText)
in (let _167_349 = (let _167_348 = (let _167_347 = (doc_of_term t)
in (_167_347)::[])
in (FStar_Pprint.colon)::_167_348)
in (_167_350)::_167_349))
in (FStar_Pprint.concat _167_351))
end
| FStar_Parser_AST.NoName (t) -> begin
(doc_of_term t)
end)
in (let _167_353 = (let _167_352 = (doc_of_aqual x.FStar_Parser_AST.aqual)
in (_167_352)::(s)::[])
in (FStar_Pprint.concat _167_353))))
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
(let _167_362 = (let _167_361 = (let _167_360 = (let _167_359 = (doc_of_pat p)
in (let _167_358 = (let _167_357 = (let _167_356 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat ps)
in (_167_356)::[])
in (FStar_Pprint.space)::_167_357)
in (_167_359)::_167_358))
in (FStar_Pprint.concat _167_360))
in (FStar_Pprint.parens _167_361))
in (FStar_Pprint.group _167_362))
end
| (FStar_Parser_AST.PatTvar (i, aq)) | (FStar_Parser_AST.PatVar (i, aq)) -> begin
(let _167_367 = (let _167_366 = (let _167_365 = (doc_of_aqual aq)
in (let _167_364 = (let _167_363 = (str i.FStar_Ident.idText)
in (_167_363)::[])
in (_167_365)::_167_364))
in (FStar_Pprint.concat _167_366))
in (FStar_Pprint.group _167_367))
end
| FStar_Parser_AST.PatName (l) -> begin
(str l.FStar_Ident.str)
end
| FStar_Parser_AST.PatList (l) -> begin
(let _167_370 = (let _167_369 = (let _167_368 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_368 doc_of_pat l))
in (FStar_Pprint.brackets _167_369))
in (FStar_Pprint.group _167_370))
end
| FStar_Parser_AST.PatTuple (l, false) -> begin
(let _167_373 = (let _167_372 = (let _167_371 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_371 doc_of_pat l))
in (FStar_Pprint.parens _167_372))
in (FStar_Pprint.group _167_373))
end
| FStar_Parser_AST.PatTuple (l, true) -> begin
(let _167_379 = (let _167_378 = (let _167_377 = (let _167_376 = (let _167_375 = (let _167_374 = (FStar_Pprint.concat ((FStar_Pprint.comma)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_374 doc_of_pat l))
in (_167_375)::(FStar_Pprint.bar)::[])
in (FStar_Pprint.bar)::_167_376)
in (FStar_Pprint.concat _167_377))
in (FStar_Pprint.parens _167_378))
in (FStar_Pprint.group _167_379))
end
| FStar_Parser_AST.PatRecord (l) -> begin
(let _167_388 = (let _167_387 = (let _167_386 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_386 (fun _67_263 -> (match (_67_263) with
| (f, e) -> begin
(let _167_385 = (let _167_384 = (str f.FStar_Ident.str)
in (let _167_383 = (let _167_382 = (let _167_381 = (doc_of_pat e)
in (_167_381)::[])
in (FStar_Pprint.equals)::_167_382)
in (_167_384)::_167_383))
in (FStar_Pprint.concat _167_385))
end)) l))
in (FStar_Pprint.braces _167_387))
in (FStar_Pprint.group _167_388))
end
| FStar_Parser_AST.PatOr (l) -> begin
(let _167_389 = (FStar_Pprint.concat ((FStar_Pprint.bar)::(FStar_Pprint.hardline)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_389 doc_of_pat l))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _167_390 = (str op)
in (FStar_Pprint.parens _167_390))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _167_397 = (let _167_396 = (let _167_395 = (let _167_394 = (doc_of_pat p)
in (let _167_393 = (let _167_392 = (let _167_391 = (doc_of_term t)
in (_167_391)::[])
in (FStar_Pprint.colon)::_167_392)
in (_167_394)::_167_393))
in (FStar_Pprint.concat _167_395))
in (FStar_Pprint.parens _167_396))
in (FStar_Pprint.group _167_397))
end))


let rec head_id_of_pat : FStar_Parser_AST.pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _67_277) -> begin
(let _167_400 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_167_400)::[])
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
(let _167_413 = (let _167_412 = (let _167_411 = (str "abstract")
in (let _167_410 = (let _167_409 = (let _167_408 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _167_407 = (let _167_406 = (let _167_405 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (_167_405)::(FStar_Pprint.space)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_406)
in (_167_408)::_167_407))
in (FStar_Pprint.space)::_167_409)
in (_167_411)::_167_410))
in (FStar_Pprint.concat _167_412))
in (FStar_Pprint.group _167_413))
end
| FStar_Parser_AST.TyconAbbrev (i, bb, k, t) -> begin
(let _167_414 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _167_414))
end
| FStar_Parser_AST.TyconRecord (i, bb, k, flds) -> begin
(let _167_438 = (let _167_437 = (let _167_436 = (str i.FStar_Ident.idText)
in (let _167_435 = (let _167_434 = (let _167_433 = (let _167_432 = (let _167_431 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _167_430 = (let _167_429 = (let _167_428 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (let _167_427 = (let _167_426 = (let _167_425 = (let _167_424 = (let _167_423 = (FStar_Pprint.concat ((FStar_Pprint.space)::(FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _167_423 (fun _67_318 -> (match (_67_318) with
| (i, t, d) -> begin
(let _167_422 = (let _167_421 = (str i.FStar_Ident.idText)
in (let _167_420 = (let _167_419 = (let _167_418 = (let _167_417 = (let _167_416 = (doc_of_term t)
in (_167_416)::[])
in (FStar_Pprint.space)::_167_417)
in (FStar_Pprint.colon)::_167_418)
in (FStar_Pprint.space)::_167_419)
in (_167_421)::_167_420))
in (FStar_Pprint.concat _167_422))
end)) flds))
in (FStar_Pprint.braces _167_424))
in (_167_425)::[])
in (FStar_Pprint.space)::_167_426)
in (_167_428)::_167_427))
in (FStar_Pprint.space)::_167_429)
in (_167_431)::_167_430))
in (FStar_Pprint.space)::_167_432)
in (FStar_Pprint.equals)::_167_433)
in (FStar_Pprint.space)::_167_434)
in (_167_436)::_167_435))
in (FStar_Pprint.concat _167_437))
in (FStar_Pprint.group _167_438))
end
| FStar_Parser_AST.TyconVariant (i, bb, k, vars) -> begin
(let _167_439 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _167_439))
end))


let doc_of_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(let _167_447 = (let _167_446 = (let _167_445 = (str "module")
in (let _167_444 = (let _167_443 = (let _167_442 = (str l.FStar_Ident.str)
in (_167_442)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_443)
in (_167_445)::_167_444))
in (FStar_Pprint.concat _167_446))
in (FStar_Pprint.group _167_447))
end
| FStar_Parser_AST.Open (l) -> begin
(let _167_455 = (let _167_454 = (let _167_453 = (str "open")
in (let _167_452 = (let _167_451 = (let _167_450 = (let _167_449 = (let _167_448 = (str l.FStar_Ident.str)
in (_167_448)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_449)
in (FStar_Pprint.equals)::_167_450)
in (FStar_Pprint.space)::_167_451)
in (_167_453)::_167_452))
in (FStar_Pprint.concat _167_454))
in (FStar_Pprint.group _167_455))
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(let _167_466 = (let _167_465 = (let _167_464 = (str "module")
in (let _167_463 = (let _167_462 = (let _167_461 = (str i.FStar_Ident.idText)
in (let _167_460 = (let _167_459 = (let _167_458 = (let _167_457 = (let _167_456 = (str l.FStar_Ident.str)
in (_167_456)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_457)
in (FStar_Pprint.equals)::_167_458)
in (FStar_Pprint.space)::_167_459)
in (_167_461)::_167_460))
in (FStar_Pprint.space)::_167_462)
in (_167_464)::_167_463))
in (FStar_Pprint.concat _167_465))
in (FStar_Pprint.group _167_466))
end
| FStar_Parser_AST.KindAbbrev (i, bb, k) -> begin
(let _167_480 = (let _167_479 = (let _167_478 = (str "kind")
in (let _167_477 = (let _167_476 = (let _167_475 = (str i.FStar_Ident.idText)
in (let _167_474 = (let _167_473 = (FStar_Pprint.separate_map FStar_Pprint.space (fun b -> (doc_of_binder b)) bb)
in (let _167_472 = (let _167_471 = (let _167_470 = (let _167_469 = (let _167_468 = (doc_of_term k)
in (_167_468)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_469)
in (FStar_Pprint.equals)::_167_470)
in (FStar_Pprint.space)::_167_471)
in (_167_473)::_167_472))
in (_167_475)::_167_474))
in (FStar_Pprint.space)::_167_476)
in (_167_478)::_167_477))
in (FStar_Pprint.concat _167_479))
in (FStar_Pprint.group _167_480))
end
| FStar_Parser_AST.TopLevelLet (lq, pats_terms) -> begin
(

let head_ids = (FStar_List.collect (fun _67_347 -> (match (_67_347) with
| (p, _67_346) -> begin
(head_id_of_pat p)
end)) pats_terms)
in (let _167_489 = (let _167_488 = (let _167_487 = (str "let")
in (let _167_486 = (let _167_485 = (let _167_484 = (let _167_483 = (str ", ")
in (FStar_Pprint.separate_map _167_483 (fun l -> (str l.FStar_Ident.str)) head_ids))
in (_167_484)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_485)
in (_167_487)::_167_486))
in (FStar_Pprint.concat _167_488))
in (FStar_Pprint.group _167_489)))
end
| FStar_Parser_AST.Main (e) -> begin
(let _167_495 = (let _167_494 = (let _167_493 = (str "main")
in (let _167_492 = (let _167_491 = (let _167_490 = (doc_of_term e)
in (_167_490)::[])
in (FStar_Pprint.space)::_167_491)
in (_167_493)::_167_492))
in (FStar_Pprint.concat _167_494))
in (FStar_Pprint.group _167_495))
end
| FStar_Parser_AST.Assume (i, t) -> begin
(let _167_501 = (let _167_500 = (let _167_499 = (str "assume")
in (let _167_498 = (let _167_497 = (let _167_496 = (str i.FStar_Ident.idText)
in (_167_496)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_497)
in (_167_499)::_167_498))
in (FStar_Pprint.concat _167_500))
in (FStar_Pprint.group _167_501))
end
| FStar_Parser_AST.Tycon (q, tys) -> begin
(let _167_509 = (let _167_508 = (let _167_507 = (str "type")
in (let _167_506 = (let _167_505 = (let _167_504 = (let _167_503 = (str ", ")
in (FStar_Pprint.separate_map _167_503 (fun _67_362 -> (match (_67_362) with
| (x, d) -> begin
(doc_of_tycon x)
end)) tys))
in (_167_504)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_167_505)
in (_167_507)::_167_506))
in (FStar_Pprint.concat _167_508))
in (FStar_Pprint.group _167_509))
end
| FStar_Parser_AST.Val (i, _67_365) -> begin
(let _167_513 = (let _167_512 = (str "val ")
in (let _167_511 = (let _167_510 = (str i.FStar_Ident.idText)
in (_167_510)::(FStar_Pprint.hardline)::[])
in (_167_512)::_167_511))
in (FStar_Pprint.concat _167_513))
end
| FStar_Parser_AST.Exception (i, _67_370) -> begin
(let _167_517 = (let _167_516 = (str "exception ")
in (let _167_515 = (let _167_514 = (str i.FStar_Ident.idText)
in (_167_514)::(FStar_Pprint.hardline)::[])
in (_167_516)::_167_515))
in (FStar_Pprint.concat _167_517))
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _167_521 = (let _167_520 = (str "new_effect) ")
in (let _167_519 = (let _167_518 = (str i.FStar_Ident.idText)
in (_167_518)::(FStar_Pprint.hardline)::[])
in (_167_520)::_167_519))
in (FStar_Pprint.concat _167_521))
end
| (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _167_525 = (let _167_524 = (str "new_effect_for_free ")
in (let _167_523 = (let _167_522 = (str i.FStar_Ident.idText)
in (_167_522)::(FStar_Pprint.hardline)::[])
in (_167_524)::_167_523))
in (FStar_Pprint.concat _167_525))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(str "sub_effect")
end
| FStar_Parser_AST.Pragma (p) -> begin
(str "pragma")
end
| FStar_Parser_AST.Fsdoc (d) -> begin
(let _167_528 = (let _167_527 = (let _167_526 = (doc_of_fsdoc d)
in (_167_526)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.concat _167_527))
in (FStar_Pprint.group _167_528))
end))


let doc_of_modul : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _167_531 = (FStar_All.pipe_right decls (FStar_List.map doc_of_decl))
in (FStar_All.pipe_right _167_531 FStar_Pprint.concat))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun t -> (doc_of_term t))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (doc_of_decl d))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (doc_of_modul m))





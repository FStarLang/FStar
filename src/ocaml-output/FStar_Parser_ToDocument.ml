
open Prims

let str : Prims.string  ->  FStar_Pprint.document = (fun s -> (FStar_Pprint.document_of_string s))


let doc_of_option = (fun n f x -> (match (x) with
| None -> begin
n
end
| Some (x') -> begin
(f x')
end))


let doc_of_fsdoc : (Prims.string * (Prims.string * Prims.string) Prims.list)  ->  FStar_Pprint.document = (fun _68_14 -> (match (_68_14) with
| (comment, keywords) -> begin
(let _166_24 = (let _166_23 = (let _166_22 = (str comment)
in (let _166_21 = (let _166_20 = (let _166_19 = (let _166_18 = (str ",")
in (FStar_Pprint.separate_map _166_18 (fun _68_17 -> (match (_68_17) with
| (k, v) -> begin
(let _166_17 = (let _166_16 = (str k)
in (let _166_15 = (let _166_14 = (str "->")
in (let _166_13 = (let _166_12 = (str v)
in (_166_12)::[])
in (_166_14)::_166_13))
in (_166_16)::_166_15))
in (FStar_Pprint.concat _166_17))
end)) keywords))
in (_166_19)::[])
in (FStar_Pprint.space)::_166_20)
in (_166_22)::_166_21))
in (FStar_Pprint.concat _166_23))
in (FStar_Pprint.group _166_24))
end))


let doc_of_let_qualifier : FStar_Parser_AST.let_qualifier  ->  FStar_Pprint.document = (fun _68_1 -> (match (_68_1) with
| FStar_Parser_AST.NoLetQualifier -> begin
FStar_Pprint.empty
end
| FStar_Parser_AST.Rec -> begin
(str "rec")
end
| FStar_Parser_AST.Mutable -> begin
(str "mutable")
end))


let to_string_l = (fun sep f l -> (let _166_33 = (FStar_List.map f l)
in (FStar_String.concat sep _166_33)))


let doc_of_imp : FStar_Parser_AST.imp  ->  FStar_Pprint.document = (fun _68_2 -> (match (_68_2) with
| FStar_Parser_AST.Hash -> begin
(str "#")
end
| _68_28 -> begin
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
(let _166_38 = (FStar_Pprint.document_of_char x)
in (FStar_Pprint.squotes _166_38))
end
| FStar_Const.Const_string (bytes, _68_40) -> begin
(let _166_39 = (str (FStar_Util.string_of_bytes bytes))
in (FStar_Pprint.dquotes _166_39))
end
| FStar_Const.Const_bytearray (_68_44) -> begin
(str "<bytearray>")
end
| FStar_Const.Const_int (x, _68_48) -> begin
(str x)
end
| FStar_Const.Const_range (r) -> begin
(let _166_40 = (FStar_Range.string_of_range r)
in (str _166_40))
end
| (FStar_Const.Const_reify) | (FStar_Const.Const_reflect (_)) -> begin
(str "unsupported constant")
end))


let rec doc_of_term : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun x -> (match (x.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
FStar_Pprint.underscore
end
| FStar_Parser_AST.Requires (t, _68_61) -> begin
(let _166_52 = (let _166_51 = (let _166_50 = (let _166_49 = (str "requires")
in (let _166_48 = (let _166_47 = (let _166_46 = (doc_of_term t)
in (_166_46)::[])
in (FStar_Pprint.space)::_166_47)
in (_166_49)::_166_48))
in (FStar_Pprint.concat _166_50))
in (FStar_Pprint.brackets _166_51))
in (FStar_Pprint.group _166_52))
end
| FStar_Parser_AST.Ensures (t, _68_66) -> begin
(let _166_59 = (let _166_58 = (let _166_57 = (let _166_56 = (str "ensures")
in (let _166_55 = (let _166_54 = (let _166_53 = (doc_of_term t)
in (_166_53)::[])
in (FStar_Pprint.space)::_166_54)
in (_166_56)::_166_55))
in (FStar_Pprint.concat _166_57))
in (FStar_Pprint.brackets _166_58))
in (FStar_Pprint.group _166_59))
end
| FStar_Parser_AST.Labeled (t, l, _68_72) -> begin
(let _166_68 = (let _166_67 = (let _166_66 = (let _166_65 = (str "labeled")
in (let _166_64 = (let _166_63 = (let _166_62 = (str l)
in (let _166_61 = (let _166_60 = (doc_of_term t)
in (_166_60)::[])
in (_166_62)::_166_61))
in (FStar_Pprint.space)::_166_63)
in (_166_65)::_166_64))
in (FStar_Pprint.concat _166_66))
in (FStar_Pprint.brackets _166_67))
in (FStar_Pprint.group _166_68))
end
| FStar_Parser_AST.Const (c) -> begin
(let _166_69 = (doc_of_const c)
in (FStar_Pprint.group _166_69))
end
| FStar_Parser_AST.Op (s, xs) -> begin
(let _166_76 = (let _166_75 = (let _166_74 = (str s)
in (let _166_73 = (let _166_72 = (let _166_71 = (let _166_70 = (str ", ")
in (FStar_Pprint.separate_map _166_70 doc_of_term xs))
in (FStar_Pprint.brackets _166_71))
in (_166_72)::[])
in (_166_74)::_166_73))
in (FStar_Pprint.concat _166_75))
in (FStar_Pprint.group _166_76))
end
| FStar_Parser_AST.Tvar (id) -> begin
(let _166_77 = (str id.FStar_Ident.idText)
in (FStar_Pprint.group _166_77))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _166_78 = (str l.FStar_Ident.str)
in (FStar_Pprint.group _166_78))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(let _166_90 = (let _166_89 = (let _166_88 = (let _166_87 = (str l.FStar_Ident.str)
in (let _166_86 = (let _166_85 = (let _166_84 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_92 -> (match (_68_92) with
| (a, imp) -> begin
(let _166_83 = (let _166_82 = (doc_of_imp imp)
in (let _166_81 = (let _166_80 = (doc_of_term a)
in (_166_80)::[])
in (_166_82)::_166_81))
in (FStar_Pprint.concat _166_83))
end)) args)
in (_166_84)::[])
in (FStar_Pprint.space)::_166_85)
in (_166_87)::_166_86))
in (FStar_Pprint.concat _166_88))
in (FStar_Pprint.brackets _166_89))
in (FStar_Pprint.group _166_90))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _166_103 = (let _166_102 = (let _166_101 = (let _166_100 = (str "fun")
in (let _166_99 = (let _166_98 = (let _166_97 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat pats)
in (let _166_96 = (let _166_95 = (let _166_94 = (str "->")
in (let _166_93 = (let _166_92 = (let _166_91 = (doc_of_term t)
in (_166_91)::[])
in (FStar_Pprint.space)::_166_92)
in (_166_94)::_166_93))
in (FStar_Pprint.space)::_166_95)
in (_166_97)::_166_96))
in (FStar_Pprint.space)::_166_98)
in (_166_100)::_166_99))
in (FStar_Pprint.concat _166_101))
in (FStar_Pprint.brackets _166_102))
in (FStar_Pprint.group _166_103))
end
| FStar_Parser_AST.App (t1, t2, imp) -> begin
(let _166_111 = (let _166_110 = (let _166_109 = (doc_of_term t1)
in (let _166_108 = (let _166_107 = (let _166_106 = (doc_of_imp imp)
in (let _166_105 = (let _166_104 = (doc_of_term t2)
in (_166_104)::[])
in (_166_106)::_166_105))
in (FStar_Pprint.space)::_166_107)
in (_166_109)::_166_108))
in (FStar_Pprint.concat _166_110))
in (FStar_Pprint.group _166_111))
end
| FStar_Parser_AST.Let (FStar_Parser_AST.Rec, lbs, body) -> begin
(let _166_130 = (let _166_129 = (let _166_128 = (str "let rec")
in (let _166_127 = (let _166_126 = (let _166_125 = (let _166_118 = (str " and ")
in (FStar_Pprint.separate_map _166_118 (fun _68_109 -> (match (_68_109) with
| (p, b) -> begin
(let _166_117 = (let _166_116 = (doc_of_pat p)
in (let _166_115 = (let _166_114 = (let _166_113 = (doc_of_term b)
in (_166_113)::[])
in (FStar_Pprint.equals)::_166_114)
in (_166_116)::_166_115))
in (FStar_Pprint.concat _166_117))
end)) lbs))
in (let _166_124 = (let _166_123 = (let _166_122 = (str "in")
in (let _166_121 = (let _166_120 = (let _166_119 = (doc_of_term body)
in (_166_119)::[])
in (FStar_Pprint.space)::_166_120)
in (_166_122)::_166_121))
in (FStar_Pprint.space)::_166_123)
in (_166_125)::_166_124))
in (FStar_Pprint.space)::_166_126)
in (_166_128)::_166_127))
in (FStar_Pprint.concat _166_129))
in (FStar_Pprint.group _166_130))
end
| FStar_Parser_AST.Let (q, ((pat, tm))::[], body) -> begin
(let _166_150 = (let _166_149 = (let _166_148 = (str "let")
in (let _166_147 = (let _166_146 = (let _166_145 = (doc_of_let_qualifier q)
in (let _166_144 = (let _166_143 = (let _166_142 = (doc_of_pat pat)
in (let _166_141 = (let _166_140 = (let _166_139 = (let _166_138 = (let _166_137 = (doc_of_term tm)
in (let _166_136 = (let _166_135 = (let _166_134 = (str "in")
in (let _166_133 = (let _166_132 = (let _166_131 = (doc_of_term body)
in (_166_131)::[])
in (FStar_Pprint.space)::_166_132)
in (_166_134)::_166_133))
in (FStar_Pprint.space)::_166_135)
in (_166_137)::_166_136))
in (FStar_Pprint.space)::_166_138)
in (FStar_Pprint.equals)::_166_139)
in (FStar_Pprint.space)::_166_140)
in (_166_142)::_166_141))
in (FStar_Pprint.space)::_166_143)
in (_166_145)::_166_144))
in (FStar_Pprint.space)::_166_146)
in (_166_148)::_166_147))
in (FStar_Pprint.concat _166_149))
in (FStar_Pprint.group _166_150))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _166_157 = (let _166_156 = (let _166_155 = (doc_of_term t1)
in (let _166_154 = (let _166_153 = (let _166_152 = (let _166_151 = (doc_of_term t2)
in (_166_151)::[])
in (FStar_Pprint.space)::_166_152)
in (FStar_Pprint.semi)::_166_153)
in (_166_155)::_166_154))
in (FStar_Pprint.concat _166_156))
in (FStar_Pprint.group _166_157))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _166_176 = (let _166_175 = (let _166_174 = (str "if")
in (let _166_173 = (let _166_172 = (let _166_171 = (doc_of_term t1)
in (let _166_170 = (let _166_169 = (let _166_168 = (str "then")
in (let _166_167 = (let _166_166 = (let _166_165 = (let _166_158 = (doc_of_term t2)
in (FStar_Pprint.nest (Prims.parse_int "2") _166_158))
in (let _166_164 = (let _166_163 = (str "else")
in (let _166_162 = (let _166_161 = (let _166_160 = (let _166_159 = (doc_of_term t3)
in (FStar_Pprint.nest (Prims.parse_int "2") _166_159))
in (_166_160)::[])
in (FStar_Pprint.space)::_166_161)
in (_166_163)::_166_162))
in (_166_165)::_166_164))
in (FStar_Pprint.space)::_166_166)
in (_166_168)::_166_167))
in (FStar_Pprint.space)::_166_169)
in (_166_171)::_166_170))
in (FStar_Pprint.space)::_166_172)
in (_166_174)::_166_173))
in (FStar_Pprint.concat _166_175))
in (FStar_Pprint.group _166_176))
end
| FStar_Parser_AST.Match (t, branches) -> begin
(let _166_206 = (let _166_205 = (let _166_204 = (str "match")
in (let _166_203 = (let _166_202 = (let _166_201 = (doc_of_term t)
in (let _166_200 = (let _166_199 = (let _166_198 = (str "with")
in (let _166_197 = (let _166_196 = (let _166_195 = (FStar_Pprint.separate_map FStar_Pprint.hardline (fun _68_134 -> (match (_68_134) with
| (p, w, e) -> begin
(let _166_194 = (let _166_193 = (str " | ")
in (let _166_192 = (let _166_191 = (doc_of_pat p)
in (let _166_190 = (let _166_189 = (let _166_188 = (match (w) with
| None -> begin
FStar_Pprint.empty
end
| Some (e) -> begin
(let _166_181 = (let _166_180 = (str "when ")
in (let _166_179 = (let _166_178 = (doc_of_term e)
in (_166_178)::[])
in (_166_180)::_166_179))
in (FStar_Pprint.concat _166_181))
end)
in (let _166_187 = (let _166_186 = (let _166_185 = (str "->")
in (let _166_184 = (let _166_183 = (let _166_182 = (doc_of_term e)
in (_166_182)::[])
in (FStar_Pprint.space)::_166_183)
in (_166_185)::_166_184))
in (FStar_Pprint.space)::_166_186)
in (_166_188)::_166_187))
in (FStar_Pprint.space)::_166_189)
in (_166_191)::_166_190))
in (_166_193)::_166_192))
in (FStar_Pprint.concat _166_194))
end)) branches)
in (_166_195)::[])
in (FStar_Pprint.space)::_166_196)
in (_166_198)::_166_197))
in (FStar_Pprint.space)::_166_199)
in (_166_201)::_166_200))
in (FStar_Pprint.space)::_166_202)
in (_166_204)::_166_203))
in (FStar_Pprint.concat _166_205))
in (FStar_Pprint.group _166_206))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _166_214 = (let _166_213 = (let _166_212 = (doc_of_term t1)
in (let _166_211 = (let _166_210 = (let _166_209 = (let _166_208 = (let _166_207 = (doc_of_term t2)
in (_166_207)::[])
in (FStar_Pprint.space)::_166_208)
in (FStar_Pprint.colon)::_166_209)
in (FStar_Pprint.space)::_166_210)
in (_166_212)::_166_211))
in (FStar_Pprint.concat _166_213))
in (FStar_Pprint.group _166_214))
end
| FStar_Parser_AST.Record (Some (e), fields) -> begin
(let _166_230 = (let _166_229 = (let _166_228 = (let _166_227 = (doc_of_term e)
in (let _166_226 = (let _166_225 = (let _166_224 = (str "with")
in (let _166_223 = (let _166_222 = (let _166_221 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_149 -> (match (_68_149) with
| (l, e) -> begin
(let _166_220 = (let _166_219 = (str l.FStar_Ident.str)
in (let _166_218 = (let _166_217 = (let _166_216 = (doc_of_term e)
in (_166_216)::[])
in (FStar_Pprint.equals)::_166_217)
in (_166_219)::_166_218))
in (FStar_Pprint.concat _166_220))
end)) fields)
in (_166_221)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.space)::_166_222)
in (_166_224)::_166_223))
in (FStar_Pprint.space)::_166_225)
in (_166_227)::_166_226))
in (FStar_Pprint.lbrace)::_166_228)
in (FStar_Pprint.concat _166_229))
in (FStar_Pprint.group _166_230))
end
| FStar_Parser_AST.Record (None, fields) -> begin
(let _166_240 = (let _166_239 = (let _166_238 = (let _166_237 = (FStar_Pprint.separate_map FStar_Pprint.space (fun _68_156 -> (match (_68_156) with
| (l, e) -> begin
(let _166_236 = (let _166_235 = (str l.FStar_Ident.str)
in (let _166_234 = (let _166_233 = (let _166_232 = (doc_of_term e)
in (_166_232)::[])
in (FStar_Pprint.equals)::_166_233)
in (_166_235)::_166_234))
in (FStar_Pprint.concat _166_236))
end)) fields)
in (_166_237)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_166_238)
in (FStar_Pprint.concat _166_239))
in (FStar_Pprint.group _166_240))
end
| FStar_Parser_AST.Project (e, l) -> begin
(let _166_246 = (let _166_245 = (let _166_244 = (doc_of_term e)
in (let _166_243 = (let _166_242 = (let _166_241 = (str l.FStar_Ident.str)
in (_166_241)::[])
in (FStar_Pprint.dot)::_166_242)
in (_166_244)::_166_243))
in (FStar_Pprint.concat _166_245))
in (FStar_Pprint.group _166_246))
end
| FStar_Parser_AST.Product ([], t) -> begin
(let _166_247 = (doc_of_term t)
in (FStar_Pprint.group _166_247))
end
| FStar_Parser_AST.Product ((b)::(hd)::tl, t) -> begin
(let _166_248 = (doc_of_term (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((b)::[]), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((hd)::tl), (t)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))
in (FStar_Pprint.group _166_248))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Type) -> begin
(let _166_257 = (let _166_256 = (let _166_255 = (doc_of_binder b)
in (let _166_254 = (let _166_253 = (let _166_252 = (str "->")
in (let _166_251 = (let _166_250 = (let _166_249 = (doc_of_term t)
in (_166_249)::[])
in (FStar_Pprint.space)::_166_250)
in (_166_252)::_166_251))
in (FStar_Pprint.space)::_166_253)
in (_166_255)::_166_254))
in (FStar_Pprint.concat _166_256))
in (FStar_Pprint.group _166_257))
end
| FStar_Parser_AST.Product ((b)::[], t) when (x.FStar_Parser_AST.level = FStar_Parser_AST.Kind) -> begin
(let _166_266 = (let _166_265 = (let _166_264 = (doc_of_binder b)
in (let _166_263 = (let _166_262 = (let _166_261 = (str "=>")
in (let _166_260 = (let _166_259 = (let _166_258 = (doc_of_term t)
in (_166_258)::[])
in (FStar_Pprint.space)::_166_259)
in (_166_261)::_166_260))
in (FStar_Pprint.space)::_166_262)
in (_166_264)::_166_263))
in (FStar_Pprint.concat _166_265))
in (FStar_Pprint.group _166_266))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(let _166_276 = (let _166_275 = (let _166_274 = (let _166_267 = (str " * ")
in (FStar_Pprint.separate_map _166_267 doc_of_binder binders))
in (let _166_273 = (let _166_272 = (let _166_271 = (str "*")
in (let _166_270 = (let _166_269 = (let _166_268 = (doc_of_term t)
in (_166_268)::[])
in (FStar_Pprint.space)::_166_269)
in (_166_271)::_166_270))
in (FStar_Pprint.space)::_166_272)
in (_166_274)::_166_273))
in (FStar_Pprint.concat _166_275))
in (FStar_Pprint.group _166_276))
end
| FStar_Parser_AST.QForall (bs, pats, t) -> begin
(let _166_297 = (let _166_296 = (let _166_295 = (str "forall")
in (let _166_294 = (let _166_293 = (let _166_292 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _166_291 = (let _166_290 = (let _166_289 = (let _166_288 = (let _166_287 = (str "pattern")
in (let _166_286 = (let _166_285 = (let _166_284 = (let _166_279 = (str " \\/ ")
in (let _166_278 = (let _166_277 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_277 doc_of_term))
in (FStar_Pprint.separate_map _166_279 _166_278 pats)))
in (let _166_283 = (let _166_282 = (let _166_281 = (let _166_280 = (doc_of_term t)
in (_166_280)::[])
in (FStar_Pprint.space)::_166_281)
in (FStar_Pprint.rbrace)::_166_282)
in (_166_284)::_166_283))
in (FStar_Pprint.space)::_166_285)
in (_166_287)::_166_286))
in (FStar_Pprint.colon)::_166_288)
in (FStar_Pprint.lbrace)::_166_289)
in (FStar_Pprint.dot)::_166_290)
in (_166_292)::_166_291))
in (FStar_Pprint.space)::_166_293)
in (_166_295)::_166_294))
in (FStar_Pprint.concat _166_296))
in (FStar_Pprint.group _166_297))
end
| FStar_Parser_AST.QExists (bs, pats, t) -> begin
(let _166_318 = (let _166_317 = (let _166_316 = (str "exists")
in (let _166_315 = (let _166_314 = (let _166_313 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bs)
in (let _166_312 = (let _166_311 = (let _166_310 = (let _166_309 = (let _166_308 = (str "pattern")
in (let _166_307 = (let _166_306 = (let _166_305 = (let _166_300 = (str " \\/ ")
in (let _166_299 = (let _166_298 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_298 doc_of_term))
in (FStar_Pprint.separate_map _166_300 _166_299 pats)))
in (let _166_304 = (let _166_303 = (let _166_302 = (let _166_301 = (doc_of_term t)
in (_166_301)::[])
in (FStar_Pprint.space)::_166_302)
in (FStar_Pprint.rbrace)::_166_303)
in (_166_305)::_166_304))
in (FStar_Pprint.space)::_166_306)
in (_166_308)::_166_307))
in (FStar_Pprint.colon)::_166_309)
in (FStar_Pprint.lbrace)::_166_310)
in (FStar_Pprint.dot)::_166_311)
in (_166_313)::_166_312))
in (FStar_Pprint.space)::_166_314)
in (_166_316)::_166_315))
in (FStar_Pprint.concat _166_317))
in (FStar_Pprint.group _166_318))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(let _166_325 = (let _166_324 = (let _166_323 = (doc_of_binder b)
in (let _166_322 = (let _166_321 = (let _166_320 = (let _166_319 = (doc_of_term t)
in (_166_319)::(FStar_Pprint.rbrace)::[])
in (FStar_Pprint.lbrace)::_166_320)
in (FStar_Pprint.colon)::_166_321)
in (_166_323)::_166_322))
in (FStar_Pprint.concat _166_324))
in (FStar_Pprint.group _166_325))
end
| FStar_Parser_AST.NamedTyp (x, t) -> begin
(let _166_331 = (let _166_330 = (let _166_329 = (str x.FStar_Ident.idText)
in (let _166_328 = (let _166_327 = (let _166_326 = (doc_of_term t)
in (_166_326)::[])
in (FStar_Pprint.colon)::_166_327)
in (_166_329)::_166_328))
in (FStar_Pprint.concat _166_330))
in (FStar_Pprint.group _166_331))
end
| FStar_Parser_AST.Paren (t) -> begin
(let _166_333 = (let _166_332 = (doc_of_term t)
in (FStar_Pprint.parens _166_332))
in (FStar_Pprint.group _166_333))
end
| FStar_Parser_AST.Product (bs, t) -> begin
(let _166_343 = (let _166_342 = (let _166_341 = (str "Unidentified product: [")
in (let _166_340 = (let _166_339 = (FStar_Pprint.separate_map FStar_Pprint.comma doc_of_binder bs)
in (let _166_338 = (let _166_337 = (str "]")
in (let _166_336 = (let _166_335 = (let _166_334 = (doc_of_term t)
in (_166_334)::[])
in (FStar_Pprint.space)::_166_335)
in (_166_337)::_166_336))
in (_166_339)::_166_338))
in (_166_341)::_166_340))
in (FStar_Pprint.concat _166_342))
in (FStar_Pprint.group _166_343))
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
(let _166_346 = (let _166_345 = (str i.FStar_Ident.idText)
in (_166_345)::(FStar_Pprint.colon)::(FStar_Pprint.underscore)::[])
in (FStar_Pprint.concat _166_346))
end
| (FStar_Parser_AST.TAnnotated (i, t)) | (FStar_Parser_AST.Annotated (i, t)) -> begin
(let _166_351 = (let _166_350 = (str i.FStar_Ident.idText)
in (let _166_349 = (let _166_348 = (let _166_347 = (doc_of_term t)
in (_166_347)::[])
in (FStar_Pprint.colon)::_166_348)
in (_166_350)::_166_349))
in (FStar_Pprint.concat _166_351))
end
| FStar_Parser_AST.NoName (t) -> begin
(doc_of_term t)
end)
in (let _166_353 = (let _166_352 = (doc_of_aqual x.FStar_Parser_AST.aqual)
in (_166_352)::(s)::[])
in (FStar_Pprint.concat _166_353))))
and doc_of_aqual : FStar_Parser_AST.aqual  ->  FStar_Pprint.document = (fun _68_3 -> (match (_68_3) with
| Some (FStar_Parser_AST.Equality) -> begin
(str "$")
end
| Some (FStar_Parser_AST.Implicit) -> begin
(str "#")
end
| _68_232 -> begin
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
(let _166_362 = (let _166_361 = (let _166_360 = (let _166_359 = (doc_of_pat p)
in (let _166_358 = (let _166_357 = (let _166_356 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_pat ps)
in (_166_356)::[])
in (FStar_Pprint.space)::_166_357)
in (_166_359)::_166_358))
in (FStar_Pprint.concat _166_360))
in (FStar_Pprint.parens _166_361))
in (FStar_Pprint.group _166_362))
end
| (FStar_Parser_AST.PatTvar (i, aq)) | (FStar_Parser_AST.PatVar (i, aq)) -> begin
(let _166_367 = (let _166_366 = (let _166_365 = (doc_of_aqual aq)
in (let _166_364 = (let _166_363 = (str i.FStar_Ident.idText)
in (_166_363)::[])
in (_166_365)::_166_364))
in (FStar_Pprint.concat _166_366))
in (FStar_Pprint.group _166_367))
end
| FStar_Parser_AST.PatName (l) -> begin
(str l.FStar_Ident.str)
end
| FStar_Parser_AST.PatList (l) -> begin
(let _166_370 = (let _166_369 = (let _166_368 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_368 doc_of_pat l))
in (FStar_Pprint.brackets _166_369))
in (FStar_Pprint.group _166_370))
end
| FStar_Parser_AST.PatTuple (l, false) -> begin
(let _166_373 = (let _166_372 = (let _166_371 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_371 doc_of_pat l))
in (FStar_Pprint.parens _166_372))
in (FStar_Pprint.group _166_373))
end
| FStar_Parser_AST.PatTuple (l, true) -> begin
(let _166_379 = (let _166_378 = (let _166_377 = (let _166_376 = (let _166_375 = (let _166_374 = (FStar_Pprint.concat ((FStar_Pprint.comma)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_374 doc_of_pat l))
in (_166_375)::(FStar_Pprint.bar)::[])
in (FStar_Pprint.bar)::_166_376)
in (FStar_Pprint.concat _166_377))
in (FStar_Pprint.parens _166_378))
in (FStar_Pprint.group _166_379))
end
| FStar_Parser_AST.PatRecord (l) -> begin
(let _166_388 = (let _166_387 = (let _166_386 = (FStar_Pprint.concat ((FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_386 (fun _68_263 -> (match (_68_263) with
| (f, e) -> begin
(let _166_385 = (let _166_384 = (str f.FStar_Ident.str)
in (let _166_383 = (let _166_382 = (let _166_381 = (doc_of_pat e)
in (_166_381)::[])
in (FStar_Pprint.equals)::_166_382)
in (_166_384)::_166_383))
in (FStar_Pprint.concat _166_385))
end)) l))
in (FStar_Pprint.braces _166_387))
in (FStar_Pprint.group _166_388))
end
| FStar_Parser_AST.PatOr (l) -> begin
(let _166_389 = (FStar_Pprint.concat ((FStar_Pprint.bar)::(FStar_Pprint.hardline)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_389 doc_of_pat l))
end
| FStar_Parser_AST.PatOp (op) -> begin
(let _166_390 = (str op)
in (FStar_Pprint.parens _166_390))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _166_397 = (let _166_396 = (let _166_395 = (let _166_394 = (doc_of_pat p)
in (let _166_393 = (let _166_392 = (let _166_391 = (doc_of_term t)
in (_166_391)::[])
in (FStar_Pprint.colon)::_166_392)
in (_166_394)::_166_393))
in (FStar_Pprint.concat _166_395))
in (FStar_Pprint.parens _166_396))
in (FStar_Pprint.group _166_397))
end))


let rec head_id_of_pat : FStar_Parser_AST.pattern  ->  FStar_Ident.lid Prims.list = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatName (l) -> begin
(l)::[]
end
| FStar_Parser_AST.PatVar (i, _68_277) -> begin
(let _166_400 = (FStar_Ident.lid_of_ids ((i)::[]))
in (_166_400)::[])
end
| FStar_Parser_AST.PatApp (p, _68_282) -> begin
(head_id_of_pat p)
end
| FStar_Parser_AST.PatAscribed (p, _68_287) -> begin
(head_id_of_pat p)
end
| _68_291 -> begin
[]
end))


let lids_of_let = (fun defs -> (FStar_All.pipe_right defs (FStar_List.collect (fun _68_296 -> (match (_68_296) with
| (p, _68_295) -> begin
(head_id_of_pat p)
end)))))


let doc_of_tycon : FStar_Parser_AST.tycon  ->  FStar_Pprint.document = (fun _68_4 -> (match (_68_4) with
| FStar_Parser_AST.TyconAbstract (i, bb, k) -> begin
(let _166_413 = (let _166_412 = (let _166_411 = (str "abstract")
in (let _166_410 = (let _166_409 = (let _166_408 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _166_407 = (let _166_406 = (let _166_405 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (_166_405)::(FStar_Pprint.space)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_406)
in (_166_408)::_166_407))
in (FStar_Pprint.space)::_166_409)
in (_166_411)::_166_410))
in (FStar_Pprint.concat _166_412))
in (FStar_Pprint.group _166_413))
end
| FStar_Parser_AST.TyconAbbrev (i, bb, k, t) -> begin
(let _166_414 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _166_414))
end
| FStar_Parser_AST.TyconRecord (i, bb, k, flds) -> begin
(let _166_438 = (let _166_437 = (let _166_436 = (str i.FStar_Ident.idText)
in (let _166_435 = (let _166_434 = (let _166_433 = (let _166_432 = (let _166_431 = (FStar_Pprint.separate_map FStar_Pprint.space doc_of_binder bb)
in (let _166_430 = (let _166_429 = (let _166_428 = (doc_of_option FStar_Pprint.empty doc_of_term k)
in (let _166_427 = (let _166_426 = (let _166_425 = (let _166_424 = (let _166_423 = (FStar_Pprint.concat ((FStar_Pprint.space)::(FStar_Pprint.semi)::(FStar_Pprint.space)::[]))
in (FStar_Pprint.separate_map _166_423 (fun _68_318 -> (match (_68_318) with
| (i, t, d) -> begin
(let _166_422 = (let _166_421 = (str i.FStar_Ident.idText)
in (let _166_420 = (let _166_419 = (let _166_418 = (let _166_417 = (let _166_416 = (doc_of_term t)
in (_166_416)::[])
in (FStar_Pprint.space)::_166_417)
in (FStar_Pprint.colon)::_166_418)
in (FStar_Pprint.space)::_166_419)
in (_166_421)::_166_420))
in (FStar_Pprint.concat _166_422))
end)) flds))
in (FStar_Pprint.braces _166_424))
in (_166_425)::[])
in (FStar_Pprint.space)::_166_426)
in (_166_428)::_166_427))
in (FStar_Pprint.space)::_166_429)
in (_166_431)::_166_430))
in (FStar_Pprint.space)::_166_432)
in (FStar_Pprint.equals)::_166_433)
in (FStar_Pprint.space)::_166_434)
in (_166_436)::_166_435))
in (FStar_Pprint.concat _166_437))
in (FStar_Pprint.group _166_438))
end
| FStar_Parser_AST.TyconVariant (i, bb, k, vars) -> begin
(let _166_439 = (str i.FStar_Ident.idText)
in (FStar_Pprint.group _166_439))
end))


let doc_of_decl : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.TopLevelModule (l) -> begin
(let _166_447 = (let _166_446 = (let _166_445 = (str "module")
in (let _166_444 = (let _166_443 = (let _166_442 = (str l.FStar_Ident.str)
in (_166_442)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_443)
in (_166_445)::_166_444))
in (FStar_Pprint.concat _166_446))
in (FStar_Pprint.group _166_447))
end
| FStar_Parser_AST.Open (l) -> begin
(let _166_455 = (let _166_454 = (let _166_453 = (str "open")
in (let _166_452 = (let _166_451 = (let _166_450 = (let _166_449 = (let _166_448 = (str l.FStar_Ident.str)
in (_166_448)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_449)
in (FStar_Pprint.equals)::_166_450)
in (FStar_Pprint.space)::_166_451)
in (_166_453)::_166_452))
in (FStar_Pprint.concat _166_454))
in (FStar_Pprint.group _166_455))
end
| FStar_Parser_AST.ModuleAbbrev (i, l) -> begin
(let _166_466 = (let _166_465 = (let _166_464 = (str "module")
in (let _166_463 = (let _166_462 = (let _166_461 = (str i.FStar_Ident.idText)
in (let _166_460 = (let _166_459 = (let _166_458 = (let _166_457 = (let _166_456 = (str l.FStar_Ident.str)
in (_166_456)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_457)
in (FStar_Pprint.equals)::_166_458)
in (FStar_Pprint.space)::_166_459)
in (_166_461)::_166_460))
in (FStar_Pprint.space)::_166_462)
in (_166_464)::_166_463))
in (FStar_Pprint.concat _166_465))
in (FStar_Pprint.group _166_466))
end
| FStar_Parser_AST.KindAbbrev (i, bb, k) -> begin
(let _166_480 = (let _166_479 = (let _166_478 = (str "kind")
in (let _166_477 = (let _166_476 = (let _166_475 = (str i.FStar_Ident.idText)
in (let _166_474 = (let _166_473 = (FStar_Pprint.separate_map FStar_Pprint.space (fun b -> (doc_of_binder b)) bb)
in (let _166_472 = (let _166_471 = (let _166_470 = (let _166_469 = (let _166_468 = (doc_of_term k)
in (_166_468)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_469)
in (FStar_Pprint.equals)::_166_470)
in (FStar_Pprint.space)::_166_471)
in (_166_473)::_166_472))
in (_166_475)::_166_474))
in (FStar_Pprint.space)::_166_476)
in (_166_478)::_166_477))
in (FStar_Pprint.concat _166_479))
in (FStar_Pprint.group _166_480))
end
| FStar_Parser_AST.TopLevelLet (lq, pats_terms) -> begin
(

let head_ids = (FStar_List.collect (fun _68_347 -> (match (_68_347) with
| (p, _68_346) -> begin
(head_id_of_pat p)
end)) pats_terms)
in (let _166_489 = (let _166_488 = (let _166_487 = (str "let")
in (let _166_486 = (let _166_485 = (let _166_484 = (let _166_483 = (str ", ")
in (FStar_Pprint.separate_map _166_483 (fun l -> (str l.FStar_Ident.str)) head_ids))
in (_166_484)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_485)
in (_166_487)::_166_486))
in (FStar_Pprint.concat _166_488))
in (FStar_Pprint.group _166_489)))
end
| FStar_Parser_AST.Main (e) -> begin
(let _166_495 = (let _166_494 = (let _166_493 = (str "main")
in (let _166_492 = (let _166_491 = (let _166_490 = (doc_of_term e)
in (_166_490)::[])
in (FStar_Pprint.space)::_166_491)
in (_166_493)::_166_492))
in (FStar_Pprint.concat _166_494))
in (FStar_Pprint.group _166_495))
end
| FStar_Parser_AST.Assume (i, t) -> begin
(let _166_501 = (let _166_500 = (let _166_499 = (str "assume")
in (let _166_498 = (let _166_497 = (let _166_496 = (str i.FStar_Ident.idText)
in (_166_496)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_497)
in (_166_499)::_166_498))
in (FStar_Pprint.concat _166_500))
in (FStar_Pprint.group _166_501))
end
| FStar_Parser_AST.Tycon (q, tys) -> begin
(let _166_509 = (let _166_508 = (let _166_507 = (str "type")
in (let _166_506 = (let _166_505 = (let _166_504 = (let _166_503 = (str ", ")
in (FStar_Pprint.separate_map _166_503 (fun _68_362 -> (match (_68_362) with
| (x, d) -> begin
(doc_of_tycon x)
end)) tys))
in (_166_504)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.space)::_166_505)
in (_166_507)::_166_506))
in (FStar_Pprint.concat _166_508))
in (FStar_Pprint.group _166_509))
end
| FStar_Parser_AST.Val (i, _68_365) -> begin
(let _166_513 = (let _166_512 = (str "val ")
in (let _166_511 = (let _166_510 = (str i.FStar_Ident.idText)
in (_166_510)::(FStar_Pprint.hardline)::[])
in (_166_512)::_166_511))
in (FStar_Pprint.concat _166_513))
end
| FStar_Parser_AST.Exception (i, _68_370) -> begin
(let _166_517 = (let _166_516 = (str "exception ")
in (let _166_515 = (let _166_514 = (str i.FStar_Ident.idText)
in (_166_514)::(FStar_Pprint.hardline)::[])
in (_166_516)::_166_515))
in (FStar_Pprint.concat _166_517))
end
| (FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _166_521 = (let _166_520 = (str "new_effect) ")
in (let _166_519 = (let _166_518 = (str i.FStar_Ident.idText)
in (_166_518)::(FStar_Pprint.hardline)::[])
in (_166_520)::_166_519))
in (FStar_Pprint.concat _166_521))
end
| (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (i, _, _, _, _))) | (FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (i, _, _))) -> begin
(let _166_525 = (let _166_524 = (str "new_effect_for_free ")
in (let _166_523 = (let _166_522 = (str i.FStar_Ident.idText)
in (_166_522)::(FStar_Pprint.hardline)::[])
in (_166_524)::_166_523))
in (FStar_Pprint.concat _166_525))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(str "sub_effect")
end
| FStar_Parser_AST.Pragma (p) -> begin
(str "pragma")
end
| FStar_Parser_AST.Fsdoc (d) -> begin
(let _166_528 = (let _166_527 = (let _166_526 = (doc_of_fsdoc d)
in (_166_526)::(FStar_Pprint.hardline)::[])
in (FStar_Pprint.concat _166_527))
in (FStar_Pprint.group _166_528))
end))


let doc_of_modul : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (match (m) with
| (FStar_Parser_AST.Module (_, decls)) | (FStar_Parser_AST.Interface (_, decls, _)) -> begin
(let _166_531 = (FStar_All.pipe_right decls (FStar_List.map doc_of_decl))
in (FStar_All.pipe_right _166_531 FStar_Pprint.concat))
end))


let term_to_document : FStar_Parser_AST.term  ->  FStar_Pprint.document = (fun t -> (doc_of_term t))


let decl_to_document : FStar_Parser_AST.decl  ->  FStar_Pprint.document = (fun d -> (doc_of_decl d))


let modul_to_document : FStar_Parser_AST.modul  ->  FStar_Pprint.document = (fun m -> (doc_of_modul m))





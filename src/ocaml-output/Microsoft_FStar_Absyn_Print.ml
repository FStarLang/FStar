
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ( ps ) ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_23)) -> begin
(Support.All.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_27 -> begin
false
end))

let is_type_op = (fun ( ps ) ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(Support.All.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _26_33 -> begin
false
end))

let get_lid = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_37)) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_41 -> begin
(Support.All.failwith "get_lid")
end))

let get_type_lid = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _26_46 -> begin
(Support.All.failwith "get_type_lid")
end))

let is_infix_prim_op = (fun ( e ) -> (is_prim_op (Support.Prims.fst (Support.List.split infix_prim_ops)) e))

let is_unary_prim_op = (fun ( e ) -> (is_prim_op (Support.Prims.fst (Support.List.split unary_prim_ops)) e))

let is_infix_type_op = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split infix_type_ops)) t))

let is_unary_type_op = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split unary_type_ops)) t))

let quants = ((Microsoft_FStar_Absyn_Const.forall_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exists_lid, "exists"))::((Microsoft_FStar_Absyn_Const.allTyp_lid, "forall"))::((Microsoft_FStar_Absyn_Const.exTyp_lid, "exists"))::[]

let is_b2t = (fun ( t ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.b2t_lid)::[]) t))

let is_quant = (fun ( t ) -> (is_type_op (Support.Prims.fst (Support.List.split quants)) t))

let is_ite = (fun ( t ) -> (is_type_op ((Microsoft_FStar_Absyn_Const.ite_lid)::[]) t))

let is_lex_cons = (fun ( f ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lexcons_lid)::[]) f))

let is_lex_top = (fun ( f ) -> (is_prim_op ((Microsoft_FStar_Absyn_Const.lextop_lid)::[]) f))

let is_inr = (fun ( _26_1 ) -> (match (_26_1) with
| Support.Microsoft.FStar.Util.Inl (_26_58) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr (_26_61) -> begin
true
end))

let rec reconstruct_lex = (fun ( e ) -> (match ((let _70_10202 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _70_10202.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((f, args)) -> begin
(let args = (Support.List.filter (fun ( a ) -> (((Support.Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Support.Prims.fst a)))) args)
in (let exps = (Support.List.map (fun ( _26_2 ) -> (match (_26_2) with
| (Support.Microsoft.FStar.Util.Inl (_26_72), _26_75) -> begin
(Support.All.failwith "impossible")
end
| (Support.Microsoft.FStar.Util.Inr (x), _26_80) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((Support.List.length exps) = 2))) with
| true -> begin
(match ((let _70_10205 = (Support.List.nth exps 1)
in (reconstruct_lex _70_10205))) with
| Some (xs) -> begin
(let _70_10207 = (let _70_10206 = (Support.List.nth exps 0)
in (_70_10206)::xs)
in Some (_70_10207))
end
| None -> begin
None
end)
end
| false -> begin
None
end)))
end
| _26_87 -> begin
(match ((is_lex_top e)) with
| true -> begin
Some ([])
end
| false -> begin
None
end)
end))

let rec find = (fun ( f ) ( l ) -> (match (l) with
| [] -> begin
(Support.All.failwith "blah")
end
| hd::tl -> begin
(match ((f hd)) with
| true -> begin
hd
end
| false -> begin
(find f tl)
end)
end))

let find_lid = (fun ( x ) ( xs ) -> (let _70_10221 = (find (fun ( p ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Support.Prims.fst p))) xs)
in (Support.Prims.snd _70_10221)))

let infix_prim_op_to_string = (fun ( e ) -> (let _70_10223 = (get_lid e)
in (find_lid _70_10223 infix_prim_ops)))

let unary_prim_op_to_string = (fun ( e ) -> (let _70_10225 = (get_lid e)
in (find_lid _70_10225 unary_prim_ops)))

let infix_type_op_to_string = (fun ( t ) -> (let _70_10227 = (get_type_lid t)
in (find_lid _70_10227 infix_type_ops)))

let unary_type_op_to_string = (fun ( t ) -> (let _70_10229 = (get_type_lid t)
in (find_lid _70_10229 unary_type_ops)))

let quant_to_string = (fun ( t ) -> (let _70_10231 = (get_type_lid t)
in (find_lid _70_10231 quants)))

let rec sli = (fun ( l ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end
| false -> begin
l.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText
end))

let strBvd = (fun ( bvd ) -> (match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(Support.String.strcat bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText bvd.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end
| false -> begin
(match (((Support.ST.read Microsoft_FStar_Options.hide_genident_nums) && (Support.Microsoft.FStar.Util.starts_with bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText "_"))) with
| true -> begin
(Support.All.try_with (fun ( _26_106 ) -> (match (()) with
| () -> begin
(let _26_112 = (let _70_10236 = (Support.Microsoft.FStar.Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1)
in (Support.Microsoft.FStar.Util.int_of_string _70_10236))
in "_?")
end)) (fun ( _26_105 ) -> (match (_26_105) with
| _26_109 -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun ( a ) -> (Support.All.pipe_right a (Support.List.filter (fun ( _26_3 ) -> (match (_26_3) with
| (_26_117, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_122 -> begin
true
end)))))

let const_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
"()"
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (b) -> begin
(match (b) with
| true -> begin
"true"
end
| false -> begin
"false"
end)
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (x) -> begin
(Support.Microsoft.FStar.Util.string_of_int32 x)
end
| Microsoft_FStar_Absyn_Syntax.Const_float (x) -> begin
(Support.Microsoft.FStar.Util.string_of_float x)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (x) -> begin
(Support.String.strcat (Support.String.strcat "\'" (Support.Microsoft.FStar.Util.string_of_char x)) "\'")
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _26_135)) -> begin
(Support.Microsoft.FStar.Util.format1 "\"%s\"" (Support.Microsoft.FStar.Util.string_of_bytes bytes))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray (_26_139) -> begin
"<bytearray>"
end
| Microsoft_FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_26_144) -> begin
"<int64>"
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_26_147) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_26_151) -> begin
"Typ_btvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(Support.String.strcat "Typ_const " v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_26_156) -> begin
"Typ_fun"
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_26_159) -> begin
"Typ_refine"
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _70_10276 = (tag_of_typ head)
in (let _70_10275 = (Support.All.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (Support.Microsoft.FStar.Util.format2 "Typ_app(%s, [%s args])" _70_10276 _70_10275)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_26_166) -> begin
"Typ_lam"
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_26_169) -> begin
"Typ_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_26_172)) -> begin
"Typ_meta_pattern"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_26_176)) -> begin
"Typ_meta_named"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (_26_180)) -> begin
"Typ_meta_labeled"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_26_184)) -> begin
"Typ_meta_refresh_label"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_26_188)) -> begin
"Typ_meta_slack_formula"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_26_192) -> begin
"Typ_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_26_195) -> begin
"Typ_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_26_200) -> begin
"Exp_bvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_26_203) -> begin
"Exp_fvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_26_206) -> begin
"Exp_constant"
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_26_209) -> begin
"Exp_abs"
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_26_212) -> begin
"Exp_app"
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_26_215) -> begin
"Exp_match"
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_26_218) -> begin
"Exp_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_26_221) -> begin
"Exp_let"
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_26_224) -> begin
"Exp_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_26_227) -> begin
"Exp_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_26_230, m))) -> begin
(let _70_10280 = (meta_e_to_string m)
in (Support.String.strcat "Exp_meta_desugared " _70_10280))
end))
and meta_e_to_string = (fun ( _26_4 ) -> (match (_26_4) with
| Microsoft_FStar_Absyn_Syntax.Data_app -> begin
"Data_app"
end
| Microsoft_FStar_Absyn_Syntax.Sequence -> begin
"Sequence"
end
| Microsoft_FStar_Absyn_Syntax.Primop -> begin
"Primop"
end
| Microsoft_FStar_Absyn_Syntax.MaskedEffect -> begin
"MaskedEffect"
end))
and typ_to_string = (fun ( x ) -> (let x = (Microsoft_FStar_Absyn_Util.compress_typ x)
in (match (x.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_26_243) -> begin
(Support.All.failwith "impossible")
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_26_246, l))) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _70_10286 = (Support.All.pipe_right meta meta_to_string)
in (Support.Microsoft.FStar.Util.format1 "(Meta %s)" _70_10286))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, c)) -> begin
(let _70_10288 = (binders_to_string " -> " binders)
in (let _70_10287 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_10288 _70_10287)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((xt, f)) -> begin
(let _70_10291 = (strBvd xt.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_10290 = (Support.All.pipe_right xt.Microsoft_FStar_Absyn_Syntax.sort typ_to_string)
in (let _70_10289 = (Support.All.pipe_right f formula_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s{%s}" _70_10291 _70_10290 _70_10289))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let q_to_string = (fun ( k ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t)) -> begin
(k (b, t))
end
| _26_281 -> begin
(let _70_10302 = (tag_of_typ t)
in (let _70_10301 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "<Expected a type-lambda! got %s>%s" _70_10302 _70_10301)))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _70_10303 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "(<Expected a type!>%s)" _70_10303))
end))
in (let qbinder_to_string = (q_to_string (fun ( x ) -> (binder_to_string (Support.Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun ( x ) -> (typ_to_string (Support.Prims.snd x))))
in (let args' = (match (((Support.ST.read Microsoft_FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(Support.List.filter (fun ( _26_5 ) -> (match (_26_5) with
| (_26_290, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _26_295 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((Support.List.length args) = 3))) with
| true -> begin
(let _70_10314 = (let _70_10309 = (Support.List.nth args 0)
in (arg_to_string _70_10309))
in (let _70_10313 = (let _70_10310 = (Support.List.nth args 1)
in (arg_to_string _70_10310))
in (let _70_10312 = (let _70_10311 = (Support.List.nth args 2)
in (arg_to_string _70_10311))
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _70_10314 _70_10313 _70_10312))))
end
| false -> begin
(match (((is_b2t t) && ((Support.List.length args) = 1))) with
| true -> begin
(let _70_10315 = (Support.List.nth args 0)
in (Support.All.pipe_right _70_10315 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((Support.List.length args) <= 2))) with
| true -> begin
(let _70_10320 = (quant_to_string t)
in (let _70_10319 = (let _70_10316 = (Support.List.nth args' 0)
in (qbinder_to_string _70_10316))
in (let _70_10318 = (let _70_10317 = (Support.List.nth args' 0)
in (qbody_to_string _70_10317))
in (Support.Microsoft.FStar.Util.format3 "(%s (%s). %s)" _70_10320 _70_10319 _70_10318))))
end
| false -> begin
(match (((is_infix_type_op t) && ((Support.List.length args') = 2))) with
| true -> begin
(let _70_10325 = (let _70_10321 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_10321 arg_to_string))
in (let _70_10324 = (Support.All.pipe_right t infix_type_op_to_string)
in (let _70_10323 = (let _70_10322 = (Support.List.nth args' 1)
in (Support.All.pipe_right _70_10322 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _70_10325 _70_10324 _70_10323))))
end
| false -> begin
(match (((is_unary_type_op t) && ((Support.List.length args') = 1))) with
| true -> begin
(let _70_10328 = (Support.All.pipe_right t unary_type_op_to_string)
in (let _70_10327 = (let _70_10326 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_10326 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_10328 _70_10327)))
end
| false -> begin
(let _70_10330 = (Support.All.pipe_right t typ_to_string)
in (let _70_10329 = (Support.All.pipe_right args args_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_10330 _70_10329)))
end)
end)
end)
end)
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(let _70_10332 = (binders_to_string " " binders)
in (let _70_10331 = (Support.All.pipe_right t2 typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _70_10332 _70_10331)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(let _70_10334 = (typ_to_string t)
in (let _70_10333 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(%s <: %s)" _70_10334 _70_10333)))
end
| false -> begin
(Support.All.pipe_right t typ_to_string)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Microsoft_FStar_Absyn_Visit.compress_typ_aux false x)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_26_319); Microsoft_FStar_Absyn_Syntax.tk = _26_317; Microsoft_FStar_Absyn_Syntax.pos = _26_315; Microsoft_FStar_Absyn_Syntax.fvs = _26_313; Microsoft_FStar_Absyn_Syntax.uvs = _26_311} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(Support.All.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun ( _26_325 ) -> (match (_26_325) with
| (uv, k) -> begin
(match ((false && (Support.ST.read Microsoft_FStar_Options.print_real_names))) with
| true -> begin
(let _70_10338 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_10336 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_10336))
end)
in (let _70_10337 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(U%s : %s)" _70_10338 _70_10337)))
end
| false -> begin
(let _70_10340 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_10339 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_10339))
end)
in (Support.Microsoft.FStar.Util.format1 "U%s" _70_10340))
end)
end))
and imp_to_string = (fun ( s ) ( _26_6 ) -> (match (_26_6) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.String.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.String.strcat "=" s)
end
| _26_333 -> begin
s
end))
and binder_to_string' = (fun ( is_arrow ) ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _70_10345 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.All.pipe_right _70_10345 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _70_10346 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _70_10346 imp))
end
| false -> begin
(let _70_10350 = (let _70_10349 = (let _70_10347 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _70_10347 ":"))
in (let _70_10348 = (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _70_10349 _70_10348)))
in (imp_to_string _70_10350 imp))
end)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _70_10351 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.All.pipe_right _70_10351 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _70_10352 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _70_10352 imp))
end
| false -> begin
(let _70_10356 = (let _70_10355 = (let _70_10353 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _70_10353 ":"))
in (let _70_10354 = (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _70_10355 _70_10354)))
in (imp_to_string _70_10356 imp))
end)
end)
end))
and binder_to_string = (fun ( b ) -> (binder_to_string' false b))
and arrow_binder_to_string = (fun ( b ) -> (binder_to_string' true b))
and binders_to_string = (fun ( sep ) ( bs ) -> (let bs = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
bs
end
| false -> begin
(filter_imp bs)
end)
in (match ((sep = " -> ")) with
| true -> begin
(let _70_10361 = (Support.All.pipe_right bs (Support.List.map arrow_binder_to_string))
in (Support.All.pipe_right _70_10361 (Support.String.concat sep)))
end
| false -> begin
(let _70_10362 = (Support.All.pipe_right bs (Support.List.map binder_to_string))
in (Support.All.pipe_right _70_10362 (Support.String.concat sep)))
end)))
and arg_to_string = (fun ( _26_7 ) -> (match (_26_7) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _70_10364 = (typ_to_string a)
in (imp_to_string _70_10364 imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _70_10365 = (exp_to_string x)
in (imp_to_string _70_10365 imp))
end))
and args_to_string = (fun ( args ) -> (let args = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _70_10367 = (Support.All.pipe_right args (Support.List.map arg_to_string))
in (Support.All.pipe_right _70_10367 (Support.String.concat " ")))))
and lcomp_typ_to_string = (fun ( lc ) -> (let _70_10370 = (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _70_10369 = (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _70_10370 _70_10369))))
and comp_typ_to_string = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _70_10372 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _70_10372))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _26_8 ) -> (match (_26_8) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _26_369 -> begin
false
end)))) && (not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))))) with
| true -> begin
(let _70_10374 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _70_10374))
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid))) with
| true -> begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _26_9 ) -> (match (_26_9) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _26_373 -> begin
false
end)))))) with
| true -> begin
(let _70_10376 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "ALL %s" _70_10376))
end
| false -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_effect_args)) with
| true -> begin
(let _70_10380 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_10379 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _70_10378 = (let _70_10377 = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map effect_arg_to_string))
in (Support.All.pipe_right _70_10377 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "%s (%s) %s" _70_10380 _70_10379 _70_10378))))
end
| false -> begin
(let _70_10382 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _70_10381 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format2 "%s (%s)" _70_10382 _70_10381)))
end)
end)
end)
end)
in (let dec = (let _70_10386 = (Support.All.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.collect (fun ( _26_10 ) -> (match (_26_10) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _70_10385 = (let _70_10384 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 " (decreases %s)" _70_10384))
in (_70_10385)::[])
end
| _26_379 -> begin
[]
end))))
in (Support.All.pipe_right _70_10386 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun ( e ) -> (match (e) with
| (Support.Microsoft.FStar.Util.Inr (e), _26_385) -> begin
(exp_to_string e)
end
| (Support.Microsoft.FStar.Util.Inl (wp), _26_390) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun ( phi ) -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun ( phi ) -> (let const_op = (fun ( f ) ( _26_396 ) -> f)
in (let un_op = (fun ( f ) ( _26_11 ) -> (match (_26_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _26_404)::[] -> begin
(let _70_10398 = (formula_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s %s" f _70_10398))
end
| _26_408 -> begin
(Support.All.failwith "impos")
end))
in (let bin_top = (fun ( f ) ( _26_12 ) -> (match (_26_12) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_420)::(Support.Microsoft.FStar.Util.Inl (t2), _26_415)::[] -> begin
(let _70_10404 = (formula_to_string t1)
in (let _70_10403 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _70_10404 f _70_10403)))
end
| _26_424 -> begin
(Support.All.failwith "Impos")
end))
in (let bin_eop = (fun ( f ) ( _26_13 ) -> (match (_26_13) with
| (Support.Microsoft.FStar.Util.Inr (e1), _26_436)::(Support.Microsoft.FStar.Util.Inr (e2), _26_431)::[] -> begin
(let _70_10410 = (exp_to_string e1)
in (let _70_10409 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _70_10410 f _70_10409)))
end
| _26_440 -> begin
(Support.All.failwith "impos")
end))
in (let ite = (fun ( _26_14 ) -> (match (_26_14) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_455)::(Support.Microsoft.FStar.Util.Inl (t2), _26_450)::(Support.Microsoft.FStar.Util.Inl (t3), _26_445)::[] -> begin
(let _70_10415 = (formula_to_string t1)
in (let _70_10414 = (formula_to_string t2)
in (let _70_10413 = (formula_to_string t3)
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _70_10415 _70_10414 _70_10413))))
end
| _26_459 -> begin
(Support.All.failwith "impos")
end))
in (let eq_op = (fun ( _26_15 ) -> (match (_26_15) with
| (Support.Microsoft.FStar.Util.Inl (t1), _26_480)::(Support.Microsoft.FStar.Util.Inl (t2), _26_475)::(Support.Microsoft.FStar.Util.Inr (e1), _26_470)::(Support.Microsoft.FStar.Util.Inr (e2), _26_465)::[] -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
(let _70_10421 = (typ_to_string t1)
in (let _70_10420 = (typ_to_string t2)
in (let _70_10419 = (exp_to_string e1)
in (let _70_10418 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format4 "Eq2 %s %s %s %s" _70_10421 _70_10420 _70_10419 _70_10418)))))
end
| false -> begin
(let _70_10423 = (exp_to_string e1)
in (let _70_10422 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _70_10423 _70_10422)))
end)
end
| (Support.Microsoft.FStar.Util.Inr (e1), _26_491)::(Support.Microsoft.FStar.Util.Inr (e2), _26_486)::[] -> begin
(let _70_10425 = (exp_to_string e1)
in (let _70_10424 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _70_10425 _70_10424)))
end
| _26_495 -> begin
(Support.All.failwith "Impossible")
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, phi)) -> begin
(let _70_10464 = (binders_to_string " " binders)
in (let _70_10463 = (formula_to_string phi)
in (Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" _70_10464 _70_10463)))
end
| _26_505 -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match ((Support.All.pipe_right connectives (Support.List.tryFind (fun ( _26_515 ) -> (match (_26_515) with
| (l, _26_514) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_26_518, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, _26_524, body))) -> begin
(let _70_10482 = (binders_to_string " " vars)
in (let _70_10481 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(forall %s. %s)" _70_10482 _70_10481)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, _26_531, body))) -> begin
(let _70_10484 = (binders_to_string " " vars)
in (let _70_10483 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(exists %s. %s)" _70_10484 _70_10483)))
end))))))))))
and exp_to_string = (fun ( x ) -> (match ((let _70_10486 = (Microsoft_FStar_Absyn_Util.compress_exp x)
in _70_10486.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_26_538) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _26_542))) -> begin
(exp_to_string e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(uvar_e_to_string (uv, t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _26_554)) -> begin
(sli fv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(Support.All.pipe_right c const_to_string)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, e)) -> begin
(let _70_10488 = (binders_to_string " " binders)
in (let _70_10487 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _70_10488 _70_10487)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((e, args)) -> begin
(let lex = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
None
end
| false -> begin
(reconstruct_lex x)
end)
in (match (lex) with
| Some (es) -> begin
(let _70_10491 = (let _70_10490 = (let _70_10489 = (Support.List.map exp_to_string es)
in (Support.String.concat "; " _70_10489))
in (Support.String.strcat "%[" _70_10490))
in (Support.String.strcat _70_10491 "]"))
end
| None -> begin
(let args' = (let _70_10493 = (filter_imp args)
in (Support.All.pipe_right _70_10493 (Support.List.filter (fun ( _26_16 ) -> (match (_26_16) with
| (Support.Microsoft.FStar.Util.Inr (_26_573), _26_576) -> begin
true
end
| _26_579 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((Support.List.length args') = 2))) with
| true -> begin
(let _70_10498 = (let _70_10494 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_10494 arg_to_string))
in (let _70_10497 = (Support.All.pipe_right e infix_prim_op_to_string)
in (let _70_10496 = (let _70_10495 = (Support.List.nth args' 1)
in (Support.All.pipe_right _70_10495 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _70_10498 _70_10497 _70_10496))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((Support.List.length args') = 1))) with
| true -> begin
(let _70_10501 = (Support.All.pipe_right e unary_prim_op_to_string)
in (let _70_10500 = (let _70_10499 = (Support.List.nth args' 0)
in (Support.All.pipe_right _70_10499 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_10501 _70_10500)))
end
| false -> begin
(let _70_10503 = (Support.All.pipe_right e exp_to_string)
in (let _70_10502 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_10503 _70_10502)))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _70_10511 = (Support.All.pipe_right e exp_to_string)
in (let _70_10510 = (let _70_10509 = (Support.All.pipe_right pats (Support.List.map (fun ( _26_588 ) -> (match (_26_588) with
| (p, wopt, e) -> begin
(let _70_10508 = (Support.All.pipe_right p pat_to_string)
in (let _70_10507 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _70_10505 = (Support.All.pipe_right w exp_to_string)
in (Support.Microsoft.FStar.Util.format1 "when %s" _70_10505))
end)
in (let _70_10506 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s -> %s" _70_10508 _70_10507 _70_10506))))
end))))
in (Support.Microsoft.FStar.Util.concat_l "\n\t" _70_10509))
in (Support.Microsoft.FStar.Util.format2 "(match %s with %s)" _70_10511 _70_10510)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _26_595)) -> begin
(let _70_10513 = (Support.All.pipe_right e exp_to_string)
in (let _70_10512 = (Support.All.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s:%s)" _70_10513 _70_10512)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _70_10515 = (lbs_to_string lbs)
in (let _70_10514 = (Support.All.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s in %s" _70_10515 _70_10514)))
end))
and uvar_e_to_string = (fun ( _26_605 ) -> (match (_26_605) with
| (uv, _26_604) -> begin
(let _70_10518 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_10517 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_10517))
end)
in (Support.String.strcat "\'e" _70_10518))
end))
and lbs_to_string = (fun ( lbs ) -> (let _70_10525 = (let _70_10524 = (Support.All.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (let _70_10523 = (lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _70_10522 = (Support.All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _70_10521 = (Support.All.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbdef exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s = %s" _70_10523 _70_10522 _70_10521)))))))
in (Support.Microsoft.FStar.Util.concat_l "\n and " _70_10524))
in (Support.Microsoft.FStar.Util.format2 "let %s %s" (match ((Support.Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _70_10525)))
and lbname_to_string = (fun ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (bvd) -> begin
(strBvd bvd)
end
| Support.Microsoft.FStar.Util.Inr (lid) -> begin
(sli lid)
end))
and either_to_string = (fun ( x ) -> (match (x) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(typ_to_string t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(exp_to_string e)
end))
and either_l_to_string = (fun ( delim ) ( l ) -> (let _70_10530 = (Support.All.pipe_right l (Support.List.map either_to_string))
in (Support.All.pipe_right _70_10530 (Support.Microsoft.FStar.Util.concat_l delim))))
and meta_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _26_623, _26_625)) -> begin
(let _70_10532 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(refresh) %s" _70_10532))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, _26_631, _26_633)) -> begin
(let _70_10533 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(labeled \"%s\") %s" l _70_10533))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((_26_637, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)) -> begin
(let _70_10535 = (args_to_string ps)
in (let _70_10534 = (Support.All.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "{:pattern %s} %s" _70_10535 _70_10534)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _26_648)) -> begin
(let _70_10537 = (formula_to_string t1)
in (let _70_10536 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format2 "%s /\\ %s" _70_10537 _70_10536)))
end))
and kind_to_string = (fun ( x ) -> (match ((let _70_10539 = (Microsoft_FStar_Absyn_Util.compress_kind x)
in _70_10539.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_26_653) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_26_656) -> begin
(Support.All.failwith "Impossible")
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, args)) -> begin
(uvar_k_to_string' (uv, args))
end
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
"Type"
end
| Microsoft_FStar_Absyn_Syntax.Kind_effect -> begin
"Effect"
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev (((n, args), k)) -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(kind_to_string k)
end
| false -> begin
(let _70_10541 = (sli n)
in (let _70_10540 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _70_10541 _70_10540)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(let _70_10543 = (binders_to_string " -> " binders)
in (let _70_10542 = (Support.All.pipe_right k kind_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_10543 _70_10542)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun ( uv ) -> (let _70_10545 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_10544 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_10544))
end)
in (Support.String.strcat "\'k_" _70_10545)))
and uvar_k_to_string' = (fun ( _26_678 ) -> (match (_26_678) with
| (uv, args) -> begin
(let str = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _70_10547 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _70_10547))
end)
in (let _70_10548 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(\'k_%s %s)" str _70_10548)))
end))
and pat_to_string = (fun ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, _26_683, pats)) -> begin
(let _70_10552 = (sli l.Microsoft_FStar_Absyn_Syntax.v)
in (let _70_10551 = (let _70_10550 = (Support.List.map pat_to_string pats)
in (Support.All.pipe_right _70_10550 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _70_10552 _70_10551)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _26_689)) -> begin
(let _70_10553 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".%s" _70_10553))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, _26_694)) -> begin
(let _70_10554 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".\'%s" _70_10554))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, true)) -> begin
(let _70_10555 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "#%s" _70_10555))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, false)) -> begin
(strBvd x.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_tvar (a) -> begin
(strBvd a.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(const_to_string c)
end
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_26_710) -> begin
"_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_26_713) -> begin
"\'_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _70_10556 = (Support.List.map pat_to_string ps)
in (Support.Microsoft.FStar.Util.concat_l " | " _70_10556))
end))

let subst_to_string = (fun ( subst ) -> (let _70_10564 = (let _70_10563 = (Support.List.map (fun ( _26_17 ) -> (match (_26_17) with
| Support.Microsoft.FStar.Util.Inl ((a, t)) -> begin
(let _70_10560 = (strBvd a)
in (let _70_10559 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_10560 _70_10559)))
end
| Support.Microsoft.FStar.Util.Inr ((x, e)) -> begin
(let _70_10562 = (strBvd x)
in (let _70_10561 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _70_10562 _70_10561)))
end)) subst)
in (Support.All.pipe_right _70_10563 (Support.String.concat ", ")))
in (Support.All.pipe_left (Support.Microsoft.FStar.Util.format1 "{%s}") _70_10564)))

let freevars_to_string = (fun ( fvs ) -> (let f = (fun ( l ) -> (let _70_10570 = (let _70_10569 = (Support.All.pipe_right l Support.Microsoft.FStar.Util.set_elements)
in (Support.All.pipe_right _70_10569 (Support.List.map (fun ( t ) -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.All.pipe_right _70_10570 (Support.String.concat ", "))))
in (let _70_10572 = (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _70_10571 = (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Microsoft.FStar.Util.format2 "ftvs={%s}, fxvs={%s}" _70_10572 _70_10571)))))

let qual_to_string = (fun ( _26_18 ) -> (match (_26_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (_26_737) -> begin
"discriminator"
end
| Microsoft_FStar_Absyn_Syntax.Projector (_26_740) -> begin
"projector"
end
| Microsoft_FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _70_10577 = (let _70_10576 = (Support.All.pipe_right ids (Support.List.map (fun ( lid ) -> lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
in (Support.All.pipe_right _70_10576 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format1 "record(%s)" _70_10577))
end
| _26_746 -> begin
"other"
end))

let quals_to_string = (fun ( quals ) -> (let _70_10580 = (Support.All.pipe_right quals (Support.List.map qual_to_string))
in (Support.All.pipe_right _70_10580 (Support.String.concat " "))))

let rec sigelt_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.ResetOptions, _26_751)) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.SetOptions (s), _26_757)) -> begin
(Support.Microsoft.FStar.Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _26_764, _26_766, quals, _26_769)) -> begin
(let _70_10585 = (quals_to_string quals)
in (let _70_10584 = (binders_to_string " " tps)
in (let _70_10583 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format4 "%s type %s %s : %s" _70_10585 lid.Microsoft_FStar_Absyn_Syntax.str _70_10584 _70_10583))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, _26_777, _26_779)) -> begin
(let _70_10588 = (binders_to_string " " tps)
in (let _70_10587 = (kind_to_string k)
in (let _70_10586 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_10588 _70_10587 _70_10586))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, _26_785, _26_787, _26_789, _26_791)) -> begin
(let _70_10589 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_10589))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _26_798)) -> begin
(let _70_10591 = (quals_to_string quals)
in (let _70_10590 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "%s val %s : %s" _70_10591 lid.Microsoft_FStar_Absyn_Syntax.str _70_10590)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, f, _26_804, _26_806)) -> begin
(let _70_10592 = (typ_to_string f)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _70_10592))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _26_811, _26_813, b)) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _26_819)) -> begin
(let _70_10593 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "let _ = %s" _70_10593))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _26_824, _26_826, _26_828)) -> begin
(let _70_10594 = (Support.List.map sigelt_to_string ses)
in (Support.All.pipe_right _70_10594 (Support.String.concat "\n")))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_26_832) -> begin
"new_effect { ... }"
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_26_835) -> begin
"sub_effect ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_26_838) -> begin
"kind ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, tps, c, _26_844, _26_846)) -> begin
(let _70_10597 = (sli l)
in (let _70_10596 = (binders_to_string " " tps)
in (let _70_10595 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format3 "effect %s %s = %s" _70_10597 _70_10596 _70_10595))))
end))

let format_error = (fun ( r ) ( msg ) -> (let _70_10602 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _70_10602 msg)))

let rec sigelt_to_string_short = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (((_26_853, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _26_857; Microsoft_FStar_Absyn_Syntax.lbdef = _26_855}::[]), _26_865, _26_867, _26_869)) -> begin
(let _70_10605 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str _70_10605))
end
| _26_873 -> begin
(let _70_10608 = (let _70_10607 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)
in (Support.All.pipe_right _70_10607 (Support.List.map (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.str))))
in (Support.All.pipe_right _70_10608 (Support.String.concat ", ")))
end))

let rec modul_to_string = (fun ( m ) -> (let _70_10613 = (sli m.Microsoft_FStar_Absyn_Syntax.name)
in (let _70_10612 = (let _70_10611 = (Support.List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.All.pipe_right _70_10611 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "module %s\n%s" _70_10613 _70_10612))))





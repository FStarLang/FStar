
let infix_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Addition, "+"))::((Microsoft_FStar_Absyn_Const.op_Subtraction, "-"))::((Microsoft_FStar_Absyn_Const.op_Multiply, "*"))::((Microsoft_FStar_Absyn_Const.op_Division, "/"))::((Microsoft_FStar_Absyn_Const.op_Eq, "="))::((Microsoft_FStar_Absyn_Const.op_ColonEq, ":="))::((Microsoft_FStar_Absyn_Const.op_notEq, "<>"))::((Microsoft_FStar_Absyn_Const.op_And, "&&"))::((Microsoft_FStar_Absyn_Const.op_Or, "||"))::((Microsoft_FStar_Absyn_Const.op_LTE, "<="))::((Microsoft_FStar_Absyn_Const.op_GTE, ">="))::((Microsoft_FStar_Absyn_Const.op_LT, "<"))::((Microsoft_FStar_Absyn_Const.op_GT, ">"))::((Microsoft_FStar_Absyn_Const.op_Modulus, "mod"))::[]

let unary_prim_ops = ((Microsoft_FStar_Absyn_Const.op_Negation, "not"))::((Microsoft_FStar_Absyn_Const.op_Minus, "-"))::[]

let infix_type_ops = ((Microsoft_FStar_Absyn_Const.and_lid, "/\\"))::((Microsoft_FStar_Absyn_Const.or_lid, "\\/"))::((Microsoft_FStar_Absyn_Const.imp_lid, "==>"))::((Microsoft_FStar_Absyn_Const.iff_lid, "<==>"))::((Microsoft_FStar_Absyn_Const.precedes_lid, "<<"))::((Microsoft_FStar_Absyn_Const.eq2_lid, "=="))::((Microsoft_FStar_Absyn_Const.eqT_lid, "=="))::[]

let unary_type_ops = ((Microsoft_FStar_Absyn_Const.not_lid, "~"))::[]

let is_prim_op = (fun ( ps ) ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _24_23)) -> begin
(Support.Prims.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals fv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _24_27 -> begin
false
end))

let is_type_op = (fun ( ps ) ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
(Support.Prims.pipe_right ps (Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_Absyn_Syntax.lid_equals ftv.Microsoft_FStar_Absyn_Syntax.v)))
end
| _24_33 -> begin
false
end))

let get_lid = (fun ( f ) -> (match (f.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _24_37)) -> begin
fv.Microsoft_FStar_Absyn_Syntax.v
end
| _24_41 -> begin
(failwith ("get_lid"))
end))

let get_type_lid = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (ftv) -> begin
ftv.Microsoft_FStar_Absyn_Syntax.v
end
| _24_46 -> begin
(failwith ("get_type_lid"))
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

let is_inr = (fun ( _24_1 ) -> (match (_24_1) with
| Support.Microsoft.FStar.Util.Inl (_24_58) -> begin
false
end
| Support.Microsoft.FStar.Util.Inr (_24_61) -> begin
true
end))

let rec reconstruct_lex = (fun ( e ) -> (match ((let _68_10082 = (Microsoft_FStar_Absyn_Util.compress_exp e)
in _68_10082.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((f, args)) -> begin
(let args = (Support.List.filter (fun ( a ) -> (((Support.Prims.snd a) <> Some (Microsoft_FStar_Absyn_Syntax.Implicit)) && (is_inr (Support.Prims.fst a)))) args)
in (let exps = (Support.List.map (fun ( _24_2 ) -> (match (_24_2) with
| (Support.Microsoft.FStar.Util.Inl (_24_72), _24_75) -> begin
(failwith ("impossible"))
end
| (Support.Microsoft.FStar.Util.Inr (x), _24_80) -> begin
x
end)) args)
in (match (((is_lex_cons f) && ((Support.List.length exps) = 2))) with
| true -> begin
(match ((let _68_10085 = (Support.List.nth exps 1)
in (reconstruct_lex _68_10085))) with
| Some (xs) -> begin
(let _68_10087 = (let _68_10086 = (Support.List.nth exps 0)
in (_68_10086)::xs)
in Some (_68_10087))
end
| None -> begin
None
end)
end
| false -> begin
None
end)))
end
| _24_87 -> begin
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
(failwith ("blah"))
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

let find_lid = (fun ( x ) ( xs ) -> (let _68_10101 = (find (fun ( p ) -> (Microsoft_FStar_Absyn_Syntax.lid_equals x (Support.Prims.fst p))) xs)
in (Support.Prims.snd _68_10101)))

let infix_prim_op_to_string = (fun ( e ) -> (let _68_10103 = (get_lid e)
in (find_lid _68_10103 infix_prim_ops)))

let unary_prim_op_to_string = (fun ( e ) -> (let _68_10105 = (get_lid e)
in (find_lid _68_10105 unary_prim_ops)))

let infix_type_op_to_string = (fun ( t ) -> (let _68_10107 = (get_type_lid t)
in (find_lid _68_10107 infix_type_ops)))

let unary_type_op_to_string = (fun ( t ) -> (let _68_10109 = (get_type_lid t)
in (find_lid _68_10109 unary_type_ops)))

let quant_to_string = (fun ( t ) -> (let _68_10111 = (get_type_lid t)
in (find_lid _68_10111 quants)))

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
(Support.Prims.try_with (fun ( _24_106 ) -> (match (()) with
| () -> begin
(let _24_112 = (let _68_10116 = (Support.Microsoft.FStar.Util.substring_from bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText 1)
in (Support.Microsoft.FStar.Util.int_of_string _68_10116))
in "_?")
end)) (fun ( _24_105 ) -> (match (_24_105) with
| _24_109 -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)))
end
| false -> begin
bvd.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)
end))

let filter_imp = (fun ( a ) -> (Support.Prims.pipe_right a (Support.List.filter (fun ( _24_3 ) -> (match (_24_3) with
| (_24_117, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _24_122 -> begin
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
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _24_135)) -> begin
(Support.Microsoft.FStar.Util.format1 "\"%s\"" (Support.Microsoft.FStar.Util.string_of_bytes bytes))
end
| Microsoft_FStar_Absyn_Syntax.Const_bytearray (_24_139) -> begin
"<bytearray>"
end
| Microsoft_FStar_Absyn_Syntax.Const_int (x) -> begin
x
end
| Microsoft_FStar_Absyn_Syntax.Const_int64 (_24_144) -> begin
"<int64>"
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (_24_147) -> begin
"<uint8>"
end))

let rec tag_of_typ = (fun ( t ) -> (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (_24_151) -> begin
"Typ_btvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(Support.String.strcat "Typ_const " v.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.str)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun (_24_156) -> begin
"Typ_fun"
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_24_159) -> begin
"Typ_refine"
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let _68_10156 = (tag_of_typ head)
in (let _68_10155 = (Support.Prims.pipe_left Support.Microsoft.FStar.Util.string_of_int (Support.List.length args))
in (Support.Microsoft.FStar.Util.format2 "Typ_app(%s, [%s args])" _68_10156 _68_10155)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam (_24_166) -> begin
"Typ_lam"
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed (_24_169) -> begin
"Typ_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_pattern (_24_172)) -> begin
"Typ_meta_pattern"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named (_24_176)) -> begin
"Typ_meta_named"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled (_24_180)) -> begin
"Typ_meta_labeled"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_refresh_label (_24_184)) -> begin
"Typ_meta_refresh_label"
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_slack_formula (_24_188)) -> begin
"Typ_meta_slack_formula"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar (_24_192) -> begin
"Typ_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_24_195) -> begin
"Typ_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"Typ_unknown"
end))
and tag_of_exp = (fun ( e ) -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (_24_200) -> begin
"Exp_bvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar (_24_203) -> begin
"Exp_fvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (_24_206) -> begin
"Exp_constant"
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs (_24_209) -> begin
"Exp_abs"
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (_24_212) -> begin
"Exp_app"
end
| Microsoft_FStar_Absyn_Syntax.Exp_match (_24_215) -> begin
"Exp_match"
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed (_24_218) -> begin
"Exp_ascribed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_24_221) -> begin
"Exp_let"
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar (_24_224) -> begin
"Exp_uvar"
end
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_24_227) -> begin
"Exp_delayed"
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((_24_230, m))) -> begin
(let _68_10160 = (meta_e_to_string m)
in (Support.String.strcat "Exp_meta_desugared " _68_10160))
end))
and meta_e_to_string = (fun ( _24_4 ) -> (match (_24_4) with
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
| Microsoft_FStar_Absyn_Syntax.Typ_delayed (_24_243) -> begin
(failwith ("impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_named ((_24_246, l))) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (meta) -> begin
(let _68_10166 = (Support.Prims.pipe_right meta meta_to_string)
in (Support.Microsoft.FStar.Util.format1 "(Meta %s)" _68_10166))
end
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (btv) -> begin
(strBvd btv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (v) -> begin
(sli v.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, c)) -> begin
(let _68_10168 = (binders_to_string " -> " binders)
in (let _68_10167 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _68_10168 _68_10167)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine ((xt, f)) -> begin
(let _68_10171 = (strBvd xt.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_10170 = (Support.Prims.pipe_right xt.Microsoft_FStar_Absyn_Syntax.sort typ_to_string)
in (let _68_10169 = (Support.Prims.pipe_right f formula_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s{%s}" _68_10171 _68_10170 _68_10169))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((t, args)) -> begin
(let q_to_string = (fun ( k ) ( a ) -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((b::[], t)) -> begin
(k (b, t))
end
| _24_281 -> begin
(let _68_10182 = (tag_of_typ t)
in (let _68_10181 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "<Expected a type-lambda! got %s>%s" _68_10182 _68_10181)))
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _68_10183 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "(<Expected a type!>%s)" _68_10183))
end))
in (let qbinder_to_string = (q_to_string (fun ( x ) -> (binder_to_string (Support.Prims.fst x))))
in (let qbody_to_string = (q_to_string (fun ( x ) -> (typ_to_string (Support.Prims.snd x))))
in (let args' = (match (((Support.ST.read Microsoft_FStar_Options.print_implicits) && (not ((is_quant t))))) with
| true -> begin
args
end
| false -> begin
(Support.List.filter (fun ( _24_5 ) -> (match (_24_5) with
| (_24_290, Some (Microsoft_FStar_Absyn_Syntax.Implicit)) -> begin
false
end
| _24_295 -> begin
true
end)) args)
end)
in (match (((is_ite t) && ((Support.List.length args) = 3))) with
| true -> begin
(let _68_10194 = (let _68_10189 = (Support.List.nth args 0)
in (arg_to_string _68_10189))
in (let _68_10193 = (let _68_10190 = (Support.List.nth args 1)
in (arg_to_string _68_10190))
in (let _68_10192 = (let _68_10191 = (Support.List.nth args 2)
in (arg_to_string _68_10191))
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _68_10194 _68_10193 _68_10192))))
end
| false -> begin
(match (((is_b2t t) && ((Support.List.length args) = 1))) with
| true -> begin
(let _68_10195 = (Support.List.nth args 0)
in (Support.Prims.pipe_right _68_10195 arg_to_string))
end
| false -> begin
(match (((is_quant t) && ((Support.List.length args) <= 2))) with
| true -> begin
(let _68_10200 = (quant_to_string t)
in (let _68_10199 = (let _68_10196 = (Support.List.nth args' 0)
in (qbinder_to_string _68_10196))
in (let _68_10198 = (let _68_10197 = (Support.List.nth args' 0)
in (qbody_to_string _68_10197))
in (Support.Microsoft.FStar.Util.format3 "(%s (%s). %s)" _68_10200 _68_10199 _68_10198))))
end
| false -> begin
(match (((is_infix_type_op t) && ((Support.List.length args') = 2))) with
| true -> begin
(let _68_10205 = (let _68_10201 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _68_10201 arg_to_string))
in (let _68_10204 = (Support.Prims.pipe_right t infix_type_op_to_string)
in (let _68_10203 = (let _68_10202 = (Support.List.nth args' 1)
in (Support.Prims.pipe_right _68_10202 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _68_10205 _68_10204 _68_10203))))
end
| false -> begin
(match (((is_unary_type_op t) && ((Support.List.length args') = 1))) with
| true -> begin
(let _68_10208 = (Support.Prims.pipe_right t unary_type_op_to_string)
in (let _68_10207 = (let _68_10206 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _68_10206 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _68_10208 _68_10207)))
end
| false -> begin
(let _68_10210 = (Support.Prims.pipe_right t typ_to_string)
in (let _68_10209 = (Support.Prims.pipe_right args args_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _68_10210 _68_10209)))
end)
end)
end)
end)
end)))))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, t2)) -> begin
(let _68_10212 = (binders_to_string " " binders)
in (let _68_10211 = (Support.Prims.pipe_right t2 typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _68_10212 _68_10211)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, k)) -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_real_names)) with
| true -> begin
(let _68_10214 = (typ_to_string t)
in (let _68_10213 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(%s <: %s)" _68_10214 _68_10213)))
end
| false -> begin
(Support.Prims.pipe_right t typ_to_string)
end)
end
| Microsoft_FStar_Absyn_Syntax.Typ_unknown -> begin
"<UNKNOWN>"
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(match ((Microsoft_FStar_Absyn_Visit.compress_typ_aux false x)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_uvar (_24_319); Microsoft_FStar_Absyn_Syntax.tk = _24_317; Microsoft_FStar_Absyn_Syntax.pos = _24_315; Microsoft_FStar_Absyn_Syntax.fvs = _24_313; Microsoft_FStar_Absyn_Syntax.uvs = _24_311} -> begin
(uvar_t_to_string (uv, k))
end
| t -> begin
(Support.Prims.pipe_right t typ_to_string)
end)
end)))
and uvar_t_to_string = (fun ( _24_325 ) -> (match (_24_325) with
| (uv, k) -> begin
(match ((false && (Support.ST.read Microsoft_FStar_Options.print_real_names))) with
| true -> begin
(let _68_10218 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_10216 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _68_10216))
end)
in (let _68_10217 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format2 "(U%s : %s)" _68_10218 _68_10217)))
end
| false -> begin
(let _68_10220 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_10219 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _68_10219))
end)
in (Support.Microsoft.FStar.Util.format1 "U%s" _68_10220))
end)
end))
and imp_to_string = (fun ( s ) ( _24_6 ) -> (match (_24_6) with
| Some (Microsoft_FStar_Absyn_Syntax.Implicit) -> begin
(Support.String.strcat "#" s)
end
| Some (Microsoft_FStar_Absyn_Syntax.Equality) -> begin
(Support.String.strcat "=" s)
end
| _24_333 -> begin
s
end))
and binder_to_string' = (fun ( is_arrow ) ( b ) -> (match (b) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _68_10225 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.Prims.pipe_right _68_10225 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp a.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _68_10226 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _68_10226 imp))
end
| false -> begin
(let _68_10230 = (let _68_10229 = (let _68_10227 = (strBvd a.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _68_10227 ":"))
in (let _68_10228 = (kind_to_string a.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _68_10229 _68_10228)))
in (imp_to_string _68_10230 imp))
end)
end)
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(match (((Microsoft_FStar_Absyn_Syntax.is_null_binder b) || ((let _68_10231 = (Support.ST.read Microsoft_FStar_Options.print_real_names)
in (Support.Prims.pipe_right _68_10231 Support.Prims.op_Negation)) && (Microsoft_FStar_Absyn_Syntax.is_null_pp x.Microsoft_FStar_Absyn_Syntax.v)))) with
| true -> begin
(typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
end
| false -> begin
(match (((not (is_arrow)) && (not ((Support.ST.read Microsoft_FStar_Options.print_implicits))))) with
| true -> begin
(let _68_10232 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (imp_to_string _68_10232 imp))
end
| false -> begin
(let _68_10236 = (let _68_10235 = (let _68_10233 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.String.strcat _68_10233 ":"))
in (let _68_10234 = (typ_to_string x.Microsoft_FStar_Absyn_Syntax.sort)
in (Support.String.strcat _68_10235 _68_10234)))
in (imp_to_string _68_10236 imp))
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
(let _68_10241 = (Support.Prims.pipe_right bs (Support.List.map arrow_binder_to_string))
in (Support.Prims.pipe_right _68_10241 (Support.String.concat sep)))
end
| false -> begin
(let _68_10242 = (Support.Prims.pipe_right bs (Support.List.map binder_to_string))
in (Support.Prims.pipe_right _68_10242 (Support.String.concat sep)))
end)))
and arg_to_string = (fun ( _24_7 ) -> (match (_24_7) with
| (Support.Microsoft.FStar.Util.Inl (a), imp) -> begin
(let _68_10244 = (typ_to_string a)
in (imp_to_string _68_10244 imp))
end
| (Support.Microsoft.FStar.Util.Inr (x), imp) -> begin
(let _68_10245 = (exp_to_string x)
in (imp_to_string _68_10245 imp))
end))
and args_to_string = (fun ( args ) -> (let args = (match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
args
end
| false -> begin
(filter_imp args)
end)
in (let _68_10247 = (Support.Prims.pipe_right args (Support.List.map arg_to_string))
in (Support.Prims.pipe_right _68_10247 (Support.String.concat " ")))))
and lcomp_typ_to_string = (fun ( lc ) -> (let _68_10250 = (sli lc.Microsoft_FStar_Absyn_Syntax.eff_name)
in (let _68_10249 = (typ_to_string lc.Microsoft_FStar_Absyn_Syntax.res_typ)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _68_10250 _68_10249))))
and comp_typ_to_string = (fun ( c ) -> (match (c.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Total (t) -> begin
(let _68_10252 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _68_10252))
end
| Microsoft_FStar_Absyn_Syntax.Comp (c) -> begin
(let basic = (match (((Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _24_8 ) -> (match (_24_8) with
| Microsoft_FStar_Absyn_Syntax.TOTAL -> begin
true
end
| _24_369 -> begin
false
end)))) && (not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))))) with
| true -> begin
(let _68_10254 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "Tot %s" _68_10254))
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Microsoft_FStar_Absyn_Syntax.lid_equals c.Microsoft_FStar_Absyn_Syntax.effect_name Microsoft_FStar_Absyn_Const.effect_ML_lid))) with
| true -> begin
(typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
end
| false -> begin
(match (((not ((Support.ST.read Microsoft_FStar_Options.print_effect_args))) && (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.Microsoft.FStar.Util.for_some (fun ( _24_9 ) -> (match (_24_9) with
| Microsoft_FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _24_373 -> begin
false
end)))))) with
| true -> begin
(let _68_10256 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format1 "ALL %s" _68_10256))
end
| false -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_effect_args)) with
| true -> begin
(let _68_10260 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _68_10259 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (let _68_10258 = (let _68_10257 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.effect_args (Support.List.map effect_arg_to_string))
in (Support.Prims.pipe_right _68_10257 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format3 "%s (%s) %s" _68_10260 _68_10259 _68_10258))))
end
| false -> begin
(let _68_10262 = (sli c.Microsoft_FStar_Absyn_Syntax.effect_name)
in (let _68_10261 = (typ_to_string c.Microsoft_FStar_Absyn_Syntax.result_typ)
in (Support.Microsoft.FStar.Util.format2 "%s (%s)" _68_10262 _68_10261)))
end)
end)
end)
end)
in (let dec = (let _68_10266 = (Support.Prims.pipe_right c.Microsoft_FStar_Absyn_Syntax.flags (Support.List.collect (fun ( _24_10 ) -> (match (_24_10) with
| Microsoft_FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _68_10265 = (let _68_10264 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 " (decreases %s)" _68_10264))
in (_68_10265)::[])
end
| _24_379 -> begin
[]
end))))
in (Support.Prims.pipe_right _68_10266 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "%s%s" basic dec)))
end))
and effect_arg_to_string = (fun ( e ) -> (match (e) with
| (Support.Microsoft.FStar.Util.Inr (e), _24_385) -> begin
(exp_to_string e)
end
| (Support.Microsoft.FStar.Util.Inl (wp), _24_390) -> begin
(formula_to_string wp)
end))
and formula_to_string = (fun ( phi ) -> (typ_to_string phi))
and formula_to_string_old_now_unused = (fun ( phi ) -> (let const_op = (fun ( f ) ( _24_396 ) -> f)
in (let un_op = (fun ( f ) ( _24_11 ) -> (match (_24_11) with
| (Support.Microsoft.FStar.Util.Inl (t), _24_404)::[] -> begin
(let _68_10278 = (formula_to_string t)
in (Support.Microsoft.FStar.Util.format2 "%s %s" f _68_10278))
end
| _24_408 -> begin
(failwith ("impos"))
end))
in (let bin_top = (fun ( f ) ( _24_12 ) -> (match (_24_12) with
| (Support.Microsoft.FStar.Util.Inl (t1), _24_420)::(Support.Microsoft.FStar.Util.Inl (t2), _24_415)::[] -> begin
(let _68_10284 = (formula_to_string t1)
in (let _68_10283 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _68_10284 f _68_10283)))
end
| _24_424 -> begin
(failwith ("Impos"))
end))
in (let bin_eop = (fun ( f ) ( _24_13 ) -> (match (_24_13) with
| (Support.Microsoft.FStar.Util.Inr (e1), _24_436)::(Support.Microsoft.FStar.Util.Inr (e2), _24_431)::[] -> begin
(let _68_10290 = (exp_to_string e1)
in (let _68_10289 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format3 "%s %s %s" _68_10290 f _68_10289)))
end
| _24_440 -> begin
(failwith ("impos"))
end))
in (let ite = (fun ( _24_14 ) -> (match (_24_14) with
| (Support.Microsoft.FStar.Util.Inl (t1), _24_455)::(Support.Microsoft.FStar.Util.Inl (t2), _24_450)::(Support.Microsoft.FStar.Util.Inl (t3), _24_445)::[] -> begin
(let _68_10295 = (formula_to_string t1)
in (let _68_10294 = (formula_to_string t2)
in (let _68_10293 = (formula_to_string t3)
in (Support.Microsoft.FStar.Util.format3 "if %s then %s else %s" _68_10295 _68_10294 _68_10293))))
end
| _24_459 -> begin
(failwith ("impos"))
end))
in (let eq_op = (fun ( _24_15 ) -> (match (_24_15) with
| (Support.Microsoft.FStar.Util.Inl (t1), _24_480)::(Support.Microsoft.FStar.Util.Inl (t2), _24_475)::(Support.Microsoft.FStar.Util.Inr (e1), _24_470)::(Support.Microsoft.FStar.Util.Inr (e2), _24_465)::[] -> begin
(match ((Support.ST.read Microsoft_FStar_Options.print_implicits)) with
| true -> begin
(let _68_10301 = (typ_to_string t1)
in (let _68_10300 = (typ_to_string t2)
in (let _68_10299 = (exp_to_string e1)
in (let _68_10298 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format4 "Eq2 %s %s %s %s" _68_10301 _68_10300 _68_10299 _68_10298)))))
end
| false -> begin
(let _68_10303 = (exp_to_string e1)
in (let _68_10302 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _68_10303 _68_10302)))
end)
end
| (Support.Microsoft.FStar.Util.Inr (e1), _24_491)::(Support.Microsoft.FStar.Util.Inr (e2), _24_486)::[] -> begin
(let _68_10305 = (exp_to_string e1)
in (let _68_10304 = (exp_to_string e2)
in (Support.Microsoft.FStar.Util.format2 "%s == %s" _68_10305 _68_10304)))
end
| _24_495 -> begin
(failwith ("Impossible"))
end))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (bin_top "/\\")))::((Microsoft_FStar_Absyn_Const.or_lid, (bin_top "\\/")))::((Microsoft_FStar_Absyn_Const.imp_lid, (bin_top "==>")))::((Microsoft_FStar_Absyn_Const.iff_lid, (bin_top "<==>")))::((Microsoft_FStar_Absyn_Const.ite_lid, ite))::((Microsoft_FStar_Absyn_Const.not_lid, (un_op "~")))::((Microsoft_FStar_Absyn_Const.eqT_lid, (bin_top "==")))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op "True")))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op "False")))::[]
in (let fallback = (fun ( phi ) -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((binders, phi)) -> begin
(let _68_10344 = (binders_to_string " " binders)
in (let _68_10343 = (formula_to_string phi)
in (Support.Microsoft.FStar.Util.format2 "(fun %s => %s)" _68_10344 _68_10343)))
end
| _24_505 -> begin
(typ_to_string phi)
end))
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match ((Support.Prims.pipe_right connectives (Support.List.tryFind (fun ( _24_515 ) -> (match (_24_515) with
| (l, _24_514) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some ((_24_518, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, _24_524, body))) -> begin
(let _68_10362 = (binders_to_string " " vars)
in (let _68_10361 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(forall %s. %s)" _68_10362 _68_10361)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, _24_531, body))) -> begin
(let _68_10364 = (binders_to_string " " vars)
in (let _68_10363 = (formula_to_string body)
in (Support.Microsoft.FStar.Util.format2 "(exists %s. %s)" _68_10364 _68_10363)))
end))))))))))
and exp_to_string = (fun ( x ) -> (match ((let _68_10366 = (Microsoft_FStar_Absyn_Util.compress_exp x)
in _68_10366.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_24_538) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _24_542))) -> begin
(exp_to_string e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, t)) -> begin
(uvar_e_to_string (uv, t))
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (bvv) -> begin
(strBvd bvv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _24_554)) -> begin
(sli fv.Microsoft_FStar_Absyn_Syntax.v)
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
(Support.Prims.pipe_right c const_to_string)
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, e)) -> begin
(let _68_10368 = (binders_to_string " " binders)
in (let _68_10367 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "(fun %s -> %s)" _68_10368 _68_10367)))
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
(let _68_10371 = (let _68_10370 = (let _68_10369 = (Support.List.map exp_to_string es)
in (Support.String.concat "; " _68_10369))
in (Support.String.strcat "%[" _68_10370))
in (Support.String.strcat _68_10371 "]"))
end
| None -> begin
(let args' = (let _68_10373 = (filter_imp args)
in (Support.Prims.pipe_right _68_10373 (Support.List.filter (fun ( _24_16 ) -> (match (_24_16) with
| (Support.Microsoft.FStar.Util.Inr (_24_573), _24_576) -> begin
true
end
| _24_579 -> begin
false
end)))))
in (match (((is_infix_prim_op e) && ((Support.List.length args') = 2))) with
| true -> begin
(let _68_10378 = (let _68_10374 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _68_10374 arg_to_string))
in (let _68_10377 = (Support.Prims.pipe_right e infix_prim_op_to_string)
in (let _68_10376 = (let _68_10375 = (Support.List.nth args' 1)
in (Support.Prims.pipe_right _68_10375 arg_to_string))
in (Support.Microsoft.FStar.Util.format3 "(%s %s %s)" _68_10378 _68_10377 _68_10376))))
end
| false -> begin
(match (((is_unary_prim_op e) && ((Support.List.length args') = 1))) with
| true -> begin
(let _68_10381 = (Support.Prims.pipe_right e unary_prim_op_to_string)
in (let _68_10380 = (let _68_10379 = (Support.List.nth args' 0)
in (Support.Prims.pipe_right _68_10379 arg_to_string))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _68_10381 _68_10380)))
end
| false -> begin
(let _68_10383 = (Support.Prims.pipe_right e exp_to_string)
in (let _68_10382 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _68_10383 _68_10382)))
end)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _68_10391 = (Support.Prims.pipe_right e exp_to_string)
in (let _68_10390 = (let _68_10389 = (Support.Prims.pipe_right pats (Support.List.map (fun ( _24_588 ) -> (match (_24_588) with
| (p, wopt, e) -> begin
(let _68_10388 = (Support.Prims.pipe_right p pat_to_string)
in (let _68_10387 = (match (wopt) with
| None -> begin
""
end
| Some (w) -> begin
(let _68_10385 = (Support.Prims.pipe_right w exp_to_string)
in (Support.Microsoft.FStar.Util.format1 "when %s" _68_10385))
end)
in (let _68_10386 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s %s -> %s" _68_10388 _68_10387 _68_10386))))
end))))
in (Support.Microsoft.FStar.Util.concat_l "\n\t" _68_10389))
in (Support.Microsoft.FStar.Util.format2 "(match %s with %s)" _68_10391 _68_10390)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t, _24_595)) -> begin
(let _68_10393 = (Support.Prims.pipe_right e exp_to_string)
in (let _68_10392 = (Support.Prims.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s:%s)" _68_10393 _68_10392)))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let ((lbs, e)) -> begin
(let _68_10395 = (lbs_to_string lbs)
in (let _68_10394 = (Support.Prims.pipe_right e exp_to_string)
in (Support.Microsoft.FStar.Util.format2 "%s in %s" _68_10395 _68_10394)))
end))
and uvar_e_to_string = (fun ( _24_605 ) -> (match (_24_605) with
| (uv, _24_604) -> begin
(let _68_10398 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_10397 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _68_10397))
end)
in (Support.String.strcat "\'e" _68_10398))
end))
and lbs_to_string = (fun ( lbs ) -> (let _68_10405 = (let _68_10404 = (Support.Prims.pipe_right (Support.Prims.snd lbs) (Support.List.map (fun ( lb ) -> (let _68_10403 = (lbname_to_string lb.Microsoft_FStar_Absyn_Syntax.lbname)
in (let _68_10402 = (Support.Prims.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbtyp typ_to_string)
in (let _68_10401 = (Support.Prims.pipe_right lb.Microsoft_FStar_Absyn_Syntax.lbdef exp_to_string)
in (Support.Microsoft.FStar.Util.format3 "%s:%s = %s" _68_10403 _68_10402 _68_10401)))))))
in (Support.Microsoft.FStar.Util.concat_l "\n and " _68_10404))
in (Support.Microsoft.FStar.Util.format2 "let %s %s" (match ((Support.Prims.fst lbs)) with
| true -> begin
"rec"
end
| false -> begin
""
end) _68_10405)))
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
and either_l_to_string = (fun ( delim ) ( l ) -> (let _68_10410 = (Support.Prims.pipe_right l (Support.List.map either_to_string))
in (Support.Prims.pipe_right _68_10410 (Support.Microsoft.FStar.Util.concat_l delim))))
and meta_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Meta_refresh_label ((t, _24_623, _24_625)) -> begin
(let _68_10412 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format1 "(refresh) %s" _68_10412))
end
| Microsoft_FStar_Absyn_Syntax.Meta_labeled ((t, l, _24_631, _24_633)) -> begin
(let _68_10413 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(labeled \"%s\") %s" l _68_10413))
end
| Microsoft_FStar_Absyn_Syntax.Meta_named ((_24_637, l)) -> begin
(sli l)
end
| Microsoft_FStar_Absyn_Syntax.Meta_pattern ((t, ps)) -> begin
(let _68_10415 = (args_to_string ps)
in (let _68_10414 = (Support.Prims.pipe_right t typ_to_string)
in (Support.Microsoft.FStar.Util.format2 "{:pattern %s} %s" _68_10415 _68_10414)))
end
| Microsoft_FStar_Absyn_Syntax.Meta_slack_formula ((t1, t2, _24_648)) -> begin
(let _68_10417 = (formula_to_string t1)
in (let _68_10416 = (formula_to_string t2)
in (Support.Microsoft.FStar.Util.format2 "%s /\\ %s" _68_10417 _68_10416)))
end))
and kind_to_string = (fun ( x ) -> (match ((let _68_10419 = (Microsoft_FStar_Absyn_Util.compress_kind x)
in _68_10419.Microsoft_FStar_Absyn_Syntax.n)) with
| Microsoft_FStar_Absyn_Syntax.Kind_lam (_24_653) -> begin
(failwith ("Impossible"))
end
| Microsoft_FStar_Absyn_Syntax.Kind_delayed (_24_656) -> begin
(failwith ("Impossible"))
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
(let _68_10421 = (sli n)
in (let _68_10420 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "%s %s" _68_10421 _68_10420)))
end)
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((binders, k)) -> begin
(let _68_10423 = (binders_to_string " -> " binders)
in (let _68_10422 = (Support.Prims.pipe_right k kind_to_string)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _68_10423 _68_10422)))
end
| Microsoft_FStar_Absyn_Syntax.Kind_unknown -> begin
"_"
end))
and uvar_k_to_string = (fun ( uv ) -> (let _68_10425 = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_10424 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _68_10424))
end)
in (Support.String.strcat "\'k_" _68_10425)))
and uvar_k_to_string' = (fun ( _24_678 ) -> (match (_24_678) with
| (uv, args) -> begin
(let str = (match ((Support.ST.read Microsoft_FStar_Options.hide_uvar_nums)) with
| true -> begin
"?"
end
| false -> begin
(let _68_10427 = (Support.Microsoft.FStar.Unionfind.uvar_id uv)
in (Support.Microsoft.FStar.Util.string_of_int _68_10427))
end)
in (let _68_10428 = (args_to_string args)
in (Support.Microsoft.FStar.Util.format2 "(\'k_%s %s)" str _68_10428)))
end))
and pat_to_string = (fun ( x ) -> (match (x.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((l, _24_683, pats)) -> begin
(let _68_10432 = (sli l.Microsoft_FStar_Absyn_Syntax.v)
in (let _68_10431 = (let _68_10430 = (Support.List.map pat_to_string pats)
in (Support.Prims.pipe_right _68_10430 (Support.String.concat " ")))
in (Support.Microsoft.FStar.Util.format2 "(%s %s)" _68_10432 _68_10431)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _24_689)) -> begin
(let _68_10433 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".%s" _68_10433))
end
| Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((x, _24_694)) -> begin
(let _68_10434 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 ".\'%s" _68_10434))
end
| Microsoft_FStar_Absyn_Syntax.Pat_var ((x, true)) -> begin
(let _68_10435 = (strBvd x.Microsoft_FStar_Absyn_Syntax.v)
in (Support.Microsoft.FStar.Util.format1 "#%s" _68_10435))
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
| Microsoft_FStar_Absyn_Syntax.Pat_wild (_24_710) -> begin
"_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_twild (_24_713) -> begin
"\'_"
end
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(let _68_10436 = (Support.List.map pat_to_string ps)
in (Support.Microsoft.FStar.Util.concat_l " | " _68_10436))
end))

let subst_to_string = (fun ( subst ) -> (let _68_10444 = (let _68_10443 = (Support.List.map (fun ( _24_17 ) -> (match (_24_17) with
| Support.Microsoft.FStar.Util.Inl ((a, t)) -> begin
(let _68_10440 = (strBvd a)
in (let _68_10439 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _68_10440 _68_10439)))
end
| Support.Microsoft.FStar.Util.Inr ((x, e)) -> begin
(let _68_10442 = (strBvd x)
in (let _68_10441 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format2 "(%s -> %s)" _68_10442 _68_10441)))
end)) subst)
in (Support.Prims.pipe_right _68_10443 (Support.String.concat ", ")))
in (Support.Prims.pipe_left (Support.Microsoft.FStar.Util.format1 "{%s}") _68_10444)))

let freevars_to_string = (fun ( fvs ) -> (let f = (fun ( l ) -> (let _68_10450 = (let _68_10449 = (Support.Prims.pipe_right l Support.Microsoft.FStar.Util.set_elements)
in (Support.Prims.pipe_right _68_10449 (Support.List.map (fun ( t ) -> (strBvd t.Microsoft_FStar_Absyn_Syntax.v)))))
in (Support.Prims.pipe_right _68_10450 (Support.String.concat ", "))))
in (let _68_10452 = (f fvs.Microsoft_FStar_Absyn_Syntax.ftvs)
in (let _68_10451 = (f fvs.Microsoft_FStar_Absyn_Syntax.fxvs)
in (Support.Microsoft.FStar.Util.format2 "ftvs={%s}, fxvs={%s}" _68_10452 _68_10451)))))

let qual_to_string = (fun ( _24_18 ) -> (match (_24_18) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
"logic"
end
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
"opaque"
end
| Microsoft_FStar_Absyn_Syntax.Discriminator (_24_737) -> begin
"discriminator"
end
| Microsoft_FStar_Absyn_Syntax.Projector (_24_740) -> begin
"projector"
end
| Microsoft_FStar_Absyn_Syntax.RecordType (ids) -> begin
(let _68_10457 = (let _68_10456 = (Support.Prims.pipe_right ids (Support.List.map (fun ( lid ) -> lid.Microsoft_FStar_Absyn_Syntax.ident.Microsoft_FStar_Absyn_Syntax.idText)))
in (Support.Prims.pipe_right _68_10456 (Support.String.concat ", ")))
in (Support.Microsoft.FStar.Util.format1 "record(%s)" _68_10457))
end
| _24_746 -> begin
"other"
end))

let quals_to_string = (fun ( quals ) -> (let _68_10460 = (Support.Prims.pipe_right quals (Support.List.map qual_to_string))
in (Support.Prims.pipe_right _68_10460 (Support.String.concat " "))))

let rec sigelt_to_string = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.ResetOptions, _24_751)) -> begin
"#reset-options"
end
| Microsoft_FStar_Absyn_Syntax.Sig_pragma ((Microsoft_FStar_Absyn_Syntax.SetOptions (s), _24_757)) -> begin
(Support.Microsoft.FStar.Util.format1 "#set-options \"%s\"" s)
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((lid, tps, k, _24_764, _24_766, quals, _24_769)) -> begin
(let _68_10465 = (quals_to_string quals)
in (let _68_10464 = (binders_to_string " " tps)
in (let _68_10463 = (kind_to_string k)
in (Support.Microsoft.FStar.Util.format4 "%s type %s %s : %s" _68_10465 lid.Microsoft_FStar_Absyn_Syntax.str _68_10464 _68_10463))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, k, t, _24_777, _24_779)) -> begin
(let _68_10468 = (binders_to_string " " tps)
in (let _68_10467 = (kind_to_string k)
in (let _68_10466 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format4 "type %s %s : %s = %s" lid.Microsoft_FStar_Absyn_Syntax.str _68_10468 _68_10467 _68_10466))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((lid, t, _24_785, _24_787, _24_789, _24_791)) -> begin
(let _68_10469 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "datacon %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _68_10469))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _24_798)) -> begin
(let _68_10471 = (quals_to_string quals)
in (let _68_10470 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format3 "%s val %s : %s" _68_10471 lid.Microsoft_FStar_Absyn_Syntax.str _68_10470)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((lid, f, _24_804, _24_806)) -> begin
(let _68_10472 = (typ_to_string f)
in (Support.Microsoft.FStar.Util.format2 "val %s : %s" lid.Microsoft_FStar_Absyn_Syntax.str _68_10472))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let ((lbs, _24_811, _24_813, b)) -> begin
(lbs_to_string lbs)
end
| Microsoft_FStar_Absyn_Syntax.Sig_main ((e, _24_819)) -> begin
(let _68_10473 = (exp_to_string e)
in (Support.Microsoft.FStar.Util.format1 "let _ = %s" _68_10473))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _24_824, _24_826, _24_828)) -> begin
(let _68_10474 = (Support.List.map sigelt_to_string ses)
in (Support.Prims.pipe_right _68_10474 (Support.String.concat "\n")))
end
| Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_24_832) -> begin
"new_effect { ... }"
end
| Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_24_835) -> begin
"sub_effect ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_24_838) -> begin
"kind ..."
end
| Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev ((l, tps, c, _24_844, _24_846)) -> begin
(let _68_10477 = (sli l)
in (let _68_10476 = (binders_to_string " " tps)
in (let _68_10475 = (comp_typ_to_string c)
in (Support.Microsoft.FStar.Util.format3 "effect %s %s = %s" _68_10477 _68_10476 _68_10475))))
end))

let format_error = (fun ( r ) ( msg ) -> (let _68_10482 = (Support.Microsoft.FStar.Range.string_of_range r)
in (Support.Microsoft.FStar.Util.format2 "%s: %s\n" _68_10482 msg)))

let rec sigelt_to_string_short = (fun ( x ) -> (match (x) with
| Microsoft_FStar_Absyn_Syntax.Sig_let (((_24_853, {Microsoft_FStar_Absyn_Syntax.lbname = Support.Microsoft.FStar.Util.Inr (l); Microsoft_FStar_Absyn_Syntax.lbtyp = t; Microsoft_FStar_Absyn_Syntax.lbeff = _24_857; Microsoft_FStar_Absyn_Syntax.lbdef = _24_855}::[]), _24_865, _24_867, _24_869)) -> begin
(let _68_10485 = (typ_to_string t)
in (Support.Microsoft.FStar.Util.format2 "let %s : %s" l.Microsoft_FStar_Absyn_Syntax.str _68_10485))
end
| _24_873 -> begin
(let _68_10488 = (let _68_10487 = (Microsoft_FStar_Absyn_Util.lids_of_sigelt x)
in (Support.Prims.pipe_right _68_10487 (Support.List.map (fun ( l ) -> l.Microsoft_FStar_Absyn_Syntax.str))))
in (Support.Prims.pipe_right _68_10488 (Support.String.concat ", ")))
end))

let rec modul_to_string = (fun ( m ) -> (let _68_10493 = (sli m.Microsoft_FStar_Absyn_Syntax.name)
in (let _68_10492 = (let _68_10491 = (Support.List.map sigelt_to_string m.Microsoft_FStar_Absyn_Syntax.declarations)
in (Support.Prims.pipe_right _68_10491 (Support.String.concat "\n")))
in (Support.Microsoft.FStar.Util.format2 "module %s\n%s" _68_10493 _68_10492))))





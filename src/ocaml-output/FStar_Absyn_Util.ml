
open Prims

let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Fatal: %s" ((s)::[]))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(

let _32_36 = (let _129_8 = (let _129_7 = (FStar_Range.string_of_range r)
in (_129_7)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _129_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(

let _32_40 = (FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((s)::[]))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Error: %s" ((s)::[]))
end
| _32_45 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _32_1 -> (match (_32_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _32_60 -> begin
false
end))


type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}


let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun _32_66 -> (match (()) with
| () -> begin
(let _129_36 = (let _129_35 = (let _129_31 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _129_31))
in (let _129_34 = (let _129_33 = (let _129_32 = (

let _32_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _129_32))
in (Prims.strcat "_" _129_33))
in (Prims.strcat _129_35 _129_34)))
in (Prims.strcat "_" _129_36))
end)); reset = (fun _32_69 -> (match (()) with
| () -> begin
(

let _32_70 = (FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"))
in (FStar_Util.incr n_resets))
end))}))


let gensym : Prims.unit  ->  Prims.string = (fun _32_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))


let reset_gensym : Prims.unit  ->  Prims.unit = (fun _32_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))


let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| _129_44 when (_129_44 = (Prims.parse_int "0")) -> begin
[]
end
| n -> begin
(let _129_46 = (gensym ())
in (let _129_45 = (gensyms (n - (Prims.parse_int "1")))
in (_129_46)::_129_45))
end))


let genident : FStar_Range.range Prims.option  ->  FStar_Ident.ident = (fun r -> (

let sym = (gensym ())
in (match (r) with
| None -> begin
(FStar_Ident.mk_ident ((sym), (FStar_Absyn_Syntax.dummyRange)))
end
| Some (r) -> begin
(FStar_Ident.mk_ident ((sym), (r)))
end)))


let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Ident.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Ident.idText))


let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange)


let mkbvd = (fun _32_87 -> (match (_32_87) with
| (x, y) -> begin
{FStar_Absyn_Syntax.ppname = x; FStar_Absyn_Syntax.realname = y}
end))


let setsort = (fun w t -> {FStar_Absyn_Syntax.v = w.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = w.FStar_Absyn_Syntax.p})


let withinfo = (fun e s r -> {FStar_Absyn_Syntax.v = e; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = r})


let withsort = (fun e s -> (withinfo e s FStar_Absyn_Syntax.dummyRange))


let bvar_ppname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)


let bvar_realname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname)


let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.FStar_Absyn_Syntax.v bv2.FStar_Absyn_Syntax.v))


let lbname_eq = (fun l1 l2 -> (match (((l1), (l2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _32_114 -> begin
false
end))


let fvar_eq = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))


let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})


let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)


let btvar_to_typ : FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.typ = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))


let bvd_to_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))


let bvar_to_exp : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.exp = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))


let bvd_to_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))


let new_bvd = (fun ropt -> (

let f = (fun ropt -> (

let id = (genident ropt)
in (mkbvd ((id), (id)))))
in (f ropt)))


let freshen_bvd = (fun bvd' -> (let _129_87 = (let _129_86 = (genident (Some ((range_of_bvd bvd'))))
in ((bvd'.FStar_Absyn_Syntax.ppname), (_129_86)))
in (mkbvd _129_87)))


let freshen_bvar = (fun b -> (let _129_89 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _129_89 b.FStar_Absyn_Syntax.sort)))


let gen_bvar = (fun sort -> (

let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))


let gen_bvar_p = (fun r sort -> (

let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))


let bvdef_of_str = (fun s -> (

let f = (fun s -> (

let id = (FStar_Ident.id_of_text s)
in (mkbvd ((id), (id)))))
in (f s)))


let set_bvd_range = (fun bvd r -> {FStar_Absyn_Syntax.ppname = (FStar_Ident.mk_ident ((bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText), (r))); FStar_Absyn_Syntax.realname = (FStar_Ident.mk_ident ((bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText), (r)))})


let set_lid_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun l r -> (

let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[])) (FStar_List.map (fun i -> (FStar_Ident.mk_ident ((i.FStar_Ident.idText), (r))))))
in (FStar_Ident.lid_of_ids ids)))


let fv : FStar_Ident.lid  ->  (FStar_Ident.lid, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l -> (withinfo l FStar_Absyn_Syntax.tun (FStar_Ident.range_of_lid l)))


let fvvar_of_lid = (fun l t -> (withinfo l t (FStar_Ident.range_of_lid l)))


let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _129_114 = (let _129_113 = (let _129_112 = (set_lid_range l r)
in (fv _129_112))
in ((_129_113), (dc)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _129_114 None r)))


let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))


let order_bvd = (fun x y -> (match (((x), (y))) with
| (FStar_Util.Inl (_32_160), FStar_Util.Inr (_32_163)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Util.Inr (_32_167), FStar_Util.Inl (_32_170)) -> begin
(Prims.parse_int "1")
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))


let arg_of_non_null_binder = (fun _32_185 -> (match (_32_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _129_123 = (let _129_122 = (btvar_to_typ a)
in FStar_Util.Inl (_129_122))
in ((_129_123), (imp)))
end
| FStar_Util.Inr (x) -> begin
(let _129_125 = (let _129_124 = (bvar_to_exp x)
in FStar_Util.Inr (_129_124))
in ((_129_125), (imp)))
end)
end))


let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _129_129 = (arg_of_non_null_binder b)
in (_129_129)::[])
end))))


let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _129_139 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(

let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _129_134 = (let _129_133 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_129_133))
in ((_129_134), ((Prims.snd b))))
end
| FStar_Util.Inr (x) -> begin
(let _129_136 = (let _129_135 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_129_135))
in ((_129_136), ((Prims.snd b))))
end)
in (let _129_137 = (arg_of_non_null_binder b)
in ((b), (_129_137))))
end else begin
(let _129_138 = (arg_of_non_null_binder b)
in ((b), (_129_138)))
end)))
in (FStar_All.pipe_right _129_139 FStar_List.unzip)))


let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let b = (let _129_145 = (let _129_144 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _129_144))
in (FStar_Ident.id_of_text _129_145))
in (

let b = (bvd_to_bvar_s (mkbvd ((b), (b))) a.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inl (b)), (imp))))
end
| (FStar_Util.Inr (y), imp) -> begin
(

let x = (let _129_147 = (let _129_146 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _129_146))
in (FStar_Ident.id_of_text _129_147))
in (

let x = (bvd_to_bvar_s (mkbvd ((x), (x))) y.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inr (x)), (imp))))
end)
end else begin
b
end))))


let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _129_151 = (let _129_150 = (name_binders binders)
in ((_129_150), (comp)))
in (FStar_Absyn_Syntax.mk_Typ_fun _129_151 None t.FStar_Absyn_Syntax.pos))
end
| _32_220 -> begin
t
end))


let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _32_2 -> (match (_32_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _129_156 = (let _129_155 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _129_155))
in ((_129_156), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _129_158 = (let _129_157 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _129_157))
in ((_129_158), (imp)))
end)))))


let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _32_3 -> (match (_32_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _129_163 = (let _129_162 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_129_162))
in ((_129_163), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _129_165 = (let _129_164 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_129_164))
in ((_129_165), (imp)))
end)))))


let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _129_171 = (let _129_168 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _129_168 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _129_170 = (let _129_169 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _129_169 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _129_171 _129_170))))


let subst_to_string = (fun s -> (let _129_174 = (FStar_All.pipe_right s (FStar_List.map (fun _32_4 -> (match (_32_4) with
| FStar_Util.Inl (b, _32_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _32_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _129_174 (FStar_String.concat ", "))))


let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _32_5 -> (match (_32_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _32_262 -> begin
None
end))))


let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _32_6 -> (match (_32_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _32_271 -> begin
None
end))))


let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _32_278 -> begin
(

let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _129_199 = (let _129_198 = (compose_subst s' s)
in (let _129_197 = (FStar_Util.mk_ref None)
in ((t'), (_129_198), (_129_197))))
in (FStar_Absyn_Syntax.mk_Typ_delayed _129_199 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (mk_t ())
in (

let _32_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(

let rec aux = (fun s' -> (match (s') with
| (s0)::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _32_305 -> begin
(aux rest)
end)
end
| _32_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _32_316 -> begin
(let _129_204 = (let _129_203 = (FStar_Util.mk_ref None)
in ((t0), (s), (_129_203)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _129_204 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _32_323 -> begin
(

let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _129_209 = (let _129_208 = (compose_subst s' s)
in (let _129_207 = (FStar_Util.mk_ref None)
in ((e), (_129_208), (_129_207))))
in (FStar_Absyn_Syntax.mk_Exp_delayed _129_209 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let rec aux = (fun s -> (match (s) with
| (s0)::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _32_340 -> begin
(aux rest)
end)
end
| _32_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _32_350 -> begin
(let _129_213 = (let _129_212 = (FStar_Util.mk_ref None)
in ((e0), (s), (_129_212)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _129_213 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _32_357 -> begin
(

let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _129_218 = (let _129_217 = (compose_subst s' s)
in (let _129_216 = (FStar_Util.mk_ref None)
in ((k), (_129_217), (_129_216))))
in (FStar_Absyn_Syntax.mk_Kind_delayed _129_218 k0.FStar_Absyn_Syntax.pos))
end
| _32_368 -> begin
(let _129_220 = (let _129_219 = (FStar_Util.mk_ref None)
in ((k0), (s), (_129_219)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _129_220 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _32_7 -> (match (_32_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _129_224 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_129_224))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _32_381 -> begin
(

let _32_382 = t
in (let _129_234 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _129_233 = (FStar_List.map (fun _32_8 -> (match (_32_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _129_229 = (let _129_228 = (subst_typ' s t)
in FStar_Util.Inl (_129_228))
in ((_129_229), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _129_231 = (let _129_230 = (subst_exp' s e)
in FStar_Util.Inr (_129_230))
in ((_129_231), (imp)))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _129_232 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _32_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _129_234; FStar_Absyn_Syntax.effect_args = _129_233; FStar_Absyn_Syntax.flags = _129_232}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _32_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _129_237 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _129_237))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _129_238 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _129_238))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))


let mk_subst = (fun s -> (s)::[])


let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))


let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))


let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))


let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))


let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))


let subst_binder = (fun s _32_9 -> (match (_32_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _129_266 = (let _129_265 = (

let _32_423 = a
in (let _129_264 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _32_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _129_264; FStar_Absyn_Syntax.p = _32_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_129_265))
in ((_129_266), (imp)))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _129_269 = (let _129_268 = (

let _32_429 = x
in (let _129_267 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _32_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _129_267; FStar_Absyn_Syntax.p = _32_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_129_268))
in ((_129_269), (imp)))
end))


let subst_arg = (fun s _32_10 -> (match (_32_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _129_273 = (let _129_272 = (subst_typ s t)
in FStar_Util.Inl (_129_272))
in ((_129_273), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _129_275 = (let _129_274 = (subst_exp s e)
in FStar_Util.Inr (_129_274))
in ((_129_275), (imp)))
end))


let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _32_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))


let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _32_450 -> begin
(FStar_List.map (subst_arg s) args)
end))


let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match (((f), (a))) with
| ((FStar_Util.Inl (a), _32_456), (FStar_Util.Inl (t), _32_461)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t)))
end
| ((FStar_Util.Inr (x), _32_467), (FStar_Util.Inr (v), _32_472)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v)))
end
| _32_476 -> begin
(FStar_All.failwith "Ill-formed substitution")
end))


let mk_subst_one_binder : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.binder  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _129_290 = (let _129_289 = (let _129_288 = (btvar_to_typ a)
in ((b.FStar_Absyn_Syntax.v), (_129_288)))
in FStar_Util.Inl (_129_289))
in (_129_290)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _129_293 = (let _129_292 = (let _129_291 = (bvar_to_exp x)
in ((y.FStar_Absyn_Syntax.v), (_129_291)))
in FStar_Util.Inr (_129_292))
in (_129_293)::[])
end
end
| _32_490 -> begin
[]
end)
end)


let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (

let rec aux = (fun out bs1 bs2 -> (match (((bs1), (bs2))) with
| ([], []) -> begin
Some (out)
end
| ((b1)::bs1, (b2)::bs2) -> begin
(let _129_305 = (let _129_304 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _129_304 out))
in (aux _129_305 bs1 bs2))
end
| _32_508 -> begin
None
end))
in (aux [] bs1 bs2)))


let subst_of_list : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.subst = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)


type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}


let is_Mkred_ctrl : red_ctrl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl"))))


let alpha_ctrl : red_ctrl = {stop_if_empty_subst = false; descend = true}


let subst_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = true}


let null_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = false}


let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))


let map_knd = (fun s vk mt me descend binders k -> (let _129_326 = (subst_kind' s k)
in ((_129_326), (descend))))


let map_typ = (fun s mk vt me descend binders t -> (let _129_334 = (subst_typ' s t)
in ((_129_334), (descend))))


let map_exp = (fun s mk me ve descend binders e -> (let _129_342 = (subst_exp' s e)
in ((_129_342), (descend))))


let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _32_11 -> (match (_32_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _129_359 = (let _129_358 = (map_exp descend binders e)
in (FStar_All.pipe_right _129_358 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_129_359))
end
| f -> begin
f
end)))))


let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _32_557 = (map_typ descend binders t)
in (match (_32_557) with
| (t, descend) -> begin
(let _129_382 = (FStar_Absyn_Syntax.mk_Total t)
in ((_129_382), (descend)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _32_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_32_562) with
| (t, descend) -> begin
(

let _32_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_32_565) with
| (args, descend) -> begin
(let _129_385 = (let _129_384 = (

let _32_566 = ct
in (let _129_383 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _32_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _129_383}))
in (FStar_Absyn_Syntax.mk_Comp _129_384))
in ((_129_385), (descend)))
end))
end))
end))


let visit_knd = (fun s vk mt me ctrl binders k -> (

let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(

let _32_579 = (vk null_ctrl binders k)
in (match (_32_579) with
| (k, _32_578) -> begin
((k), (ctrl))
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))


let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (

let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(

let k' = (let _129_431 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _129_431))
in (

let k' = (compress_kind k')
in (

let _32_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _129_433 = (let _129_432 = (subst_of_list formals actuals)
in (subst_kind _129_432 k'))
in (compress_kind _129_433))
end
| _32_602 -> begin
if ((FStar_List.length actuals) = (Prims.parse_int "0")) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _32_604 -> begin
k
end)
end
| _32_606 -> begin
k
end)))


let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (

let visit_prod = (fun bs tc -> (

let _32_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _32_620 b -> (match (_32_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _32_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_32_629) with
| (k, _32_628) -> begin
(

let a = (

let _32_630 = a
in {FStar_Absyn_Syntax.v = _32_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _32_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inl (a)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (

let _32_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inl (a)), (s), (boundvars'))
end
| _32_636 -> begin
(

let b = (let _129_510 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _129_510 k))
in (

let s = (let _129_513 = (let _129_512 = (let _129_511 = (btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_129_511)))
in FStar_Util.Inl (_129_512))
in (extend_subst _129_513 s))
in ((FStar_Util.Inl (b)), (s), ((FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_32_642) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _32_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_32_650) with
| (t, _32_649) -> begin
(

let x = (

let _32_651 = x
in {FStar_Absyn_Syntax.v = _32_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _32_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inr (x)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (

let _32_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inr (x)), (s), (boundvars'))
end
| _32_657 -> begin
(

let y = (let _129_523 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _129_523 t))
in (

let s = (let _129_526 = (let _129_525 = (let _129_524 = (bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_129_524)))
in FStar_Util.Inr (_129_525))
in (extend_subst _129_526 s))
in ((FStar_Util.Inr (y)), (s), ((FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_32_663) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end)
end)) (([]), (boundvars), (s))))
in (match (_32_667) with
| (bs, boundvars, s) -> begin
(

let tc = (match (((s), (tc))) with
| ([], _32_670) -> begin
tc
end
| (_32_673, FStar_Util.Inl (t)) -> begin
(let _129_537 = (let _129_536 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _129_536))
in FStar_Util.Inl (_129_537))
end
| (_32_678, FStar_Util.Inr (c)) -> begin
(let _129_560 = (let _129_559 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _129_559))
in FStar_Util.Inr (_129_560))
end)
in (((FStar_List.rev bs)), (tc)))
end)))
in (

let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_32_685) -> begin
(let _129_562 = (let _129_561 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _129_561))
in ((_129_562), (ctrl)))
end
| _32_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _129_572 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t0.FStar_Absyn_Syntax.pos)
in ((_129_572), (ctrl)))
end
| _32_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod ((((FStar_Util.Inr (x)), (None)))::[]) (FStar_Util.Inl (t)))) with
| (((FStar_Util.Inr (x), _32_706))::[], FStar_Util.Inl (t)) -> begin
(let _129_573 = (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_129_573), (ctrl)))
end
| _32_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _129_574 = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_129_574), (ctrl)))
end
| _32_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _32_725 -> begin
(

let _32_729 = (vt null_ctrl boundvars t)
in (match (_32_729) with
| (t, _32_728) -> begin
((t), (ctrl))
end))
end))))
and compress_typ' : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(

let res = (let _129_594 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _129_594))
in (

let res = (compress_typ' res)
in (

let _32_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (let _129_596 = (mk_t ())
in (compress_typ' _129_596))
in (

let _32_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _32_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_32_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _32_759 -> begin
t
end)))


let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_32_769) -> begin
(let _129_662 = (let _129_661 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _129_661))
in ((_129_662), (ctrl)))
end
| _32_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _32_774 -> begin
(

let _32_778 = (ve null_ctrl binders e)
in (match (_32_778) with
| (e, _32_777) -> begin
((e), (ctrl))
end))
end)))
and compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(

let e = (let _129_691 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _129_691))
in (

let res = (compress_exp e)
in (

let _32_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _32_791 -> begin
e
end)))


let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _32_802, _32_804) -> begin
(unmeta_exp e)
end
| _32_808 -> begin
e
end)))


let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (

let s = (mk_subst [])
in (

let doit = (fun t -> (let _129_716 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _129_716)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_32_824) -> begin
(doit t)
end
| _32_827 -> begin
t
end)))))


let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match ((((Prims.fst formal)), ((Prims.fst actual)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (b)))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (y)))
end
| _32_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))


let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _32_12 -> (match (_32_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _129_723 = (compress_typ t)
in Some (_129_723))
end))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _129_728 = (let _129_727 = (let _129_726 = (FStar_Absyn_Syntax.mk_ident (((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText)), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (_129_726)::[])
in (FStar_List.append lid.FStar_Ident.ns _129_727))
in (FStar_Ident.lid_of_ids _129_728)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _129_736 = (let _129_735 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _129_735; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _129_736)))


let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))


let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))


let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_32_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _32_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((

let _32_865 = ct
in {FStar_Absyn_Syntax.effect_name = _32_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _32_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _32_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _32_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _32_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _32_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _32_863.FStar_Absyn_Syntax.uvs})
end))


let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_32_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))


let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_32_877) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))


let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _32_13 -> (match (_32_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _32_889 -> begin
false
end)))))


let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _32_14 -> (match (_32_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _32_895 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _32_15 -> (match (_32_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _32_901 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _32_16 -> (match (_32_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _32_907 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _32_17 -> (match (_32_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _32_913 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_32_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _32_18 -> (match (_32_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _32_924 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _32_19 -> (match (_32_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _32_931 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))


let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _129_775 = (compress_typ t)
in _129_775.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_32_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _32_940 -> begin
true
end))


let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _129_778 = (compress_typ t)
in _129_778.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_32_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _32_950 -> begin
false
end)
end
| _32_952 -> begin
false
end))


let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _129_781 = (compress_typ t)
in _129_781.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_32_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (_req)::(_ens)::((FStar_Util.Inr (pats), _32_966))::_32_962 -> begin
(match ((let _129_782 = (unmeta_exp pats)
in _129_782.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _32_983); FStar_Absyn_Syntax.tk = _32_980; FStar_Absyn_Syntax.pos = _32_978; FStar_Absyn_Syntax.fvs = _32_976; FStar_Absyn_Syntax.uvs = _32_974}, _32_988) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _32_992 -> begin
false
end)
end
| _32_994 -> begin
false
end)
end
| _32_996 -> begin
false
end)
end
| _32_998 -> begin
false
end))


let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _32_20 -> (match (_32_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _32_1005 -> begin
false
end)))))
end
| _32_1007 -> begin
false
end))


let comp_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
t
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.result_typ
end))


let set_result_typ = (fun c t -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_32_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (

let _32_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _32_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _32_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _32_1020.FStar_Absyn_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _32_21 -> (match (_32_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _32_1027 -> begin
false
end)))))


let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _129_792 = (compress_exp e)
in _129_792.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_1040)) -> begin
(is_atom e)
end
| _32_1045 -> begin
false
end))


let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]


let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _32_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _32_1053 -> begin
false
end))


let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _32_1057, _32_1059) -> begin
(unascribe e)
end
| _32_1063 -> begin
e
end))


let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _32_1068) -> begin
(ascribe_typ t' k)
end
| _32_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed ((t), (k)) t.FStar_Absyn_Syntax.pos)
end))


let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _32_1076) -> begin
(unascribe_typ t)
end
| _32_1080 -> begin
t
end))


let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _32_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _32_1090) -> begin
(unrefine t)
end
| _32_1094 -> begin
t
end)))


let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _129_806 = (compress_exp e)
in _129_806.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_32_1097) -> begin
true
end
| _32_1100 -> begin
false
end))


let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _129_809 = (compress_typ t)
in _129_809.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_32_1103) -> begin
true
end
| _32_1106 -> begin
false
end))


let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _32_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _32_1116) -> begin
(pre_typ t)
end
| _32_1120 -> begin
t
end)))


let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (

let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _32_1131; FStar_Absyn_Syntax.pos = _32_1129; FStar_Absyn_Syntax.fvs = _32_1127; FStar_Absyn_Syntax.uvs = _32_1125}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _32_1141 -> begin
None
end)))


let rec lids_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.lident Prims.list = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _32_1235) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| _32_1251 -> begin
None
end))


let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun _32_22 -> (match (_32_22) with
| (FStar_Util.Inl (x), _32_1362, _32_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _32_1369, _32_1371) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun _32_23 -> (match (_32_23) with
| (FStar_Util.Inl (hd), _32_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _32_1382) -> begin
hd.FStar_Absyn_Syntax.pos
end))


let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))


let mk_typ_app : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ = (fun f args -> (

let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app ((f), (args)) None r)))


let mk_exp_app : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun f args -> (

let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app ((f), (args)) None r)))


let mk_data : FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun l args -> (match (args) with
| [] -> begin
(let _129_842 = (let _129_841 = (let _129_840 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in ((_129_840), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_129_841))
in (FStar_Absyn_Syntax.mk_Exp_meta _129_842))
end
| _32_1398 -> begin
(let _129_846 = (let _129_845 = (let _129_844 = (let _129_843 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _129_843 args))
in ((_129_844), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_129_845))
in (FStar_Absyn_Syntax.mk_Exp_meta _129_846))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _129_852 = (let _129_851 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_129_851), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _129_852))
end else begin
x
end)


let mk_field_projector_name = (fun lid x i -> (

let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _129_858 = (let _129_857 = (let _129_856 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _129_856))
in ((_129_857), (x.FStar_Absyn_Syntax.p)))
in (FStar_Absyn_Syntax.mk_ident _129_858))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (

let y = (

let _32_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _32_1407.FStar_Absyn_Syntax.realname})
in (let _129_862 = (let _129_861 = (let _129_860 = (let _129_859 = (unmangle_field_name nm)
in (_129_859)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _129_860))
in (FStar_Ident.lid_of_ids _129_861))
in ((_129_862), (y))))))


let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_32_1413) -> begin
(let _129_867 = (let _129_866 = (let _129_865 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _129_865))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _129_866))
in (FStar_All.failwith _129_867))
end
| _32_1416 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))


type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)


let no_bvars : (FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set) = ((FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs), (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs))


let fvs_included : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun fvs1 fvs2 -> ((FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)))


let eq_fvars = (fun v1 v2 -> (match (((v1), (v2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Syntax.bvd_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _32_1432 -> begin
false
end))


let eq_binder = (fun b1 b2 -> (match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _32_1446 -> begin
false
end))


let uv_eq = (fun _32_1450 _32_1454 -> (match (((_32_1450), (_32_1454))) with
| ((uv1, _32_1449), (uv2, _32_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))


let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _129_884 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _129_883 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _129_882 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _129_884; FStar_Absyn_Syntax.uvars_t = _129_883; FStar_Absyn_Syntax.uvars_e = _129_882}))))


let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _129_890 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _129_889 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _129_890; FStar_Absyn_Syntax.fxvs = _129_889})))


let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _32_1461 _32_1464 -> (match (((_32_1461), (_32_1464))) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _129_896 = (union_fvs fvs1 fvs2)
in (let _129_895 = (union_uvs uvs1 uvs2)
in ((_129_896), (_129_895))))
end))


let sub_fv = (fun _32_1467 _32_1470 -> (match (((_32_1467), (_32_1470))) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _129_901 = (

let _32_1471 = fvs
in (let _129_900 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _129_899 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _129_900; FStar_Absyn_Syntax.fxvs = _129_899})))
in ((_129_901), (uvs)))
end))


let stash = (fun uvonly s _32_1479 -> (match (_32_1479) with
| (fvs, uvs) -> begin
(

let _32_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))


let single_fv = (fun x -> (let _129_906 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _129_906)))


let single_uv = (fun u -> (let _129_908 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _129_908)))


let single_uvt = (fun u -> (let _129_910 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _129_910)))


let rec vs_typ' = (fun t uvonly cont -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_32_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _129_1025 = (let _129_1024 = (

let _32_1495 = FStar_Absyn_Syntax.no_fvs
in (let _129_1023 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _129_1023; FStar_Absyn_Syntax.fxvs = _32_1495.FStar_Absyn_Syntax.fxvs}))
in ((_129_1024), (FStar_Absyn_Syntax.no_uvs)))
in (cont _129_1025))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _129_1028 = (let _129_1027 = (

let _32_1501 = FStar_Absyn_Syntax.no_uvs
in (let _129_1026 = (single_uvt ((uv), (k)))
in {FStar_Absyn_Syntax.uvars_k = _32_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _129_1026; FStar_Absyn_Syntax.uvars_e = _32_1501.FStar_Absyn_Syntax.uvars_e}))
in ((FStar_Absyn_Syntax.no_fvs), (_129_1027)))
in (cont _129_1028))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _32_1513 -> (match (_32_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _129_1032 = (let _129_1031 = (union_fvs_uvs vs1 vs2)
in (sub_fv _129_1031 bvs))
in (cont _129_1032))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _32_1521 -> (match (_32_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _129_1036 = (let _129_1035 = (union_fvs_uvs vs1 vs2)
in (sub_fv _129_1035 bvs))
in (cont _129_1036))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders ((((FStar_Util.Inr (x)), (None)))::[]) uvonly (fun _32_1529 -> (match (_32_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _129_1040 = (let _129_1039 = (union_fvs_uvs vs1 vs2)
in (sub_fv _129_1039 bvs))
in (cont _129_1040))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _129_1043 = (union_fvs_uvs vs1 vs2)
in (cont _129_1043))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _32_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _32_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _129_1046 = (union_fvs_uvs vs1 vs2)
in (cont _129_1046))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont ((no_bvars), (((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))))
end
| ((FStar_Util.Inl (a), _32_1587))::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _32_1595 -> (match (_32_1595) with
| ((tvars, vvars), vs2) -> begin
(let _129_1053 = (let _129_1052 = (let _129_1050 = (FStar_Util.set_add a tvars)
in ((_129_1050), (vvars)))
in (let _129_1051 = (union_fvs_uvs vs vs2)
in ((_129_1052), (_129_1051))))
in (cont _129_1053))
end)))))
end
| ((FStar_Util.Inr (x), _32_1600))::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _32_1608 -> (match (_32_1608) with
| ((tvars, vvars), vs2) -> begin
(let _129_1059 = (let _129_1058 = (let _129_1056 = (FStar_Util.set_add x vvars)
in ((tvars), (_129_1056)))
in (let _129_1057 = (union_fvs_uvs vs vs2)
in ((_129_1058), (_129_1057))))
in (cont _129_1059))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| ((FStar_Util.Inl (t), _32_1618))::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _129_1063 = (union_fvs_uvs ft1 ft2)
in (cont _129_1063))))))
end
| ((FStar_Util.Inr (e), _32_1627))::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _129_1066 = (union_fvs_uvs ft1 ft2)
in (cont _129_1066))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _129_1069 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _129_1068 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in ((_129_1069), (_129_1068))))) with
| (Some (_32_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (

let _32_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_typ' t uvonly (fun fvs -> (

let _32_1652 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_kind' = (fun k uvonly cont -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_32_1665, k) -> begin
(let _129_1074 = (let _129_1073 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _129_1073))
in (FStar_All.failwith _129_1074))
end
| FStar_Absyn_Syntax.Kind_delayed (_32_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _32_1681 -> (match (_32_1681) with
| (fvs, uvs) -> begin
(let _129_1078 = (let _129_1077 = (

let _32_1682 = uvs
in (let _129_1076 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _129_1076; FStar_Absyn_Syntax.uvars_t = _32_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _32_1682.FStar_Absyn_Syntax.uvars_e}))
in ((fvs), (_129_1077)))
in (cont _129_1078))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_32_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _32_1695 -> (match (_32_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _129_1082 = (let _129_1081 = (union_fvs_uvs vs1 vs2)
in (sub_fv _129_1081 bvs))
in (cont _129_1082))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _129_1085 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _129_1084 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in ((_129_1085), (_129_1084))))) with
| (Some (_32_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (

let _32_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_kind' k uvonly (fun fvs -> (

let _32_1717 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_exp' = (fun e uvonly cont -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_32_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _129_1091 = (let _129_1090 = (

let _32_1742 = FStar_Absyn_Syntax.no_uvs
in (let _129_1089 = (single_uvt ((uv), (t)))
in {FStar_Absyn_Syntax.uvars_k = _32_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _32_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _129_1089}))
in ((FStar_Absyn_Syntax.no_fvs), (_129_1090)))
in (cont _129_1091))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _129_1094 = (let _129_1093 = (

let _32_1746 = FStar_Absyn_Syntax.no_fvs
in (let _129_1092 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _32_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _129_1092}))
in ((_129_1093), (FStar_Absyn_Syntax.no_uvs)))
in (cont _129_1094))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _32_1750, _32_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _32_1761 -> (match (_32_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _129_1098 = (let _129_1097 = (union_fvs_uvs vs1 vs2)
in (sub_fv _129_1097 bvs))
in (cont _129_1098))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _129_1101 = (union_fvs_uvs ft1 ft2)
in (cont _129_1101))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _32_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _129_1104 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _129_1103 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in ((_129_1104), (_129_1103))))) with
| (Some (_32_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (

let _32_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_exp' e uvonly (fun fvs -> (

let _32_1801 = (stash uvonly e fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_comp' = (fun c uvonly k -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if uvonly then begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly k)
end else begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _129_1110 = (union_fvs_uvs vs1 vs2)
in (k _129_1110))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _129_1113 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _129_1112 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in ((_129_1113), (_129_1112))))) with
| (Some (_32_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (

let _32_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_comp' c uvonly (fun fvs -> (

let _32_1838 = (stash uvonly c fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_either = (fun te uvonly cont -> (match (te) with
| FStar_Util.Inl (t) -> begin
(vs_typ t uvonly cont)
end
| FStar_Util.Inr (e) -> begin
(vs_exp e uvonly cont)
end))
and vs_either_l = (fun tes uvonly cont -> (match (tes) with
| [] -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| (hd)::tl -> begin
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _129_1120 = (union_fvs_uvs ft1 ft2)
in (cont _129_1120))))))
end))


let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _32_1867 -> (match (_32_1867) with
| (x, _32_1866) -> begin
x
end))))


let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _32_1872 -> (match (_32_1872) with
| (x, _32_1871) -> begin
x
end))))


let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _32_1877 -> (match (_32_1877) with
| (x, _32_1876) -> begin
x
end))))


let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _32_1882 -> (match (_32_1882) with
| (x, _32_1881) -> begin
x
end))))


let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _129_1136 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _129_1136))
end
| FStar_Util.Inr (e) -> begin
(let _129_1137 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _129_1137))
end)) FStar_Absyn_Syntax.no_fvs)))


let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _32_24 -> (match (_32_24) with
| FStar_Util.Inl (a) -> begin
(FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)
end
| FStar_Util.Inr (x) -> begin
(FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)
end)))))


type syntax_sum =
| SynSumKind of FStar_Absyn_Syntax.knd
| SynSumType of FStar_Absyn_Syntax.typ
| SynSumExp of FStar_Absyn_Syntax.exp
| SynSumComp of (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax


let is_SynSumKind = (fun _discr_ -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))


let is_SynSumType = (fun _discr_ -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))


let is_SynSumExp = (fun _discr_ -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))


let is_SynSumComp = (fun _discr_ -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))


let ___SynSumKind____0 = (fun projectee -> (match (projectee) with
| SynSumKind (_32_1899) -> begin
_32_1899
end))


let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_32_1902) -> begin
_32_1902
end))


let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_32_1905) -> begin
_32_1905
end))


let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_32_1908) -> begin
_32_1908
end))


let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (

let out = (let _129_1211 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _129_1211 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _129_1209 = (uvars_in_kind k)
in (union_uvs _129_1209 out))
end
| _32_1916 -> begin
(

let _32_1917 = out
in (let _129_1210 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _129_1210; FStar_Absyn_Syntax.uvars_t = _32_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _32_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (

let out = (let _129_1216 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _129_1216 (FStar_List.fold_left (fun out _32_1923 -> (match (_32_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _129_1214 = (uvars_in_typ t)
in (union_uvs _129_1214 out))
end
| _32_1927 -> begin
(

let _32_1928 = out
in (let _129_1215 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _32_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _129_1215; FStar_Absyn_Syntax.uvars_e = _32_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (

let out = (let _129_1221 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _129_1221 (FStar_List.fold_left (fun out _32_1934 -> (match (_32_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _129_1219 = (uvars_in_exp e)
in (union_uvs _129_1219 out))
end
| _32_1938 -> begin
(

let _32_1939 = out
in (let _129_1220 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _32_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _32_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _129_1220}))
end)
end)) out)))
in (

let _32_1950 = (match (s) with
| SynSumKind (k) -> begin
(FStar_ST.op_Colon_Equals k.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumType (t) -> begin
(FStar_ST.op_Colon_Equals t.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumExp (e) -> begin
(FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.uvs (Some (out)))
end
| SynSumComp (c) -> begin
(FStar_ST.op_Colon_Equals c.FStar_Absyn_Syntax.uvs (Some (out)))
end)
in out)))))
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _129_1224 = (vs_kind k true (fun _32_1956 -> (match (_32_1956) with
| (_32_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _129_1224)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _129_1227 = (vs_typ t true (fun _32_1961 -> (match (_32_1961) with
| (_32_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _129_1227)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _129_1230 = (vs_exp e true (fun _32_1966 -> (match (_32_1966) with
| (_32_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _129_1230)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _129_1233 = (vs_comp c true (fun _32_1971 -> (match (_32_1971) with
| (_32_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _129_1233)))


let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))


let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_32_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
(([]), (k))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _32_1991 = (kind_formals k)
in (match (_32_1991) with
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_32_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_32_1998) -> begin
(FStar_All.failwith "Impossible")
end)))


let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (

let _32_2005 = (kind_formals k)
in (match (_32_2005) with
| (bs, _32_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _32_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t.FStar_Absyn_Syntax.pos)
end)
end)))


let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_32_2012, k) -> begin
(unabbreviate_kind k)
end
| _32_2017 -> begin
k
end)))


let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _32_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((tps), (t)) None t.FStar_Absyn_Syntax.pos)
end))


let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _32_2027 -> begin
(

let _32_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(((FStar_List.append tps bs')), (c))
end
| _32_2033 -> begin
(let _129_1254 = (FStar_Absyn_Syntax.mk_Total t)
in ((tps), (_129_1254)))
end)
in (match (_32_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t.FStar_Absyn_Syntax.pos)
end))
end))


let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow


let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _32_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' ((tps), (k)) k.FStar_Absyn_Syntax.pos)
end))


let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _32_2046 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _129_1267 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _129_1267))
in (let _129_1268 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _129_1268 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _129_1273 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _129_1273))
in (let _129_1274 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _129_1274 r))))


let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _129_1279 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _129_1279)))


let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _32_2059 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _129_1286 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _129_1286))
in (let _129_1287 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _129_1287 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _129_1292 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _129_1292))
in (let _129_1293 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _129_1293 r))))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _129_1309 = (pre_typ t)
in _129_1309.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _32_2078 -> begin
false
end))


let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _129_1314 = (pre_typ t)
in _129_1314.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_32_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _32_2086) -> begin
(is_constructed_typ t lid)
end
| _32_2090 -> begin
false
end))


let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _32_2101) -> begin
(get_tycon t)
end
| _32_2105 -> begin
None
end)))


let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _32_25 -> (match (_32_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _32_2109 -> begin
false
end))


let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _32_2115 _32_2119 -> (match (((_32_2115), (_32_2119))) with
| ((fn1, _32_2114), (fn2, _32_2118)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))


let kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)


let kt_kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)


let tand : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.and_lid kt_kt_kt)


let tor : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.or_lid kt_kt_kt)


let timp : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.imp_lid kt_kt_kt)


let tiff : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.iff_lid kt_kt_kt)


let t_bool : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)


let t_false : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)


let t_true : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)


let b2t_v : FStar_Absyn_Syntax.typ = (let _129_1325 = (let _129_1324 = (let _129_1323 = (let _129_1322 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_129_1322)::[])
in ((_129_1323), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1324 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _129_1325))


let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _129_1336 = (let _129_1335 = (let _129_1333 = (let _129_1332 = (FStar_Absyn_Syntax.targ phi1)
in (let _129_1331 = (let _129_1330 = (FStar_Absyn_Syntax.targ phi2)
in (_129_1330)::[])
in (_129_1332)::_129_1331))
in ((tand), (_129_1333)))
in (let _129_1334 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _129_1335 None _129_1334)))
in Some (_129_1336))
end))


let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _129_1348 = (let _129_1346 = (let _129_1345 = (FStar_Absyn_Syntax.targ phi1)
in (let _129_1344 = (let _129_1343 = (FStar_Absyn_Syntax.targ phi2)
in (_129_1343)::[])
in (_129_1345)::_129_1344))
in ((op_t), (_129_1346)))
in (let _129_1347 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _129_1348 None _129_1347))))


let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _129_1354 = (let _129_1353 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _129_1352 = (let _129_1351 = (FStar_Absyn_Syntax.targ phi)
in (_129_1351)::[])
in ((_129_1353), (_129_1352))))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1354 None phi.FStar_Absyn_Syntax.pos)))


let mk_conj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))


let mk_conj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))


let mk_disj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))


let mk_disj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
end
| (hd)::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))


let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _129_1371 = (compress_typ phi1)
in _129_1371.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _32_2150 -> begin
(match ((let _129_1372 = (compress_typ phi2)
in _129_1372.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _32_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))


let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _129_1381 = (let _129_1380 = (let _129_1379 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_129_1379)::[])
in ((b2t_v), (_129_1380)))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1381 None e.FStar_Absyn_Syntax.pos)))


let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _32_2194)) -> begin
(mk_conj t1 t2)
end
| _32_2199 -> begin
t
end)))


let eq_k : FStar_Absyn_Syntax.knd = (

let a = (let _129_1384 = (new_bvd None)
in (bvd_to_bvar_s _129_1384 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (

let b = (let _129_1385 = (new_bvd None)
in (bvd_to_bvar_s _129_1385 FStar_Absyn_Syntax.ktype))
in (

let btyp = (btvar_to_typ b)
in (let _129_1392 = (let _129_1391 = (let _129_1390 = (let _129_1389 = (let _129_1388 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _129_1387 = (let _129_1386 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_129_1386)::[])
in (_129_1388)::_129_1387))
in (((FStar_Util.Inl (b)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_129_1389)
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_129_1390)
in ((_129_1391), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1392 FStar_Absyn_Syntax.dummyRange))))))


let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)


let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _32_2217 -> begin
(let _129_1410 = (let _129_1408 = (let _129_1407 = (FStar_Absyn_Syntax.itarg t1)
in (let _129_1406 = (let _129_1405 = (FStar_Absyn_Syntax.itarg t2)
in (let _129_1404 = (let _129_1403 = (FStar_Absyn_Syntax.varg e1)
in (let _129_1402 = (let _129_1401 = (FStar_Absyn_Syntax.varg e2)
in (_129_1401)::[])
in (_129_1403)::_129_1402))
in (_129_1405)::_129_1404))
in (_129_1407)::_129_1406))
in ((teq), (_129_1408)))
in (let _129_1409 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _129_1410 None _129_1409)))
end))


let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)


let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _129_1420 = (let _129_1418 = (let _129_1417 = (FStar_Absyn_Syntax.targ t1)
in (let _129_1416 = (let _129_1415 = (FStar_Absyn_Syntax.targ t2)
in (_129_1415)::[])
in (_129_1417)::_129_1416))
in ((eq_typ), (_129_1418)))
in (let _129_1419 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _129_1420 None _129_1419))))


let lex_t : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)


let lex_top : FStar_Absyn_Syntax.exp = (

let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexnil), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange))


let lex_pair : FStar_Absyn_Syntax.exp = (

let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (

let lexcons = (let _129_1430 = (let _129_1429 = (let _129_1428 = (let _129_1426 = (FStar_Absyn_Syntax.t_binder a)
in (let _129_1425 = (let _129_1424 = (let _129_1421 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _129_1421))
in (let _129_1423 = (let _129_1422 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_129_1422)::[])
in (_129_1424)::_129_1423))
in (_129_1426)::_129_1425))
in (let _129_1427 = (FStar_Absyn_Syntax.mk_Total lex_t)
in ((_129_1428), (_129_1427))))
in (FStar_Absyn_Syntax.mk_Typ_fun _129_1429 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _129_1430 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexcons), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange)))


let forall_kind : FStar_Absyn_Syntax.knd = (

let a = (let _129_1431 = (new_bvd None)
in (bvd_to_bvar_s _129_1431 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (let _129_1439 = (let _129_1438 = (let _129_1437 = (let _129_1436 = (let _129_1435 = (let _129_1434 = (let _129_1433 = (let _129_1432 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_129_1432)::[])
in ((_129_1433), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1434 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _129_1435))
in (_129_1436)::[])
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_129_1437)
in ((_129_1438), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1439 FStar_Absyn_Syntax.dummyRange))))


let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)


let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _129_1448 = (let _129_1447 = (let _129_1446 = (let _129_1445 = (let _129_1444 = (let _129_1443 = (let _129_1442 = (FStar_Absyn_Syntax.null_t_binder k)
in (_129_1442)::[])
in ((_129_1443), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1444 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _129_1445))
in (_129_1446)::[])
in ((_129_1447), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1448 FStar_Absyn_Syntax.dummyRange)))


let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _129_1455 = (let _129_1454 = (let _129_1453 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _129_1452 = (let _129_1451 = (FStar_Absyn_Syntax.null_t_binder k)
in (_129_1451)::[])
in (_129_1453)::_129_1452))
in ((_129_1454), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _129_1455 FStar_Absyn_Syntax.dummyRange)))


let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _129_1458 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _129_1458)))


let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _129_1470 = (let _129_1469 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _129_1468 = (let _129_1467 = (let _129_1466 = (let _129_1465 = (let _129_1464 = (let _129_1463 = (FStar_Absyn_Syntax.t_binder a)
in (_129_1463)::[])
in ((_129_1464), (b)))
in (FStar_Absyn_Syntax.mk_Typ_lam _129_1465 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _129_1466))
in (_129_1467)::[])
in ((_129_1469), (_129_1468))))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1470 None b.FStar_Absyn_Syntax.pos)))


let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (

let r = FStar_Absyn_Syntax.dummyRange
in (let _129_1481 = (let _129_1480 = (let _129_1479 = (let _129_1478 = (let _129_1477 = (let _129_1476 = (let _129_1475 = (FStar_Absyn_Syntax.v_binder x)
in (_129_1475)::[])
in ((_129_1476), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _129_1477 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _129_1478))
in (_129_1479)::[])
in ((tforall), (_129_1480)))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1481 None r))))


let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_lam (((b)::[]), (f)) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _129_1491 = (let _129_1490 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _129_1489 = (let _129_1488 = (FStar_Absyn_Syntax.targ body)
in (_129_1488)::[])
in ((_129_1490), (_129_1489))))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1491 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _129_1495 = (let _129_1494 = (let _129_1493 = (let _129_1492 = (FStar_Absyn_Syntax.targ body)
in (_129_1492)::[])
in (((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_129_1493)
in ((tforall), (_129_1494)))
in (FStar_Absyn_Syntax.mk_Typ_app _129_1495 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_32_2244) -> begin
true
end
| _32_2247 -> begin
false
end))


let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
((head), (args))
end
| _32_2255 -> begin
((t), ([]))
end)))


let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
((head), (args))
end
| _32_2263 -> begin
((e), ([]))
end)))


let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some (((bs), (c)))
end
| _32_2271 -> begin
None
end)))


let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (

let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))


type qpats =
FStar_Absyn_Syntax.args Prims.list


type connective =
| QAll of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| QEx of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Absyn_Syntax.args)


let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))


let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))


let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))


let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_32_2276) -> begin
_32_2276
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_32_2279) -> begin
_32_2279
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_32_2282) -> begin
_32_2282
end))


let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (

let destruct_base_conn = (fun f -> (

let _32_2288 = ((true), (false))
in (match (_32_2288) with
| (type_sort, term_sort) -> begin
(

let oneType = (type_sort)::[]
in (

let twoTypes = (type_sort)::(type_sort)::[]
in (

let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (

let twoTerms = (term_sort)::(term_sort)::[]
in (

let connectives = (((FStar_Absyn_Const.true_lid), ([])))::(((FStar_Absyn_Const.false_lid), ([])))::(((FStar_Absyn_Const.and_lid), (twoTypes)))::(((FStar_Absyn_Const.or_lid), (twoTypes)))::(((FStar_Absyn_Const.imp_lid), (twoTypes)))::(((FStar_Absyn_Const.iff_lid), (twoTypes)))::(((FStar_Absyn_Const.ite_lid), (threeTys)))::(((FStar_Absyn_Const.not_lid), (oneType)))::(((FStar_Absyn_Const.eqT_lid), (twoTypes)))::(((FStar_Absyn_Const.eq2_lid), (twoTerms)))::(((FStar_Absyn_Const.eq2_lid), ((FStar_List.append twoTypes twoTerms))))::[]
in (

let rec aux = (fun f _32_2298 -> (match (_32_2298) with
| (lid, arity) -> begin
(

let _32_2301 = (head_and_args f)
in (match (_32_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_32_2305), _32_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_32_2311), _32_2314) -> begin
(flag = term_sort)
end)) args arity)) then begin
Some (BaseConn (((lid), (args))))
end else begin
None
end
end))
end))
in (FStar_Util.find_map connectives (aux f))))))))
end)))
in (

let patterns = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, pats)) -> begin
(let _129_1559 = (compress_typ t)
in ((pats), (_129_1559)))
end
| _32_2325 -> begin
(let _129_1560 = (compress_typ t)
in (([]), (_129_1560)))
end)))
in (

let destruct_q_conn = (fun t -> (

let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (

let flat = (fun t -> (

let _32_2335 = (head_and_args t)
in (match (_32_2335) with
| (t, args) -> begin
(let _129_1574 = (FStar_All.pipe_right args (FStar_List.map (fun _32_26 -> (match (_32_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _129_1571 = (let _129_1570 = (compress_typ t)
in FStar_Util.Inl (_129_1570))
in ((_129_1571), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _129_1573 = (let _129_1572 = (compress_exp e)
in FStar_Util.Inr (_129_1572))
in ((_129_1573), (imp)))
end))))
in ((t), (_129_1574)))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _129_1581 = (flat t)
in ((qopt), (_129_1581)))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _32_2483) -> begin
(

let _32_2487 = (patterns t)
in (match (_32_2487) with
| (pats, body) -> begin
Some (QAll ((((FStar_List.rev out)), (pats), (body))))
end))
end
| (Some (false), _32_2491) -> begin
(

let _32_2495 = (patterns t)
in (match (_32_2495) with
| (pats, body) -> begin
Some (QEx ((((FStar_List.rev out)), (pats), (body))))
end))
end
| _32_2497 -> begin
None
end))
in (aux None [] t)))))
in (

let phi = (compress_typ f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))





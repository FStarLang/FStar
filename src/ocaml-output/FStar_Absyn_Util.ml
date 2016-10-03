
open Prims

let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Fatal: %s" ((s)::[]))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(

let _31_36 = (let _128_8 = (let _128_7 = (FStar_Range.string_of_range r)
in (_128_7)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _128_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(

let _31_40 = (FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((s)::[]))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Error: %s" ((s)::[]))
end
| _31_45 -> begin
(Prims.raise e)
end))


let handleable : Prims.exn  ->  Prims.bool = (fun _31_1 -> (match (_31_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _31_60 -> begin
false
end))


type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}


let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun _31_66 -> (match (()) with
| () -> begin
(let _128_36 = (let _128_35 = (let _128_31 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _128_31))
in (let _128_34 = (let _128_33 = (let _128_32 = (

let _31_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _128_32))
in (Prims.strcat "_" _128_33))
in (Prims.strcat _128_35 _128_34)))
in (Prims.strcat "_" _128_36))
end)); reset = (fun _31_69 -> (match (()) with
| () -> begin
(

let _31_70 = (FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"))
in (FStar_Util.incr n_resets))
end))}))


let gensym : Prims.unit  ->  Prims.string = (fun _31_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))


let reset_gensym : Prims.unit  ->  Prims.unit = (fun _31_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))


let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| _128_44 when (_128_44 = (Prims.parse_int "0")) -> begin
[]
end
| n -> begin
(let _128_46 = (gensym ())
in (let _128_45 = (gensyms (n - (Prims.parse_int "1")))
in (_128_46)::_128_45))
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


let mkbvd = (fun _31_87 -> (match (_31_87) with
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
| _31_114 -> begin
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


let freshen_bvd = (fun bvd' -> (let _128_87 = (let _128_86 = (genident (Some ((range_of_bvd bvd'))))
in ((bvd'.FStar_Absyn_Syntax.ppname), (_128_86)))
in (mkbvd _128_87)))


let freshen_bvar = (fun b -> (let _128_89 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _128_89 b.FStar_Absyn_Syntax.sort)))


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


let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _128_114 = (let _128_113 = (let _128_112 = (set_lid_range l r)
in (fv _128_112))
in ((_128_113), (dc)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _128_114 None r)))


let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))


let order_bvd = (fun x y -> (match (((x), (y))) with
| (FStar_Util.Inl (_31_160), FStar_Util.Inr (_31_163)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Util.Inr (_31_167), FStar_Util.Inl (_31_170)) -> begin
(Prims.parse_int "1")
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))


let arg_of_non_null_binder = (fun _31_185 -> (match (_31_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _128_123 = (let _128_122 = (btvar_to_typ a)
in FStar_Util.Inl (_128_122))
in ((_128_123), (imp)))
end
| FStar_Util.Inr (x) -> begin
(let _128_125 = (let _128_124 = (bvar_to_exp x)
in FStar_Util.Inr (_128_124))
in ((_128_125), (imp)))
end)
end))


let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _128_129 = (arg_of_non_null_binder b)
in (_128_129)::[])
end))))


let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _128_139 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(

let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _128_134 = (let _128_133 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_128_133))
in ((_128_134), ((Prims.snd b))))
end
| FStar_Util.Inr (x) -> begin
(let _128_136 = (let _128_135 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_128_135))
in ((_128_136), ((Prims.snd b))))
end)
in (let _128_137 = (arg_of_non_null_binder b)
in ((b), (_128_137))))
end else begin
(let _128_138 = (arg_of_non_null_binder b)
in ((b), (_128_138)))
end)))
in (FStar_All.pipe_right _128_139 FStar_List.unzip)))


let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let b = (let _128_145 = (let _128_144 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _128_144))
in (FStar_Ident.id_of_text _128_145))
in (

let b = (bvd_to_bvar_s (mkbvd ((b), (b))) a.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inl (b)), (imp))))
end
| (FStar_Util.Inr (y), imp) -> begin
(

let x = (let _128_147 = (let _128_146 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _128_146))
in (FStar_Ident.id_of_text _128_147))
in (

let x = (bvd_to_bvar_s (mkbvd ((x), (x))) y.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inr (x)), (imp))))
end)
end else begin
b
end))))


let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _128_151 = (let _128_150 = (name_binders binders)
in ((_128_150), (comp)))
in (FStar_Absyn_Syntax.mk_Typ_fun _128_151 None t.FStar_Absyn_Syntax.pos))
end
| _31_220 -> begin
t
end))


let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _31_2 -> (match (_31_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _128_156 = (let _128_155 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _128_155))
in ((_128_156), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _128_158 = (let _128_157 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _128_157))
in ((_128_158), (imp)))
end)))))


let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _31_3 -> (match (_31_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _128_163 = (let _128_162 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_128_162))
in ((_128_163), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _128_165 = (let _128_164 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_128_164))
in ((_128_165), (imp)))
end)))))


let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _128_171 = (let _128_168 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _128_168 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _128_170 = (let _128_169 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _128_169 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _128_171 _128_170))))


let subst_to_string = (fun s -> (let _128_174 = (FStar_All.pipe_right s (FStar_List.map (fun _31_4 -> (match (_31_4) with
| FStar_Util.Inl (b, _31_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _31_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _128_174 (FStar_String.concat ", "))))


let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _31_5 -> (match (_31_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _31_262 -> begin
None
end))))


let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _31_6 -> (match (_31_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _31_271 -> begin
None
end))))


let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _31_278 -> begin
(

let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _128_199 = (let _128_198 = (compose_subst s' s)
in (let _128_197 = (FStar_Util.mk_ref None)
in ((t'), (_128_198), (_128_197))))
in (FStar_Absyn_Syntax.mk_Typ_delayed _128_199 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (mk_t ())
in (

let _31_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
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
| _31_305 -> begin
(aux rest)
end)
end
| _31_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _31_316 -> begin
(let _128_204 = (let _128_203 = (FStar_Util.mk_ref None)
in ((t0), (s), (_128_203)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _128_204 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _31_323 -> begin
(

let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _128_209 = (let _128_208 = (compose_subst s' s)
in (let _128_207 = (FStar_Util.mk_ref None)
in ((e), (_128_208), (_128_207))))
in (FStar_Absyn_Syntax.mk_Exp_delayed _128_209 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let rec aux = (fun s -> (match (s) with
| (s0)::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _31_340 -> begin
(aux rest)
end)
end
| _31_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _31_350 -> begin
(let _128_213 = (let _128_212 = (FStar_Util.mk_ref None)
in ((e0), (s), (_128_212)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _128_213 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _31_357 -> begin
(

let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _128_218 = (let _128_217 = (compose_subst s' s)
in (let _128_216 = (FStar_Util.mk_ref None)
in ((k), (_128_217), (_128_216))))
in (FStar_Absyn_Syntax.mk_Kind_delayed _128_218 k0.FStar_Absyn_Syntax.pos))
end
| _31_368 -> begin
(let _128_220 = (let _128_219 = (FStar_Util.mk_ref None)
in ((k0), (s), (_128_219)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _128_220 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_7 -> (match (_31_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _128_224 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_128_224))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _31_381 -> begin
(

let _31_382 = t
in (let _128_234 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _128_233 = (FStar_List.map (fun _31_8 -> (match (_31_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _128_229 = (let _128_228 = (subst_typ' s t)
in FStar_Util.Inl (_128_228))
in ((_128_229), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _128_231 = (let _128_230 = (subst_exp' s e)
in FStar_Util.Inr (_128_230))
in ((_128_231), (imp)))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _128_232 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _31_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _128_234; FStar_Absyn_Syntax.effect_args = _128_233; FStar_Absyn_Syntax.flags = _128_232}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _31_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _128_237 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _128_237))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _128_238 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _128_238))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))


let mk_subst = (fun s -> (s)::[])


let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))


let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))


let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))


let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))


let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))


let subst_binder = (fun s _31_9 -> (match (_31_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _128_266 = (let _128_265 = (

let _31_423 = a
in (let _128_264 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _31_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _128_264; FStar_Absyn_Syntax.p = _31_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_128_265))
in ((_128_266), (imp)))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _128_269 = (let _128_268 = (

let _31_429 = x
in (let _128_267 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _31_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _128_267; FStar_Absyn_Syntax.p = _31_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_128_268))
in ((_128_269), (imp)))
end))


let subst_arg = (fun s _31_10 -> (match (_31_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _128_273 = (let _128_272 = (subst_typ s t)
in FStar_Util.Inl (_128_272))
in ((_128_273), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _128_275 = (let _128_274 = (subst_exp s e)
in FStar_Util.Inr (_128_274))
in ((_128_275), (imp)))
end))


let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _31_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))


let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _31_450 -> begin
(FStar_List.map (subst_arg s) args)
end))


let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match (((f), (a))) with
| ((FStar_Util.Inl (a), _31_456), (FStar_Util.Inl (t), _31_461)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t)))
end
| ((FStar_Util.Inr (x), _31_467), (FStar_Util.Inr (v), _31_472)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v)))
end
| _31_476 -> begin
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
(let _128_290 = (let _128_289 = (let _128_288 = (btvar_to_typ a)
in ((b.FStar_Absyn_Syntax.v), (_128_288)))
in FStar_Util.Inl (_128_289))
in (_128_290)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _128_293 = (let _128_292 = (let _128_291 = (bvar_to_exp x)
in ((y.FStar_Absyn_Syntax.v), (_128_291)))
in FStar_Util.Inr (_128_292))
in (_128_293)::[])
end
end
| _31_490 -> begin
[]
end)
end)


let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (

let rec aux = (fun out bs1 bs2 -> (match (((bs1), (bs2))) with
| ([], []) -> begin
Some (out)
end
| ((b1)::bs1, (b2)::bs2) -> begin
(let _128_305 = (let _128_304 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _128_304 out))
in (aux _128_305 bs1 bs2))
end
| _31_508 -> begin
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


let map_knd = (fun s vk mt me descend binders k -> (let _128_326 = (subst_kind' s k)
in ((_128_326), (descend))))


let map_typ = (fun s mk vt me descend binders t -> (let _128_334 = (subst_typ' s t)
in ((_128_334), (descend))))


let map_exp = (fun s mk me ve descend binders e -> (let _128_342 = (subst_exp' s e)
in ((_128_342), (descend))))


let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_11 -> (match (_31_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _128_359 = (let _128_358 = (map_exp descend binders e)
in (FStar_All.pipe_right _128_358 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_128_359))
end
| f -> begin
f
end)))))


let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _31_557 = (map_typ descend binders t)
in (match (_31_557) with
| (t, descend) -> begin
(let _128_382 = (FStar_Absyn_Syntax.mk_Total t)
in ((_128_382), (descend)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _31_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_31_562) with
| (t, descend) -> begin
(

let _31_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_31_565) with
| (args, descend) -> begin
(let _128_385 = (let _128_384 = (

let _31_566 = ct
in (let _128_383 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _31_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _128_383}))
in (FStar_Absyn_Syntax.mk_Comp _128_384))
in ((_128_385), (descend)))
end))
end))
end))


let visit_knd = (fun s vk mt me ctrl binders k -> (

let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(

let _31_579 = (vk null_ctrl binders k)
in (match (_31_579) with
| (k, _31_578) -> begin
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

let k' = (let _128_431 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _128_431))
in (

let k' = (compress_kind k')
in (

let _31_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _128_433 = (let _128_432 = (subst_of_list formals actuals)
in (subst_kind _128_432 k'))
in (compress_kind _128_433))
end
| _31_602 -> begin
if ((FStar_List.length actuals) = (Prims.parse_int "0")) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _31_604 -> begin
k
end)
end
| _31_606 -> begin
k
end)))


let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (

let visit_prod = (fun bs tc -> (

let _31_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _31_620 b -> (match (_31_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _31_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_31_629) with
| (k, _31_628) -> begin
(

let a = (

let _31_630 = a
in {FStar_Absyn_Syntax.v = _31_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _31_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inl (a)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (

let _31_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inl (a)), (s), (boundvars'))
end
| _31_636 -> begin
(

let b = (let _128_510 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _128_510 k))
in (

let s = (let _128_513 = (let _128_512 = (let _128_511 = (btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_128_511)))
in FStar_Util.Inl (_128_512))
in (extend_subst _128_513 s))
in ((FStar_Util.Inl (b)), (s), ((FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_31_642) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _31_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_31_650) with
| (t, _31_649) -> begin
(

let x = (

let _31_651 = x
in {FStar_Absyn_Syntax.v = _31_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _31_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inr (x)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (

let _31_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inr (x)), (s), (boundvars'))
end
| _31_657 -> begin
(

let y = (let _128_523 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _128_523 t))
in (

let s = (let _128_526 = (let _128_525 = (let _128_524 = (bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_128_524)))
in FStar_Util.Inr (_128_525))
in (extend_subst _128_526 s))
in ((FStar_Util.Inr (y)), (s), ((FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_31_663) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end)
end)) (([]), (boundvars), (s))))
in (match (_31_667) with
| (bs, boundvars, s) -> begin
(

let tc = (match (((s), (tc))) with
| ([], _31_670) -> begin
tc
end
| (_31_673, FStar_Util.Inl (t)) -> begin
(let _128_537 = (let _128_536 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _128_536))
in FStar_Util.Inl (_128_537))
end
| (_31_678, FStar_Util.Inr (c)) -> begin
(let _128_560 = (let _128_559 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _128_559))
in FStar_Util.Inr (_128_560))
end)
in (((FStar_List.rev bs)), (tc)))
end)))
in (

let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_31_685) -> begin
(let _128_562 = (let _128_561 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _128_561))
in ((_128_562), (ctrl)))
end
| _31_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _128_572 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t0.FStar_Absyn_Syntax.pos)
in ((_128_572), (ctrl)))
end
| _31_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod ((((FStar_Util.Inr (x)), (None)))::[]) (FStar_Util.Inl (t)))) with
| (((FStar_Util.Inr (x), _31_706))::[], FStar_Util.Inl (t)) -> begin
(let _128_573 = (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_128_573), (ctrl)))
end
| _31_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _128_574 = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_128_574), (ctrl)))
end
| _31_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _31_725 -> begin
(

let _31_729 = (vt null_ctrl boundvars t)
in (match (_31_729) with
| (t, _31_728) -> begin
((t), (ctrl))
end))
end))))
and compress_typ' : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(

let res = (let _128_594 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _128_594))
in (

let res = (compress_typ' res)
in (

let _31_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (let _128_596 = (mk_t ())
in (compress_typ' _128_596))
in (

let _31_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _31_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_31_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _31_759 -> begin
t
end)))


let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_31_769) -> begin
(let _128_662 = (let _128_661 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _128_661))
in ((_128_662), (ctrl)))
end
| _31_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _31_774 -> begin
(

let _31_778 = (ve null_ctrl binders e)
in (match (_31_778) with
| (e, _31_777) -> begin
((e), (ctrl))
end))
end)))
and compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(

let e = (let _128_691 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _128_691))
in (

let res = (compress_exp e)
in (

let _31_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _31_791 -> begin
e
end)))


let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _31_802, _31_804) -> begin
(unmeta_exp e)
end
| _31_808 -> begin
e
end)))


let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (

let s = (mk_subst [])
in (

let doit = (fun t -> (let _128_716 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _128_716)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_31_824) -> begin
(doit t)
end
| _31_827 -> begin
t
end)))))


let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match ((((Prims.fst formal)), ((Prims.fst actual)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (b)))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (y)))
end
| _31_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))


let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _31_12 -> (match (_31_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _128_723 = (compress_typ t)
in Some (_128_723))
end))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _128_728 = (let _128_727 = (let _128_726 = (FStar_Absyn_Syntax.mk_ident (((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText)), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (_128_726)::[])
in (FStar_List.append lid.FStar_Ident.ns _128_727))
in (FStar_Ident.lid_of_ids _128_728)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _128_736 = (let _128_735 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _128_735; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _128_736)))


let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))


let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))


let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _31_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((

let _31_865 = ct
in {FStar_Absyn_Syntax.effect_name = _31_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _31_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _31_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _31_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _31_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _31_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _31_863.FStar_Absyn_Syntax.uvs})
end))


let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))


let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_31_877) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))


let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_13 -> (match (_31_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_889 -> begin
false
end)))))


let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_14 -> (match (_31_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_895 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_15 -> (match (_31_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_901 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_16 -> (match (_31_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _31_907 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_17 -> (match (_31_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _31_913 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _31_18 -> (match (_31_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _31_924 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_19 -> (match (_31_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _31_931 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))


let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _128_775 = (compress_typ t)
in _128_775.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _31_940 -> begin
true
end))


let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _128_778 = (compress_typ t)
in _128_778.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _31_950 -> begin
false
end)
end
| _31_952 -> begin
false
end))


let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _128_781 = (compress_typ t)
in _128_781.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (_req)::(_ens)::((FStar_Util.Inr (pats), _31_966))::_31_962 -> begin
(match ((let _128_782 = (unmeta_exp pats)
in _128_782.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _31_983); FStar_Absyn_Syntax.tk = _31_980; FStar_Absyn_Syntax.pos = _31_978; FStar_Absyn_Syntax.fvs = _31_976; FStar_Absyn_Syntax.uvs = _31_974}, _31_988) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _31_992 -> begin
false
end)
end
| _31_994 -> begin
false
end)
end
| _31_996 -> begin
false
end)
end
| _31_998 -> begin
false
end))


let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _31_20 -> (match (_31_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _31_1005 -> begin
false
end)))))
end
| _31_1007 -> begin
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
| FStar_Absyn_Syntax.Total (_31_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (

let _31_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _31_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _31_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _31_1020.FStar_Absyn_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_21 -> (match (_31_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_1027 -> begin
false
end)))))


let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _128_792 = (compress_exp e)
in _128_792.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_1040)) -> begin
(is_atom e)
end
| _31_1045 -> begin
false
end))


let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]


let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _31_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _31_1053 -> begin
false
end))


let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _31_1057, _31_1059) -> begin
(unascribe e)
end
| _31_1063 -> begin
e
end))


let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _31_1068) -> begin
(ascribe_typ t' k)
end
| _31_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed ((t), (k)) t.FStar_Absyn_Syntax.pos)
end))


let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1076) -> begin
(unascribe_typ t)
end
| _31_1080 -> begin
t
end))


let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _31_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1090) -> begin
(unrefine t)
end
| _31_1094 -> begin
t
end)))


let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _128_806 = (compress_exp e)
in _128_806.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_31_1097) -> begin
true
end
| _31_1100 -> begin
false
end))


let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _128_809 = (compress_typ t)
in _128_809.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_1103) -> begin
true
end
| _31_1106 -> begin
false
end))


let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _31_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1116) -> begin
(pre_typ t)
end
| _31_1120 -> begin
t
end)))


let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (

let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _31_1131; FStar_Absyn_Syntax.pos = _31_1129; FStar_Absyn_Syntax.fvs = _31_1127; FStar_Absyn_Syntax.uvs = _31_1125}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _31_1141 -> begin
None
end)))


let rec lids_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.lident Prims.list = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _31_1235) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| _31_1251 -> begin
None
end))


let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun _31_22 -> (match (_31_22) with
| (FStar_Util.Inl (x), _31_1362, _31_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _31_1369, _31_1371) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun _31_23 -> (match (_31_23) with
| (FStar_Util.Inl (hd), _31_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _31_1382) -> begin
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
(let _128_842 = (let _128_841 = (let _128_840 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in ((_128_840), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_128_841))
in (FStar_Absyn_Syntax.mk_Exp_meta _128_842))
end
| _31_1398 -> begin
(let _128_846 = (let _128_845 = (let _128_844 = (let _128_843 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _128_843 args))
in ((_128_844), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_128_845))
in (FStar_Absyn_Syntax.mk_Exp_meta _128_846))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _128_852 = (let _128_851 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_128_851), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _128_852))
end else begin
x
end)


let mk_field_projector_name = (fun lid x i -> (

let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _128_858 = (let _128_857 = (let _128_856 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _128_856))
in ((_128_857), (x.FStar_Absyn_Syntax.p)))
in (FStar_Absyn_Syntax.mk_ident _128_858))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (

let y = (

let _31_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _31_1407.FStar_Absyn_Syntax.realname})
in (let _128_862 = (let _128_861 = (let _128_860 = (let _128_859 = (unmangle_field_name nm)
in (_128_859)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _128_860))
in (FStar_Ident.lid_of_ids _128_861))
in ((_128_862), (y))))))


let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_31_1413) -> begin
(let _128_867 = (let _128_866 = (let _128_865 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _128_865))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _128_866))
in (FStar_All.failwith _128_867))
end
| _31_1416 -> begin
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
| _31_1432 -> begin
false
end))


let eq_binder = (fun b1 b2 -> (match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _31_1446 -> begin
false
end))


let uv_eq = (fun _31_1450 _31_1454 -> (match (((_31_1450), (_31_1454))) with
| ((uv1, _31_1449), (uv2, _31_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))


let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _128_884 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _128_883 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _128_882 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _128_884; FStar_Absyn_Syntax.uvars_t = _128_883; FStar_Absyn_Syntax.uvars_e = _128_882}))))


let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _128_890 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _128_889 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _128_890; FStar_Absyn_Syntax.fxvs = _128_889})))


let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _31_1461 _31_1464 -> (match (((_31_1461), (_31_1464))) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _128_896 = (union_fvs fvs1 fvs2)
in (let _128_895 = (union_uvs uvs1 uvs2)
in ((_128_896), (_128_895))))
end))


let sub_fv = (fun _31_1467 _31_1470 -> (match (((_31_1467), (_31_1470))) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _128_901 = (

let _31_1471 = fvs
in (let _128_900 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _128_899 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _128_900; FStar_Absyn_Syntax.fxvs = _128_899})))
in ((_128_901), (uvs)))
end))


let stash = (fun uvonly s _31_1479 -> (match (_31_1479) with
| (fvs, uvs) -> begin
(

let _31_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))


let single_fv = (fun x -> (let _128_906 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _128_906)))


let single_uv = (fun u -> (let _128_908 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _128_908)))


let single_uvt = (fun u -> (let _128_910 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _128_910)))


let rec vs_typ' = (fun t uvonly cont -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_31_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _128_1025 = (let _128_1024 = (

let _31_1495 = FStar_Absyn_Syntax.no_fvs
in (let _128_1023 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _128_1023; FStar_Absyn_Syntax.fxvs = _31_1495.FStar_Absyn_Syntax.fxvs}))
in ((_128_1024), (FStar_Absyn_Syntax.no_uvs)))
in (cont _128_1025))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _128_1028 = (let _128_1027 = (

let _31_1501 = FStar_Absyn_Syntax.no_uvs
in (let _128_1026 = (single_uvt ((uv), (k)))
in {FStar_Absyn_Syntax.uvars_k = _31_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _128_1026; FStar_Absyn_Syntax.uvars_e = _31_1501.FStar_Absyn_Syntax.uvars_e}))
in ((FStar_Absyn_Syntax.no_fvs), (_128_1027)))
in (cont _128_1028))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _31_1513 -> (match (_31_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _128_1032 = (let _128_1031 = (union_fvs_uvs vs1 vs2)
in (sub_fv _128_1031 bvs))
in (cont _128_1032))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _31_1521 -> (match (_31_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _128_1036 = (let _128_1035 = (union_fvs_uvs vs1 vs2)
in (sub_fv _128_1035 bvs))
in (cont _128_1036))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders ((((FStar_Util.Inr (x)), (None)))::[]) uvonly (fun _31_1529 -> (match (_31_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _128_1040 = (let _128_1039 = (union_fvs_uvs vs1 vs2)
in (sub_fv _128_1039 bvs))
in (cont _128_1040))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _128_1043 = (union_fvs_uvs vs1 vs2)
in (cont _128_1043))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _31_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _128_1046 = (union_fvs_uvs vs1 vs2)
in (cont _128_1046))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont ((no_bvars), (((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))))
end
| ((FStar_Util.Inl (a), _31_1587))::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _31_1595 -> (match (_31_1595) with
| ((tvars, vvars), vs2) -> begin
(let _128_1053 = (let _128_1052 = (let _128_1050 = (FStar_Util.set_add a tvars)
in ((_128_1050), (vvars)))
in (let _128_1051 = (union_fvs_uvs vs vs2)
in ((_128_1052), (_128_1051))))
in (cont _128_1053))
end)))))
end
| ((FStar_Util.Inr (x), _31_1600))::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _31_1608 -> (match (_31_1608) with
| ((tvars, vvars), vs2) -> begin
(let _128_1059 = (let _128_1058 = (let _128_1056 = (FStar_Util.set_add x vvars)
in ((tvars), (_128_1056)))
in (let _128_1057 = (union_fvs_uvs vs vs2)
in ((_128_1058), (_128_1057))))
in (cont _128_1059))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| ((FStar_Util.Inl (t), _31_1618))::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _128_1063 = (union_fvs_uvs ft1 ft2)
in (cont _128_1063))))))
end
| ((FStar_Util.Inr (e), _31_1627))::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _128_1066 = (union_fvs_uvs ft1 ft2)
in (cont _128_1066))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _128_1069 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _128_1068 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in ((_128_1069), (_128_1068))))) with
| (Some (_31_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (

let _31_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_typ' t uvonly (fun fvs -> (

let _31_1652 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_kind' = (fun k uvonly cont -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_31_1665, k) -> begin
(let _128_1074 = (let _128_1073 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _128_1073))
in (FStar_All.failwith _128_1074))
end
| FStar_Absyn_Syntax.Kind_delayed (_31_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _31_1681 -> (match (_31_1681) with
| (fvs, uvs) -> begin
(let _128_1078 = (let _128_1077 = (

let _31_1682 = uvs
in (let _128_1076 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _128_1076; FStar_Absyn_Syntax.uvars_t = _31_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _31_1682.FStar_Absyn_Syntax.uvars_e}))
in ((fvs), (_128_1077)))
in (cont _128_1078))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_31_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _31_1695 -> (match (_31_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _128_1082 = (let _128_1081 = (union_fvs_uvs vs1 vs2)
in (sub_fv _128_1081 bvs))
in (cont _128_1082))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _128_1085 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _128_1084 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in ((_128_1085), (_128_1084))))) with
| (Some (_31_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (

let _31_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_kind' k uvonly (fun fvs -> (

let _31_1717 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_exp' = (fun e uvonly cont -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_31_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _128_1091 = (let _128_1090 = (

let _31_1742 = FStar_Absyn_Syntax.no_uvs
in (let _128_1089 = (single_uvt ((uv), (t)))
in {FStar_Absyn_Syntax.uvars_k = _31_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _31_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _128_1089}))
in ((FStar_Absyn_Syntax.no_fvs), (_128_1090)))
in (cont _128_1091))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _128_1094 = (let _128_1093 = (

let _31_1746 = FStar_Absyn_Syntax.no_fvs
in (let _128_1092 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _31_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _128_1092}))
in ((_128_1093), (FStar_Absyn_Syntax.no_uvs)))
in (cont _128_1094))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _31_1750, _31_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _31_1761 -> (match (_31_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _128_1098 = (let _128_1097 = (union_fvs_uvs vs1 vs2)
in (sub_fv _128_1097 bvs))
in (cont _128_1098))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _128_1101 = (union_fvs_uvs ft1 ft2)
in (cont _128_1101))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _128_1104 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _128_1103 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in ((_128_1104), (_128_1103))))) with
| (Some (_31_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (

let _31_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_exp' e uvonly (fun fvs -> (

let _31_1801 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _128_1110 = (union_fvs_uvs vs1 vs2)
in (k _128_1110))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _128_1113 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _128_1112 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in ((_128_1113), (_128_1112))))) with
| (Some (_31_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (

let _31_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_comp' c uvonly (fun fvs -> (

let _31_1838 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _128_1120 = (union_fvs_uvs ft1 ft2)
in (cont _128_1120))))))
end))


let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _31_1867 -> (match (_31_1867) with
| (x, _31_1866) -> begin
x
end))))


let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _31_1872 -> (match (_31_1872) with
| (x, _31_1871) -> begin
x
end))))


let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _31_1877 -> (match (_31_1877) with
| (x, _31_1876) -> begin
x
end))))


let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _31_1882 -> (match (_31_1882) with
| (x, _31_1881) -> begin
x
end))))


let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _128_1136 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _128_1136))
end
| FStar_Util.Inr (e) -> begin
(let _128_1137 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _128_1137))
end)) FStar_Absyn_Syntax.no_fvs)))


let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _31_24 -> (match (_31_24) with
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
| SynSumKind (_31_1899) -> begin
_31_1899
end))


let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_31_1902) -> begin
_31_1902
end))


let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_31_1905) -> begin
_31_1905
end))


let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_31_1908) -> begin
_31_1908
end))


let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (

let out = (let _128_1211 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _128_1211 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _128_1209 = (uvars_in_kind k)
in (union_uvs _128_1209 out))
end
| _31_1916 -> begin
(

let _31_1917 = out
in (let _128_1210 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _128_1210; FStar_Absyn_Syntax.uvars_t = _31_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _31_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (

let out = (let _128_1216 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _128_1216 (FStar_List.fold_left (fun out _31_1923 -> (match (_31_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _128_1214 = (uvars_in_typ t)
in (union_uvs _128_1214 out))
end
| _31_1927 -> begin
(

let _31_1928 = out
in (let _128_1215 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _31_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _128_1215; FStar_Absyn_Syntax.uvars_e = _31_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (

let out = (let _128_1221 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _128_1221 (FStar_List.fold_left (fun out _31_1934 -> (match (_31_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _128_1219 = (uvars_in_exp e)
in (union_uvs _128_1219 out))
end
| _31_1938 -> begin
(

let _31_1939 = out
in (let _128_1220 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _31_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _31_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _128_1220}))
end)
end)) out)))
in (

let _31_1950 = (match (s) with
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _128_1224 = (vs_kind k true (fun _31_1956 -> (match (_31_1956) with
| (_31_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _128_1224)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _128_1227 = (vs_typ t true (fun _31_1961 -> (match (_31_1961) with
| (_31_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _128_1227)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _128_1230 = (vs_exp e true (fun _31_1966 -> (match (_31_1966) with
| (_31_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _128_1230)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _128_1233 = (vs_comp c true (fun _31_1971 -> (match (_31_1971) with
| (_31_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _128_1233)))


let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))


let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_31_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
(([]), (k))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _31_1991 = (kind_formals k)
in (match (_31_1991) with
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_31_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_31_1998) -> begin
(FStar_All.failwith "Impossible")
end)))


let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (

let _31_2005 = (kind_formals k)
in (match (_31_2005) with
| (bs, _31_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _31_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t.FStar_Absyn_Syntax.pos)
end)
end)))


let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_31_2012, k) -> begin
(unabbreviate_kind k)
end
| _31_2017 -> begin
k
end)))


let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _31_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((tps), (t)) None t.FStar_Absyn_Syntax.pos)
end))


let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _31_2027 -> begin
(

let _31_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(((FStar_List.append tps bs')), (c))
end
| _31_2033 -> begin
(let _128_1254 = (FStar_Absyn_Syntax.mk_Total t)
in ((tps), (_128_1254)))
end)
in (match (_31_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t.FStar_Absyn_Syntax.pos)
end))
end))


let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow


let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _31_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' ((tps), (k)) k.FStar_Absyn_Syntax.pos)
end))


let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _31_2046 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _128_1267 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _128_1267))
in (let _128_1268 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _128_1268 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _128_1273 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _128_1273))
in (let _128_1274 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _128_1274 r))))


let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _128_1279 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _128_1279)))


let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _31_2059 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _128_1286 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _128_1286))
in (let _128_1287 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _128_1287 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _128_1292 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _128_1292))
in (let _128_1293 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _128_1293 r))))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _128_1309 = (pre_typ t)
in _128_1309.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _31_2078 -> begin
false
end))


let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _128_1314 = (pre_typ t)
in _128_1314.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_31_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _31_2086) -> begin
(is_constructed_typ t lid)
end
| _31_2090 -> begin
false
end))


let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _31_2101) -> begin
(get_tycon t)
end
| _31_2105 -> begin
None
end)))


let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _31_25 -> (match (_31_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _31_2109 -> begin
false
end))


let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _31_2115 _31_2119 -> (match (((_31_2115), (_31_2119))) with
| ((fn1, _31_2114), (fn2, _31_2118)) -> begin
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


let b2t_v : FStar_Absyn_Syntax.typ = (let _128_1325 = (let _128_1324 = (let _128_1323 = (let _128_1322 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_128_1322)::[])
in ((_128_1323), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1324 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _128_1325))


let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _128_1336 = (let _128_1335 = (let _128_1333 = (let _128_1332 = (FStar_Absyn_Syntax.targ phi1)
in (let _128_1331 = (let _128_1330 = (FStar_Absyn_Syntax.targ phi2)
in (_128_1330)::[])
in (_128_1332)::_128_1331))
in ((tand), (_128_1333)))
in (let _128_1334 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _128_1335 None _128_1334)))
in Some (_128_1336))
end))


let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _128_1348 = (let _128_1346 = (let _128_1345 = (FStar_Absyn_Syntax.targ phi1)
in (let _128_1344 = (let _128_1343 = (FStar_Absyn_Syntax.targ phi2)
in (_128_1343)::[])
in (_128_1345)::_128_1344))
in ((op_t), (_128_1346)))
in (let _128_1347 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _128_1348 None _128_1347))))


let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _128_1354 = (let _128_1353 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _128_1352 = (let _128_1351 = (FStar_Absyn_Syntax.targ phi)
in (_128_1351)::[])
in ((_128_1353), (_128_1352))))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1354 None phi.FStar_Absyn_Syntax.pos)))


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


let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _128_1371 = (compress_typ phi1)
in _128_1371.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _31_2150 -> begin
(match ((let _128_1372 = (compress_typ phi2)
in _128_1372.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _31_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))


let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _128_1381 = (let _128_1380 = (let _128_1379 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_128_1379)::[])
in ((b2t_v), (_128_1380)))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1381 None e.FStar_Absyn_Syntax.pos)))


let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _31_2194)) -> begin
(mk_conj t1 t2)
end
| _31_2199 -> begin
t
end)))


let eq_k : FStar_Absyn_Syntax.knd = (

let a = (let _128_1384 = (new_bvd None)
in (bvd_to_bvar_s _128_1384 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (

let b = (let _128_1385 = (new_bvd None)
in (bvd_to_bvar_s _128_1385 FStar_Absyn_Syntax.ktype))
in (

let btyp = (btvar_to_typ b)
in (let _128_1392 = (let _128_1391 = (let _128_1390 = (let _128_1389 = (let _128_1388 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _128_1387 = (let _128_1386 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_128_1386)::[])
in (_128_1388)::_128_1387))
in (((FStar_Util.Inl (b)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_128_1389)
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_128_1390)
in ((_128_1391), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1392 FStar_Absyn_Syntax.dummyRange))))))


let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)


let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _31_2217 -> begin
(let _128_1410 = (let _128_1408 = (let _128_1407 = (FStar_Absyn_Syntax.itarg t1)
in (let _128_1406 = (let _128_1405 = (FStar_Absyn_Syntax.itarg t2)
in (let _128_1404 = (let _128_1403 = (FStar_Absyn_Syntax.varg e1)
in (let _128_1402 = (let _128_1401 = (FStar_Absyn_Syntax.varg e2)
in (_128_1401)::[])
in (_128_1403)::_128_1402))
in (_128_1405)::_128_1404))
in (_128_1407)::_128_1406))
in ((teq), (_128_1408)))
in (let _128_1409 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _128_1410 None _128_1409)))
end))


let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)


let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _128_1420 = (let _128_1418 = (let _128_1417 = (FStar_Absyn_Syntax.targ t1)
in (let _128_1416 = (let _128_1415 = (FStar_Absyn_Syntax.targ t2)
in (_128_1415)::[])
in (_128_1417)::_128_1416))
in ((eq_typ), (_128_1418)))
in (let _128_1419 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _128_1420 None _128_1419))))


let lex_t : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)


let lex_top : FStar_Absyn_Syntax.exp = (

let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexnil), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange))


let lex_pair : FStar_Absyn_Syntax.exp = (

let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (

let lexcons = (let _128_1430 = (let _128_1429 = (let _128_1428 = (let _128_1426 = (FStar_Absyn_Syntax.t_binder a)
in (let _128_1425 = (let _128_1424 = (let _128_1421 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _128_1421))
in (let _128_1423 = (let _128_1422 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_128_1422)::[])
in (_128_1424)::_128_1423))
in (_128_1426)::_128_1425))
in (let _128_1427 = (FStar_Absyn_Syntax.mk_Total lex_t)
in ((_128_1428), (_128_1427))))
in (FStar_Absyn_Syntax.mk_Typ_fun _128_1429 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _128_1430 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexcons), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange)))


let forall_kind : FStar_Absyn_Syntax.knd = (

let a = (let _128_1431 = (new_bvd None)
in (bvd_to_bvar_s _128_1431 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (let _128_1439 = (let _128_1438 = (let _128_1437 = (let _128_1436 = (let _128_1435 = (let _128_1434 = (let _128_1433 = (let _128_1432 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_128_1432)::[])
in ((_128_1433), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1434 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _128_1435))
in (_128_1436)::[])
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_128_1437)
in ((_128_1438), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1439 FStar_Absyn_Syntax.dummyRange))))


let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)


let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _128_1448 = (let _128_1447 = (let _128_1446 = (let _128_1445 = (let _128_1444 = (let _128_1443 = (let _128_1442 = (FStar_Absyn_Syntax.null_t_binder k)
in (_128_1442)::[])
in ((_128_1443), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1444 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _128_1445))
in (_128_1446)::[])
in ((_128_1447), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1448 FStar_Absyn_Syntax.dummyRange)))


let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _128_1455 = (let _128_1454 = (let _128_1453 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _128_1452 = (let _128_1451 = (FStar_Absyn_Syntax.null_t_binder k)
in (_128_1451)::[])
in (_128_1453)::_128_1452))
in ((_128_1454), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _128_1455 FStar_Absyn_Syntax.dummyRange)))


let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _128_1458 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _128_1458)))


let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _128_1470 = (let _128_1469 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _128_1468 = (let _128_1467 = (let _128_1466 = (let _128_1465 = (let _128_1464 = (let _128_1463 = (FStar_Absyn_Syntax.t_binder a)
in (_128_1463)::[])
in ((_128_1464), (b)))
in (FStar_Absyn_Syntax.mk_Typ_lam _128_1465 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _128_1466))
in (_128_1467)::[])
in ((_128_1469), (_128_1468))))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1470 None b.FStar_Absyn_Syntax.pos)))


let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (

let r = FStar_Absyn_Syntax.dummyRange
in (let _128_1481 = (let _128_1480 = (let _128_1479 = (let _128_1478 = (let _128_1477 = (let _128_1476 = (let _128_1475 = (FStar_Absyn_Syntax.v_binder x)
in (_128_1475)::[])
in ((_128_1476), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _128_1477 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _128_1478))
in (_128_1479)::[])
in ((tforall), (_128_1480)))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1481 None r))))


let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_lam (((b)::[]), (f)) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _128_1491 = (let _128_1490 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _128_1489 = (let _128_1488 = (FStar_Absyn_Syntax.targ body)
in (_128_1488)::[])
in ((_128_1490), (_128_1489))))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1491 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _128_1495 = (let _128_1494 = (let _128_1493 = (let _128_1492 = (FStar_Absyn_Syntax.targ body)
in (_128_1492)::[])
in (((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_128_1493)
in ((tforall), (_128_1494)))
in (FStar_Absyn_Syntax.mk_Typ_app _128_1495 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_31_2244) -> begin
true
end
| _31_2247 -> begin
false
end))


let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
((head), (args))
end
| _31_2255 -> begin
((t), ([]))
end)))


let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
((head), (args))
end
| _31_2263 -> begin
((e), ([]))
end)))


let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some (((bs), (c)))
end
| _31_2271 -> begin
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
| QAll (_31_2276) -> begin
_31_2276
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_31_2279) -> begin
_31_2279
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_31_2282) -> begin
_31_2282
end))


let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (

let destruct_base_conn = (fun f -> (

let _31_2288 = ((true), (false))
in (match (_31_2288) with
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

let rec aux = (fun f _31_2298 -> (match (_31_2298) with
| (lid, arity) -> begin
(

let _31_2301 = (head_and_args f)
in (match (_31_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_31_2305), _31_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_31_2311), _31_2314) -> begin
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
(let _128_1559 = (compress_typ t)
in ((pats), (_128_1559)))
end
| _31_2325 -> begin
(let _128_1560 = (compress_typ t)
in (([]), (_128_1560)))
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

let _31_2335 = (head_and_args t)
in (match (_31_2335) with
| (t, args) -> begin
(let _128_1574 = (FStar_All.pipe_right args (FStar_List.map (fun _31_26 -> (match (_31_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _128_1571 = (let _128_1570 = (compress_typ t)
in FStar_Util.Inl (_128_1570))
in ((_128_1571), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _128_1573 = (let _128_1572 = (compress_exp e)
in FStar_Util.Inr (_128_1572))
in ((_128_1573), (imp)))
end))))
in ((t), (_128_1574)))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _128_1581 = (flat t)
in ((qopt), (_128_1581)))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _31_2483) -> begin
(

let _31_2487 = (patterns t)
in (match (_31_2487) with
| (pats, body) -> begin
Some (QAll ((((FStar_List.rev out)), (pats), (body))))
end))
end
| (Some (false), _31_2491) -> begin
(

let _31_2495 = (patterns t)
in (match (_31_2495) with
| (pats, body) -> begin
Some (QEx ((((FStar_List.rev out)), (pats), (body))))
end))
end
| _31_2497 -> begin
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





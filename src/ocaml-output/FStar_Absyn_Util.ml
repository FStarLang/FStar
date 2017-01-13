
open Prims

type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}


let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkgensym_t"))))


let gs : gensym_t = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let n_resets = (FStar_Util.mk_ref (Prims.parse_int "0"))
in {gensym = (fun _33_31 -> (match (()) with
| () -> begin
(let _134_26 = (let _134_25 = (let _134_21 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _134_21))
in (let _134_24 = (let _134_23 = (let _134_22 = (

let _33_32 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _134_22))
in (Prims.strcat "_" _134_23))
in (Prims.strcat _134_25 _134_24)))
in (Prims.strcat "_" _134_26))
end)); reset = (fun _33_34 -> (match (()) with
| () -> begin
(

let _33_35 = (FStar_ST.op_Colon_Equals ctr (Prims.parse_int "0"))
in (FStar_Util.incr n_resets))
end))}))


let gensym : Prims.unit  ->  Prims.string = (fun _33_37 -> (match (()) with
| () -> begin
(gs.gensym ())
end))


let reset_gensym : Prims.unit  ->  Prims.unit = (fun _33_38 -> (match (()) with
| () -> begin
(gs.reset ())
end))


let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| _134_34 when (_134_34 = (Prims.parse_int "0")) -> begin
[]
end
| n -> begin
(let _134_36 = (gensym ())
in (let _134_35 = (gensyms (n - (Prims.parse_int "1")))
in (_134_36)::_134_35))
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


let mkbvd = (fun _33_52 -> (match (_33_52) with
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
| _33_79 -> begin
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


let freshen_bvd = (fun bvd' -> (let _134_77 = (let _134_76 = (genident (Some ((range_of_bvd bvd'))))
in ((bvd'.FStar_Absyn_Syntax.ppname), (_134_76)))
in (mkbvd _134_77)))


let freshen_bvar = (fun b -> (let _134_79 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _134_79 b.FStar_Absyn_Syntax.sort)))


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


let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _134_104 = (let _134_103 = (let _134_102 = (set_lid_range l r)
in (fv _134_102))
in ((_134_103), (dc)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _134_104 None r)))


let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))


let order_bvd = (fun x y -> (match (((x), (y))) with
| (FStar_Util.Inl (_33_125), FStar_Util.Inr (_33_128)) -> begin
(~- ((Prims.parse_int "1")))
end
| (FStar_Util.Inr (_33_132), FStar_Util.Inl (_33_135)) -> begin
(Prims.parse_int "1")
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))


let arg_of_non_null_binder = (fun _33_150 -> (match (_33_150) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _134_113 = (let _134_112 = (btvar_to_typ a)
in FStar_Util.Inl (_134_112))
in ((_134_113), (imp)))
end
| FStar_Util.Inr (x) -> begin
(let _134_115 = (let _134_114 = (bvar_to_exp x)
in FStar_Util.Inr (_134_114))
in ((_134_115), (imp)))
end)
end))


let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _134_119 = (arg_of_non_null_binder b)
in (_134_119)::[])
end))))


let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _134_129 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(

let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _134_124 = (let _134_123 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_134_123))
in ((_134_124), ((Prims.snd b))))
end
| FStar_Util.Inr (x) -> begin
(let _134_126 = (let _134_125 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_134_125))
in ((_134_126), ((Prims.snd b))))
end)
in (let _134_127 = (arg_of_non_null_binder b)
in ((b), (_134_127))))
end else begin
(let _134_128 = (arg_of_non_null_binder b)
in ((b), (_134_128)))
end)))
in (FStar_All.pipe_right _134_129 FStar_List.unzip)))


let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let b = (let _134_135 = (let _134_134 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _134_134))
in (FStar_Ident.id_of_text _134_135))
in (

let b = (bvd_to_bvar_s (mkbvd ((b), (b))) a.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inl (b)), (imp))))
end
| (FStar_Util.Inr (y), imp) -> begin
(

let x = (let _134_137 = (let _134_136 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _134_136))
in (FStar_Ident.id_of_text _134_137))
in (

let x = (bvd_to_bvar_s (mkbvd ((x), (x))) y.FStar_Absyn_Syntax.sort)
in ((FStar_Util.Inr (x)), (imp))))
end)
end else begin
b
end))))


let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _134_141 = (let _134_140 = (name_binders binders)
in ((_134_140), (comp)))
in (FStar_Absyn_Syntax.mk_Typ_fun _134_141 None t.FStar_Absyn_Syntax.pos))
end
| _33_185 -> begin
t
end))


let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _33_1 -> (match (_33_1) with
| (FStar_Util.Inl (k), imp) -> begin
(let _134_146 = (let _134_145 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _134_145))
in ((_134_146), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _134_148 = (let _134_147 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _134_147))
in ((_134_148), (imp)))
end)))))


let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _33_2 -> (match (_33_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _134_153 = (let _134_152 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_134_152))
in ((_134_153), (imp)))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _134_155 = (let _134_154 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_134_154))
in ((_134_155), (imp)))
end)))))


let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _134_161 = (let _134_158 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _134_158 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _134_160 = (let _134_159 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _134_159 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _134_161 _134_160))))


let subst_to_string = (fun s -> (let _134_164 = (FStar_All.pipe_right s (FStar_List.map (fun _33_3 -> (match (_33_3) with
| FStar_Util.Inl (b, _33_211) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _33_216) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _134_164 (FStar_String.concat ", "))))


let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _33_4 -> (match (_33_4) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _33_227 -> begin
None
end))))


let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _33_5 -> (match (_33_5) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _33_236 -> begin
None
end))))


let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _33_243 -> begin
(

let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _134_189 = (let _134_188 = (compose_subst s' s)
in (let _134_187 = (FStar_Util.mk_ref None)
in ((t'), (_134_188), (_134_187))))
in (FStar_Absyn_Syntax.mk_Typ_delayed _134_189 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (mk_t ())
in (

let _33_258 = (FStar_ST.op_Colon_Equals m (Some (t)))
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
| _33_270 -> begin
(aux rest)
end)
end
| _33_272 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _33_281 -> begin
(let _134_194 = (let _134_193 = (FStar_Util.mk_ref None)
in ((t0), (s), (_134_193)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _134_194 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _33_288 -> begin
(

let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _134_199 = (let _134_198 = (compose_subst s' s)
in (let _134_197 = (FStar_Util.mk_ref None)
in ((e), (_134_198), (_134_197))))
in (FStar_Absyn_Syntax.mk_Exp_delayed _134_199 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let rec aux = (fun s -> (match (s) with
| (s0)::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _33_305 -> begin
(aux rest)
end)
end
| _33_307 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _33_315 -> begin
(let _134_203 = (let _134_202 = (FStar_Util.mk_ref None)
in ((e0), (s), (_134_202)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _134_203 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | (([])::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _33_322 -> begin
(

let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _134_208 = (let _134_207 = (compose_subst s' s)
in (let _134_206 = (FStar_Util.mk_ref None)
in ((k), (_134_207), (_134_206))))
in (FStar_Absyn_Syntax.mk_Kind_delayed _134_208 k0.FStar_Absyn_Syntax.pos))
end
| _33_333 -> begin
(let _134_210 = (let _134_209 = (FStar_Util.mk_ref None)
in ((k0), (s), (_134_209)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _134_210 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _33_6 -> (match (_33_6) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _134_214 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_134_214))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _33_346 -> begin
(

let _33_347 = t
in (let _134_224 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _134_223 = (FStar_List.map (fun _33_7 -> (match (_33_7) with
| (FStar_Util.Inl (t), imp) -> begin
(let _134_219 = (let _134_218 = (subst_typ' s t)
in FStar_Util.Inl (_134_218))
in ((_134_219), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _134_221 = (let _134_220 = (subst_exp' s e)
in FStar_Util.Inr (_134_220))
in ((_134_221), (imp)))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _134_222 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _33_347.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _134_224; FStar_Absyn_Syntax.effect_args = _134_223; FStar_Absyn_Syntax.flags = _134_222}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | (([])::[]) -> begin
t
end
| _33_364 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _134_227 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _134_227))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _134_228 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _134_228))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))


let mk_subst = (fun s -> (s)::[])


let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))


let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))


let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))


let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))


let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))


let subst_binder = (fun s _33_8 -> (match (_33_8) with
| (FStar_Util.Inl (a), imp) -> begin
(let _134_256 = (let _134_255 = (

let _33_388 = a
in (let _134_254 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _33_388.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _134_254; FStar_Absyn_Syntax.p = _33_388.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_134_255))
in ((_134_256), (imp)))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _134_259 = (let _134_258 = (

let _33_394 = x
in (let _134_257 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _33_394.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _134_257; FStar_Absyn_Syntax.p = _33_394.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_134_258))
in ((_134_259), (imp)))
end))


let subst_arg = (fun s _33_9 -> (match (_33_9) with
| (FStar_Util.Inl (t), imp) -> begin
(let _134_263 = (let _134_262 = (subst_typ s t)
in FStar_Util.Inl (_134_262))
in ((_134_263), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _134_265 = (let _134_264 = (subst_exp s e)
in FStar_Util.Inr (_134_264))
in ((_134_265), (imp)))
end))


let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _33_410 -> begin
(FStar_List.map (subst_binder s) bs)
end))


let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _33_415 -> begin
(FStar_List.map (subst_arg s) args)
end))


let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match (((f), (a))) with
| ((FStar_Util.Inl (a), _33_421), (FStar_Util.Inl (t), _33_426)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (t)))
end
| ((FStar_Util.Inr (x), _33_432), (FStar_Util.Inr (v), _33_437)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (v)))
end
| _33_441 -> begin
(failwith "Ill-formed substitution")
end))


let mk_subst_one_binder : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.binder  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _134_280 = (let _134_279 = (let _134_278 = (btvar_to_typ a)
in ((b.FStar_Absyn_Syntax.v), (_134_278)))
in FStar_Util.Inl (_134_279))
in (_134_280)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _134_283 = (let _134_282 = (let _134_281 = (bvar_to_exp x)
in ((y.FStar_Absyn_Syntax.v), (_134_281)))
in FStar_Util.Inr (_134_282))
in (_134_283)::[])
end
end
| _33_455 -> begin
[]
end)
end)


let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (

let rec aux = (fun out bs1 bs2 -> (match (((bs1), (bs2))) with
| ([], []) -> begin
Some (out)
end
| ((b1)::bs1, (b2)::bs2) -> begin
(let _134_295 = (let _134_294 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _134_294 out))
in (aux _134_295 bs1 bs2))
end
| _33_473 -> begin
None
end))
in (aux [] bs1 bs2)))


let subst_of_list : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.subst = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(failwith "Ill-formed substitution")
end)


type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}


let is_Mkred_ctrl : red_ctrl  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkred_ctrl"))))


let alpha_ctrl : red_ctrl = {stop_if_empty_subst = false; descend = true}


let subst_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = true}


let null_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = false}


let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))


let map_knd = (fun s vk mt me descend binders k -> (let _134_316 = (subst_kind' s k)
in ((_134_316), (descend))))


let map_typ = (fun s mk vt me descend binders t -> (let _134_324 = (subst_typ' s t)
in ((_134_324), (descend))))


let map_exp = (fun s mk me ve descend binders e -> (let _134_332 = (subst_exp' s e)
in ((_134_332), (descend))))


let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _33_10 -> (match (_33_10) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _134_349 = (let _134_348 = (map_exp descend binders e)
in (FStar_All.pipe_right _134_348 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_134_349))
end
| f -> begin
f
end)))))


let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(

let _33_522 = (map_typ descend binders t)
in (match (_33_522) with
| (t, descend) -> begin
(let _134_372 = (FStar_Absyn_Syntax.mk_Total t)
in ((_134_372), (descend)))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _33_527 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_33_527) with
| (t, descend) -> begin
(

let _33_530 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_33_530) with
| (args, descend) -> begin
(let _134_375 = (let _134_374 = (

let _33_531 = ct
in (let _134_373 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _33_531.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _134_373}))
in (FStar_Absyn_Syntax.mk_Comp _134_374))
in ((_134_375), (descend)))
end))
end))
end))


let visit_knd = (fun s vk mt me ctrl binders k -> (

let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(

let _33_544 = (vk null_ctrl binders k)
in (match (_33_544) with
| (k, _33_543) -> begin
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

let k' = (let _134_421 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _134_421))
in (

let k' = (compress_kind k')
in (

let _33_554 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _134_423 = (let _134_422 = (subst_of_list formals actuals)
in (subst_kind _134_422 k'))
in (compress_kind _134_423))
end
| _33_567 -> begin
if ((FStar_List.length actuals) = (Prims.parse_int "0")) then begin
k
end else begin
(failwith "Wrong arity for kind unifier")
end
end)
end
| _33_569 -> begin
k
end)
end
| _33_571 -> begin
k
end)))


let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (

let visit_prod = (fun bs tc -> (

let _33_632 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _33_585 b -> (match (_33_585) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(

let _33_594 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_33_594) with
| (k, _33_593) -> begin
(

let a = (

let _33_595 = a
in {FStar_Absyn_Syntax.v = _33_595.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _33_595.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inl (a)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (

let _33_607 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inl (a)), (s), (boundvars'))
end
| _33_601 -> begin
(

let b = (let _134_500 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _134_500 k))
in (

let s = (let _134_503 = (let _134_502 = (let _134_501 = (btvar_to_typ b)
in ((a.FStar_Absyn_Syntax.v), (_134_501)))
in FStar_Util.Inl (_134_502))
in (extend_subst _134_503 s))
in ((FStar_Util.Inl (b)), (s), ((FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_33_607) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(

let _33_615 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_33_615) with
| (t, _33_614) -> begin
(

let x = (

let _33_616 = x
in {FStar_Absyn_Syntax.v = _33_616.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _33_616.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((((FStar_Util.Inr (x)), (imp)))::bs), (boundvars), (s))
end else begin
(

let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (

let _33_628 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
((FStar_Util.Inr (x)), (s), (boundvars'))
end
| _33_622 -> begin
(

let y = (let _134_513 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _134_513 t))
in (

let s = (let _134_516 = (let _134_515 = (let _134_514 = (bvar_to_exp y)
in ((x.FStar_Absyn_Syntax.v), (_134_514)))
in FStar_Util.Inr (_134_515))
in (extend_subst _134_516 s))
in ((FStar_Util.Inr (y)), (s), ((FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars))))
end)
in (match (_33_628) with
| (b, s, boundvars) -> begin
(((((b), (imp)))::bs), (boundvars), (s))
end)))
end)
end))
end)
end)) (([]), (boundvars), (s))))
in (match (_33_632) with
| (bs, boundvars, s) -> begin
(

let tc = (match (((s), (tc))) with
| ([], _33_635) -> begin
tc
end
| (_33_638, FStar_Util.Inl (t)) -> begin
(let _134_527 = (let _134_526 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _134_526))
in FStar_Util.Inl (_134_527))
end
| (_33_643, FStar_Util.Inr (c)) -> begin
(let _134_550 = (let _134_549 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _134_549))
in FStar_Util.Inr (_134_550))
end)
in (((FStar_List.rev bs)), (tc)))
end)))
in (

let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_33_650) -> begin
(let _134_552 = (let _134_551 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _134_551))
in ((_134_552), (ctrl)))
end
| _33_653 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _134_562 = (FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t0.FStar_Absyn_Syntax.pos)
in ((_134_562), (ctrl)))
end
| _33_663 -> begin
(failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod ((((FStar_Util.Inr (x)), (None)))::[]) (FStar_Util.Inl (t)))) with
| (((FStar_Util.Inr (x), _33_671))::[], FStar_Util.Inl (t)) -> begin
(let _134_563 = (FStar_Absyn_Syntax.mk_Typ_refine ((x), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_134_563), (ctrl)))
end
| _33_678 -> begin
(failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _134_564 = (FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t0.FStar_Absyn_Syntax.pos)
in ((_134_564), (ctrl)))
end
| _33_688 -> begin
(failwith "Impossible")
end)
end
| _33_690 -> begin
(

let _33_694 = (vt null_ctrl boundvars t)
in (match (_33_694) with
| (t, _33_693) -> begin
((t), (ctrl))
end))
end))))
and compress_typ' : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(

let res = (let _134_584 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _134_584))
in (

let res = (compress_typ' res)
in (

let _33_706 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(

let t = (let _134_586 = (mk_t ())
in (compress_typ' _134_586))
in (

let _33_714 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _33_717 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_33_721) -> begin
(failwith "Impossible: compress returned a delayed type")
end
| _33_724 -> begin
t
end)))


let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_33_734) -> begin
(let _134_652 = (let _134_651 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _134_651))
in ((_134_652), (ctrl)))
end
| _33_737 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _33_739 -> begin
(

let _33_743 = (ve null_ctrl binders e)
in (match (_33_743) with
| (e, _33_742) -> begin
((e), (ctrl))
end))
end)))
and compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(

let e = (let _134_681 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _134_681))
in (

let res = (compress_exp e)
in (

let _33_753 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _33_756 -> begin
e
end)))


let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _33_761)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _33_767, _33_769) -> begin
(unmeta_exp e)
end
| _33_773 -> begin
e
end)))


let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (

let s = (mk_subst [])
in (

let doit = (fun t -> (let _134_706 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _134_706)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_33_789) -> begin
(doit t)
end
| _33_792 -> begin
t
end)))))


let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match ((((Prims.fst formal)), ((Prims.fst actual)))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl (((a.FStar_Absyn_Syntax.v), (b)))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr (((x.FStar_Absyn_Syntax.v), (y)))
end
| _33_808 -> begin
(failwith "Ill-typed substitution")
end)) formals actuals))


let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _33_11 -> (match (_33_11) with
| None -> begin
None
end
| Some (t) -> begin
(let _134_713 = (compress_typ t)
in Some (_134_713))
end))


let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _134_718 = (let _134_717 = (let _134_716 = (FStar_Absyn_Syntax.mk_ident (((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText)), (lid.FStar_Ident.ident.FStar_Ident.idRange)))
in (_134_716)::[])
in (FStar_List.append lid.FStar_Ident.ns _134_717))
in (FStar_Ident.lid_of_ids _134_718)))


let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (

let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText (Prims.parse_int "0"))
in (FStar_Util.is_upper c)))


let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _134_726 = (let _134_725 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _134_725; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _134_726)))


let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))


let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))


let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_33_824) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(

let _33_828 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((

let _33_830 = ct
in {FStar_Absyn_Syntax.effect_name = _33_830.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _33_830.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _33_830.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _33_828.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _33_828.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _33_828.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _33_828.FStar_Absyn_Syntax.uvs})
end))


let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_33_834) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))


let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_33_842) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))


let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))


let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _33_12 -> (match (_33_12) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _33_854 -> begin
false
end)))))


let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _33_13 -> (match (_33_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _33_860 -> begin
false
end))))))


let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _33_14 -> (match (_33_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _33_866 -> begin
false
end))))))


let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _33_15 -> (match (_33_15) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _33_872 -> begin
false
end)))))


let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _33_16 -> (match (_33_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _33_878 -> begin
false
end)))))


let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))


let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_33_882) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _33_17 -> (match (_33_17) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _33_889 -> begin
false
end)))))
end))


let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))


let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))


let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _33_18 -> (match (_33_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _33_896 -> begin
false
end))))))


let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))


let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _134_765 = (compress_typ t)
in _134_765.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_33_900, c) -> begin
(is_pure_or_ghost_comp c)
end
| _33_905 -> begin
true
end))


let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _134_768 = (compress_typ t)
in _134_768.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_33_908, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _33_915 -> begin
false
end)
end
| _33_917 -> begin
false
end))


let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _134_771 = (compress_typ t)
in _134_771.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_33_920, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (_req)::(_ens)::((FStar_Util.Inr (pats), _33_931))::_33_927 -> begin
(match ((let _134_772 = (unmeta_exp pats)
in _134_772.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _33_948); FStar_Absyn_Syntax.tk = _33_945; FStar_Absyn_Syntax.pos = _33_943; FStar_Absyn_Syntax.fvs = _33_941; FStar_Absyn_Syntax.uvs = _33_939}, _33_953) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _33_957 -> begin
false
end)
end
| _33_959 -> begin
false
end)
end
| _33_961 -> begin
false
end)
end
| _33_963 -> begin
false
end))


let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _33_19 -> (match (_33_19) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _33_970 -> begin
false
end)))))
end
| _33_972 -> begin
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
| FStar_Absyn_Syntax.Total (_33_981) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (

let _33_985 = ct
in {FStar_Absyn_Syntax.effect_name = _33_985.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _33_985.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _33_985.FStar_Absyn_Syntax.flags}))
end))


let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _33_20 -> (match (_33_20) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _33_992 -> begin
false
end)))))


let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _134_782 = (compress_exp e)
in _134_782.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _33_1005)) -> begin
(is_atom e)
end
| _33_1010 -> begin
false
end))


let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]


let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _33_1014) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _33_1018 -> begin
false
end))


let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _33_1022, _33_1024) -> begin
(unascribe e)
end
| _33_1028 -> begin
e
end))


let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _33_1033) -> begin
(ascribe_typ t' k)
end
| _33_1037 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed ((t), (k)) t.FStar_Absyn_Syntax.pos)
end))


let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_1041) -> begin
(unascribe_typ t)
end
| _33_1045 -> begin
t
end))


let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _33_1050) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_1055) -> begin
(unrefine t)
end
| _33_1059 -> begin
t
end)))


let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _134_796 = (compress_exp e)
in _134_796.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_33_1062) -> begin
true
end
| _33_1065 -> begin
false
end))


let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _134_799 = (compress_typ t)
in _134_799.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_33_1068) -> begin
true
end
| _33_1071 -> begin
false
end))


let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _33_1076) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_1081) -> begin
(pre_typ t)
end
| _33_1085 -> begin
t
end)))


let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (

let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _33_1096; FStar_Absyn_Syntax.pos = _33_1094; FStar_Absyn_Syntax.fvs = _33_1092; FStar_Absyn_Syntax.uvs = _33_1090}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _33_1106 -> begin
None
end)))


let rec lids_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.lident Prims.list = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _33_1200) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))


let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| (l)::[] -> begin
Some (l)
end
| _33_1216 -> begin
None
end))


let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))


let range_of_lb = (fun _33_21 -> (match (_33_21) with
| (FStar_Util.Inl (x), _33_1327, _33_1329) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _33_1334, _33_1336) -> begin
(FStar_Ident.range_of_lid l)
end))


let range_of_arg = (fun _33_22 -> (match (_33_22) with
| (FStar_Util.Inl (hd), _33_1342) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _33_1347) -> begin
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
(let _134_832 = (let _134_831 = (let _134_830 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in ((_134_830), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_134_831))
in (FStar_Absyn_Syntax.mk_Exp_meta _134_832))
end
| _33_1363 -> begin
(let _134_836 = (let _134_835 = (let _134_834 = (let _134_833 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _134_833 args))
in ((_134_834), (FStar_Absyn_Syntax.Data_app)))
in FStar_Absyn_Syntax.Meta_desugared (_134_835))
in (FStar_Absyn_Syntax.mk_Exp_meta _134_836))
end))


let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident (((Prims.strcat "^fname^" x.FStar_Ident.idText)), (x.FStar_Ident.idRange))))


let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _134_842 = (let _134_841 = (FStar_Util.substring_from x.FStar_Ident.idText (Prims.parse_int "7"))
in ((_134_841), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident _134_842))
end else begin
x
end)


let mk_field_projector_name = (fun lid x i -> (

let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _134_848 = (let _134_847 = (let _134_846 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _134_846))
in ((_134_847), (x.FStar_Absyn_Syntax.p)))
in (FStar_Absyn_Syntax.mk_ident _134_848))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (

let y = (

let _33_1372 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _33_1372.FStar_Absyn_Syntax.realname})
in (let _134_852 = (let _134_851 = (let _134_850 = (let _134_849 = (unmangle_field_name nm)
in (_134_849)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _134_850))
in (FStar_Ident.lid_of_ids _134_851))
in ((_134_852), (y))))))


let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_33_1378) -> begin
(let _134_857 = (let _134_856 = (let _134_855 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _134_855))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _134_856))
in (failwith _134_857))
end
| _33_1381 -> begin
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
| _33_1397 -> begin
false
end))


let eq_binder = (fun b1 b2 -> (match ((((Prims.fst b1)), ((Prims.fst b2)))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _33_1411 -> begin
false
end))


let uv_eq = (fun _33_1415 _33_1419 -> (match (((_33_1415), (_33_1419))) with
| ((uv1, _33_1414), (uv2, _33_1418)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))


let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _134_874 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _134_873 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _134_872 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _134_874; FStar_Absyn_Syntax.uvars_t = _134_873; FStar_Absyn_Syntax.uvars_e = _134_872}))))


let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _134_880 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _134_879 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _134_880; FStar_Absyn_Syntax.fxvs = _134_879})))


let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _33_1426 _33_1429 -> (match (((_33_1426), (_33_1429))) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _134_886 = (union_fvs fvs1 fvs2)
in (let _134_885 = (union_uvs uvs1 uvs2)
in ((_134_886), (_134_885))))
end))


let sub_fv = (fun _33_1432 _33_1435 -> (match (((_33_1432), (_33_1435))) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _134_891 = (

let _33_1436 = fvs
in (let _134_890 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _134_889 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _134_890; FStar_Absyn_Syntax.fxvs = _134_889})))
in ((_134_891), (uvs)))
end))


let stash = (fun uvonly s _33_1444 -> (match (_33_1444) with
| (fvs, uvs) -> begin
(

let _33_1445 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))


let single_fv = (fun x -> (let _134_896 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _134_896)))


let single_uv = (fun u -> (let _134_898 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _134_898)))


let single_uvt = (fun u -> (let _134_900 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _134_900)))


let rec vs_typ' = (fun t uvonly cont -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_33_1456) -> begin
(failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _134_1015 = (let _134_1014 = (

let _33_1460 = FStar_Absyn_Syntax.no_fvs
in (let _134_1013 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _134_1013; FStar_Absyn_Syntax.fxvs = _33_1460.FStar_Absyn_Syntax.fxvs}))
in ((_134_1014), (FStar_Absyn_Syntax.no_uvs)))
in (cont _134_1015))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _134_1018 = (let _134_1017 = (

let _33_1466 = FStar_Absyn_Syntax.no_uvs
in (let _134_1016 = (single_uvt ((uv), (k)))
in {FStar_Absyn_Syntax.uvars_k = _33_1466.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _134_1016; FStar_Absyn_Syntax.uvars_e = _33_1466.FStar_Absyn_Syntax.uvars_e}))
in ((FStar_Absyn_Syntax.no_fvs), (_134_1017)))
in (cont _134_1018))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _33_1478 -> (match (_33_1478) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _134_1022 = (let _134_1021 = (union_fvs_uvs vs1 vs2)
in (sub_fv _134_1021 bvs))
in (cont _134_1022))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _33_1486 -> (match (_33_1486) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _134_1026 = (let _134_1025 = (union_fvs_uvs vs1 vs2)
in (sub_fv _134_1025 bvs))
in (cont _134_1026))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders ((((FStar_Util.Inr (x)), (None)))::[]) uvonly (fun _33_1494 -> (match (_33_1494) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _134_1030 = (let _134_1029 = (union_fvs_uvs vs1 vs2)
in (sub_fv _134_1029 bvs))
in (cont _134_1030))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _134_1033 = (union_fvs_uvs vs1 vs2)
in (cont _134_1033))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _33_1504) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _33_1510)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _134_1036 = (union_fvs_uvs vs1 vs2)
in (cont _134_1036))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont ((no_bvars), (((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))))
end
| ((FStar_Util.Inl (a), _33_1552))::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _33_1560 -> (match (_33_1560) with
| ((tvars, vvars), vs2) -> begin
(let _134_1043 = (let _134_1042 = (let _134_1040 = (FStar_Util.set_add a tvars)
in ((_134_1040), (vvars)))
in (let _134_1041 = (union_fvs_uvs vs vs2)
in ((_134_1042), (_134_1041))))
in (cont _134_1043))
end)))))
end
| ((FStar_Util.Inr (x), _33_1565))::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _33_1573 -> (match (_33_1573) with
| ((tvars, vvars), vs2) -> begin
(let _134_1049 = (let _134_1048 = (let _134_1046 = (FStar_Util.set_add x vvars)
in ((tvars), (_134_1046)))
in (let _134_1047 = (union_fvs_uvs vs vs2)
in ((_134_1048), (_134_1047))))
in (cont _134_1049))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| ((FStar_Util.Inl (t), _33_1583))::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _134_1053 = (union_fvs_uvs ft1 ft2)
in (cont _134_1053))))))
end
| ((FStar_Util.Inr (e), _33_1592))::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _134_1056 = (union_fvs_uvs ft1 ft2)
in (cont _134_1056))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _134_1059 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _134_1058 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in ((_134_1059), (_134_1058))))) with
| (Some (_33_1602), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (

let _33_1610 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_typ' t uvonly (fun fvs -> (

let _33_1617 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_kind' = (fun k uvonly cont -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_33_1630, k) -> begin
(let _134_1064 = (let _134_1063 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _134_1063))
in (failwith _134_1064))
end
| FStar_Absyn_Syntax.Kind_delayed (_33_1635) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _33_1646 -> (match (_33_1646) with
| (fvs, uvs) -> begin
(let _134_1068 = (let _134_1067 = (

let _33_1647 = uvs
in (let _134_1066 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _134_1066; FStar_Absyn_Syntax.uvars_t = _33_1647.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _33_1647.FStar_Absyn_Syntax.uvars_e}))
in ((fvs), (_134_1067)))
in (cont _134_1068))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_1650, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _33_1660 -> (match (_33_1660) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _134_1072 = (let _134_1071 = (union_fvs_uvs vs1 vs2)
in (sub_fv _134_1071 bvs))
in (cont _134_1072))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _134_1075 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _134_1074 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in ((_134_1075), (_134_1074))))) with
| (Some (_33_1667), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (

let _33_1675 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_kind' k uvonly (fun fvs -> (

let _33_1682 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont ((fvs), (uvs)))
end))
and vs_exp' = (fun e uvonly cont -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_33_1695) -> begin
(failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _134_1081 = (let _134_1080 = (

let _33_1707 = FStar_Absyn_Syntax.no_uvs
in (let _134_1079 = (single_uvt ((uv), (t)))
in {FStar_Absyn_Syntax.uvars_k = _33_1707.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _33_1707.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _134_1079}))
in ((FStar_Absyn_Syntax.no_fvs), (_134_1080)))
in (cont _134_1081))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end else begin
(let _134_1084 = (let _134_1083 = (

let _33_1711 = FStar_Absyn_Syntax.no_fvs
in (let _134_1082 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _33_1711.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _134_1082}))
in ((_134_1083), (FStar_Absyn_Syntax.no_uvs)))
in (cont _134_1084))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _33_1715, _33_1717) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _33_1726 -> (match (_33_1726) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _134_1088 = (let _134_1087 = (union_fvs_uvs vs1 vs2)
in (sub_fv _134_1087 bvs))
in (cont _134_1088))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _134_1091 = (union_fvs_uvs ft1 ft2)
in (cont _134_1091))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont ((FStar_Absyn_Syntax.no_fvs), (FStar_Absyn_Syntax.no_uvs)))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _33_1742)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _134_1094 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _134_1093 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in ((_134_1094), (_134_1093))))) with
| (Some (_33_1751), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (

let _33_1759 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_exp' e uvonly (fun fvs -> (

let _33_1766 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _134_1100 = (union_fvs_uvs vs1 vs2)
in (k _134_1100))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _134_1103 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _134_1102 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in ((_134_1103), (_134_1102))))) with
| (Some (_33_1788), None) -> begin
(failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (

let _33_1796 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont ((FStar_Absyn_Syntax.no_fvs), (uvs)))
end else begin
(vs_comp' c uvonly (fun fvs -> (

let _33_1803 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _134_1110 = (union_fvs_uvs ft1 ft2)
in (cont _134_1110))))))
end))


let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _33_1832 -> (match (_33_1832) with
| (x, _33_1831) -> begin
x
end))))


let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _33_1837 -> (match (_33_1837) with
| (x, _33_1836) -> begin
x
end))))


let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _33_1842 -> (match (_33_1842) with
| (x, _33_1841) -> begin
x
end))))


let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _33_1847 -> (match (_33_1847) with
| (x, _33_1846) -> begin
x
end))))


let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _134_1126 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _134_1126))
end
| FStar_Util.Inr (e) -> begin
(let _134_1127 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _134_1127))
end)) FStar_Absyn_Syntax.no_fvs)))


let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _33_23 -> (match (_33_23) with
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
| SynSumKind (_33_1864) -> begin
_33_1864
end))


let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_33_1867) -> begin
_33_1867
end))


let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_33_1870) -> begin
_33_1870
end))


let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_33_1873) -> begin
_33_1873
end))


let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (

let out = (let _134_1201 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _134_1201 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _134_1199 = (uvars_in_kind k)
in (union_uvs _134_1199 out))
end
| _33_1881 -> begin
(

let _33_1882 = out
in (let _134_1200 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _134_1200; FStar_Absyn_Syntax.uvars_t = _33_1882.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _33_1882.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (

let out = (let _134_1206 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _134_1206 (FStar_List.fold_left (fun out _33_1888 -> (match (_33_1888) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _134_1204 = (uvars_in_typ t)
in (union_uvs _134_1204 out))
end
| _33_1892 -> begin
(

let _33_1893 = out
in (let _134_1205 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _33_1893.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _134_1205; FStar_Absyn_Syntax.uvars_e = _33_1893.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (

let out = (let _134_1211 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _134_1211 (FStar_List.fold_left (fun out _33_1899 -> (match (_33_1899) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _134_1209 = (uvars_in_exp e)
in (union_uvs _134_1209 out))
end
| _33_1903 -> begin
(

let _33_1904 = out
in (let _134_1210 = (FStar_Util.set_add ((u), (t)) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _33_1904.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _33_1904.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _134_1210}))
end)
end)) out)))
in (

let _33_1915 = (match (s) with
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _134_1214 = (vs_kind k true (fun _33_1921 -> (match (_33_1921) with
| (_33_1919, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _134_1214)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _134_1217 = (vs_typ t true (fun _33_1926 -> (match (_33_1926) with
| (_33_1924, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _134_1217)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _134_1220 = (vs_exp e true (fun _33_1931 -> (match (_33_1931) with
| (_33_1929, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _134_1220)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _134_1223 = (vs_comp c true (fun _33_1936 -> (match (_33_1936) with
| (_33_1934, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _134_1223)))


let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))


let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_33_1942) -> begin
(failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
(([]), (k))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(

let _33_1956 = (kind_formals k)
in (match (_33_1956) with
| (bs', k) -> begin
(((FStar_List.append bs bs')), (k))
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_33_1958, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_33_1963) -> begin
(failwith "Impossible")
end)))


let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (

let _33_1970 = (kind_formals k)
in (match (_33_1970) with
| (bs, _33_1969) -> begin
(match (bs) with
| [] -> begin
t
end
| _33_1973 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((bs), (t)) None t.FStar_Absyn_Syntax.pos)
end)
end)))


let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (

let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_33_1977, k) -> begin
(unabbreviate_kind k)
end
| _33_1982 -> begin
k
end)))


let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _33_1987 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam ((tps), (t)) None t.FStar_Absyn_Syntax.pos)
end))


let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _33_1992 -> begin
(

let _33_2001 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(((FStar_List.append tps bs')), (c))
end
| _33_1998 -> begin
(let _134_1244 = (FStar_Absyn_Syntax.mk_Total t)
in ((tps), (_134_1244)))
end)
in (match (_33_2001) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun ((bs), (c)) None t.FStar_Absyn_Syntax.pos)
end))
end))


let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow


let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _33_2006 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' ((tps), (k)) k.FStar_Absyn_Syntax.pos)
end))


let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _33_2011 -> begin
false
end))


let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _134_1257 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _134_1257))
in (let _134_1258 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _134_1258 r))))


let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _134_1263 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _134_1263))
in (let _134_1264 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _134_1264 r))))


let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _134_1269 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _134_1269)))


let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _33_2024 -> begin
false
end))


let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _134_1276 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _134_1276))
in (let _134_1277 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _134_1277 r))))


let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (

let t = (let _134_1282 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _134_1282))
in (let _134_1283 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _134_1283 r))))


let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))


let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))


let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))


let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))


let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))


let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (

let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))


let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _134_1299 = (pre_typ t)
in _134_1299.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _33_2043 -> begin
false
end))


let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _134_1304 = (pre_typ t)
in _134_1304.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_33_2047) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _33_2051) -> begin
(is_constructed_typ t lid)
end
| _33_2055 -> begin
false
end))


let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (

let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _33_2066) -> begin
(get_tycon t)
end
| _33_2070 -> begin
None
end)))


let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _33_24 -> (match (_33_24) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _33_2074 -> begin
false
end))


let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _33_2080 _33_2084 -> (match (((_33_2080), (_33_2084))) with
| ((fn1, _33_2079), (fn2, _33_2083)) -> begin
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


let b2t_v : FStar_Absyn_Syntax.typ = (let _134_1315 = (let _134_1314 = (let _134_1313 = (let _134_1312 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_134_1312)::[])
in ((_134_1313), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1314 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _134_1315))


let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _134_1326 = (let _134_1325 = (let _134_1323 = (let _134_1322 = (FStar_Absyn_Syntax.targ phi1)
in (let _134_1321 = (let _134_1320 = (FStar_Absyn_Syntax.targ phi2)
in (_134_1320)::[])
in (_134_1322)::_134_1321))
in ((tand), (_134_1323)))
in (let _134_1324 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_1325 None _134_1324)))
in Some (_134_1326))
end))


let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _134_1338 = (let _134_1336 = (let _134_1335 = (FStar_Absyn_Syntax.targ phi1)
in (let _134_1334 = (let _134_1333 = (FStar_Absyn_Syntax.targ phi2)
in (_134_1333)::[])
in (_134_1335)::_134_1334))
in ((op_t), (_134_1336)))
in (let _134_1337 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_1338 None _134_1337))))


let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _134_1344 = (let _134_1343 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _134_1342 = (let _134_1341 = (FStar_Absyn_Syntax.targ phi)
in (_134_1341)::[])
in ((_134_1343), (_134_1342))))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1344 None phi.FStar_Absyn_Syntax.pos)))


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


let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _134_1361 = (compress_typ phi1)
in _134_1361.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _33_2115 -> begin
(match ((let _134_1362 = (compress_typ phi2)
in _134_1362.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _33_2119 -> begin
(mk_binop timp phi1 phi2)
end)
end))


let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))


let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _134_1371 = (let _134_1370 = (let _134_1369 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_134_1369)::[])
in ((b2t_v), (_134_1370)))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1371 None e.FStar_Absyn_Syntax.pos)))


let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _33_2159)) -> begin
(mk_conj t1 t2)
end
| _33_2164 -> begin
t
end)))


let eq_k : FStar_Absyn_Syntax.knd = (

let a = (let _134_1374 = (new_bvd None)
in (bvd_to_bvar_s _134_1374 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (

let b = (let _134_1375 = (new_bvd None)
in (bvd_to_bvar_s _134_1375 FStar_Absyn_Syntax.ktype))
in (

let btyp = (btvar_to_typ b)
in (let _134_1382 = (let _134_1381 = (let _134_1380 = (let _134_1379 = (let _134_1378 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _134_1377 = (let _134_1376 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_134_1376)::[])
in (_134_1378)::_134_1377))
in (((FStar_Util.Inl (b)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_134_1379)
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_134_1380)
in ((_134_1381), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1382 FStar_Absyn_Syntax.dummyRange))))))


let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)


let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match (((t1.FStar_Absyn_Syntax.n), (t2.FStar_Absyn_Syntax.n))) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(failwith "DIE! mk_eq with tun")
end
| _33_2182 -> begin
(let _134_1400 = (let _134_1398 = (let _134_1397 = (FStar_Absyn_Syntax.itarg t1)
in (let _134_1396 = (let _134_1395 = (FStar_Absyn_Syntax.itarg t2)
in (let _134_1394 = (let _134_1393 = (FStar_Absyn_Syntax.varg e1)
in (let _134_1392 = (let _134_1391 = (FStar_Absyn_Syntax.varg e2)
in (_134_1391)::[])
in (_134_1393)::_134_1392))
in (_134_1395)::_134_1394))
in (_134_1397)::_134_1396))
in ((teq), (_134_1398)))
in (let _134_1399 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_1400 None _134_1399)))
end))


let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)


let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _134_1410 = (let _134_1408 = (let _134_1407 = (FStar_Absyn_Syntax.targ t1)
in (let _134_1406 = (let _134_1405 = (FStar_Absyn_Syntax.targ t2)
in (_134_1405)::[])
in (_134_1407)::_134_1406))
in ((eq_typ), (_134_1408)))
in (let _134_1409 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _134_1410 None _134_1409))))


let lex_t : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)


let lex_top : FStar_Absyn_Syntax.exp = (

let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexnil), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange))


let lex_pair : FStar_Absyn_Syntax.exp = (

let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (

let lexcons = (let _134_1420 = (let _134_1419 = (let _134_1418 = (let _134_1416 = (FStar_Absyn_Syntax.t_binder a)
in (let _134_1415 = (let _134_1414 = (let _134_1411 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _134_1411))
in (let _134_1413 = (let _134_1412 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_134_1412)::[])
in (_134_1414)::_134_1413))
in (_134_1416)::_134_1415))
in (let _134_1417 = (FStar_Absyn_Syntax.mk_Total lex_t)
in ((_134_1418), (_134_1417))))
in (FStar_Absyn_Syntax.mk_Typ_fun _134_1419 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _134_1420 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar ((lexcons), (Some (FStar_Absyn_Syntax.Data_ctor))) None FStar_Absyn_Syntax.dummyRange)))


let forall_kind : FStar_Absyn_Syntax.knd = (

let a = (let _134_1421 = (new_bvd None)
in (bvd_to_bvar_s _134_1421 FStar_Absyn_Syntax.ktype))
in (

let atyp = (btvar_to_typ a)
in (let _134_1429 = (let _134_1428 = (let _134_1427 = (let _134_1426 = (let _134_1425 = (let _134_1424 = (let _134_1423 = (let _134_1422 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_134_1422)::[])
in ((_134_1423), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1424 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _134_1425))
in (_134_1426)::[])
in (((FStar_Util.Inl (a)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_134_1427)
in ((_134_1428), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1429 FStar_Absyn_Syntax.dummyRange))))


let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)


let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _134_1438 = (let _134_1437 = (let _134_1436 = (let _134_1435 = (let _134_1434 = (let _134_1433 = (let _134_1432 = (FStar_Absyn_Syntax.null_t_binder k)
in (_134_1432)::[])
in ((_134_1433), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1434 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _134_1435))
in (_134_1436)::[])
in ((_134_1437), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1438 FStar_Absyn_Syntax.dummyRange)))


let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _134_1445 = (let _134_1444 = (let _134_1443 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _134_1442 = (let _134_1441 = (FStar_Absyn_Syntax.null_t_binder k)
in (_134_1441)::[])
in (_134_1443)::_134_1442))
in ((_134_1444), (FStar_Absyn_Syntax.ktype)))
in (FStar_Absyn_Syntax.mk_Kind_arrow _134_1445 FStar_Absyn_Syntax.dummyRange)))


let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _134_1448 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _134_1448)))


let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _134_1460 = (let _134_1459 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _134_1458 = (let _134_1457 = (let _134_1456 = (let _134_1455 = (let _134_1454 = (let _134_1453 = (FStar_Absyn_Syntax.t_binder a)
in (_134_1453)::[])
in ((_134_1454), (b)))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_1455 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _134_1456))
in (_134_1457)::[])
in ((_134_1459), (_134_1458))))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1460 None b.FStar_Absyn_Syntax.pos)))


let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (

let r = FStar_Absyn_Syntax.dummyRange
in (let _134_1471 = (let _134_1470 = (let _134_1469 = (let _134_1468 = (let _134_1467 = (let _134_1466 = (let _134_1465 = (FStar_Absyn_Syntax.v_binder x)
in (_134_1465)::[])
in ((_134_1466), (body)))
in (FStar_Absyn_Syntax.mk_Typ_lam _134_1467 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _134_1468))
in (_134_1469)::[])
in ((tforall), (_134_1470)))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1471 None r))))


let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(

let body = (FStar_Absyn_Syntax.mk_Typ_lam (((b)::[]), (f)) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _134_1481 = (let _134_1480 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _134_1479 = (let _134_1478 = (FStar_Absyn_Syntax.targ body)
in (_134_1478)::[])
in ((_134_1480), (_134_1479))))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1481 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _134_1485 = (let _134_1484 = (let _134_1483 = (let _134_1482 = (FStar_Absyn_Syntax.targ body)
in (_134_1482)::[])
in (((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort)), (Some (FStar_Absyn_Syntax.Implicit (false)))))::_134_1483)
in ((tforall), (_134_1484)))
in (FStar_Absyn_Syntax.mk_Typ_app _134_1485 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))


let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_33_2209) -> begin
true
end
| _33_2212 -> begin
false
end))


let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
((head), (args))
end
| _33_2220 -> begin
((t), ([]))
end)))


let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (

let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
((head), (args))
end
| _33_2228 -> begin
((e), ([]))
end)))


let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (

let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some (((bs), (c)))
end
| _33_2236 -> begin
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
| QAll (_33_2241) -> begin
_33_2241
end))


let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_33_2244) -> begin
_33_2244
end))


let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_33_2247) -> begin
_33_2247
end))


let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (

let destruct_base_conn = (fun f -> (

let _33_2253 = ((true), (false))
in (match (_33_2253) with
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

let rec aux = (fun f _33_2263 -> (match (_33_2263) with
| (lid, arity) -> begin
(

let _33_2266 = (head_and_args f)
in (match (_33_2266) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_33_2270), _33_2273) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_33_2276), _33_2279) -> begin
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
(let _134_1549 = (compress_typ t)
in ((pats), (_134_1549)))
end
| _33_2290 -> begin
(let _134_1550 = (compress_typ t)
in (([]), (_134_1550)))
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

let _33_2300 = (head_and_args t)
in (match (_33_2300) with
| (t, args) -> begin
(let _134_1564 = (FStar_All.pipe_right args (FStar_List.map (fun _33_25 -> (match (_33_25) with
| (FStar_Util.Inl (t), imp) -> begin
(let _134_1561 = (let _134_1560 = (compress_typ t)
in FStar_Util.Inl (_134_1560))
in ((_134_1561), (imp)))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _134_1563 = (let _134_1562 = (compress_exp e)
in FStar_Util.Inr (_134_1562))
in ((_134_1563), (imp)))
end))))
in ((t), (_134_1564)))
end)))
in (

let rec aux = (fun qopt out t -> (match ((let _134_1571 = (flat t)
in ((qopt), (_134_1571)))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, ((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (_)::((FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam ((b)::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _))::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _33_2448) -> begin
(

let _33_2452 = (patterns t)
in (match (_33_2452) with
| (pats, body) -> begin
Some (QAll ((((FStar_List.rev out)), (pats), (body))))
end))
end
| (Some (false), _33_2456) -> begin
(

let _33_2460 = (patterns t)
in (match (_33_2460) with
| (pats, body) -> begin
Some (QEx ((((FStar_List.rev out)), (pats), (body))))
end))
end
| _33_2462 -> begin
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





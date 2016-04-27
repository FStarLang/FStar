
open Prims
# 26 "FStar.Absyn.Util.fst"
let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Fatal: %s" ((s)::[]))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(
# 33 "FStar.Absyn.Util.fst"
let _31_36 = (let _120_8 = (let _120_7 = (FStar_Range.string_of_range r)
in (_120_7)::(if warning then begin
"Warning"
end else begin
"Error"
end)::(msg)::[])
in (FStar_Util.fprint FStar_Util.stderr "%s : %s\n%s\n" _120_8))
in ())
end
| FStar_Util.NYI (s) -> begin
(
# 36 "FStar.Absyn.Util.fst"
let _31_40 = (FStar_Util.fprint FStar_Util.stderr "Feature not yet implemented: %s" ((s)::[]))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(FStar_Util.fprint FStar_Util.stderr "Error: %s" ((s)::[]))
end
| _31_45 -> begin
(Prims.raise e)
end))

# 40 "FStar.Absyn.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _31_1 -> (match (_31_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _31_60 -> begin
false
end))

# 47 "FStar.Absyn.Util.fst"
type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

# 53 "FStar.Absyn.Util.fst"
let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

# 56 "FStar.Absyn.Util.fst"
let gs : gensym_t = (
# 58 "FStar.Absyn.Util.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 59 "FStar.Absyn.Util.fst"
let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _31_66 -> (match (()) with
| () -> begin
(let _120_36 = (let _120_33 = (let _120_32 = (let _120_31 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _120_31))
in (Prims.strcat "_" _120_32))
in (Prims.strcat _120_33 "_"))
in (let _120_35 = (let _120_34 = (
# 60 "FStar.Absyn.Util.fst"
let _31_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _120_34))
in (Prims.strcat _120_36 _120_35)))
end)); reset = (fun _31_69 -> (match (()) with
| () -> begin
(
# 61 "FStar.Absyn.Util.fst"
let _31_70 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

# 61 "FStar.Absyn.Util.fst"
let gensym : Prims.unit  ->  Prims.string = (fun _31_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

# 62 "FStar.Absyn.Util.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (fun _31_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))

# 63 "FStar.Absyn.Util.fst"
let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _120_45 = (gensym ())
in (let _120_44 = (gensyms (n - 1))
in (_120_45)::_120_44))
end))

# 66 "FStar.Absyn.Util.fst"
let genident : FStar_Range.range Prims.option  ->  FStar_Ident.ident = (fun r -> (
# 69 "FStar.Absyn.Util.fst"
let sym = (gensym ())
in (match (r) with
| None -> begin
(FStar_Ident.mk_ident (sym, FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(FStar_Ident.mk_ident (sym, r))
end)))

# 72 "FStar.Absyn.Util.fst"
let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Ident.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Ident.idText))

# 74 "FStar.Absyn.Util.fst"
let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange)

# 75 "FStar.Absyn.Util.fst"
let mkbvd = (fun _31_87 -> (match (_31_87) with
| (x, y) -> begin
{FStar_Absyn_Syntax.ppname = x; FStar_Absyn_Syntax.realname = y}
end))

# 77 "FStar.Absyn.Util.fst"
let setsort = (fun w t -> {FStar_Absyn_Syntax.v = w.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = w.FStar_Absyn_Syntax.p})

# 78 "FStar.Absyn.Util.fst"
let withinfo = (fun e s r -> {FStar_Absyn_Syntax.v = e; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = r})

# 79 "FStar.Absyn.Util.fst"
let withsort = (fun e s -> (withinfo e s FStar_Absyn_Syntax.dummyRange))

# 80 "FStar.Absyn.Util.fst"
let bvar_ppname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)

# 81 "FStar.Absyn.Util.fst"
let bvar_realname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname)

# 82 "FStar.Absyn.Util.fst"
let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.FStar_Absyn_Syntax.v bv2.FStar_Absyn_Syntax.v))

# 83 "FStar.Absyn.Util.fst"
let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _31_114 -> begin
false
end))

# 87 "FStar.Absyn.Util.fst"
let fvar_eq = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))

# 88 "FStar.Absyn.Util.fst"
let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

# 89 "FStar.Absyn.Util.fst"
let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)

# 90 "FStar.Absyn.Util.fst"
let btvar_to_typ : FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.typ = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))

# 91 "FStar.Absyn.Util.fst"
let bvd_to_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

# 92 "FStar.Absyn.Util.fst"
let bvar_to_exp : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.exp = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))

# 93 "FStar.Absyn.Util.fst"
let bvd_to_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

# 94 "FStar.Absyn.Util.fst"
let new_bvd = (fun ropt -> (
# 96 "FStar.Absyn.Util.fst"
let f = (fun ropt -> (
# 96 "FStar.Absyn.Util.fst"
let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

# 97 "FStar.Absyn.Util.fst"
let freshen_bvd = (fun bvd' -> (let _120_86 = (let _120_85 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _120_85))
in (mkbvd _120_86)))

# 98 "FStar.Absyn.Util.fst"
let freshen_bvar = (fun b -> (let _120_88 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_88 b.FStar_Absyn_Syntax.sort)))

# 99 "FStar.Absyn.Util.fst"
let gen_bvar = (fun sort -> (
# 100 "FStar.Absyn.Util.fst"
let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

# 100 "FStar.Absyn.Util.fst"
let gen_bvar_p = (fun r sort -> (
# 101 "FStar.Absyn.Util.fst"
let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

# 101 "FStar.Absyn.Util.fst"
let bvdef_of_str = (fun s -> (
# 103 "FStar.Absyn.Util.fst"
let f = (fun s -> (
# 103 "FStar.Absyn.Util.fst"
let id = (FStar_Ident.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

# 104 "FStar.Absyn.Util.fst"
let set_bvd_range = (fun bvd r -> {FStar_Absyn_Syntax.ppname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, r)); FStar_Absyn_Syntax.realname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText, r))})

# 106 "FStar.Absyn.Util.fst"
let set_lid_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun l r -> (
# 108 "FStar.Absyn.Util.fst"
let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[])) (FStar_List.map (fun i -> (FStar_Ident.mk_ident (i.FStar_Ident.idText, r)))))
in (FStar_Ident.lid_of_ids ids)))

# 109 "FStar.Absyn.Util.fst"
let fv : FStar_Ident.lid  ->  (FStar_Ident.lid, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l -> (withinfo l FStar_Absyn_Syntax.tun (FStar_Ident.range_of_lid l)))

# 110 "FStar.Absyn.Util.fst"
let fvvar_of_lid = (fun l t -> (withinfo l t (FStar_Ident.range_of_lid l)))

# 111 "FStar.Absyn.Util.fst"
let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _120_113 = (let _120_112 = (let _120_111 = (set_lid_range l r)
in (fv _120_111))
in (_120_112, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _120_113 None r)))

# 112 "FStar.Absyn.Util.fst"
let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))

# 113 "FStar.Absyn.Util.fst"
let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_31_160), FStar_Util.Inr (_31_163)) -> begin
(- (1))
end
| (FStar_Util.Inr (_31_167), FStar_Util.Inl (_31_170)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))

# 118 "FStar.Absyn.Util.fst"
let arg_of_non_null_binder = (fun _31_185 -> (match (_31_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _120_122 = (let _120_121 = (btvar_to_typ a)
in FStar_Util.Inl (_120_121))
in (_120_122, imp))
end
| FStar_Util.Inr (x) -> begin
(let _120_124 = (let _120_123 = (bvar_to_exp x)
in FStar_Util.Inr (_120_123))
in (_120_124, imp))
end)
end))

# 121 "FStar.Absyn.Util.fst"
let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _120_128 = (arg_of_non_null_binder b)
in (_120_128)::[])
end))))

# 126 "FStar.Absyn.Util.fst"
let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _120_138 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(
# 130 "FStar.Absyn.Util.fst"
let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _120_133 = (let _120_132 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_120_132))
in (_120_133, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _120_135 = (let _120_134 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_120_134))
in (_120_135, (Prims.snd b)))
end)
in (let _120_136 = (arg_of_non_null_binder b)
in (b, _120_136)))
end else begin
(let _120_137 = (arg_of_non_null_binder b)
in (b, _120_137))
end)))
in (FStar_All.pipe_right _120_138 FStar_List.unzip)))

# 138 "FStar.Absyn.Util.fst"
let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 145 "FStar.Absyn.Util.fst"
let b = (let _120_144 = (let _120_143 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_143))
in (FStar_Ident.id_of_text _120_144))
in (
# 146 "FStar.Absyn.Util.fst"
let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(
# 150 "FStar.Absyn.Util.fst"
let x = (let _120_146 = (let _120_145 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_145))
in (FStar_Ident.id_of_text _120_146))
in (
# 151 "FStar.Absyn.Util.fst"
let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

# 153 "FStar.Absyn.Util.fst"
let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _120_150 = (let _120_149 = (name_binders binders)
in (_120_149, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _120_150 None t.FStar_Absyn_Syntax.pos))
end
| _31_220 -> begin
t
end))

# 157 "FStar.Absyn.Util.fst"
let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _31_2 -> (match (_31_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _120_155 = (let _120_154 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _120_154))
in (_120_155, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _120_157 = (let _120_156 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _120_156))
in (_120_157, imp))
end)))))

# 161 "FStar.Absyn.Util.fst"
let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _31_3 -> (match (_31_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _120_162 = (let _120_161 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_120_161))
in (_120_162, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _120_164 = (let _120_163 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_120_163))
in (_120_164, imp))
end)))))

# 165 "FStar.Absyn.Util.fst"
let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _120_170 = (let _120_167 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _120_167 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _120_169 = (let _120_168 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _120_168 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _120_170 _120_169))))

# 169 "FStar.Absyn.Util.fst"
let subst_to_string = (fun s -> (let _120_173 = (FStar_All.pipe_right s (FStar_List.map (fun _31_4 -> (match (_31_4) with
| FStar_Util.Inl (b, _31_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _31_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _120_173 (FStar_String.concat ", "))))

# 174 "FStar.Absyn.Util.fst"
let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _31_5 -> (match (_31_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _31_262 -> begin
None
end))))

# 177 "FStar.Absyn.Util.fst"
let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _31_6 -> (match (_31_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _31_271 -> begin
None
end))))

# 178 "FStar.Absyn.Util.fst"
let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _31_278 -> begin
(
# 183 "FStar.Absyn.Util.fst"
let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _120_198 = (let _120_197 = (compose_subst s' s)
in (let _120_196 = (FStar_Util.mk_ref None)
in (t', _120_197, _120_196)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _120_198 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 191 "FStar.Absyn.Util.fst"
let t = (mk_t ())
in (
# 192 "FStar.Absyn.Util.fst"
let _31_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(
# 196 "FStar.Absyn.Util.fst"
let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
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
(let _120_203 = (let _120_202 = (FStar_Util.mk_ref None)
in (t0, s, _120_202))
in (FStar_Absyn_Syntax.mk_Typ_delayed _120_203 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _31_323 -> begin
(
# 216 "FStar.Absyn.Util.fst"
let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _120_208 = (let _120_207 = (compose_subst s' s)
in (let _120_206 = (FStar_Util.mk_ref None)
in (e, _120_207, _120_206)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _120_208 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(
# 222 "FStar.Absyn.Util.fst"
let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
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
(let _120_212 = (let _120_211 = (FStar_Util.mk_ref None)
in (e0, s, _120_211))
in (FStar_Absyn_Syntax.mk_Exp_delayed _120_212 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _31_357 -> begin
(
# 241 "FStar.Absyn.Util.fst"
let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _120_217 = (let _120_216 = (compose_subst s' s)
in (let _120_215 = (FStar_Util.mk_ref None)
in (k, _120_216, _120_215)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _120_217 k0.FStar_Absyn_Syntax.pos))
end
| _31_368 -> begin
(let _120_219 = (let _120_218 = (FStar_Util.mk_ref None)
in (k0, s, _120_218))
in (FStar_Absyn_Syntax.mk_Kind_delayed _120_219 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_7 -> (match (_31_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _120_223 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_120_223))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_381 -> begin
(
# 258 "FStar.Absyn.Util.fst"
let _31_382 = t
in (let _120_233 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _120_232 = (FStar_List.map (fun _31_8 -> (match (_31_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_228 = (let _120_227 = (subst_typ' s t)
in FStar_Util.Inl (_120_227))
in (_120_228, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_230 = (let _120_229 = (subst_exp' s e)
in FStar_Util.Inr (_120_229))
in (_120_230, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _120_231 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _31_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _120_233; FStar_Absyn_Syntax.effect_args = _120_232; FStar_Absyn_Syntax.flags = _120_231}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _31_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _120_236 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _120_236))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _120_237 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _120_237))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))

# 270 "FStar.Absyn.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 271 "FStar.Absyn.Util.fst"
let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))

# 272 "FStar.Absyn.Util.fst"
let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))

# 273 "FStar.Absyn.Util.fst"
let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))

# 274 "FStar.Absyn.Util.fst"
let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))

# 275 "FStar.Absyn.Util.fst"
let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))

# 276 "FStar.Absyn.Util.fst"
let subst_binder = (fun s _31_9 -> (match (_31_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _120_265 = (let _120_264 = (
# 278 "FStar.Absyn.Util.fst"
let _31_423 = a
in (let _120_263 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _31_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _120_263; FStar_Absyn_Syntax.p = _31_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_120_264))
in (_120_265, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _120_268 = (let _120_267 = (
# 279 "FStar.Absyn.Util.fst"
let _31_429 = x
in (let _120_266 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _31_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _120_266; FStar_Absyn_Syntax.p = _31_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_120_267))
in (_120_268, imp))
end))

# 279 "FStar.Absyn.Util.fst"
let subst_arg = (fun s _31_10 -> (match (_31_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_272 = (let _120_271 = (subst_typ s t)
in FStar_Util.Inl (_120_271))
in (_120_272, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_274 = (let _120_273 = (subst_exp s e)
in FStar_Util.Inr (_120_273))
in (_120_274, imp))
end))

# 282 "FStar.Absyn.Util.fst"
let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _31_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))

# 285 "FStar.Absyn.Util.fst"
let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _31_450 -> begin
(FStar_List.map (subst_arg s) args)
end))

# 288 "FStar.Absyn.Util.fst"
let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _31_456), (FStar_Util.Inl (t), _31_461)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _31_467), (FStar_Util.Inr (v), _31_472)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _31_476 -> begin
(FStar_All.failwith "Ill-formed substitution")
end))

# 292 "FStar.Absyn.Util.fst"
let mk_subst_one_binder : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.binder  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _120_289 = (let _120_288 = (let _120_287 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _120_287))
in FStar_Util.Inl (_120_288))
in (_120_289)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _120_292 = (let _120_291 = (let _120_290 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _120_290))
in FStar_Util.Inr (_120_291))
in (_120_292)::[])
end
end
| _31_490 -> begin
[]
end)
end)

# 305 "FStar.Absyn.Util.fst"
let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (
# 307 "FStar.Absyn.Util.fst"
let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _120_304 = (let _120_303 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _120_303 out))
in (aux _120_304 bs1 bs2))
end
| _31_508 -> begin
None
end))
in (aux [] bs1 bs2)))

# 312 "FStar.Absyn.Util.fst"
let subst_of_list : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.subst = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 316 "FStar.Absyn.Util.fst"
type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}

# 317 "FStar.Absyn.Util.fst"
let is_Mkred_ctrl : red_ctrl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl"))))

# 320 "FStar.Absyn.Util.fst"
let alpha_ctrl : red_ctrl = {stop_if_empty_subst = false; descend = true}

# 321 "FStar.Absyn.Util.fst"
let subst_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = true}

# 322 "FStar.Absyn.Util.fst"
let null_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = false}

# 323 "FStar.Absyn.Util.fst"
let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))

# 324 "FStar.Absyn.Util.fst"
let map_knd = (fun s vk mt me descend binders k -> (let _120_325 = (subst_kind' s k)
in (_120_325, descend)))

# 327 "FStar.Absyn.Util.fst"
let map_typ = (fun s mk vt me descend binders t -> (let _120_333 = (subst_typ' s t)
in (_120_333, descend)))

# 329 "FStar.Absyn.Util.fst"
let map_exp = (fun s mk me ve descend binders e -> (let _120_341 = (subst_exp' s e)
in (_120_341, descend)))

# 331 "FStar.Absyn.Util.fst"
let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _31_11 -> (match (_31_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _120_358 = (let _120_357 = (map_exp descend binders e)
in (FStar_All.pipe_right _120_357 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_120_358))
end
| f -> begin
f
end)))))

# 335 "FStar.Absyn.Util.fst"
let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 338 "FStar.Absyn.Util.fst"
let _31_557 = (map_typ descend binders t)
in (match (_31_557) with
| (t, descend) -> begin
(let _120_381 = (FStar_Absyn_Syntax.mk_Total t)
in (_120_381, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 341 "FStar.Absyn.Util.fst"
let _31_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_31_562) with
| (t, descend) -> begin
(
# 342 "FStar.Absyn.Util.fst"
let _31_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_31_565) with
| (args, descend) -> begin
(let _120_384 = (let _120_383 = (
# 343 "FStar.Absyn.Util.fst"
let _31_566 = ct
in (let _120_382 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _31_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _120_382}))
in (FStar_Absyn_Syntax.mk_Comp _120_383))
in (_120_384, descend))
end))
end))
end))

# 343 "FStar.Absyn.Util.fst"
let visit_knd = (fun s vk mt me ctrl binders k -> (
# 346 "FStar.Absyn.Util.fst"
let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(
# 348 "FStar.Absyn.Util.fst"
let _31_579 = (vk null_ctrl binders k)
in (match (_31_579) with
| (k, _31_578) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

# 349 "FStar.Absyn.Util.fst"
let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (
# 352 "FStar.Absyn.Util.fst"
let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(
# 355 "FStar.Absyn.Util.fst"
let k' = (let _120_430 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _120_430))
in (
# 356 "FStar.Absyn.Util.fst"
let k' = (compress_kind k')
in (
# 357 "FStar.Absyn.Util.fst"
let _31_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _120_432 = (let _120_431 = (subst_of_list formals actuals)
in (subst_kind _120_431 k'))
in (compress_kind _120_432))
end
| _31_602 -> begin
if ((FStar_List.length actuals) = 0) then begin
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

# 371 "FStar.Absyn.Util.fst"
let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (
# 375 "FStar.Absyn.Util.fst"
let visit_prod = (fun bs tc -> (
# 376 "FStar.Absyn.Util.fst"
let _31_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _31_620 b -> (match (_31_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 378 "FStar.Absyn.Util.fst"
let _31_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_31_629) with
| (k, _31_628) -> begin
(
# 379 "FStar.Absyn.Util.fst"
let a = (
# 379 "FStar.Absyn.Util.fst"
let _31_630 = a
in {FStar_Absyn_Syntax.v = _31_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _31_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(
# 383 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (
# 384 "FStar.Absyn.Util.fst"
let _31_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _31_636 -> begin
(
# 387 "FStar.Absyn.Util.fst"
let b = (let _120_509 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_509 k))
in (
# 388 "FStar.Absyn.Util.fst"
let s = (let _120_512 = (let _120_511 = (let _120_510 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _120_510))
in FStar_Util.Inl (_120_511))
in (extend_subst _120_512 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_31_642) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(
# 393 "FStar.Absyn.Util.fst"
let _31_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_31_650) with
| (t, _31_649) -> begin
(
# 394 "FStar.Absyn.Util.fst"
let x = (
# 394 "FStar.Absyn.Util.fst"
let _31_651 = x
in {FStar_Absyn_Syntax.v = _31_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _31_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(
# 398 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (
# 399 "FStar.Absyn.Util.fst"
let _31_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _31_657 -> begin
(
# 402 "FStar.Absyn.Util.fst"
let y = (let _120_522 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _120_522 t))
in (
# 403 "FStar.Absyn.Util.fst"
let s = (let _120_525 = (let _120_524 = (let _120_523 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _120_523))
in FStar_Util.Inr (_120_524))
in (extend_subst _120_525 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_31_663) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_31_667) with
| (bs, boundvars, s) -> begin
(
# 407 "FStar.Absyn.Util.fst"
let tc = (match ((s, tc)) with
| ([], _31_670) -> begin
tc
end
| (_31_673, FStar_Util.Inl (t)) -> begin
(let _120_536 = (let _120_535 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _120_535))
in FStar_Util.Inl (_120_536))
end
| (_31_678, FStar_Util.Inr (c)) -> begin
(let _120_559 = (let _120_558 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _120_558))
in FStar_Util.Inr (_120_559))
end)
in ((FStar_List.rev bs), tc))
end)))
in (
# 413 "FStar.Absyn.Util.fst"
let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_31_685) -> begin
(let _120_561 = (let _120_560 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _120_560))
in (_120_561, ctrl))
end
| _31_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _120_571 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_120_571, ctrl))
end
| _31_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _31_706)::[], FStar_Util.Inl (t)) -> begin
(let _120_572 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_120_572, ctrl))
end
| _31_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _120_573 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_120_573, ctrl))
end
| _31_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _31_725 -> begin
(
# 437 "FStar.Absyn.Util.fst"
let _31_729 = (vt null_ctrl boundvars t)
in (match (_31_729) with
| (t, _31_728) -> begin
(t, ctrl)
end))
end))))
and compress_typ' : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 440 "FStar.Absyn.Util.fst"
let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(
# 443 "FStar.Absyn.Util.fst"
let res = (let _120_593 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _120_593))
in (
# 444 "FStar.Absyn.Util.fst"
let res = (compress_typ' res)
in (
# 445 "FStar.Absyn.Util.fst"
let _31_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 450 "FStar.Absyn.Util.fst"
let t = (let _120_595 = (mk_t ())
in (compress_typ' _120_595))
in (
# 451 "FStar.Absyn.Util.fst"
let _31_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _31_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 457 "FStar.Absyn.Util.fst"
let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_31_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _31_759 -> begin
t
end)))

# 460 "FStar.Absyn.Util.fst"
let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (
# 463 "FStar.Absyn.Util.fst"
let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_31_769) -> begin
(let _120_661 = (let _120_660 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _120_660))
in (_120_661, ctrl))
end
| _31_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _31_774 -> begin
(
# 467 "FStar.Absyn.Util.fst"
let _31_778 = (ve null_ctrl binders e)
in (match (_31_778) with
| (e, _31_777) -> begin
(e, ctrl)
end))
end)))
and compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (
# 470 "FStar.Absyn.Util.fst"
let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(
# 473 "FStar.Absyn.Util.fst"
let e = (let _120_690 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _120_690))
in (
# 474 "FStar.Absyn.Util.fst"
let res = (compress_exp e)
in (
# 475 "FStar.Absyn.Util.fst"
let _31_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _31_791 -> begin
e
end)))

# 477 "FStar.Absyn.Util.fst"
let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (
# 480 "FStar.Absyn.Util.fst"
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

# 484 "FStar.Absyn.Util.fst"
let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 487 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (
# 488 "FStar.Absyn.Util.fst"
let s = (mk_subst [])
in (
# 489 "FStar.Absyn.Util.fst"
let doit = (fun t -> (let _120_715 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _120_715)))
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

# 494 "FStar.Absyn.Util.fst"
let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _31_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

# 500 "FStar.Absyn.Util.fst"
let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _31_12 -> (match (_31_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _120_722 = (compress_typ t)
in Some (_120_722))
end))

# 504 "FStar.Absyn.Util.fst"
let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _120_727 = (let _120_726 = (let _120_725 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange))
in (_120_725)::[])
in (FStar_List.append lid.FStar_Ident.ns _120_726))
in (FStar_Ident.lid_of_ids _120_727)))

# 507 "FStar.Absyn.Util.fst"
let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (
# 510 "FStar.Absyn.Util.fst"
let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 511 "FStar.Absyn.Util.fst"
let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _120_735 = (let _120_734 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _120_734; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _120_735)))

# 517 "FStar.Absyn.Util.fst"
let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

# 519 "FStar.Absyn.Util.fst"
let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

# 527 "FStar.Absyn.Util.fst"
let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 531 "FStar.Absyn.Util.fst"
let _31_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((
# 531 "FStar.Absyn.Util.fst"
let _31_865 = ct
in {FStar_Absyn_Syntax.effect_name = _31_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _31_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _31_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _31_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _31_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _31_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _31_863.FStar_Absyn_Syntax.uvs})
end))

# 531 "FStar.Absyn.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

# 535 "FStar.Absyn.Util.fst"
let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_31_877) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))

# 539 "FStar.Absyn.Util.fst"
let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))

# 544 "FStar.Absyn.Util.fst"
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_13 -> (match (_31_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_889 -> begin
false
end)))))

# 547 "FStar.Absyn.Util.fst"
let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_14 -> (match (_31_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_895 -> begin
false
end))))))

# 549 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_15 -> (match (_31_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_901 -> begin
false
end))))))

# 553 "FStar.Absyn.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_16 -> (match (_31_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _31_907 -> begin
false
end)))))

# 555 "FStar.Absyn.Util.fst"
let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_17 -> (match (_31_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _31_913 -> begin
false
end)))))

# 557 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

# 561 "FStar.Absyn.Util.fst"
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

# 568 "FStar.Absyn.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

# 573 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 575 "FStar.Absyn.Util.fst"
let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _31_19 -> (match (_31_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _31_931 -> begin
false
end))))))

# 581 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

# 584 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _120_774 = (compress_typ t)
in _120_774.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _31_940 -> begin
true
end))

# 588 "FStar.Absyn.Util.fst"
let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _120_777 = (compress_typ t)
in _120_777.FStar_Absyn_Syntax.n)) with
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

# 594 "FStar.Absyn.Util.fst"
let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _120_780 = (compress_typ t)
in _120_780.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _31_966)::_31_962 -> begin
(match ((let _120_781 = (unmeta_exp pats)
in _120_781.FStar_Absyn_Syntax.n)) with
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

# 609 "FStar.Absyn.Util.fst"
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

# 615 "FStar.Absyn.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
t
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.result_typ
end))

# 619 "FStar.Absyn.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_31_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (
# 623 "FStar.Absyn.Util.fst"
let _31_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _31_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _31_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _31_1020.FStar_Absyn_Syntax.flags}))
end))

# 623 "FStar.Absyn.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _31_21 -> (match (_31_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _31_1027 -> begin
false
end)))))

# 626 "FStar.Absyn.Util.fst"
let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _120_791 = (compress_exp e)
in _120_791.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_1040)) -> begin
(is_atom e)
end
| _31_1045 -> begin
false
end))

# 636 "FStar.Absyn.Util.fst"
let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

# 653 "FStar.Absyn.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _31_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _31_1053 -> begin
false
end))

# 657 "FStar.Absyn.Util.fst"
let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _31_1057, _31_1059) -> begin
(unascribe e)
end
| _31_1063 -> begin
e
end))

# 661 "FStar.Absyn.Util.fst"
let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _31_1068) -> begin
(ascribe_typ t' k)
end
| _31_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

# 665 "FStar.Absyn.Util.fst"
let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1076) -> begin
(unascribe_typ t)
end
| _31_1080 -> begin
t
end))

# 669 "FStar.Absyn.Util.fst"
let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 672 "FStar.Absyn.Util.fst"
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

# 676 "FStar.Absyn.Util.fst"
let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _120_805 = (compress_exp e)
in _120_805.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_31_1097) -> begin
true
end
| _31_1100 -> begin
false
end))

# 680 "FStar.Absyn.Util.fst"
let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _120_808 = (compress_typ t)
in _120_808.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_31_1103) -> begin
true
end
| _31_1106 -> begin
false
end))

# 684 "FStar.Absyn.Util.fst"
let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 687 "FStar.Absyn.Util.fst"
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

# 691 "FStar.Absyn.Util.fst"
let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (
# 694 "FStar.Absyn.Util.fst"
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

# 698 "FStar.Absyn.Util.fst"
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

# 713 "FStar.Absyn.Util.fst"
let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _31_1251 -> begin
None
end))

# 717 "FStar.Absyn.Util.fst"
let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 732 "FStar.Absyn.Util.fst"
let range_of_lb = (fun _31_22 -> (match (_31_22) with
| (FStar_Util.Inl (x), _31_1362, _31_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _31_1369, _31_1371) -> begin
(FStar_Ident.range_of_lid l)
end))

# 736 "FStar.Absyn.Util.fst"
let range_of_arg = (fun _31_23 -> (match (_31_23) with
| (FStar_Util.Inl (hd), _31_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _31_1382) -> begin
hd.FStar_Absyn_Syntax.pos
end))

# 740 "FStar.Absyn.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 743 "FStar.Absyn.Util.fst"
let mk_typ_app : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ = (fun f args -> (
# 746 "FStar.Absyn.Util.fst"
let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

# 747 "FStar.Absyn.Util.fst"
let mk_exp_app : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun f args -> (
# 750 "FStar.Absyn.Util.fst"
let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

# 751 "FStar.Absyn.Util.fst"
let mk_data : FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun l args -> (match (args) with
| [] -> begin
(let _120_841 = (let _120_840 = (let _120_839 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_120_839, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_120_840))
in (FStar_Absyn_Syntax.mk_Exp_meta _120_841))
end
| _31_1398 -> begin
(let _120_845 = (let _120_844 = (let _120_843 = (let _120_842 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _120_842 args))
in (_120_843, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_120_844))
in (FStar_Absyn_Syntax.mk_Exp_meta _120_845))
end))

# 758 "FStar.Absyn.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 760 "FStar.Absyn.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _120_851 = (let _120_850 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_120_850, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _120_851))
end else begin
x
end)

# 764 "FStar.Absyn.Util.fst"
let mk_field_projector_name = (fun lid x i -> (
# 767 "FStar.Absyn.Util.fst"
let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _120_857 = (let _120_856 = (let _120_855 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _120_855))
in (_120_856, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _120_857))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (
# 770 "FStar.Absyn.Util.fst"
let y = (
# 770 "FStar.Absyn.Util.fst"
let _31_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _31_1407.FStar_Absyn_Syntax.realname})
in (let _120_861 = (let _120_860 = (let _120_859 = (let _120_858 = (unmangle_field_name nm)
in (_120_858)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _120_859))
in (FStar_Ident.lid_of_ids _120_860))
in (_120_861, y)))))

# 771 "FStar.Absyn.Util.fst"
let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_31_1413) -> begin
(let _120_866 = (let _120_865 = (let _120_864 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _120_864))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _120_865))
in (FStar_All.failwith _120_866))
end
| _31_1416 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))

# 776 "FStar.Absyn.Util.fst"
type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)

# 782 "FStar.Absyn.Util.fst"
let no_bvars : (FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set) = (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)

# 783 "FStar.Absyn.Util.fst"
let fvs_included : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun fvs1 fvs2 -> ((FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)))

# 786 "FStar.Absyn.Util.fst"
let eq_fvars = (fun v1 v2 -> (match ((v1, v2)) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Syntax.bvd_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _31_1432 -> begin
false
end))

# 791 "FStar.Absyn.Util.fst"
let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _31_1446 -> begin
false
end))

# 796 "FStar.Absyn.Util.fst"
let uv_eq = (fun _31_1450 _31_1454 -> (match ((_31_1450, _31_1454)) with
| ((uv1, _31_1449), (uv2, _31_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

# 798 "FStar.Absyn.Util.fst"
let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _120_883 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _120_882 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _120_881 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _120_883; FStar_Absyn_Syntax.uvars_t = _120_882; FStar_Absyn_Syntax.uvars_e = _120_881}))))

# 803 "FStar.Absyn.Util.fst"
let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _120_889 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _120_888 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _120_889; FStar_Absyn_Syntax.fxvs = _120_888})))

# 809 "FStar.Absyn.Util.fst"
let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _31_1461 _31_1464 -> (match ((_31_1461, _31_1464)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _120_895 = (union_fvs fvs1 fvs2)
in (let _120_894 = (union_uvs uvs1 uvs2)
in (_120_895, _120_894)))
end))

# 813 "FStar.Absyn.Util.fst"
let sub_fv = (fun _31_1467 _31_1470 -> (match ((_31_1467, _31_1470)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _120_900 = (
# 816 "FStar.Absyn.Util.fst"
let _31_1471 = fvs
in (let _120_899 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _120_898 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _120_899; FStar_Absyn_Syntax.fxvs = _120_898})))
in (_120_900, uvs))
end))

# 818 "FStar.Absyn.Util.fst"
let stash = (fun uvonly s _31_1479 -> (match (_31_1479) with
| (fvs, uvs) -> begin
(
# 821 "FStar.Absyn.Util.fst"
let _31_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

# 823 "FStar.Absyn.Util.fst"
let single_fv = (fun x -> (let _120_905 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _120_905)))

# 825 "FStar.Absyn.Util.fst"
let single_uv = (fun u -> (let _120_907 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _120_907)))

# 826 "FStar.Absyn.Util.fst"
let single_uvt = (fun u -> (let _120_909 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _120_909)))

# 827 "FStar.Absyn.Util.fst"
let rec vs_typ' = (fun t uvonly cont -> (
# 830 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_31_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _120_1024 = (let _120_1023 = (
# 836 "FStar.Absyn.Util.fst"
let _31_1495 = FStar_Absyn_Syntax.no_fvs
in (let _120_1022 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _120_1022; FStar_Absyn_Syntax.fxvs = _31_1495.FStar_Absyn_Syntax.fxvs}))
in (_120_1023, FStar_Absyn_Syntax.no_uvs))
in (cont _120_1024))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _120_1027 = (let _120_1026 = (
# 839 "FStar.Absyn.Util.fst"
let _31_1501 = FStar_Absyn_Syntax.no_uvs
in (let _120_1025 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _31_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _120_1025; FStar_Absyn_Syntax.uvars_e = _31_1501.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _120_1026))
in (cont _120_1027))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _31_1513 -> (match (_31_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _120_1031 = (let _120_1030 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1030 bvs))
in (cont _120_1031))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _31_1521 -> (match (_31_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _120_1035 = (let _120_1034 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1034 bvs))
in (cont _120_1035))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _31_1529 -> (match (_31_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _120_1039 = (let _120_1038 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1038 bvs))
in (cont _120_1039))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _120_1042 = (union_fvs_uvs vs1 vs2)
in (cont _120_1042))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _31_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _31_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _120_1045 = (union_fvs_uvs vs1 vs2)
in (cont _120_1045))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _31_1587)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _31_1595 -> (match (_31_1595) with
| ((tvars, vvars), vs2) -> begin
(let _120_1052 = (let _120_1051 = (let _120_1049 = (FStar_Util.set_add a tvars)
in (_120_1049, vvars))
in (let _120_1050 = (union_fvs_uvs vs vs2)
in (_120_1051, _120_1050)))
in (cont _120_1052))
end)))))
end
| (FStar_Util.Inr (x), _31_1600)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _31_1608 -> (match (_31_1608) with
| ((tvars, vvars), vs2) -> begin
(let _120_1058 = (let _120_1057 = (let _120_1055 = (FStar_Util.set_add x vvars)
in (tvars, _120_1055))
in (let _120_1056 = (union_fvs_uvs vs vs2)
in (_120_1057, _120_1056)))
in (cont _120_1058))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _31_1618)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _120_1062 = (union_fvs_uvs ft1 ft2)
in (cont _120_1062))))))
end
| (FStar_Util.Inr (e), _31_1627)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _120_1065 = (union_fvs_uvs ft1 ft2)
in (cont _120_1065))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _120_1068 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _120_1067 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_120_1068, _120_1067)))) with
| (Some (_31_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (
# 911 "FStar.Absyn.Util.fst"
let _31_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (
# 915 "FStar.Absyn.Util.fst"
let _31_1652 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (
# 919 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_31_1665, k) -> begin
(let _120_1073 = (let _120_1072 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _120_1072))
in (FStar_All.failwith _120_1073))
end
| FStar_Absyn_Syntax.Kind_delayed (_31_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _31_1681 -> (match (_31_1681) with
| (fvs, uvs) -> begin
(let _120_1077 = (let _120_1076 = (
# 929 "FStar.Absyn.Util.fst"
let _31_1682 = uvs
in (let _120_1075 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _120_1075; FStar_Absyn_Syntax.uvars_t = _31_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _31_1682.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _120_1076))
in (cont _120_1077))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_31_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _31_1695 -> (match (_31_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _120_1081 = (let _120_1080 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1080 bvs))
in (cont _120_1081))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _120_1084 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _120_1083 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_120_1084, _120_1083)))) with
| (Some (_31_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (
# 943 "FStar.Absyn.Util.fst"
let _31_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (
# 947 "FStar.Absyn.Util.fst"
let _31_1717 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (
# 951 "FStar.Absyn.Util.fst"
let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_31_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _120_1090 = (let _120_1089 = (
# 957 "FStar.Absyn.Util.fst"
let _31_1742 = FStar_Absyn_Syntax.no_uvs
in (let _120_1088 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _31_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _31_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _120_1088}))
in (FStar_Absyn_Syntax.no_fvs, _120_1089))
in (cont _120_1090))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _120_1093 = (let _120_1092 = (
# 962 "FStar.Absyn.Util.fst"
let _31_1746 = FStar_Absyn_Syntax.no_fvs
in (let _120_1091 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _31_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _120_1091}))
in (_120_1092, FStar_Absyn_Syntax.no_uvs))
in (cont _120_1093))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _31_1750, _31_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _31_1761 -> (match (_31_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _120_1097 = (let _120_1096 = (union_fvs_uvs vs1 vs2)
in (sub_fv _120_1096 bvs))
in (cont _120_1097))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _120_1100 = (union_fvs_uvs ft1 ft2)
in (cont _120_1100))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _31_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _120_1103 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _120_1102 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_120_1103, _120_1102)))) with
| (Some (_31_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (
# 986 "FStar.Absyn.Util.fst"
let _31_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (
# 990 "FStar.Absyn.Util.fst"
let _31_1801 = (stash uvonly e fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_comp' = (fun c uvonly k -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(vs_typ t uvonly k)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
if uvonly then begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly k)
end else begin
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _120_1109 = (union_fvs_uvs vs1 vs2)
in (k _120_1109))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _120_1112 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _120_1111 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_120_1112, _120_1111)))) with
| (Some (_31_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (
# 1007 "FStar.Absyn.Util.fst"
let _31_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (
# 1011 "FStar.Absyn.Util.fst"
let _31_1838 = (stash uvonly c fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
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
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| hd::tl -> begin
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _120_1119 = (union_fvs_uvs ft1 ft2)
in (cont _120_1119))))))
end))

# 1025 "FStar.Absyn.Util.fst"
let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _31_1867 -> (match (_31_1867) with
| (x, _31_1866) -> begin
x
end))))

# 1028 "FStar.Absyn.Util.fst"
let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _31_1872 -> (match (_31_1872) with
| (x, _31_1871) -> begin
x
end))))

# 1031 "FStar.Absyn.Util.fst"
let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _31_1877 -> (match (_31_1877) with
| (x, _31_1876) -> begin
x
end))))

# 1034 "FStar.Absyn.Util.fst"
let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _31_1882 -> (match (_31_1882) with
| (x, _31_1881) -> begin
x
end))))

# 1037 "FStar.Absyn.Util.fst"
let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _120_1135 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _120_1135))
end
| FStar_Util.Inr (e) -> begin
(let _120_1136 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _120_1136))
end)) FStar_Absyn_Syntax.no_fvs)))

# 1042 "FStar.Absyn.Util.fst"
let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _31_24 -> (match (_31_24) with
| FStar_Util.Inl (a) -> begin
(FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)
end
| FStar_Util.Inr (x) -> begin
(FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)
end)))))

# 1047 "FStar.Absyn.Util.fst"
type syntax_sum =
| SynSumKind of FStar_Absyn_Syntax.knd
| SynSumType of FStar_Absyn_Syntax.typ
| SynSumExp of FStar_Absyn_Syntax.exp
| SynSumComp of (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax

# 1050 "FStar.Absyn.Util.fst"
let is_SynSumKind = (fun _discr_ -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))

# 1051 "FStar.Absyn.Util.fst"
let is_SynSumType = (fun _discr_ -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))

# 1052 "FStar.Absyn.Util.fst"
let is_SynSumExp = (fun _discr_ -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))

# 1053 "FStar.Absyn.Util.fst"
let is_SynSumComp = (fun _discr_ -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))

# 1050 "FStar.Absyn.Util.fst"
let ___SynSumKind____0 = (fun projectee -> (match (projectee) with
| SynSumKind (_31_1899) -> begin
_31_1899
end))

# 1051 "FStar.Absyn.Util.fst"
let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_31_1902) -> begin
_31_1902
end))

# 1052 "FStar.Absyn.Util.fst"
let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_31_1905) -> begin
_31_1905
end))

# 1053 "FStar.Absyn.Util.fst"
let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_31_1908) -> begin
_31_1908
end))

# 1053 "FStar.Absyn.Util.fst"
let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (
# 1056 "FStar.Absyn.Util.fst"
let out = (let _120_1210 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _120_1210 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _120_1208 = (uvars_in_kind k)
in (union_uvs _120_1208 out))
end
| _31_1916 -> begin
(
# 1059 "FStar.Absyn.Util.fst"
let _31_1917 = out
in (let _120_1209 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _120_1209; FStar_Absyn_Syntax.uvars_t = _31_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _31_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (
# 1060 "FStar.Absyn.Util.fst"
let out = (let _120_1215 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _120_1215 (FStar_List.fold_left (fun out _31_1923 -> (match (_31_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _120_1213 = (uvars_in_typ t)
in (union_uvs _120_1213 out))
end
| _31_1927 -> begin
(
# 1063 "FStar.Absyn.Util.fst"
let _31_1928 = out
in (let _120_1214 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _31_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _120_1214; FStar_Absyn_Syntax.uvars_e = _31_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (
# 1064 "FStar.Absyn.Util.fst"
let out = (let _120_1220 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _120_1220 (FStar_List.fold_left (fun out _31_1934 -> (match (_31_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _120_1218 = (uvars_in_exp e)
in (union_uvs _120_1218 out))
end
| _31_1938 -> begin
(
# 1067 "FStar.Absyn.Util.fst"
let _31_1939 = out
in (let _120_1219 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _31_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _31_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _120_1219}))
end)
end)) out)))
in (
# 1068 "FStar.Absyn.Util.fst"
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _120_1223 = (vs_kind k true (fun _31_1956 -> (match (_31_1956) with
| (_31_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _120_1223)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _120_1226 = (vs_typ t true (fun _31_1961 -> (match (_31_1961) with
| (_31_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _120_1226)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _120_1229 = (vs_exp e true (fun _31_1966 -> (match (_31_1966) with
| (_31_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _120_1229)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _120_1232 = (vs_comp c true (fun _31_1971 -> (match (_31_1971) with
| (_31_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _120_1232)))

# 1085 "FStar.Absyn.Util.fst"
let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

# 1090 "FStar.Absyn.Util.fst"
let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (
# 1096 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_31_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 1104 "FStar.Absyn.Util.fst"
let _31_1991 = (kind_formals k)
in (match (_31_1991) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_31_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_31_1998) -> begin
(FStar_All.failwith "Impossible")
end)))

# 1107 "FStar.Absyn.Util.fst"
let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (
# 1110 "FStar.Absyn.Util.fst"
let _31_2005 = (kind_formals k)
in (match (_31_2005) with
| (bs, _31_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _31_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

# 1113 "FStar.Absyn.Util.fst"
let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (
# 1116 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_31_2012, k) -> begin
(unabbreviate_kind k)
end
| _31_2017 -> begin
k
end)))

# 1119 "FStar.Absyn.Util.fst"
let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _31_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

# 1124 "FStar.Absyn.Util.fst"
let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _31_2027 -> begin
(
# 1130 "FStar.Absyn.Util.fst"
let _31_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _31_2033 -> begin
(let _120_1253 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _120_1253))
end)
in (match (_31_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

# 1133 "FStar.Absyn.Util.fst"
let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow

# 1135 "FStar.Absyn.Util.fst"
let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _31_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

# 1139 "FStar.Absyn.Util.fst"
let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _31_2046 -> begin
false
end))

# 1147 "FStar.Absyn.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1150 "FStar.Absyn.Util.fst"
let t = (let _120_1266 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _120_1266))
in (let _120_1267 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1267 r))))

# 1151 "FStar.Absyn.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1154 "FStar.Absyn.Util.fst"
let t = (let _120_1272 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _120_1272))
in (let _120_1273 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1273 r))))

# 1155 "FStar.Absyn.Util.fst"
let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _120_1278 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _120_1278)))

# 1158 "FStar.Absyn.Util.fst"
let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _31_2059 -> begin
false
end))

# 1162 "FStar.Absyn.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1165 "FStar.Absyn.Util.fst"
let t = (let _120_1285 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _120_1285))
in (let _120_1286 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1286 r))))

# 1166 "FStar.Absyn.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1169 "FStar.Absyn.Util.fst"
let t = (let _120_1291 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _120_1291))
in (let _120_1292 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _120_1292 r))))

# 1170 "FStar.Absyn.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))

# 1177 "FStar.Absyn.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

# 1179 "FStar.Absyn.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

# 1180 "FStar.Absyn.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 1181 "FStar.Absyn.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

# 1182 "FStar.Absyn.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 1185 "FStar.Absyn.Util.fst"
let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 1187 "FStar.Absyn.Util.fst"
let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _120_1308 = (pre_typ t)
in _120_1308.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _31_2078 -> begin
false
end))

# 1192 "FStar.Absyn.Util.fst"
let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _120_1313 = (pre_typ t)
in _120_1313.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_31_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _31_2086) -> begin
(is_constructed_typ t lid)
end
| _31_2090 -> begin
false
end))

# 1197 "FStar.Absyn.Util.fst"
let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (
# 1200 "FStar.Absyn.Util.fst"
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

# 1205 "FStar.Absyn.Util.fst"
let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _31_25 -> (match (_31_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _31_2109 -> begin
false
end))

# 1209 "FStar.Absyn.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _31_2115 _31_2119 -> (match ((_31_2115, _31_2119)) with
| ((fn1, _31_2114), (fn2, _31_2118)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 1216 "FStar.Absyn.Util.fst"
let kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1219 "FStar.Absyn.Util.fst"
let kt_kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1220 "FStar.Absyn.Util.fst"
let tand : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.and_lid kt_kt_kt)

# 1222 "FStar.Absyn.Util.fst"
let tor : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.or_lid kt_kt_kt)

# 1223 "FStar.Absyn.Util.fst"
let timp : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.imp_lid kt_kt_kt)

# 1224 "FStar.Absyn.Util.fst"
let tiff : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.iff_lid kt_kt_kt)

# 1225 "FStar.Absyn.Util.fst"
let t_bool : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)

# 1226 "FStar.Absyn.Util.fst"
let t_false : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)

# 1227 "FStar.Absyn.Util.fst"
let t_true : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)

# 1228 "FStar.Absyn.Util.fst"
let b2t_v : FStar_Absyn_Syntax.typ = (let _120_1324 = (let _120_1323 = (let _120_1322 = (let _120_1321 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_120_1321)::[])
in (_120_1322, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1323 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _120_1324))

# 1229 "FStar.Absyn.Util.fst"
let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _120_1335 = (let _120_1334 = (let _120_1332 = (let _120_1331 = (FStar_Absyn_Syntax.targ phi1)
in (let _120_1330 = (let _120_1329 = (FStar_Absyn_Syntax.targ phi2)
in (_120_1329)::[])
in (_120_1331)::_120_1330))
in (tand, _120_1332))
in (let _120_1333 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _120_1334 None _120_1333)))
in Some (_120_1335))
end))

# 1233 "FStar.Absyn.Util.fst"
let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _120_1347 = (let _120_1345 = (let _120_1344 = (FStar_Absyn_Syntax.targ phi1)
in (let _120_1343 = (let _120_1342 = (FStar_Absyn_Syntax.targ phi2)
in (_120_1342)::[])
in (_120_1344)::_120_1343))
in (op_t, _120_1345))
in (let _120_1346 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _120_1347 None _120_1346))))

# 1234 "FStar.Absyn.Util.fst"
let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _120_1353 = (let _120_1352 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _120_1351 = (let _120_1350 = (FStar_Absyn_Syntax.targ phi)
in (_120_1350)::[])
in (_120_1352, _120_1351)))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1353 None phi.FStar_Absyn_Syntax.pos)))

# 1235 "FStar.Absyn.Util.fst"
let mk_conj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 1236 "FStar.Absyn.Util.fst"
let mk_conj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 1239 "FStar.Absyn.Util.fst"
let mk_disj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 1240 "FStar.Absyn.Util.fst"
let mk_disj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 1243 "FStar.Absyn.Util.fst"
let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _120_1370 = (compress_typ phi1)
in _120_1370.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _31_2150 -> begin
(match ((let _120_1371 = (compress_typ phi2)
in _120_1371.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _31_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 1253 "FStar.Absyn.Util.fst"
let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 1254 "FStar.Absyn.Util.fst"
let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _120_1380 = (let _120_1379 = (let _120_1378 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_120_1378)::[])
in (b2t_v, _120_1379))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1380 None e.FStar_Absyn_Syntax.pos)))

# 1255 "FStar.Absyn.Util.fst"
let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (
# 1258 "FStar.Absyn.Util.fst"
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

# 1266 "FStar.Absyn.Util.fst"
let eq_k : FStar_Absyn_Syntax.knd = (
# 1270 "FStar.Absyn.Util.fst"
let a = (let _120_1383 = (new_bvd None)
in (bvd_to_bvar_s _120_1383 FStar_Absyn_Syntax.ktype))
in (
# 1271 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (
# 1272 "FStar.Absyn.Util.fst"
let b = (let _120_1384 = (new_bvd None)
in (bvd_to_bvar_s _120_1384 FStar_Absyn_Syntax.ktype))
in (
# 1273 "FStar.Absyn.Util.fst"
let btyp = (btvar_to_typ b)
in (let _120_1391 = (let _120_1390 = (let _120_1389 = (let _120_1388 = (let _120_1387 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _120_1386 = (let _120_1385 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_120_1385)::[])
in (_120_1387)::_120_1386))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit (false))))::_120_1388)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_120_1389)
in (_120_1390, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1391 FStar_Absyn_Syntax.dummyRange))))))

# 1275 "FStar.Absyn.Util.fst"
let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)

# 1277 "FStar.Absyn.Util.fst"
let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _31_2217 -> begin
(let _120_1409 = (let _120_1407 = (let _120_1406 = (FStar_Absyn_Syntax.itarg t1)
in (let _120_1405 = (let _120_1404 = (FStar_Absyn_Syntax.itarg t2)
in (let _120_1403 = (let _120_1402 = (FStar_Absyn_Syntax.varg e1)
in (let _120_1401 = (let _120_1400 = (FStar_Absyn_Syntax.varg e2)
in (_120_1400)::[])
in (_120_1402)::_120_1401))
in (_120_1404)::_120_1403))
in (_120_1406)::_120_1405))
in (teq, _120_1407))
in (let _120_1408 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _120_1409 None _120_1408)))
end))

# 1281 "FStar.Absyn.Util.fst"
let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

# 1282 "FStar.Absyn.Util.fst"
let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _120_1419 = (let _120_1417 = (let _120_1416 = (FStar_Absyn_Syntax.targ t1)
in (let _120_1415 = (let _120_1414 = (FStar_Absyn_Syntax.targ t2)
in (_120_1414)::[])
in (_120_1416)::_120_1415))
in (eq_typ, _120_1417))
in (let _120_1418 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _120_1419 None _120_1418))))

# 1283 "FStar.Absyn.Util.fst"
let lex_t : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

# 1285 "FStar.Absyn.Util.fst"
let lex_top : FStar_Absyn_Syntax.exp = (
# 1287 "FStar.Absyn.Util.fst"
let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

# 1288 "FStar.Absyn.Util.fst"
let lex_pair : FStar_Absyn_Syntax.exp = (
# 1291 "FStar.Absyn.Util.fst"
let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (
# 1292 "FStar.Absyn.Util.fst"
let lexcons = (let _120_1429 = (let _120_1428 = (let _120_1427 = (let _120_1425 = (FStar_Absyn_Syntax.t_binder a)
in (let _120_1424 = (let _120_1423 = (let _120_1420 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _120_1420))
in (let _120_1422 = (let _120_1421 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_120_1421)::[])
in (_120_1423)::_120_1422))
in (_120_1425)::_120_1424))
in (let _120_1426 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_120_1427, _120_1426)))
in (FStar_Absyn_Syntax.mk_Typ_fun _120_1428 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _120_1429 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

# 1293 "FStar.Absyn.Util.fst"
let forall_kind : FStar_Absyn_Syntax.knd = (
# 1296 "FStar.Absyn.Util.fst"
let a = (let _120_1430 = (new_bvd None)
in (bvd_to_bvar_s _120_1430 FStar_Absyn_Syntax.ktype))
in (
# 1297 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (let _120_1438 = (let _120_1437 = (let _120_1436 = (let _120_1435 = (let _120_1434 = (let _120_1433 = (let _120_1432 = (let _120_1431 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_120_1431)::[])
in (_120_1432, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1433 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _120_1434))
in (_120_1435)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_120_1436)
in (_120_1437, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1438 FStar_Absyn_Syntax.dummyRange))))

# 1301 "FStar.Absyn.Util.fst"
let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)

# 1302 "FStar.Absyn.Util.fst"
let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _120_1447 = (let _120_1446 = (let _120_1445 = (let _120_1444 = (let _120_1443 = (let _120_1442 = (let _120_1441 = (FStar_Absyn_Syntax.null_t_binder k)
in (_120_1441)::[])
in (_120_1442, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1443 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _120_1444))
in (_120_1445)::[])
in (_120_1446, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1447 FStar_Absyn_Syntax.dummyRange)))

# 1304 "FStar.Absyn.Util.fst"
let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _120_1454 = (let _120_1453 = (let _120_1452 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _120_1451 = (let _120_1450 = (FStar_Absyn_Syntax.null_t_binder k)
in (_120_1450)::[])
in (_120_1452)::_120_1451))
in (_120_1453, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _120_1454 FStar_Absyn_Syntax.dummyRange)))

# 1305 "FStar.Absyn.Util.fst"
let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _120_1457 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _120_1457)))

# 1307 "FStar.Absyn.Util.fst"
let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _120_1469 = (let _120_1468 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _120_1467 = (let _120_1466 = (let _120_1465 = (let _120_1464 = (let _120_1463 = (let _120_1462 = (FStar_Absyn_Syntax.t_binder a)
in (_120_1462)::[])
in (_120_1463, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _120_1464 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _120_1465))
in (_120_1466)::[])
in (_120_1468, _120_1467)))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1469 None b.FStar_Absyn_Syntax.pos)))

# 1310 "FStar.Absyn.Util.fst"
let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (
# 1313 "FStar.Absyn.Util.fst"
let r = FStar_Absyn_Syntax.dummyRange
in (let _120_1480 = (let _120_1479 = (let _120_1478 = (let _120_1477 = (let _120_1476 = (let _120_1475 = (let _120_1474 = (FStar_Absyn_Syntax.v_binder x)
in (_120_1474)::[])
in (_120_1475, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _120_1476 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _120_1477))
in (_120_1478)::[])
in (tforall, _120_1479))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1480 None r))))

# 1314 "FStar.Absyn.Util.fst"
let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(
# 1320 "FStar.Absyn.Util.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _120_1490 = (let _120_1489 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _120_1488 = (let _120_1487 = (FStar_Absyn_Syntax.targ body)
in (_120_1487)::[])
in (_120_1489, _120_1488)))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1490 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _120_1494 = (let _120_1493 = (let _120_1492 = (let _120_1491 = (FStar_Absyn_Syntax.targ body)
in (_120_1491)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit (false))))::_120_1492)
in (tforall, _120_1493))
in (FStar_Absyn_Syntax.mk_Typ_app _120_1494 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))

# 1323 "FStar.Absyn.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_31_2244) -> begin
true
end
| _31_2247 -> begin
false
end))

# 1328 "FStar.Absyn.Util.fst"
let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (
# 1331 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _31_2255 -> begin
(t, [])
end)))

# 1334 "FStar.Absyn.Util.fst"
let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (
# 1337 "FStar.Absyn.Util.fst"
let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _31_2263 -> begin
(e, [])
end)))

# 1340 "FStar.Absyn.Util.fst"
let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (
# 1343 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _31_2271 -> begin
None
end)))

# 1346 "FStar.Absyn.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 1349 "FStar.Absyn.Util.fst"
let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 1365 "FStar.Absyn.Util.fst"
type qpats =
FStar_Absyn_Syntax.args Prims.list

# 1370 "FStar.Absyn.Util.fst"
type connective =
| QAll of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| QEx of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Absyn_Syntax.args)

# 1372 "FStar.Absyn.Util.fst"
let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 1373 "FStar.Absyn.Util.fst"
let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 1374 "FStar.Absyn.Util.fst"
let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 1372 "FStar.Absyn.Util.fst"
let ___QAll____0 = (fun projectee -> (match (projectee) with
| QAll (_31_2276) -> begin
_31_2276
end))

# 1373 "FStar.Absyn.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_31_2279) -> begin
_31_2279
end))

# 1374 "FStar.Absyn.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_31_2282) -> begin
_31_2282
end))

# 1374 "FStar.Absyn.Util.fst"
let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (
# 1377 "FStar.Absyn.Util.fst"
let destruct_base_conn = (fun f -> (
# 1378 "FStar.Absyn.Util.fst"
let _31_2288 = (true, false)
in (match (_31_2288) with
| (type_sort, term_sort) -> begin
(
# 1379 "FStar.Absyn.Util.fst"
let oneType = (type_sort)::[]
in (
# 1380 "FStar.Absyn.Util.fst"
let twoTypes = (type_sort)::(type_sort)::[]
in (
# 1381 "FStar.Absyn.Util.fst"
let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (
# 1382 "FStar.Absyn.Util.fst"
let twoTerms = (term_sort)::(term_sort)::[]
in (
# 1383 "FStar.Absyn.Util.fst"
let connectives = ((FStar_Absyn_Const.true_lid, []))::((FStar_Absyn_Const.false_lid, []))::((FStar_Absyn_Const.and_lid, twoTypes))::((FStar_Absyn_Const.or_lid, twoTypes))::((FStar_Absyn_Const.imp_lid, twoTypes))::((FStar_Absyn_Const.iff_lid, twoTypes))::((FStar_Absyn_Const.ite_lid, threeTys))::((FStar_Absyn_Const.not_lid, oneType))::((FStar_Absyn_Const.eqT_lid, twoTypes))::((FStar_Absyn_Const.eq2_lid, twoTerms))::((FStar_Absyn_Const.eq2_lid, (FStar_List.append twoTypes twoTerms)))::[]
in (
# 1395 "FStar.Absyn.Util.fst"
let rec aux = (fun f _31_2298 -> (match (_31_2298) with
| (lid, arity) -> begin
(
# 1396 "FStar.Absyn.Util.fst"
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
Some (BaseConn ((lid, args)))
end else begin
None
end
end))
end))
in (FStar_Util.find_map connectives (aux f))))))))
end)))
in (
# 1406 "FStar.Absyn.Util.fst"
let patterns = (fun t -> (
# 1407 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, pats)) -> begin
(let _120_1558 = (compress_typ t)
in (pats, _120_1558))
end
| _31_2325 -> begin
(let _120_1559 = (compress_typ t)
in ([], _120_1559))
end)))
in (
# 1412 "FStar.Absyn.Util.fst"
let destruct_q_conn = (fun t -> (
# 1413 "FStar.Absyn.Util.fst"
let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (
# 1414 "FStar.Absyn.Util.fst"
let flat = (fun t -> (
# 1415 "FStar.Absyn.Util.fst"
let _31_2335 = (head_and_args t)
in (match (_31_2335) with
| (t, args) -> begin
(let _120_1573 = (FStar_All.pipe_right args (FStar_List.map (fun _31_26 -> (match (_31_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _120_1570 = (let _120_1569 = (compress_typ t)
in FStar_Util.Inl (_120_1569))
in (_120_1570, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _120_1572 = (let _120_1571 = (compress_exp e)
in FStar_Util.Inr (_120_1571))
in (_120_1572, imp))
end))))
in (t, _120_1573))
end)))
in (
# 1418 "FStar.Absyn.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _120_1580 = (flat t)
in (qopt, _120_1580))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _31_2483) -> begin
(
# 1430 "FStar.Absyn.Util.fst"
let _31_2487 = (patterns t)
in (match (_31_2487) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _31_2491) -> begin
(
# 1434 "FStar.Absyn.Util.fst"
let _31_2495 = (patterns t)
in (match (_31_2495) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _31_2497 -> begin
None
end))
in (aux None [] t)))))
in (
# 1440 "FStar.Absyn.Util.fst"
let phi = (compress_typ f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))





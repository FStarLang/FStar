
open Prims
# 28 "FStar.Absyn.Util.fst"
let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(let _112_7 = (FStar_Util.format1 "Fatal: %s" s)
in (FStar_Util.print_string _112_7))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(
# 33 "FStar.Absyn.Util.fst"
let _27_36 = (let _112_9 = (let _112_8 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _112_8 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _112_9))
in ())
end
| FStar_Util.NYI (s) -> begin
(
# 36 "FStar.Absyn.Util.fst"
let _27_40 = (let _112_10 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _112_10))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _112_11 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _112_11))
end
| _27_45 -> begin
(Prims.raise e)
end))

# 42 "FStar.Absyn.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _27_1 -> (match (_27_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _27_60 -> begin
false
end))

# 53 "FStar.Absyn.Util.fst"
type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

# 53 "FStar.Absyn.Util.fst"
let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

# 57 "FStar.Absyn.Util.fst"
let gs : gensym_t = (
# 58 "FStar.Absyn.Util.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 59 "FStar.Absyn.Util.fst"
let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _27_66 -> (match (()) with
| () -> begin
(let _112_39 = (let _112_36 = (let _112_35 = (let _112_34 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _112_34))
in (Prims.strcat "_" _112_35))
in (Prims.strcat _112_36 "_"))
in (let _112_38 = (let _112_37 = (
# 60 "FStar.Absyn.Util.fst"
let _27_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _112_37))
in (Prims.strcat _112_39 _112_38)))
end)); reset = (fun _27_69 -> (match (()) with
| () -> begin
(
# 61 "FStar.Absyn.Util.fst"
let _27_70 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

# 62 "FStar.Absyn.Util.fst"
let gensym : Prims.unit  ->  Prims.string = (fun _27_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

# 63 "FStar.Absyn.Util.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (fun _27_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))

# 64 "FStar.Absyn.Util.fst"
let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _112_48 = (gensym ())
in (let _112_47 = (gensyms (n - 1))
in (_112_48)::_112_47))
end))

# 68 "FStar.Absyn.Util.fst"
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

# 74 "FStar.Absyn.Util.fst"
let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Ident.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Ident.idText))

# 75 "FStar.Absyn.Util.fst"
let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange)

# 76 "FStar.Absyn.Util.fst"
let mkbvd = (fun _27_87 -> (match (_27_87) with
| (x, y) -> begin
{FStar_Absyn_Syntax.ppname = x; FStar_Absyn_Syntax.realname = y}
end))

# 78 "FStar.Absyn.Util.fst"
let setsort = (fun w t -> {FStar_Absyn_Syntax.v = w.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = w.FStar_Absyn_Syntax.p})

# 79 "FStar.Absyn.Util.fst"
let withinfo = (fun e s r -> {FStar_Absyn_Syntax.v = e; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = r})

# 80 "FStar.Absyn.Util.fst"
let withsort = (fun e s -> (withinfo e s FStar_Absyn_Syntax.dummyRange))

# 81 "FStar.Absyn.Util.fst"
let bvar_ppname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)

# 82 "FStar.Absyn.Util.fst"
let bvar_realname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname)

# 83 "FStar.Absyn.Util.fst"
let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.FStar_Absyn_Syntax.v bv2.FStar_Absyn_Syntax.v))

# 84 "FStar.Absyn.Util.fst"
let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _27_114 -> begin
false
end))

# 88 "FStar.Absyn.Util.fst"
let fvar_eq = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))

# 89 "FStar.Absyn.Util.fst"
let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

# 90 "FStar.Absyn.Util.fst"
let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)

# 91 "FStar.Absyn.Util.fst"
let btvar_to_typ : FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.typ = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))

# 92 "FStar.Absyn.Util.fst"
let bvd_to_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

# 93 "FStar.Absyn.Util.fst"
let bvar_to_exp : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.exp = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))

# 94 "FStar.Absyn.Util.fst"
let bvd_to_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

# 95 "FStar.Absyn.Util.fst"
let new_bvd = (fun ropt -> (
# 96 "FStar.Absyn.Util.fst"
let f = (fun ropt -> (
# 96 "FStar.Absyn.Util.fst"
let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

# 98 "FStar.Absyn.Util.fst"
let freshen_bvd = (fun bvd' -> (let _112_89 = (let _112_88 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _112_88))
in (mkbvd _112_89)))

# 99 "FStar.Absyn.Util.fst"
let freshen_bvar = (fun b -> (let _112_91 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _112_91 b.FStar_Absyn_Syntax.sort)))

# 100 "FStar.Absyn.Util.fst"
let gen_bvar = (fun sort -> (
# 100 "FStar.Absyn.Util.fst"
let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

# 101 "FStar.Absyn.Util.fst"
let gen_bvar_p = (fun r sort -> (
# 101 "FStar.Absyn.Util.fst"
let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

# 102 "FStar.Absyn.Util.fst"
let bvdef_of_str = (fun s -> (
# 103 "FStar.Absyn.Util.fst"
let f = (fun s -> (
# 103 "FStar.Absyn.Util.fst"
let id = (FStar_Ident.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

# 105 "FStar.Absyn.Util.fst"
let set_bvd_range = (fun bvd r -> {FStar_Absyn_Syntax.ppname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, r)); FStar_Absyn_Syntax.realname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText, r))})

# 107 "FStar.Absyn.Util.fst"
let set_lid_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun l r -> (
# 108 "FStar.Absyn.Util.fst"
let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[])) (FStar_List.map (fun i -> (FStar_Ident.mk_ident (i.FStar_Ident.idText, r)))))
in (FStar_Ident.lid_of_ids ids)))

# 110 "FStar.Absyn.Util.fst"
let fv : FStar_Ident.lid  ->  (FStar_Ident.lid, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t = (fun l -> (withinfo l FStar_Absyn_Syntax.tun (FStar_Ident.range_of_lid l)))

# 111 "FStar.Absyn.Util.fst"
let fvvar_of_lid = (fun l t -> (withinfo l t (FStar_Ident.range_of_lid l)))

# 112 "FStar.Absyn.Util.fst"
let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _112_116 = (let _112_115 = (let _112_114 = (set_lid_range l r)
in (fv _112_114))
in (_112_115, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _112_116 None r)))

# 113 "FStar.Absyn.Util.fst"
let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))

# 114 "FStar.Absyn.Util.fst"
let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_27_160), FStar_Util.Inr (_27_163)) -> begin
(- (1))
end
| (FStar_Util.Inr (_27_167), FStar_Util.Inl (_27_170)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))

# 119 "FStar.Absyn.Util.fst"
let arg_of_non_null_binder = (fun _27_185 -> (match (_27_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _112_125 = (let _112_124 = (btvar_to_typ a)
in FStar_Util.Inl (_112_124))
in (_112_125, imp))
end
| FStar_Util.Inr (x) -> begin
(let _112_127 = (let _112_126 = (bvar_to_exp x)
in FStar_Util.Inr (_112_126))
in (_112_127, imp))
end)
end))

# 123 "FStar.Absyn.Util.fst"
let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _112_131 = (arg_of_non_null_binder b)
in (_112_131)::[])
end))))

# 127 "FStar.Absyn.Util.fst"
let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _112_141 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(
# 130 "FStar.Absyn.Util.fst"
let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _112_136 = (let _112_135 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_112_135))
in (_112_136, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _112_138 = (let _112_137 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_112_137))
in (_112_138, (Prims.snd b)))
end)
in (let _112_139 = (arg_of_non_null_binder b)
in (b, _112_139)))
end else begin
(let _112_140 = (arg_of_non_null_binder b)
in (b, _112_140))
end)))
in (FStar_All.pipe_right _112_141 FStar_List.unzip)))

# 140 "FStar.Absyn.Util.fst"
let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 145 "FStar.Absyn.Util.fst"
let b = (let _112_147 = (let _112_146 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _112_146))
in (FStar_Ident.id_of_text _112_147))
in (
# 146 "FStar.Absyn.Util.fst"
let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(
# 150 "FStar.Absyn.Util.fst"
let x = (let _112_149 = (let _112_148 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _112_148))
in (FStar_Ident.id_of_text _112_149))
in (
# 151 "FStar.Absyn.Util.fst"
let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

# 155 "FStar.Absyn.Util.fst"
let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _112_153 = (let _112_152 = (name_binders binders)
in (_112_152, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _112_153 None t.FStar_Absyn_Syntax.pos))
end
| _27_220 -> begin
t
end))

# 158 "FStar.Absyn.Util.fst"
let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _27_2 -> (match (_27_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _112_158 = (let _112_157 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _112_157))
in (_112_158, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _112_160 = (let _112_159 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _112_159))
in (_112_160, imp))
end)))))

# 162 "FStar.Absyn.Util.fst"
let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _27_3 -> (match (_27_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _112_165 = (let _112_164 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_112_164))
in (_112_165, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _112_167 = (let _112_166 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_112_166))
in (_112_167, imp))
end)))))

# 167 "FStar.Absyn.Util.fst"
let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _112_173 = (let _112_170 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _112_170 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _112_172 = (let _112_171 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _112_171 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _112_173 _112_172))))

# 174 "FStar.Absyn.Util.fst"
let subst_to_string = (fun s -> (let _112_176 = (FStar_All.pipe_right s (FStar_List.map (fun _27_4 -> (match (_27_4) with
| FStar_Util.Inl (b, _27_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _27_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _112_176 (FStar_String.concat ", "))))

# 177 "FStar.Absyn.Util.fst"
let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _27_5 -> (match (_27_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _27_262 -> begin
None
end))))

# 178 "FStar.Absyn.Util.fst"
let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _27_6 -> (match (_27_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _27_271 -> begin
None
end))))

# 179 "FStar.Absyn.Util.fst"
let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _27_278 -> begin
(
# 183 "FStar.Absyn.Util.fst"
let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _112_201 = (let _112_200 = (compose_subst s' s)
in (let _112_199 = (FStar_Util.mk_ref None)
in (t', _112_200, _112_199)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _112_201 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 191 "FStar.Absyn.Util.fst"
let t = (mk_t ())
in (
# 192 "FStar.Absyn.Util.fst"
let _27_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
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
| _27_305 -> begin
(aux rest)
end)
end
| _27_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _27_316 -> begin
(let _112_206 = (let _112_205 = (FStar_Util.mk_ref None)
in (t0, s, _112_205))
in (FStar_Absyn_Syntax.mk_Typ_delayed _112_206 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _27_323 -> begin
(
# 216 "FStar.Absyn.Util.fst"
let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _112_211 = (let _112_210 = (compose_subst s' s)
in (let _112_209 = (FStar_Util.mk_ref None)
in (e, _112_210, _112_209)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _112_211 None e.FStar_Absyn_Syntax.pos))
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
| _27_340 -> begin
(aux rest)
end)
end
| _27_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _27_350 -> begin
(let _112_215 = (let _112_214 = (FStar_Util.mk_ref None)
in (e0, s, _112_214))
in (FStar_Absyn_Syntax.mk_Exp_delayed _112_215 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _27_357 -> begin
(
# 241 "FStar.Absyn.Util.fst"
let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _112_220 = (let _112_219 = (compose_subst s' s)
in (let _112_218 = (FStar_Util.mk_ref None)
in (k, _112_219, _112_218)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _112_220 k0.FStar_Absyn_Syntax.pos))
end
| _27_368 -> begin
(let _112_222 = (let _112_221 = (FStar_Util.mk_ref None)
in (k0, s, _112_221))
in (FStar_Absyn_Syntax.mk_Kind_delayed _112_222 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _27_7 -> (match (_27_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _112_226 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_112_226))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _27_381 -> begin
(
# 258 "FStar.Absyn.Util.fst"
let _27_382 = t
in (let _112_236 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _112_235 = (FStar_List.map (fun _27_8 -> (match (_27_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _112_231 = (let _112_230 = (subst_typ' s t)
in FStar_Util.Inl (_112_230))
in (_112_231, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _112_233 = (let _112_232 = (subst_exp' s e)
in FStar_Util.Inr (_112_232))
in (_112_233, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _112_234 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _27_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _112_236; FStar_Absyn_Syntax.effect_args = _112_235; FStar_Absyn_Syntax.flags = _112_234}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _27_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _112_239 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _112_239))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _112_240 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _112_240))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))

# 271 "FStar.Absyn.Util.fst"
let mk_subst = (fun s -> (s)::[])

# 272 "FStar.Absyn.Util.fst"
let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))

# 273 "FStar.Absyn.Util.fst"
let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))

# 274 "FStar.Absyn.Util.fst"
let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))

# 275 "FStar.Absyn.Util.fst"
let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))

# 276 "FStar.Absyn.Util.fst"
let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))

# 277 "FStar.Absyn.Util.fst"
let subst_binder = (fun s _27_9 -> (match (_27_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _112_268 = (let _112_267 = (
# 278 "FStar.Absyn.Util.fst"
let _27_423 = a
in (let _112_266 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _27_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _112_266; FStar_Absyn_Syntax.p = _27_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_112_267))
in (_112_268, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _112_271 = (let _112_270 = (
# 279 "FStar.Absyn.Util.fst"
let _27_429 = x
in (let _112_269 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _27_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _112_269; FStar_Absyn_Syntax.p = _27_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_112_270))
in (_112_271, imp))
end))

# 280 "FStar.Absyn.Util.fst"
let subst_arg = (fun s _27_10 -> (match (_27_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _112_275 = (let _112_274 = (subst_typ s t)
in FStar_Util.Inl (_112_274))
in (_112_275, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _112_277 = (let _112_276 = (subst_exp s e)
in FStar_Util.Inr (_112_276))
in (_112_277, imp))
end))

# 283 "FStar.Absyn.Util.fst"
let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _27_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))

# 286 "FStar.Absyn.Util.fst"
let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _27_450 -> begin
(FStar_List.map (subst_arg s) args)
end))

# 289 "FStar.Absyn.Util.fst"
let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _27_456), (FStar_Util.Inl (t), _27_461)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _27_467), (FStar_Util.Inr (v), _27_472)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _27_476 -> begin
(FStar_All.failwith "Ill-formed substitution")
end))

# 293 "FStar.Absyn.Util.fst"
let mk_subst_one_binder : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.binder  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _112_292 = (let _112_291 = (let _112_290 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _112_290))
in FStar_Util.Inl (_112_291))
in (_112_292)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _112_295 = (let _112_294 = (let _112_293 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _112_293))
in FStar_Util.Inr (_112_294))
in (_112_295)::[])
end
end
| _27_490 -> begin
[]
end)
end)

# 306 "FStar.Absyn.Util.fst"
let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.typ), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * FStar_Absyn_Syntax.exp)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (
# 307 "FStar.Absyn.Util.fst"
let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _112_307 = (let _112_306 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _112_306 out))
in (aux _112_307 bs1 bs2))
end
| _27_508 -> begin
None
end))
in (aux [] bs1 bs2)))

# 313 "FStar.Absyn.Util.fst"
let subst_of_list : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.subst = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 317 "FStar.Absyn.Util.fst"
type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}

# 317 "FStar.Absyn.Util.fst"
let is_Mkred_ctrl : red_ctrl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl"))))

# 321 "FStar.Absyn.Util.fst"
let alpha_ctrl : red_ctrl = {stop_if_empty_subst = false; descend = true}

# 322 "FStar.Absyn.Util.fst"
let subst_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = true}

# 323 "FStar.Absyn.Util.fst"
let null_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = false}

# 324 "FStar.Absyn.Util.fst"
let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))

# 326 "FStar.Absyn.Util.fst"
let map_knd = (fun s vk mt me descend binders k -> (let _112_328 = (subst_kind' s k)
in (_112_328, descend)))

# 328 "FStar.Absyn.Util.fst"
let map_typ = (fun s mk vt me descend binders t -> (let _112_336 = (subst_typ' s t)
in (_112_336, descend)))

# 330 "FStar.Absyn.Util.fst"
let map_exp = (fun s mk me ve descend binders e -> (let _112_344 = (subst_exp' s e)
in (_112_344, descend)))

# 332 "FStar.Absyn.Util.fst"
let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _27_11 -> (match (_27_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _112_361 = (let _112_360 = (map_exp descend binders e)
in (FStar_All.pipe_right _112_360 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_112_361))
end
| f -> begin
f
end)))))

# 336 "FStar.Absyn.Util.fst"
let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 338 "FStar.Absyn.Util.fst"
let _27_557 = (map_typ descend binders t)
in (match (_27_557) with
| (t, descend) -> begin
(let _112_384 = (FStar_Absyn_Syntax.mk_Total t)
in (_112_384, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 341 "FStar.Absyn.Util.fst"
let _27_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_27_562) with
| (t, descend) -> begin
(
# 342 "FStar.Absyn.Util.fst"
let _27_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_27_565) with
| (args, descend) -> begin
(let _112_387 = (let _112_386 = (
# 343 "FStar.Absyn.Util.fst"
let _27_566 = ct
in (let _112_385 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _27_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _112_385}))
in (FStar_Absyn_Syntax.mk_Comp _112_386))
in (_112_387, descend))
end))
end))
end))

# 345 "FStar.Absyn.Util.fst"
let visit_knd = (fun s vk mt me ctrl binders k -> (
# 346 "FStar.Absyn.Util.fst"
let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(
# 348 "FStar.Absyn.Util.fst"
let _27_579 = (vk null_ctrl binders k)
in (match (_27_579) with
| (k, _27_578) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

# 351 "FStar.Absyn.Util.fst"
let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (
# 352 "FStar.Absyn.Util.fst"
let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(
# 355 "FStar.Absyn.Util.fst"
let k' = (let _112_433 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _112_433))
in (
# 356 "FStar.Absyn.Util.fst"
let k' = (compress_kind k')
in (
# 357 "FStar.Absyn.Util.fst"
let _27_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _112_435 = (let _112_434 = (subst_of_list formals actuals)
in (subst_kind _112_434 k'))
in (compress_kind _112_435))
end
| _27_602 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _27_604 -> begin
k
end)
end
| _27_606 -> begin
k
end)))

# 374 "FStar.Absyn.Util.fst"
let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (
# 375 "FStar.Absyn.Util.fst"
let visit_prod = (fun bs tc -> (
# 376 "FStar.Absyn.Util.fst"
let _27_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _27_620 b -> (match (_27_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 378 "FStar.Absyn.Util.fst"
let _27_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_27_629) with
| (k, _27_628) -> begin
(
# 379 "FStar.Absyn.Util.fst"
let a = (
# 379 "FStar.Absyn.Util.fst"
let _27_630 = a
in {FStar_Absyn_Syntax.v = _27_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _27_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(
# 383 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (
# 384 "FStar.Absyn.Util.fst"
let _27_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _27_636 -> begin
(
# 387 "FStar.Absyn.Util.fst"
let b = (let _112_512 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _112_512 k))
in (
# 388 "FStar.Absyn.Util.fst"
let s = (let _112_515 = (let _112_514 = (let _112_513 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _112_513))
in FStar_Util.Inl (_112_514))
in (extend_subst _112_515 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_27_642) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(
# 393 "FStar.Absyn.Util.fst"
let _27_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_27_650) with
| (t, _27_649) -> begin
(
# 394 "FStar.Absyn.Util.fst"
let x = (
# 394 "FStar.Absyn.Util.fst"
let _27_651 = x
in {FStar_Absyn_Syntax.v = _27_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _27_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(
# 398 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (
# 399 "FStar.Absyn.Util.fst"
let _27_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _27_657 -> begin
(
# 402 "FStar.Absyn.Util.fst"
let y = (let _112_525 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _112_525 t))
in (
# 403 "FStar.Absyn.Util.fst"
let s = (let _112_528 = (let _112_527 = (let _112_526 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _112_526))
in FStar_Util.Inr (_112_527))
in (extend_subst _112_528 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_27_663) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_27_667) with
| (bs, boundvars, s) -> begin
(
# 407 "FStar.Absyn.Util.fst"
let tc = (match ((s, tc)) with
| ([], _27_670) -> begin
tc
end
| (_27_673, FStar_Util.Inl (t)) -> begin
(let _112_539 = (let _112_538 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _112_538))
in FStar_Util.Inl (_112_539))
end
| (_27_678, FStar_Util.Inr (c)) -> begin
(let _112_562 = (let _112_561 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _112_561))
in FStar_Util.Inr (_112_562))
end)
in ((FStar_List.rev bs), tc))
end)))
in (
# 413 "FStar.Absyn.Util.fst"
let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_27_685) -> begin
(let _112_564 = (let _112_563 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _112_563))
in (_112_564, ctrl))
end
| _27_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _112_574 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_112_574, ctrl))
end
| _27_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _27_706)::[], FStar_Util.Inl (t)) -> begin
(let _112_575 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_112_575, ctrl))
end
| _27_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _112_576 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_112_576, ctrl))
end
| _27_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _27_725 -> begin
(
# 437 "FStar.Absyn.Util.fst"
let _27_729 = (vt null_ctrl boundvars t)
in (match (_27_729) with
| (t, _27_728) -> begin
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
let res = (let _112_596 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _112_596))
in (
# 444 "FStar.Absyn.Util.fst"
let res = (compress_typ' res)
in (
# 445 "FStar.Absyn.Util.fst"
let _27_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 450 "FStar.Absyn.Util.fst"
let t = (let _112_598 = (mk_t ())
in (compress_typ' _112_598))
in (
# 451 "FStar.Absyn.Util.fst"
let _27_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _27_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 457 "FStar.Absyn.Util.fst"
let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_27_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _27_759 -> begin
t
end)))

# 462 "FStar.Absyn.Util.fst"
let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (
# 463 "FStar.Absyn.Util.fst"
let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_27_769) -> begin
(let _112_664 = (let _112_663 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _112_663))
in (_112_664, ctrl))
end
| _27_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _27_774 -> begin
(
# 467 "FStar.Absyn.Util.fst"
let _27_778 = (ve null_ctrl binders e)
in (match (_27_778) with
| (e, _27_777) -> begin
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
let e = (let _112_693 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _112_693))
in (
# 474 "FStar.Absyn.Util.fst"
let res = (compress_exp e)
in (
# 475 "FStar.Absyn.Util.fst"
let _27_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _27_791 -> begin
e
end)))

# 479 "FStar.Absyn.Util.fst"
let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (
# 480 "FStar.Absyn.Util.fst"
let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _27_802, _27_804) -> begin
(unmeta_exp e)
end
| _27_808 -> begin
e
end)))

# 486 "FStar.Absyn.Util.fst"
let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 487 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (
# 488 "FStar.Absyn.Util.fst"
let s = (mk_subst [])
in (
# 489 "FStar.Absyn.Util.fst"
let doit = (fun t -> (let _112_718 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _112_718)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_27_824) -> begin
(doit t)
end
| _27_827 -> begin
t
end)))))

# 496 "FStar.Absyn.Util.fst"
let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _27_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

# 502 "FStar.Absyn.Util.fst"
let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _27_12 -> (match (_27_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _112_725 = (compress_typ t)
in Some (_112_725))
end))

# 506 "FStar.Absyn.Util.fst"
let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _112_730 = (let _112_729 = (let _112_728 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange))
in (_112_728)::[])
in (FStar_List.append lid.FStar_Ident.ns _112_729))
in (FStar_Ident.lid_of_ids _112_730)))

# 509 "FStar.Absyn.Util.fst"
let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (
# 510 "FStar.Absyn.Util.fst"
let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 513 "FStar.Absyn.Util.fst"
let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _112_738 = (let _112_737 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _112_737; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _112_738)))

# 519 "FStar.Absyn.Util.fst"
let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

# 521 "FStar.Absyn.Util.fst"
let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

# 529 "FStar.Absyn.Util.fst"
let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_27_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 531 "FStar.Absyn.Util.fst"
let _27_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((
# 531 "FStar.Absyn.Util.fst"
let _27_865 = ct
in {FStar_Absyn_Syntax.effect_name = _27_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _27_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _27_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _27_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _27_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _27_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _27_863.FStar_Absyn_Syntax.uvs})
end))

# 533 "FStar.Absyn.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_27_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

# 537 "FStar.Absyn.Util.fst"
let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_27_877) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))

# 541 "FStar.Absyn.Util.fst"
let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))

# 546 "FStar.Absyn.Util.fst"
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _27_13 -> (match (_27_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _27_889 -> begin
false
end)))))

# 549 "FStar.Absyn.Util.fst"
let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _27_14 -> (match (_27_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _27_895 -> begin
false
end))))))

# 551 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _27_15 -> (match (_27_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _27_901 -> begin
false
end))))))

# 555 "FStar.Absyn.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _27_16 -> (match (_27_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _27_907 -> begin
false
end)))))

# 557 "FStar.Absyn.Util.fst"
let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _27_17 -> (match (_27_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _27_913 -> begin
false
end)))))

# 559 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

# 563 "FStar.Absyn.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_27_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_18 -> (match (_27_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _27_924 -> begin
false
end)))))
end))

# 570 "FStar.Absyn.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

# 575 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 577 "FStar.Absyn.Util.fst"
let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _27_19 -> (match (_27_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _27_931 -> begin
false
end))))))

# 583 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

# 586 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _112_777 = (compress_typ t)
in _112_777.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_27_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _27_940 -> begin
true
end))

# 590 "FStar.Absyn.Util.fst"
let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _112_780 = (compress_typ t)
in _112_780.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_27_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _27_950 -> begin
false
end)
end
| _27_952 -> begin
false
end))

# 597 "FStar.Absyn.Util.fst"
let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _112_783 = (compress_typ t)
in _112_783.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_27_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _27_966)::_27_962 -> begin
(match ((let _112_784 = (unmeta_exp pats)
in _112_784.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _27_983); FStar_Absyn_Syntax.tk = _27_980; FStar_Absyn_Syntax.pos = _27_978; FStar_Absyn_Syntax.fvs = _27_976; FStar_Absyn_Syntax.uvs = _27_974}, _27_988) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _27_992 -> begin
false
end)
end
| _27_994 -> begin
false
end)
end
| _27_996 -> begin
false
end)
end
| _27_998 -> begin
false
end))

# 611 "FStar.Absyn.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _27_20 -> (match (_27_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _27_1005 -> begin
false
end)))))
end
| _27_1007 -> begin
false
end))

# 617 "FStar.Absyn.Util.fst"
let comp_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
t
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.result_typ
end))

# 621 "FStar.Absyn.Util.fst"
let set_result_typ = (fun c t -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_27_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (
# 623 "FStar.Absyn.Util.fst"
let _27_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _27_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _27_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _27_1020.FStar_Absyn_Syntax.flags}))
end))

# 625 "FStar.Absyn.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _27_21 -> (match (_27_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _27_1027 -> begin
false
end)))))

# 631 "FStar.Absyn.Util.fst"
let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _112_794 = (compress_exp e)
in _112_794.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_1040)) -> begin
(is_atom e)
end
| _27_1045 -> begin
false
end))

# 638 "FStar.Absyn.Util.fst"
let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

# 655 "FStar.Absyn.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _27_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _27_1053 -> begin
false
end))

# 659 "FStar.Absyn.Util.fst"
let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _27_1057, _27_1059) -> begin
(unascribe e)
end
| _27_1063 -> begin
e
end))

# 663 "FStar.Absyn.Util.fst"
let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _27_1068) -> begin
(ascribe_typ t' k)
end
| _27_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

# 667 "FStar.Absyn.Util.fst"
let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _27_1076) -> begin
(unascribe_typ t)
end
| _27_1080 -> begin
t
end))

# 671 "FStar.Absyn.Util.fst"
let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 672 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _27_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _27_1090) -> begin
(unrefine t)
end
| _27_1094 -> begin
t
end)))

# 678 "FStar.Absyn.Util.fst"
let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _112_808 = (compress_exp e)
in _112_808.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_27_1097) -> begin
true
end
| _27_1100 -> begin
false
end))

# 682 "FStar.Absyn.Util.fst"
let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _112_811 = (compress_typ t)
in _112_811.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_27_1103) -> begin
true
end
| _27_1106 -> begin
false
end))

# 686 "FStar.Absyn.Util.fst"
let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 687 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _27_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _27_1116) -> begin
(pre_typ t)
end
| _27_1120 -> begin
t
end)))

# 693 "FStar.Absyn.Util.fst"
let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (
# 694 "FStar.Absyn.Util.fst"
let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _27_1131; FStar_Absyn_Syntax.pos = _27_1129; FStar_Absyn_Syntax.fvs = _27_1127; FStar_Absyn_Syntax.uvs = _27_1125}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _27_1141 -> begin
None
end)))

# 700 "FStar.Absyn.Util.fst"
let rec lids_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.lident Prims.list = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _27_1235) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

# 715 "FStar.Absyn.Util.fst"
let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _27_1251 -> begin
None
end))

# 719 "FStar.Absyn.Util.fst"
let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 734 "FStar.Absyn.Util.fst"
let range_of_lb = (fun _27_22 -> (match (_27_22) with
| (FStar_Util.Inl (x), _27_1362, _27_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _27_1369, _27_1371) -> begin
(FStar_Ident.range_of_lid l)
end))

# 738 "FStar.Absyn.Util.fst"
let range_of_arg = (fun _27_23 -> (match (_27_23) with
| (FStar_Util.Inl (hd), _27_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _27_1382) -> begin
hd.FStar_Absyn_Syntax.pos
end))

# 742 "FStar.Absyn.Util.fst"
let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 745 "FStar.Absyn.Util.fst"
let mk_typ_app : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ = (fun f args -> (
# 746 "FStar.Absyn.Util.fst"
let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

# 749 "FStar.Absyn.Util.fst"
let mk_exp_app : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun f args -> (
# 750 "FStar.Absyn.Util.fst"
let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

# 753 "FStar.Absyn.Util.fst"
let mk_data : FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun l args -> (match (args) with
| [] -> begin
(let _112_844 = (let _112_843 = (let _112_842 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_112_842, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_112_843))
in (FStar_Absyn_Syntax.mk_Exp_meta _112_844))
end
| _27_1398 -> begin
(let _112_848 = (let _112_847 = (let _112_846 = (let _112_845 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _112_845 args))
in (_112_846, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_112_847))
in (FStar_Absyn_Syntax.mk_Exp_meta _112_848))
end))

# 760 "FStar.Absyn.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 761 "FStar.Absyn.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _112_854 = (let _112_853 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_112_853, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _112_854))
end else begin
x
end)

# 766 "FStar.Absyn.Util.fst"
let mk_field_projector_name = (fun lid x i -> (
# 767 "FStar.Absyn.Util.fst"
let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _112_860 = (let _112_859 = (let _112_858 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _112_858))
in (_112_859, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _112_860))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (
# 770 "FStar.Absyn.Util.fst"
let y = (
# 770 "FStar.Absyn.Util.fst"
let _27_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _27_1407.FStar_Absyn_Syntax.realname})
in (let _112_864 = (let _112_863 = (let _112_862 = (let _112_861 = (unmangle_field_name nm)
in (_112_861)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _112_862))
in (FStar_Ident.lid_of_ids _112_863))
in (_112_864, y)))))

# 773 "FStar.Absyn.Util.fst"
let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_27_1413) -> begin
(let _112_869 = (let _112_868 = (let _112_867 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _112_867))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _112_868))
in (FStar_All.failwith _112_869))
end
| _27_1416 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))

# 782 "FStar.Absyn.Util.fst"
type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)

# 783 "FStar.Absyn.Util.fst"
let no_bvars : ((FStar_Absyn_Syntax.btvar Prims.list * (FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.btvar  ->  Prims.bool)) * (FStar_Absyn_Syntax.bvvar Prims.list * (FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.bool))) = (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)

# 784 "FStar.Absyn.Util.fst"
let fvs_included : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun fvs1 fvs2 -> ((FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)))

# 788 "FStar.Absyn.Util.fst"
let eq_fvars = (fun v1 v2 -> (match ((v1, v2)) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Syntax.bvd_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _27_1432 -> begin
false
end))

# 793 "FStar.Absyn.Util.fst"
let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _27_1446 -> begin
false
end))

# 798 "FStar.Absyn.Util.fst"
let uv_eq = (fun _27_1450 _27_1454 -> (match ((_27_1450, _27_1454)) with
| ((uv1, _27_1449), (uv2, _27_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

# 799 "FStar.Absyn.Util.fst"
let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _112_898 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _112_897 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _112_896 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _112_898; FStar_Absyn_Syntax.uvars_t = _112_897; FStar_Absyn_Syntax.uvars_e = _112_896}))))

# 805 "FStar.Absyn.Util.fst"
let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _112_904 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _112_903 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _112_904; FStar_Absyn_Syntax.fxvs = _112_903})))

# 811 "FStar.Absyn.Util.fst"
let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _27_1461 _27_1464 -> (match ((_27_1461, _27_1464)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _112_910 = (union_fvs fvs1 fvs2)
in (let _112_909 = (union_uvs uvs1 uvs2)
in (_112_910, _112_909)))
end))

# 815 "FStar.Absyn.Util.fst"
let sub_fv = (fun _27_1467 _27_1470 -> (match ((_27_1467, _27_1470)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _112_931 = (
# 816 "FStar.Absyn.Util.fst"
let _27_1471 = fvs
in (let _112_930 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _112_929 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _112_930; FStar_Absyn_Syntax.fxvs = _112_929})))
in (_112_931, uvs))
end))

# 820 "FStar.Absyn.Util.fst"
let stash = (fun uvonly s _27_1479 -> (match (_27_1479) with
| (fvs, uvs) -> begin
(
# 821 "FStar.Absyn.Util.fst"
let _27_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

# 825 "FStar.Absyn.Util.fst"
let single_fv = (fun x -> (let _112_942 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _112_942)))

# 826 "FStar.Absyn.Util.fst"
let single_uv = (fun u -> (let _112_950 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _112_950)))

# 827 "FStar.Absyn.Util.fst"
let single_uvt = (fun u -> (let _112_958 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _112_958)))

# 829 "FStar.Absyn.Util.fst"
let rec vs_typ' = (fun t uvonly cont -> (
# 830 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_27_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _112_1073 = (let _112_1072 = (
# 836 "FStar.Absyn.Util.fst"
let _27_1495 = FStar_Absyn_Syntax.no_fvs
in (let _112_1071 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _112_1071; FStar_Absyn_Syntax.fxvs = _27_1495.FStar_Absyn_Syntax.fxvs}))
in (_112_1072, FStar_Absyn_Syntax.no_uvs))
in (cont _112_1073))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _112_1076 = (let _112_1075 = (
# 839 "FStar.Absyn.Util.fst"
let _27_1501 = FStar_Absyn_Syntax.no_uvs
in (let _112_1074 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _27_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _112_1074; FStar_Absyn_Syntax.uvars_e = _27_1501.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _112_1075))
in (cont _112_1076))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _27_1513 -> (match (_27_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _112_1080 = (let _112_1079 = (union_fvs_uvs vs1 vs2)
in (sub_fv _112_1079 bvs))
in (cont _112_1080))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _27_1521 -> (match (_27_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _112_1084 = (let _112_1083 = (union_fvs_uvs vs1 vs2)
in (sub_fv _112_1083 bvs))
in (cont _112_1084))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _27_1529 -> (match (_27_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _112_1088 = (let _112_1087 = (union_fvs_uvs vs1 vs2)
in (sub_fv _112_1087 bvs))
in (cont _112_1088))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _112_1091 = (union_fvs_uvs vs1 vs2)
in (cont _112_1091))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _27_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _27_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _112_1094 = (union_fvs_uvs vs1 vs2)
in (cont _112_1094))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _27_1587)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _27_1595 -> (match (_27_1595) with
| ((tvars, vvars), vs2) -> begin
(let _112_1131 = (let _112_1130 = (let _112_1128 = (FStar_Util.set_add a tvars)
in (_112_1128, vvars))
in (let _112_1129 = (union_fvs_uvs vs vs2)
in (_112_1130, _112_1129)))
in (cont _112_1131))
end)))))
end
| (FStar_Util.Inr (x), _27_1600)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _27_1608 -> (match (_27_1608) with
| ((tvars, vvars), vs2) -> begin
(let _112_1155 = (let _112_1154 = (let _112_1152 = (FStar_Util.set_add x vvars)
in (tvars, _112_1152))
in (let _112_1153 = (union_fvs_uvs vs vs2)
in (_112_1154, _112_1153)))
in (cont _112_1155))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _27_1618)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _112_1159 = (union_fvs_uvs ft1 ft2)
in (cont _112_1159))))))
end
| (FStar_Util.Inr (e), _27_1627)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _112_1162 = (union_fvs_uvs ft1 ft2)
in (cont _112_1162))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _112_1165 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _112_1164 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_112_1165, _112_1164)))) with
| (Some (_27_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (
# 911 "FStar.Absyn.Util.fst"
let _27_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (
# 915 "FStar.Absyn.Util.fst"
let _27_1652 = (stash uvonly t fvs)
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
| FStar_Absyn_Syntax.Kind_lam (_27_1665, k) -> begin
(let _112_1170 = (let _112_1169 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _112_1169))
in (FStar_All.failwith _112_1170))
end
| FStar_Absyn_Syntax.Kind_delayed (_27_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _27_1681 -> (match (_27_1681) with
| (fvs, uvs) -> begin
(let _112_1174 = (let _112_1173 = (
# 929 "FStar.Absyn.Util.fst"
let _27_1682 = uvs
in (let _112_1172 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _112_1172; FStar_Absyn_Syntax.uvars_t = _27_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _27_1682.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _112_1173))
in (cont _112_1174))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_27_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _27_1695 -> (match (_27_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _112_1178 = (let _112_1177 = (union_fvs_uvs vs1 vs2)
in (sub_fv _112_1177 bvs))
in (cont _112_1178))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _112_1181 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _112_1180 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_112_1181, _112_1180)))) with
| (Some (_27_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (
# 943 "FStar.Absyn.Util.fst"
let _27_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (
# 947 "FStar.Absyn.Util.fst"
let _27_1717 = (stash uvonly k fvs)
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
| FStar_Absyn_Syntax.Exp_delayed (_27_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _112_1187 = (let _112_1186 = (
# 957 "FStar.Absyn.Util.fst"
let _27_1742 = FStar_Absyn_Syntax.no_uvs
in (let _112_1185 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _27_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _27_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _112_1185}))
in (FStar_Absyn_Syntax.no_fvs, _112_1186))
in (cont _112_1187))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _112_1190 = (let _112_1189 = (
# 962 "FStar.Absyn.Util.fst"
let _27_1746 = FStar_Absyn_Syntax.no_fvs
in (let _112_1188 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _27_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _112_1188}))
in (_112_1189, FStar_Absyn_Syntax.no_uvs))
in (cont _112_1190))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _27_1750, _27_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _27_1761 -> (match (_27_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _112_1194 = (let _112_1193 = (union_fvs_uvs vs1 vs2)
in (sub_fv _112_1193 bvs))
in (cont _112_1194))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _112_1197 = (union_fvs_uvs ft1 ft2)
in (cont _112_1197))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _27_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _112_1200 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _112_1199 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_112_1200, _112_1199)))) with
| (Some (_27_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (
# 986 "FStar.Absyn.Util.fst"
let _27_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (
# 990 "FStar.Absyn.Util.fst"
let _27_1801 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _112_1206 = (union_fvs_uvs vs1 vs2)
in (k _112_1206))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _112_1209 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _112_1208 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_112_1209, _112_1208)))) with
| (Some (_27_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (
# 1007 "FStar.Absyn.Util.fst"
let _27_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (
# 1011 "FStar.Absyn.Util.fst"
let _27_1838 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _112_1216 = (union_fvs_uvs ft1 ft2)
in (cont _112_1216))))))
end))

# 1027 "FStar.Absyn.Util.fst"
let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _27_1867 -> (match (_27_1867) with
| (x, _27_1866) -> begin
x
end))))

# 1030 "FStar.Absyn.Util.fst"
let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _27_1872 -> (match (_27_1872) with
| (x, _27_1871) -> begin
x
end))))

# 1033 "FStar.Absyn.Util.fst"
let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _27_1877 -> (match (_27_1877) with
| (x, _27_1876) -> begin
x
end))))

# 1036 "FStar.Absyn.Util.fst"
let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _27_1882 -> (match (_27_1882) with
| (x, _27_1881) -> begin
x
end))))

# 1039 "FStar.Absyn.Util.fst"
let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _112_1232 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _112_1232))
end
| FStar_Util.Inr (e) -> begin
(let _112_1233 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _112_1233))
end)) FStar_Absyn_Syntax.no_fvs)))

# 1044 "FStar.Absyn.Util.fst"
let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _27_24 -> (match (_27_24) with
| FStar_Util.Inl (a) -> begin
(FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)
end
| FStar_Util.Inr (x) -> begin
(FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)
end)))))

# 1049 "FStar.Absyn.Util.fst"
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
| SynSumKind (_27_1899) -> begin
_27_1899
end))

# 1051 "FStar.Absyn.Util.fst"
let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_27_1902) -> begin
_27_1902
end))

# 1052 "FStar.Absyn.Util.fst"
let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_27_1905) -> begin
_27_1905
end))

# 1053 "FStar.Absyn.Util.fst"
let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_27_1908) -> begin
_27_1908
end))

# 1055 "FStar.Absyn.Util.fst"
let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (
# 1056 "FStar.Absyn.Util.fst"
let out = (let _112_1307 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _112_1307 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _112_1305 = (uvars_in_kind k)
in (union_uvs _112_1305 out))
end
| _27_1916 -> begin
(
# 1059 "FStar.Absyn.Util.fst"
let _27_1917 = out
in (let _112_1306 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _112_1306; FStar_Absyn_Syntax.uvars_t = _27_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _27_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (
# 1060 "FStar.Absyn.Util.fst"
let out = (let _112_1312 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _112_1312 (FStar_List.fold_left (fun out _27_1923 -> (match (_27_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _112_1310 = (uvars_in_typ t)
in (union_uvs _112_1310 out))
end
| _27_1927 -> begin
(
# 1063 "FStar.Absyn.Util.fst"
let _27_1928 = out
in (let _112_1311 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _27_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _112_1311; FStar_Absyn_Syntax.uvars_e = _27_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (
# 1064 "FStar.Absyn.Util.fst"
let out = (let _112_1317 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _112_1317 (FStar_List.fold_left (fun out _27_1934 -> (match (_27_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _112_1315 = (uvars_in_exp e)
in (union_uvs _112_1315 out))
end
| _27_1938 -> begin
(
# 1067 "FStar.Absyn.Util.fst"
let _27_1939 = out
in (let _112_1316 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _27_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _27_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _112_1316}))
end)
end)) out)))
in (
# 1068 "FStar.Absyn.Util.fst"
let _27_1950 = (match (s) with
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _112_1320 = (vs_kind k true (fun _27_1956 -> (match (_27_1956) with
| (_27_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _112_1320)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _112_1323 = (vs_typ t true (fun _27_1961 -> (match (_27_1961) with
| (_27_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _112_1323)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _112_1326 = (vs_exp e true (fun _27_1966 -> (match (_27_1966) with
| (_27_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _112_1326)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _112_1329 = (vs_comp c true (fun _27_1971 -> (match (_27_1971) with
| (_27_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _112_1329)))

# 1087 "FStar.Absyn.Util.fst"
let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

# 1095 "FStar.Absyn.Util.fst"
let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (
# 1096 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_27_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 1104 "FStar.Absyn.Util.fst"
let _27_1991 = (kind_formals k)
in (match (_27_1991) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_27_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_27_1998) -> begin
(FStar_All.failwith "Impossible")
end)))

# 1109 "FStar.Absyn.Util.fst"
let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (
# 1110 "FStar.Absyn.Util.fst"
let _27_2005 = (kind_formals k)
in (match (_27_2005) with
| (bs, _27_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _27_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

# 1115 "FStar.Absyn.Util.fst"
let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (
# 1116 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_27_2012, k) -> begin
(unabbreviate_kind k)
end
| _27_2017 -> begin
k
end)))

# 1121 "FStar.Absyn.Util.fst"
let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _27_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

# 1126 "FStar.Absyn.Util.fst"
let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _27_2027 -> begin
(
# 1130 "FStar.Absyn.Util.fst"
let _27_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _27_2033 -> begin
(let _112_1350 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _112_1350))
end)
in (match (_27_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

# 1135 "FStar.Absyn.Util.fst"
let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow

# 1137 "FStar.Absyn.Util.fst"
let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _27_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

# 1145 "FStar.Absyn.Util.fst"
let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _27_2046 -> begin
false
end))

# 1149 "FStar.Absyn.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1150 "FStar.Absyn.Util.fst"
let t = (let _112_1363 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _112_1363))
in (let _112_1364 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _112_1364 r))))

# 1153 "FStar.Absyn.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1154 "FStar.Absyn.Util.fst"
let t = (let _112_1369 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _112_1369))
in (let _112_1370 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _112_1370 r))))

# 1157 "FStar.Absyn.Util.fst"
let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _112_1375 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _112_1375)))

# 1160 "FStar.Absyn.Util.fst"
let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _27_2059 -> begin
false
end))

# 1164 "FStar.Absyn.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1165 "FStar.Absyn.Util.fst"
let t = (let _112_1382 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _112_1382))
in (let _112_1383 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _112_1383 r))))

# 1168 "FStar.Absyn.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1169 "FStar.Absyn.Util.fst"
let t = (let _112_1388 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _112_1388))
in (let _112_1389 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _112_1389 r))))

# 1173 "FStar.Absyn.Util.fst"
let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))

# 1179 "FStar.Absyn.Util.fst"
let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

# 1180 "FStar.Absyn.Util.fst"
let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

# 1181 "FStar.Absyn.Util.fst"
let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 1182 "FStar.Absyn.Util.fst"
let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

# 1184 "FStar.Absyn.Util.fst"
let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (
# 1185 "FStar.Absyn.Util.fst"
let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 1189 "FStar.Absyn.Util.fst"
let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _112_1405 = (pre_typ t)
in _112_1405.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _27_2078 -> begin
false
end))

# 1194 "FStar.Absyn.Util.fst"
let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _112_1410 = (pre_typ t)
in _112_1410.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_27_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _27_2086) -> begin
(is_constructed_typ t lid)
end
| _27_2090 -> begin
false
end))

# 1199 "FStar.Absyn.Util.fst"
let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (
# 1200 "FStar.Absyn.Util.fst"
let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _27_2101) -> begin
(get_tycon t)
end
| _27_2105 -> begin
None
end)))

# 1207 "FStar.Absyn.Util.fst"
let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _27_25 -> (match (_27_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _27_2109 -> begin
false
end))

# 1211 "FStar.Absyn.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _27_2115 _27_2119 -> (match ((_27_2115, _27_2119)) with
| ((fn1, _27_2114), (fn2, _27_2118)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 1219 "FStar.Absyn.Util.fst"
let kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1220 "FStar.Absyn.Util.fst"
let kt_kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1222 "FStar.Absyn.Util.fst"
let tand : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.and_lid kt_kt_kt)

# 1223 "FStar.Absyn.Util.fst"
let tor : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.or_lid kt_kt_kt)

# 1224 "FStar.Absyn.Util.fst"
let timp : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.imp_lid kt_kt_kt)

# 1225 "FStar.Absyn.Util.fst"
let tiff : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.iff_lid kt_kt_kt)

# 1226 "FStar.Absyn.Util.fst"
let t_bool : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)

# 1227 "FStar.Absyn.Util.fst"
let t_false : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)

# 1228 "FStar.Absyn.Util.fst"
let t_true : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)

# 1229 "FStar.Absyn.Util.fst"
let b2t_v : FStar_Absyn_Syntax.typ = (let _112_1421 = (let _112_1420 = (let _112_1419 = (let _112_1418 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_112_1418)::[])
in (_112_1419, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1420 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _112_1421))

# 1231 "FStar.Absyn.Util.fst"
let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _112_1432 = (let _112_1431 = (let _112_1429 = (let _112_1428 = (FStar_Absyn_Syntax.targ phi1)
in (let _112_1427 = (let _112_1426 = (FStar_Absyn_Syntax.targ phi2)
in (_112_1426)::[])
in (_112_1428)::_112_1427))
in (tand, _112_1429))
in (let _112_1430 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _112_1431 None _112_1430)))
in Some (_112_1432))
end))

# 1234 "FStar.Absyn.Util.fst"
let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _112_1444 = (let _112_1442 = (let _112_1441 = (FStar_Absyn_Syntax.targ phi1)
in (let _112_1440 = (let _112_1439 = (FStar_Absyn_Syntax.targ phi2)
in (_112_1439)::[])
in (_112_1441)::_112_1440))
in (op_t, _112_1442))
in (let _112_1443 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _112_1444 None _112_1443))))

# 1235 "FStar.Absyn.Util.fst"
let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _112_1450 = (let _112_1449 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _112_1448 = (let _112_1447 = (FStar_Absyn_Syntax.targ phi)
in (_112_1447)::[])
in (_112_1449, _112_1448)))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1450 None phi.FStar_Absyn_Syntax.pos)))

# 1236 "FStar.Absyn.Util.fst"
let mk_conj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 1237 "FStar.Absyn.Util.fst"
let mk_conj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 1240 "FStar.Absyn.Util.fst"
let mk_disj : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 1241 "FStar.Absyn.Util.fst"
let mk_disj_l : FStar_Absyn_Syntax.typ Prims.list  ->  FStar_Absyn_Syntax.typ = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 1244 "FStar.Absyn.Util.fst"
let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _112_1467 = (compress_typ phi1)
in _112_1467.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _27_2150 -> begin
(match ((let _112_1468 = (compress_typ phi2)
in _112_1468.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _27_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 1254 "FStar.Absyn.Util.fst"
let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 1255 "FStar.Absyn.Util.fst"
let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _112_1477 = (let _112_1476 = (let _112_1475 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_112_1475)::[])
in (b2t_v, _112_1476))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1477 None e.FStar_Absyn_Syntax.pos)))

# 1257 "FStar.Absyn.Util.fst"
let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (
# 1258 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _27_2194)) -> begin
(mk_conj t1 t2)
end
| _27_2199 -> begin
t
end)))

# 1269 "FStar.Absyn.Util.fst"
let eq_k : FStar_Absyn_Syntax.knd = (
# 1270 "FStar.Absyn.Util.fst"
let a = (let _112_1480 = (new_bvd None)
in (bvd_to_bvar_s _112_1480 FStar_Absyn_Syntax.ktype))
in (
# 1271 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (
# 1272 "FStar.Absyn.Util.fst"
let b = (let _112_1481 = (new_bvd None)
in (bvd_to_bvar_s _112_1481 FStar_Absyn_Syntax.ktype))
in (
# 1273 "FStar.Absyn.Util.fst"
let btyp = (btvar_to_typ b)
in (let _112_1488 = (let _112_1487 = (let _112_1486 = (let _112_1485 = (let _112_1484 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _112_1483 = (let _112_1482 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_112_1482)::[])
in (_112_1484)::_112_1483))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit (false))))::_112_1485)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_112_1486)
in (_112_1487, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1488 FStar_Absyn_Syntax.dummyRange))))))

# 1277 "FStar.Absyn.Util.fst"
let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)

# 1278 "FStar.Absyn.Util.fst"
let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _27_2217 -> begin
(let _112_1506 = (let _112_1504 = (let _112_1503 = (FStar_Absyn_Syntax.itarg t1)
in (let _112_1502 = (let _112_1501 = (FStar_Absyn_Syntax.itarg t2)
in (let _112_1500 = (let _112_1499 = (FStar_Absyn_Syntax.varg e1)
in (let _112_1498 = (let _112_1497 = (FStar_Absyn_Syntax.varg e2)
in (_112_1497)::[])
in (_112_1499)::_112_1498))
in (_112_1501)::_112_1500))
in (_112_1503)::_112_1502))
in (teq, _112_1504))
in (let _112_1505 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _112_1506 None _112_1505)))
end))

# 1282 "FStar.Absyn.Util.fst"
let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

# 1283 "FStar.Absyn.Util.fst"
let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _112_1516 = (let _112_1514 = (let _112_1513 = (FStar_Absyn_Syntax.targ t1)
in (let _112_1512 = (let _112_1511 = (FStar_Absyn_Syntax.targ t2)
in (_112_1511)::[])
in (_112_1513)::_112_1512))
in (eq_typ, _112_1514))
in (let _112_1515 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _112_1516 None _112_1515))))

# 1285 "FStar.Absyn.Util.fst"
let lex_t : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

# 1286 "FStar.Absyn.Util.fst"
let lex_top : FStar_Absyn_Syntax.exp = (
# 1287 "FStar.Absyn.Util.fst"
let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

# 1290 "FStar.Absyn.Util.fst"
let lex_pair : FStar_Absyn_Syntax.exp = (
# 1291 "FStar.Absyn.Util.fst"
let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (
# 1292 "FStar.Absyn.Util.fst"
let lexcons = (let _112_1526 = (let _112_1525 = (let _112_1524 = (let _112_1522 = (FStar_Absyn_Syntax.t_binder a)
in (let _112_1521 = (let _112_1520 = (let _112_1517 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _112_1517))
in (let _112_1519 = (let _112_1518 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_112_1518)::[])
in (_112_1520)::_112_1519))
in (_112_1522)::_112_1521))
in (let _112_1523 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_112_1524, _112_1523)))
in (FStar_Absyn_Syntax.mk_Typ_fun _112_1525 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _112_1526 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

# 1295 "FStar.Absyn.Util.fst"
let forall_kind : FStar_Absyn_Syntax.knd = (
# 1296 "FStar.Absyn.Util.fst"
let a = (let _112_1527 = (new_bvd None)
in (bvd_to_bvar_s _112_1527 FStar_Absyn_Syntax.ktype))
in (
# 1297 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (let _112_1535 = (let _112_1534 = (let _112_1533 = (let _112_1532 = (let _112_1531 = (let _112_1530 = (let _112_1529 = (let _112_1528 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_112_1528)::[])
in (_112_1529, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1530 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _112_1531))
in (_112_1532)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_112_1533)
in (_112_1534, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1535 FStar_Absyn_Syntax.dummyRange))))

# 1302 "FStar.Absyn.Util.fst"
let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)

# 1304 "FStar.Absyn.Util.fst"
let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _112_1544 = (let _112_1543 = (let _112_1542 = (let _112_1541 = (let _112_1540 = (let _112_1539 = (let _112_1538 = (FStar_Absyn_Syntax.null_t_binder k)
in (_112_1538)::[])
in (_112_1539, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1540 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _112_1541))
in (_112_1542)::[])
in (_112_1543, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1544 FStar_Absyn_Syntax.dummyRange)))

# 1305 "FStar.Absyn.Util.fst"
let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _112_1551 = (let _112_1550 = (let _112_1549 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _112_1548 = (let _112_1547 = (FStar_Absyn_Syntax.null_t_binder k)
in (_112_1547)::[])
in (_112_1549)::_112_1548))
in (_112_1550, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _112_1551 FStar_Absyn_Syntax.dummyRange)))

# 1307 "FStar.Absyn.Util.fst"
let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _112_1554 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _112_1554)))

# 1309 "FStar.Absyn.Util.fst"
let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _112_1566 = (let _112_1565 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _112_1564 = (let _112_1563 = (let _112_1562 = (let _112_1561 = (let _112_1560 = (let _112_1559 = (FStar_Absyn_Syntax.t_binder a)
in (_112_1559)::[])
in (_112_1560, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _112_1561 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _112_1562))
in (_112_1563)::[])
in (_112_1565, _112_1564)))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1566 None b.FStar_Absyn_Syntax.pos)))

# 1312 "FStar.Absyn.Util.fst"
let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (
# 1313 "FStar.Absyn.Util.fst"
let r = FStar_Absyn_Syntax.dummyRange
in (let _112_1577 = (let _112_1576 = (let _112_1575 = (let _112_1574 = (let _112_1573 = (let _112_1572 = (let _112_1571 = (FStar_Absyn_Syntax.v_binder x)
in (_112_1571)::[])
in (_112_1572, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _112_1573 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _112_1574))
in (_112_1575)::[])
in (tforall, _112_1576))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1577 None r))))

# 1316 "FStar.Absyn.Util.fst"
let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(
# 1320 "FStar.Absyn.Util.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _112_1587 = (let _112_1586 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _112_1585 = (let _112_1584 = (FStar_Absyn_Syntax.targ body)
in (_112_1584)::[])
in (_112_1586, _112_1585)))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1587 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _112_1591 = (let _112_1590 = (let _112_1589 = (let _112_1588 = (FStar_Absyn_Syntax.targ body)
in (_112_1588)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit (false))))::_112_1589)
in (tforall, _112_1590))
in (FStar_Absyn_Syntax.mk_Typ_app _112_1591 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))

# 1325 "FStar.Absyn.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_27_2244) -> begin
true
end
| _27_2247 -> begin
false
end))

# 1330 "FStar.Absyn.Util.fst"
let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (
# 1331 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _27_2255 -> begin
(t, [])
end)))

# 1336 "FStar.Absyn.Util.fst"
let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (
# 1337 "FStar.Absyn.Util.fst"
let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _27_2263 -> begin
(e, [])
end)))

# 1342 "FStar.Absyn.Util.fst"
let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (
# 1343 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _27_2271 -> begin
None
end)))

# 1348 "FStar.Absyn.Util.fst"
let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (
# 1349 "FStar.Absyn.Util.fst"
let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 1370 "FStar.Absyn.Util.fst"
type qpats =
FStar_Absyn_Syntax.args Prims.list

# 1371 "FStar.Absyn.Util.fst"
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
| QAll (_27_2276) -> begin
_27_2276
end))

# 1373 "FStar.Absyn.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_27_2279) -> begin
_27_2279
end))

# 1374 "FStar.Absyn.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_27_2282) -> begin
_27_2282
end))

# 1376 "FStar.Absyn.Util.fst"
let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (
# 1377 "FStar.Absyn.Util.fst"
let destruct_base_conn = (fun f -> (
# 1378 "FStar.Absyn.Util.fst"
let _27_2288 = (true, false)
in (match (_27_2288) with
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
let rec aux = (fun f _27_2298 -> (match (_27_2298) with
| (lid, arity) -> begin
(
# 1396 "FStar.Absyn.Util.fst"
let _27_2301 = (head_and_args f)
in (match (_27_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_27_2305), _27_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_27_2311), _27_2314) -> begin
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
(let _112_1655 = (compress_typ t)
in (pats, _112_1655))
end
| _27_2325 -> begin
(let _112_1656 = (compress_typ t)
in ([], _112_1656))
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
let _27_2335 = (head_and_args t)
in (match (_27_2335) with
| (t, args) -> begin
(let _112_1670 = (FStar_All.pipe_right args (FStar_List.map (fun _27_26 -> (match (_27_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _112_1667 = (let _112_1666 = (compress_typ t)
in FStar_Util.Inl (_112_1666))
in (_112_1667, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _112_1669 = (let _112_1668 = (compress_exp e)
in FStar_Util.Inr (_112_1668))
in (_112_1669, imp))
end))))
in (t, _112_1670))
end)))
in (
# 1418 "FStar.Absyn.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _112_1677 = (flat t)
in (qopt, _112_1677))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _27_2483) -> begin
(
# 1430 "FStar.Absyn.Util.fst"
let _27_2487 = (patterns t)
in (match (_27_2487) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _27_2491) -> begin
(
# 1434 "FStar.Absyn.Util.fst"
let _27_2495 = (patterns t)
in (match (_27_2495) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _27_2497 -> begin
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





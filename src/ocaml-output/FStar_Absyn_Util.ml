
open Prims
# 28 "FStar.Absyn.Util.fst"
let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(let _100_7 = (FStar_Util.format1 "Fatal: %s" s)
in (FStar_Util.print_string _100_7))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(
# 33 "FStar.Absyn.Util.fst"
let _21_36 = (let _100_9 = (let _100_8 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _100_8 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _100_9))
in ())
end
| FStar_Util.NYI (s) -> begin
(
# 36 "FStar.Absyn.Util.fst"
let _21_40 = (let _100_10 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _100_10))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _100_11 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _100_11))
end
| _21_45 -> begin
(Prims.raise e)
end))

# 42 "FStar.Absyn.Util.fst"
let handleable : Prims.exn  ->  Prims.bool = (fun _21_1 -> (match (_21_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _21_60 -> begin
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
in {gensym = (fun _21_66 -> (match (()) with
| () -> begin
(let _100_39 = (let _100_36 = (let _100_35 = (let _100_34 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _100_34))
in (Prims.strcat "_" _100_35))
in (Prims.strcat _100_36 "_"))
in (let _100_38 = (let _100_37 = (
# 60 "FStar.Absyn.Util.fst"
let _21_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _100_37))
in (Prims.strcat _100_39 _100_38)))
end)); reset = (fun _21_69 -> (match (()) with
| () -> begin
(
# 61 "FStar.Absyn.Util.fst"
let _21_70 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

# 62 "FStar.Absyn.Util.fst"
let gensym : Prims.unit  ->  Prims.string = (fun _21_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

# 63 "FStar.Absyn.Util.fst"
let reset_gensym : Prims.unit  ->  Prims.unit = (fun _21_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))

# 64 "FStar.Absyn.Util.fst"
let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _100_48 = (gensym ())
in (let _100_47 = (gensyms (n - 1))
in (_100_48)::_100_47))
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
let mkbvd = (fun _21_87 -> (match (_21_87) with
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
| _21_114 -> begin
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
let freshen_bvd = (fun bvd' -> (let _100_89 = (let _100_88 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _100_88))
in (mkbvd _100_89)))

# 99 "FStar.Absyn.Util.fst"
let freshen_bvar = (fun b -> (let _100_91 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _100_91 b.FStar_Absyn_Syntax.sort)))

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
let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.exp = (fun dc l r -> (let _100_116 = (let _100_115 = (let _100_114 = (set_lid_range l r)
in (fv _100_114))
in (_100_115, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _100_116 None r)))

# 113 "FStar.Absyn.Util.fst"
let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))

# 114 "FStar.Absyn.Util.fst"
let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_21_160), FStar_Util.Inr (_21_163)) -> begin
(- (1))
end
| (FStar_Util.Inr (_21_167), FStar_Util.Inl (_21_170)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))

# 119 "FStar.Absyn.Util.fst"
let arg_of_non_null_binder = (fun _21_185 -> (match (_21_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _100_125 = (let _100_124 = (btvar_to_typ a)
in FStar_Util.Inl (_100_124))
in (_100_125, imp))
end
| FStar_Util.Inr (x) -> begin
(let _100_127 = (let _100_126 = (bvar_to_exp x)
in FStar_Util.Inr (_100_126))
in (_100_127, imp))
end)
end))

# 123 "FStar.Absyn.Util.fst"
let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _100_131 = (arg_of_non_null_binder b)
in (_100_131)::[])
end))))

# 127 "FStar.Absyn.Util.fst"
let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * ((FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _100_141 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(
# 130 "FStar.Absyn.Util.fst"
let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _100_136 = (let _100_135 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_100_135))
in (_100_136, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _100_138 = (let _100_137 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_100_137))
in (_100_138, (Prims.snd b)))
end)
in (let _100_139 = (arg_of_non_null_binder b)
in (b, _100_139)))
end else begin
(let _100_140 = (arg_of_non_null_binder b)
in (b, _100_140))
end)))
in (FStar_All.pipe_right _100_141 FStar_List.unzip)))

# 140 "FStar.Absyn.Util.fst"
let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 145 "FStar.Absyn.Util.fst"
let b = (let _100_147 = (let _100_146 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _100_146))
in (FStar_Ident.id_of_text _100_147))
in (
# 146 "FStar.Absyn.Util.fst"
let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(
# 150 "FStar.Absyn.Util.fst"
let x = (let _100_149 = (let _100_148 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _100_148))
in (FStar_Ident.id_of_text _100_149))
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
(let _100_153 = (let _100_152 = (name_binders binders)
in (_100_152, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _100_153 None t.FStar_Absyn_Syntax.pos))
end
| _21_220 -> begin
t
end))

# 158 "FStar.Absyn.Util.fst"
let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _21_2 -> (match (_21_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _100_158 = (let _100_157 = (FStar_Absyn_Syntax.null_t_binder k)
in (FStar_All.pipe_left Prims.fst _100_157))
in (_100_158, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _100_160 = (let _100_159 = (FStar_Absyn_Syntax.null_v_binder t)
in (FStar_All.pipe_left Prims.fst _100_159))
in (_100_160, imp))
end)))))

# 162 "FStar.Absyn.Util.fst"
let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _21_3 -> (match (_21_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _100_165 = (let _100_164 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_100_164))
in (_100_165, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _100_167 = (let _100_166 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_100_166))
in (_100_167, imp))
end)))))

# 167 "FStar.Absyn.Util.fst"
let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.binder Prims.list = (fun fvs -> (let _100_173 = (let _100_170 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _100_170 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _100_172 = (let _100_171 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _100_171 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _100_173 _100_172))))

# 174 "FStar.Absyn.Util.fst"
let subst_to_string = (fun s -> (let _100_176 = (FStar_All.pipe_right s (FStar_List.map (fun _21_4 -> (match (_21_4) with
| FStar_Util.Inl (b, _21_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _21_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _100_176 (FStar_String.concat ", "))))

# 177 "FStar.Absyn.Util.fst"
let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _21_5 -> (match (_21_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _21_262 -> begin
None
end))))

# 178 "FStar.Absyn.Util.fst"
let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _21_6 -> (match (_21_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _21_271 -> begin
None
end))))

# 179 "FStar.Absyn.Util.fst"
let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _21_278 -> begin
(
# 183 "FStar.Absyn.Util.fst"
let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _100_201 = (let _100_200 = (compose_subst s' s)
in (let _100_199 = (FStar_Util.mk_ref None)
in (t', _100_200, _100_199)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _100_201 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 191 "FStar.Absyn.Util.fst"
let t = (mk_t ())
in (
# 192 "FStar.Absyn.Util.fst"
let _21_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
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
| _21_305 -> begin
(aux rest)
end)
end
| _21_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _21_316 -> begin
(let _100_206 = (let _100_205 = (FStar_Util.mk_ref None)
in (t0, s, _100_205))
in (FStar_Absyn_Syntax.mk_Typ_delayed _100_206 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _21_323 -> begin
(
# 216 "FStar.Absyn.Util.fst"
let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _100_211 = (let _100_210 = (compose_subst s' s)
in (let _100_209 = (FStar_Util.mk_ref None)
in (e, _100_210, _100_209)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _100_211 None e.FStar_Absyn_Syntax.pos))
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
| _21_340 -> begin
(aux rest)
end)
end
| _21_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _21_350 -> begin
(let _100_215 = (let _100_214 = (FStar_Util.mk_ref None)
in (e0, s, _100_214))
in (FStar_Absyn_Syntax.mk_Exp_delayed _100_215 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _21_357 -> begin
(
# 241 "FStar.Absyn.Util.fst"
let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _100_220 = (let _100_219 = (compose_subst s' s)
in (let _100_218 = (FStar_Util.mk_ref None)
in (k, _100_219, _100_218)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _100_220 k0.FStar_Absyn_Syntax.pos))
end
| _21_368 -> begin
(let _100_222 = (let _100_221 = (FStar_Util.mk_ref None)
in (k0, s, _100_221))
in (FStar_Absyn_Syntax.mk_Kind_delayed _100_222 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _21_7 -> (match (_21_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _100_226 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_100_226))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _21_381 -> begin
(
# 258 "FStar.Absyn.Util.fst"
let _21_382 = t
in (let _100_236 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _100_235 = (FStar_List.map (fun _21_8 -> (match (_21_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _100_231 = (let _100_230 = (subst_typ' s t)
in FStar_Util.Inl (_100_230))
in (_100_231, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _100_233 = (let _100_232 = (subst_exp' s e)
in FStar_Util.Inr (_100_232))
in (_100_233, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _100_234 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _21_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _100_236; FStar_Absyn_Syntax.effect_args = _100_235; FStar_Absyn_Syntax.flags = _100_234}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _21_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _100_239 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _100_239))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _100_240 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _100_240))
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
let subst_binder = (fun s _21_9 -> (match (_21_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _100_268 = (let _100_267 = (
# 278 "FStar.Absyn.Util.fst"
let _21_423 = a
in (let _100_266 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _21_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _100_266; FStar_Absyn_Syntax.p = _21_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_100_267))
in (_100_268, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _100_271 = (let _100_270 = (
# 279 "FStar.Absyn.Util.fst"
let _21_429 = x
in (let _100_269 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _21_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _100_269; FStar_Absyn_Syntax.p = _21_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_100_270))
in (_100_271, imp))
end))

# 280 "FStar.Absyn.Util.fst"
let subst_arg = (fun s _21_10 -> (match (_21_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _100_275 = (let _100_274 = (subst_typ s t)
in FStar_Util.Inl (_100_274))
in (_100_275, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _100_277 = (let _100_276 = (subst_exp s e)
in FStar_Util.Inr (_100_276))
in (_100_277, imp))
end))

# 283 "FStar.Absyn.Util.fst"
let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _21_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))

# 286 "FStar.Absyn.Util.fst"
let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _21_450 -> begin
(FStar_List.map (subst_arg s) args)
end))

# 289 "FStar.Absyn.Util.fst"
let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _21_456), (FStar_Util.Inl (t), _21_461)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _21_467), (FStar_Util.Inr (v), _21_472)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _21_476 -> begin
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
(let _100_292 = (let _100_291 = (let _100_290 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _100_290))
in FStar_Util.Inl (_100_291))
in (_100_292)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _100_295 = (let _100_294 = (let _100_293 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _100_293))
in FStar_Util.Inr (_100_294))
in (_100_295)::[])
end
end
| _21_490 -> begin
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
(let _100_307 = (let _100_306 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _100_306 out))
in (aux _100_307 bs1 bs2))
end
| _21_508 -> begin
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
let map_knd = (fun s vk mt me descend binders k -> (let _100_328 = (subst_kind' s k)
in (_100_328, descend)))

# 328 "FStar.Absyn.Util.fst"
let map_typ = (fun s mk vt me descend binders t -> (let _100_336 = (subst_typ' s t)
in (_100_336, descend)))

# 330 "FStar.Absyn.Util.fst"
let map_exp = (fun s mk me ve descend binders e -> (let _100_344 = (subst_exp' s e)
in (_100_344, descend)))

# 332 "FStar.Absyn.Util.fst"
let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _21_11 -> (match (_21_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _100_361 = (let _100_360 = (map_exp descend binders e)
in (FStar_All.pipe_right _100_360 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_100_361))
end
| f -> begin
f
end)))))

# 336 "FStar.Absyn.Util.fst"
let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(
# 338 "FStar.Absyn.Util.fst"
let _21_557 = (map_typ descend binders t)
in (match (_21_557) with
| (t, descend) -> begin
(let _100_384 = (FStar_Absyn_Syntax.mk_Total t)
in (_100_384, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 341 "FStar.Absyn.Util.fst"
let _21_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_21_562) with
| (t, descend) -> begin
(
# 342 "FStar.Absyn.Util.fst"
let _21_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_21_565) with
| (args, descend) -> begin
(let _100_387 = (let _100_386 = (
# 343 "FStar.Absyn.Util.fst"
let _21_566 = ct
in (let _100_385 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _21_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _100_385}))
in (FStar_Absyn_Syntax.mk_Comp _100_386))
in (_100_387, descend))
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
let _21_579 = (vk null_ctrl binders k)
in (match (_21_579) with
| (k, _21_578) -> begin
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
let k' = (let _100_433 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _100_433))
in (
# 356 "FStar.Absyn.Util.fst"
let k' = (compress_kind k')
in (
# 357 "FStar.Absyn.Util.fst"
let _21_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _100_435 = (let _100_434 = (subst_of_list formals actuals)
in (subst_kind _100_434 k'))
in (compress_kind _100_435))
end
| _21_602 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _21_604 -> begin
k
end)
end
| _21_606 -> begin
k
end)))

# 374 "FStar.Absyn.Util.fst"
let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (
# 375 "FStar.Absyn.Util.fst"
let visit_prod = (fun bs tc -> (
# 376 "FStar.Absyn.Util.fst"
let _21_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _21_620 b -> (match (_21_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(
# 378 "FStar.Absyn.Util.fst"
let _21_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_21_629) with
| (k, _21_628) -> begin
(
# 379 "FStar.Absyn.Util.fst"
let a = (
# 379 "FStar.Absyn.Util.fst"
let _21_630 = a
in {FStar_Absyn_Syntax.v = _21_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _21_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(
# 383 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (
# 384 "FStar.Absyn.Util.fst"
let _21_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _21_636 -> begin
(
# 387 "FStar.Absyn.Util.fst"
let b = (let _100_512 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _100_512 k))
in (
# 388 "FStar.Absyn.Util.fst"
let s = (let _100_515 = (let _100_514 = (let _100_513 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _100_513))
in FStar_Util.Inl (_100_514))
in (extend_subst _100_515 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_21_642) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(
# 393 "FStar.Absyn.Util.fst"
let _21_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_21_650) with
| (t, _21_649) -> begin
(
# 394 "FStar.Absyn.Util.fst"
let x = (
# 394 "FStar.Absyn.Util.fst"
let _21_651 = x
in {FStar_Absyn_Syntax.v = _21_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _21_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(
# 398 "FStar.Absyn.Util.fst"
let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (
# 399 "FStar.Absyn.Util.fst"
let _21_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _21_657 -> begin
(
# 402 "FStar.Absyn.Util.fst"
let y = (let _100_525 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _100_525 t))
in (
# 403 "FStar.Absyn.Util.fst"
let s = (let _100_528 = (let _100_527 = (let _100_526 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _100_526))
in FStar_Util.Inr (_100_527))
in (extend_subst _100_528 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_21_663) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_21_667) with
| (bs, boundvars, s) -> begin
(
# 407 "FStar.Absyn.Util.fst"
let tc = (match ((s, tc)) with
| ([], _21_670) -> begin
tc
end
| (_21_673, FStar_Util.Inl (t)) -> begin
(let _100_539 = (let _100_538 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _100_538))
in FStar_Util.Inl (_100_539))
end
| (_21_678, FStar_Util.Inr (c)) -> begin
(let _100_562 = (let _100_561 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _100_561))
in FStar_Util.Inr (_100_562))
end)
in ((FStar_List.rev bs), tc))
end)))
in (
# 413 "FStar.Absyn.Util.fst"
let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_21_685) -> begin
(let _100_564 = (let _100_563 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _100_563))
in (_100_564, ctrl))
end
| _21_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _100_574 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_100_574, ctrl))
end
| _21_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _21_706)::[], FStar_Util.Inl (t)) -> begin
(let _100_575 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_100_575, ctrl))
end
| _21_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _100_576 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_100_576, ctrl))
end
| _21_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _21_725 -> begin
(
# 437 "FStar.Absyn.Util.fst"
let _21_729 = (vt null_ctrl boundvars t)
in (match (_21_729) with
| (t, _21_728) -> begin
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
let res = (let _100_596 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _100_596))
in (
# 444 "FStar.Absyn.Util.fst"
let res = (compress_typ' res)
in (
# 445 "FStar.Absyn.Util.fst"
let _21_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(
# 450 "FStar.Absyn.Util.fst"
let t = (let _100_598 = (mk_t ())
in (compress_typ' _100_598))
in (
# 451 "FStar.Absyn.Util.fst"
let _21_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _21_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 457 "FStar.Absyn.Util.fst"
let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_21_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _21_759 -> begin
t
end)))

# 462 "FStar.Absyn.Util.fst"
let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (
# 463 "FStar.Absyn.Util.fst"
let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_21_769) -> begin
(let _100_664 = (let _100_663 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _100_663))
in (_100_664, ctrl))
end
| _21_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _21_774 -> begin
(
# 467 "FStar.Absyn.Util.fst"
let _21_778 = (ve null_ctrl binders e)
in (match (_21_778) with
| (e, _21_777) -> begin
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
let e = (let _100_693 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _100_693))
in (
# 474 "FStar.Absyn.Util.fst"
let res = (compress_exp e)
in (
# 475 "FStar.Absyn.Util.fst"
let _21_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _21_791 -> begin
e
end)))

# 479 "FStar.Absyn.Util.fst"
let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (
# 480 "FStar.Absyn.Util.fst"
let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _21_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _21_802, _21_804) -> begin
(unmeta_exp e)
end
| _21_808 -> begin
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
let doit = (fun t -> (let _100_718 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _100_718)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_21_824) -> begin
(doit t)
end
| _21_827 -> begin
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
| _21_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

# 502 "FStar.Absyn.Util.fst"
let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _21_12 -> (match (_21_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _100_725 = (compress_typ t)
in Some (_100_725))
end))

# 506 "FStar.Absyn.Util.fst"
let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (let _100_730 = (let _100_729 = (let _100_728 = (FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange))
in (_100_728)::[])
in (FStar_List.append lid.FStar_Ident.ns _100_729))
in (FStar_Ident.lid_of_ids _100_730)))

# 509 "FStar.Absyn.Util.fst"
let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (
# 510 "FStar.Absyn.Util.fst"
let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 513 "FStar.Absyn.Util.fst"
let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.comp = (fun t r -> (let _100_738 = (let _100_737 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _100_737; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _100_738)))

# 519 "FStar.Absyn.Util.fst"
let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

# 521 "FStar.Absyn.Util.fst"
let gtotal_comp : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.comp = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

# 529 "FStar.Absyn.Util.fst"
let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_21_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(
# 531 "FStar.Absyn.Util.fst"
let _21_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((
# 531 "FStar.Absyn.Util.fst"
let _21_865 = ct
in {FStar_Absyn_Syntax.effect_name = _21_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _21_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _21_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _21_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _21_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _21_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _21_863.FStar_Absyn_Syntax.uvs})
end))

# 533 "FStar.Absyn.Util.fst"
let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_21_869) -> begin
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
| FStar_Absyn_Syntax.Total (_21_877) -> begin
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
let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _21_13 -> (match (_21_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _21_889 -> begin
false
end)))))

# 549 "FStar.Absyn.Util.fst"
let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _21_14 -> (match (_21_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _21_895 -> begin
false
end))))))

# 551 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _21_15 -> (match (_21_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _21_901 -> begin
false
end))))))

# 555 "FStar.Absyn.Util.fst"
let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _21_16 -> (match (_21_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _21_907 -> begin
false
end)))))

# 557 "FStar.Absyn.Util.fst"
let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _21_17 -> (match (_21_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _21_913 -> begin
false
end)))))

# 559 "FStar.Absyn.Util.fst"
let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

# 563 "FStar.Absyn.Util.fst"
let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_21_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _21_18 -> (match (_21_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _21_924 -> begin
false
end)))))
end))

# 570 "FStar.Absyn.Util.fst"
let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

# 575 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 577 "FStar.Absyn.Util.fst"
let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _21_19 -> (match (_21_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _21_931 -> begin
false
end))))))

# 583 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

# 586 "FStar.Absyn.Util.fst"
let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _100_777 = (compress_typ t)
in _100_777.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_21_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _21_940 -> begin
true
end))

# 590 "FStar.Absyn.Util.fst"
let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _100_780 = (compress_typ t)
in _100_780.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_21_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _21_950 -> begin
false
end)
end
| _21_952 -> begin
false
end))

# 597 "FStar.Absyn.Util.fst"
let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _100_783 = (compress_typ t)
in _100_783.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_21_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _21_966)::_21_962 -> begin
(match ((let _100_784 = (unmeta_exp pats)
in _100_784.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _21_983); FStar_Absyn_Syntax.tk = _21_980; FStar_Absyn_Syntax.pos = _21_978; FStar_Absyn_Syntax.fvs = _21_976; FStar_Absyn_Syntax.uvs = _21_974}, _21_988) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _21_992 -> begin
false
end)
end
| _21_994 -> begin
false
end)
end
| _21_996 -> begin
false
end)
end
| _21_998 -> begin
false
end))

# 611 "FStar.Absyn.Util.fst"
let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _21_20 -> (match (_21_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _21_1005 -> begin
false
end)))))
end
| _21_1007 -> begin
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
| FStar_Absyn_Syntax.Total (_21_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (
# 623 "FStar.Absyn.Util.fst"
let _21_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _21_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _21_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _21_1020.FStar_Absyn_Syntax.flags}))
end))

# 625 "FStar.Absyn.Util.fst"
let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _21_21 -> (match (_21_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _21_1027 -> begin
false
end)))))

# 631 "FStar.Absyn.Util.fst"
let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _100_794 = (compress_exp e)
in _100_794.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _21_1040)) -> begin
(is_atom e)
end
| _21_1045 -> begin
false
end))

# 638 "FStar.Absyn.Util.fst"
let primops : FStar_Absyn_Syntax.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

# 655 "FStar.Absyn.Util.fst"
let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _21_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _21_1053 -> begin
false
end))

# 659 "FStar.Absyn.Util.fst"
let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _21_1057, _21_1059) -> begin
(unascribe e)
end
| _21_1063 -> begin
e
end))

# 663 "FStar.Absyn.Util.fst"
let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _21_1068) -> begin
(ascribe_typ t' k)
end
| _21_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

# 667 "FStar.Absyn.Util.fst"
let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _21_1076) -> begin
(unascribe_typ t)
end
| _21_1080 -> begin
t
end))

# 671 "FStar.Absyn.Util.fst"
let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 672 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _21_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _21_1090) -> begin
(unrefine t)
end
| _21_1094 -> begin
t
end)))

# 678 "FStar.Absyn.Util.fst"
let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _100_808 = (compress_exp e)
in _100_808.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_21_1097) -> begin
true
end
| _21_1100 -> begin
false
end))

# 682 "FStar.Absyn.Util.fst"
let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _100_811 = (compress_typ t)
in _100_811.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_21_1103) -> begin
true
end
| _21_1106 -> begin
false
end))

# 686 "FStar.Absyn.Util.fst"
let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (
# 687 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _21_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _21_1116) -> begin
(pre_typ t)
end
| _21_1120 -> begin
t
end)))

# 693 "FStar.Absyn.Util.fst"
let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (
# 694 "FStar.Absyn.Util.fst"
let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _21_1131; FStar_Absyn_Syntax.pos = _21_1129; FStar_Absyn_Syntax.fvs = _21_1127; FStar_Absyn_Syntax.uvs = _21_1125}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _21_1141 -> begin
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
| FStar_Absyn_Syntax.Sig_new_effect (n, _21_1235) -> begin
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
| _21_1251 -> begin
None
end))

# 719 "FStar.Absyn.Util.fst"
let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 734 "FStar.Absyn.Util.fst"
let range_of_lb = (fun _21_22 -> (match (_21_22) with
| (FStar_Util.Inl (x), _21_1362, _21_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _21_1369, _21_1371) -> begin
(FStar_Ident.range_of_lid l)
end))

# 738 "FStar.Absyn.Util.fst"
let range_of_arg = (fun _21_23 -> (match (_21_23) with
| (FStar_Util.Inl (hd), _21_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _21_1382) -> begin
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
(let _100_844 = (let _100_843 = (let _100_842 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_100_842, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_100_843))
in (FStar_Absyn_Syntax.mk_Exp_meta _100_844))
end
| _21_1398 -> begin
(let _100_848 = (let _100_847 = (let _100_846 = (let _100_845 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _100_845 args))
in (_100_846, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_100_847))
in (FStar_Absyn_Syntax.mk_Exp_meta _100_848))
end))

# 760 "FStar.Absyn.Util.fst"
let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 761 "FStar.Absyn.Util.fst"
let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _100_854 = (let _100_853 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_100_853, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _100_854))
end else begin
x
end)

# 766 "FStar.Absyn.Util.fst"
let mk_field_projector_name = (fun lid x i -> (
# 767 "FStar.Absyn.Util.fst"
let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _100_860 = (let _100_859 = (let _100_858 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _100_858))
in (_100_859, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _100_860))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (
# 770 "FStar.Absyn.Util.fst"
let y = (
# 770 "FStar.Absyn.Util.fst"
let _21_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _21_1407.FStar_Absyn_Syntax.realname})
in (let _100_864 = (let _100_863 = (let _100_862 = (let _100_861 = (unmangle_field_name nm)
in (_100_861)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _100_862))
in (FStar_Ident.lid_of_ids _100_863))
in (_100_864, y)))))

# 773 "FStar.Absyn.Util.fst"
let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_21_1413) -> begin
(let _100_869 = (let _100_868 = (let _100_867 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _100_867))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _100_868))
in (FStar_All.failwith _100_869))
end
| _21_1416 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))

# 782 "FStar.Absyn.Util.fst"
type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)

# 783 "FStar.Absyn.Util.fst"
let no_bvars : (FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set) = (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)

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
| _21_1432 -> begin
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
| _21_1446 -> begin
false
end))

# 798 "FStar.Absyn.Util.fst"
let uv_eq = (fun _21_1450 _21_1454 -> (match ((_21_1450, _21_1454)) with
| ((uv1, _21_1449), (uv2, _21_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

# 799 "FStar.Absyn.Util.fst"
let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _100_886 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _100_885 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _100_884 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _100_886; FStar_Absyn_Syntax.uvars_t = _100_885; FStar_Absyn_Syntax.uvars_e = _100_884}))))

# 805 "FStar.Absyn.Util.fst"
let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _100_892 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _100_891 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _100_892; FStar_Absyn_Syntax.fxvs = _100_891})))

# 811 "FStar.Absyn.Util.fst"
let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _21_1461 _21_1464 -> (match ((_21_1461, _21_1464)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _100_898 = (union_fvs fvs1 fvs2)
in (let _100_897 = (union_uvs uvs1 uvs2)
in (_100_898, _100_897)))
end))

# 815 "FStar.Absyn.Util.fst"
let sub_fv = (fun _21_1467 _21_1470 -> (match ((_21_1467, _21_1470)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _100_903 = (
# 816 "FStar.Absyn.Util.fst"
let _21_1471 = fvs
in (let _100_902 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _100_901 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _100_902; FStar_Absyn_Syntax.fxvs = _100_901})))
in (_100_903, uvs))
end))

# 820 "FStar.Absyn.Util.fst"
let stash = (fun uvonly s _21_1479 -> (match (_21_1479) with
| (fvs, uvs) -> begin
(
# 821 "FStar.Absyn.Util.fst"
let _21_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

# 825 "FStar.Absyn.Util.fst"
let single_fv = (fun x -> (let _100_908 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _100_908)))

# 826 "FStar.Absyn.Util.fst"
let single_uv = (fun u -> (let _100_910 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _100_910)))

# 827 "FStar.Absyn.Util.fst"
let single_uvt = (fun u -> (let _100_912 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _100_912)))

# 829 "FStar.Absyn.Util.fst"
let rec vs_typ' = (fun t uvonly cont -> (
# 830 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_21_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _100_1027 = (let _100_1026 = (
# 836 "FStar.Absyn.Util.fst"
let _21_1495 = FStar_Absyn_Syntax.no_fvs
in (let _100_1025 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _100_1025; FStar_Absyn_Syntax.fxvs = _21_1495.FStar_Absyn_Syntax.fxvs}))
in (_100_1026, FStar_Absyn_Syntax.no_uvs))
in (cont _100_1027))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _100_1030 = (let _100_1029 = (
# 839 "FStar.Absyn.Util.fst"
let _21_1501 = FStar_Absyn_Syntax.no_uvs
in (let _100_1028 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _21_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _100_1028; FStar_Absyn_Syntax.uvars_e = _21_1501.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _100_1029))
in (cont _100_1030))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _21_1513 -> (match (_21_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _100_1034 = (let _100_1033 = (union_fvs_uvs vs1 vs2)
in (sub_fv _100_1033 bvs))
in (cont _100_1034))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _21_1521 -> (match (_21_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _100_1038 = (let _100_1037 = (union_fvs_uvs vs1 vs2)
in (sub_fv _100_1037 bvs))
in (cont _100_1038))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _21_1529 -> (match (_21_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _100_1042 = (let _100_1041 = (union_fvs_uvs vs1 vs2)
in (sub_fv _100_1041 bvs))
in (cont _100_1042))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _100_1045 = (union_fvs_uvs vs1 vs2)
in (cont _100_1045))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _21_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _21_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _100_1048 = (union_fvs_uvs vs1 vs2)
in (cont _100_1048))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _21_1587)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _21_1595 -> (match (_21_1595) with
| ((tvars, vvars), vs2) -> begin
(let _100_1055 = (let _100_1054 = (let _100_1052 = (FStar_Util.set_add a tvars)
in (_100_1052, vvars))
in (let _100_1053 = (union_fvs_uvs vs vs2)
in (_100_1054, _100_1053)))
in (cont _100_1055))
end)))))
end
| (FStar_Util.Inr (x), _21_1600)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _21_1608 -> (match (_21_1608) with
| ((tvars, vvars), vs2) -> begin
(let _100_1061 = (let _100_1060 = (let _100_1058 = (FStar_Util.set_add x vvars)
in (tvars, _100_1058))
in (let _100_1059 = (union_fvs_uvs vs vs2)
in (_100_1060, _100_1059)))
in (cont _100_1061))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _21_1618)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _100_1065 = (union_fvs_uvs ft1 ft2)
in (cont _100_1065))))))
end
| (FStar_Util.Inr (e), _21_1627)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _100_1068 = (union_fvs_uvs ft1 ft2)
in (cont _100_1068))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _100_1071 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _100_1070 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_100_1071, _100_1070)))) with
| (Some (_21_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (
# 911 "FStar.Absyn.Util.fst"
let _21_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (
# 915 "FStar.Absyn.Util.fst"
let _21_1652 = (stash uvonly t fvs)
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
| FStar_Absyn_Syntax.Kind_lam (_21_1665, k) -> begin
(let _100_1076 = (let _100_1075 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _100_1075))
in (FStar_All.failwith _100_1076))
end
| FStar_Absyn_Syntax.Kind_delayed (_21_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _21_1681 -> (match (_21_1681) with
| (fvs, uvs) -> begin
(let _100_1080 = (let _100_1079 = (
# 929 "FStar.Absyn.Util.fst"
let _21_1682 = uvs
in (let _100_1078 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _100_1078; FStar_Absyn_Syntax.uvars_t = _21_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _21_1682.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _100_1079))
in (cont _100_1080))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_21_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _21_1695 -> (match (_21_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _100_1084 = (let _100_1083 = (union_fvs_uvs vs1 vs2)
in (sub_fv _100_1083 bvs))
in (cont _100_1084))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _100_1087 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _100_1086 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_100_1087, _100_1086)))) with
| (Some (_21_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (
# 943 "FStar.Absyn.Util.fst"
let _21_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (
# 947 "FStar.Absyn.Util.fst"
let _21_1717 = (stash uvonly k fvs)
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
| FStar_Absyn_Syntax.Exp_delayed (_21_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _100_1093 = (let _100_1092 = (
# 957 "FStar.Absyn.Util.fst"
let _21_1742 = FStar_Absyn_Syntax.no_uvs
in (let _100_1091 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _21_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _21_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _100_1091}))
in (FStar_Absyn_Syntax.no_fvs, _100_1092))
in (cont _100_1093))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _100_1096 = (let _100_1095 = (
# 962 "FStar.Absyn.Util.fst"
let _21_1746 = FStar_Absyn_Syntax.no_fvs
in (let _100_1094 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _21_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _100_1094}))
in (_100_1095, FStar_Absyn_Syntax.no_uvs))
in (cont _100_1096))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _21_1750, _21_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _21_1761 -> (match (_21_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _100_1100 = (let _100_1099 = (union_fvs_uvs vs1 vs2)
in (sub_fv _100_1099 bvs))
in (cont _100_1100))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _100_1103 = (union_fvs_uvs ft1 ft2)
in (cont _100_1103))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _21_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _100_1106 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _100_1105 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_100_1106, _100_1105)))) with
| (Some (_21_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (
# 986 "FStar.Absyn.Util.fst"
let _21_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (
# 990 "FStar.Absyn.Util.fst"
let _21_1801 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _100_1112 = (union_fvs_uvs vs1 vs2)
in (k _100_1112))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _100_1115 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _100_1114 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_100_1115, _100_1114)))) with
| (Some (_21_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (
# 1007 "FStar.Absyn.Util.fst"
let _21_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (
# 1011 "FStar.Absyn.Util.fst"
let _21_1838 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _100_1122 = (union_fvs_uvs ft1 ft2)
in (cont _100_1122))))))
end))

# 1027 "FStar.Absyn.Util.fst"
let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _21_1867 -> (match (_21_1867) with
| (x, _21_1866) -> begin
x
end))))

# 1030 "FStar.Absyn.Util.fst"
let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _21_1872 -> (match (_21_1872) with
| (x, _21_1871) -> begin
x
end))))

# 1033 "FStar.Absyn.Util.fst"
let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _21_1877 -> (match (_21_1877) with
| (x, _21_1876) -> begin
x
end))))

# 1036 "FStar.Absyn.Util.fst"
let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _21_1882 -> (match (_21_1882) with
| (x, _21_1881) -> begin
x
end))))

# 1039 "FStar.Absyn.Util.fst"
let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _100_1138 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _100_1138))
end
| FStar_Util.Inr (e) -> begin
(let _100_1139 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _100_1139))
end)) FStar_Absyn_Syntax.no_fvs)))

# 1044 "FStar.Absyn.Util.fst"
let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _21_24 -> (match (_21_24) with
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
| SynSumKind (_21_1899) -> begin
_21_1899
end))

# 1051 "FStar.Absyn.Util.fst"
let ___SynSumType____0 = (fun projectee -> (match (projectee) with
| SynSumType (_21_1902) -> begin
_21_1902
end))

# 1052 "FStar.Absyn.Util.fst"
let ___SynSumExp____0 = (fun projectee -> (match (projectee) with
| SynSumExp (_21_1905) -> begin
_21_1905
end))

# 1053 "FStar.Absyn.Util.fst"
let ___SynSumComp____0 = (fun projectee -> (match (projectee) with
| SynSumComp (_21_1908) -> begin
_21_1908
end))

# 1055 "FStar.Absyn.Util.fst"
let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (
# 1056 "FStar.Absyn.Util.fst"
let out = (let _100_1213 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _100_1213 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _100_1211 = (uvars_in_kind k)
in (union_uvs _100_1211 out))
end
| _21_1916 -> begin
(
# 1059 "FStar.Absyn.Util.fst"
let _21_1917 = out
in (let _100_1212 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _100_1212; FStar_Absyn_Syntax.uvars_t = _21_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _21_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (
# 1060 "FStar.Absyn.Util.fst"
let out = (let _100_1218 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _100_1218 (FStar_List.fold_left (fun out _21_1923 -> (match (_21_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _100_1216 = (uvars_in_typ t)
in (union_uvs _100_1216 out))
end
| _21_1927 -> begin
(
# 1063 "FStar.Absyn.Util.fst"
let _21_1928 = out
in (let _100_1217 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _21_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _100_1217; FStar_Absyn_Syntax.uvars_e = _21_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (
# 1064 "FStar.Absyn.Util.fst"
let out = (let _100_1223 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _100_1223 (FStar_List.fold_left (fun out _21_1934 -> (match (_21_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _100_1221 = (uvars_in_exp e)
in (union_uvs _100_1221 out))
end
| _21_1938 -> begin
(
# 1067 "FStar.Absyn.Util.fst"
let _21_1939 = out
in (let _100_1222 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _21_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _21_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _100_1222}))
end)
end)) out)))
in (
# 1068 "FStar.Absyn.Util.fst"
let _21_1950 = (match (s) with
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _100_1226 = (vs_kind k true (fun _21_1956 -> (match (_21_1956) with
| (_21_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _100_1226)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _100_1229 = (vs_typ t true (fun _21_1961 -> (match (_21_1961) with
| (_21_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _100_1229)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _100_1232 = (vs_exp e true (fun _21_1966 -> (match (_21_1966) with
| (_21_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _100_1232)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _100_1235 = (vs_comp c true (fun _21_1971 -> (match (_21_1971) with
| (_21_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _100_1235)))

# 1087 "FStar.Absyn.Util.fst"
let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

# 1095 "FStar.Absyn.Util.fst"
let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (
# 1096 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_21_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(
# 1104 "FStar.Absyn.Util.fst"
let _21_1991 = (kind_formals k)
in (match (_21_1991) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_21_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_21_1998) -> begin
(FStar_All.failwith "Impossible")
end)))

# 1109 "FStar.Absyn.Util.fst"
let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (
# 1110 "FStar.Absyn.Util.fst"
let _21_2005 = (kind_formals k)
in (match (_21_2005) with
| (bs, _21_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _21_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

# 1115 "FStar.Absyn.Util.fst"
let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (
# 1116 "FStar.Absyn.Util.fst"
let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_21_2012, k) -> begin
(unabbreviate_kind k)
end
| _21_2017 -> begin
k
end)))

# 1121 "FStar.Absyn.Util.fst"
let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _21_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

# 1126 "FStar.Absyn.Util.fst"
let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _21_2027 -> begin
(
# 1130 "FStar.Absyn.Util.fst"
let _21_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _21_2033 -> begin
(let _100_1256 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _100_1256))
end)
in (match (_21_2036) with
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
| _21_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

# 1145 "FStar.Absyn.Util.fst"
let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _21_2046 -> begin
false
end))

# 1149 "FStar.Absyn.Util.fst"
let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1150 "FStar.Absyn.Util.fst"
let t = (let _100_1269 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _100_1269))
in (let _100_1270 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _100_1270 r))))

# 1153 "FStar.Absyn.Util.fst"
let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1154 "FStar.Absyn.Util.fst"
let t = (let _100_1275 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _100_1275))
in (let _100_1276 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _100_1276 r))))

# 1157 "FStar.Absyn.Util.fst"
let is_tuple_data_lid : FStar_Absyn_Syntax.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _100_1281 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _100_1281)))

# 1160 "FStar.Absyn.Util.fst"
let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _21_2059 -> begin
false
end))

# 1164 "FStar.Absyn.Util.fst"
let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1165 "FStar.Absyn.Util.fst"
let t = (let _100_1288 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _100_1288))
in (let _100_1289 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _100_1289 r))))

# 1168 "FStar.Absyn.Util.fst"
let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (
# 1169 "FStar.Absyn.Util.fst"
let t = (let _100_1294 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _100_1294))
in (let _100_1295 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _100_1295 r))))

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
let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _100_1311 = (pre_typ t)
in _100_1311.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _21_2078 -> begin
false
end))

# 1194 "FStar.Absyn.Util.fst"
let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _100_1316 = (pre_typ t)
in _100_1316.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_21_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _21_2086) -> begin
(is_constructed_typ t lid)
end
| _21_2090 -> begin
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
| FStar_Absyn_Syntax.Typ_app (t, _21_2101) -> begin
(get_tycon t)
end
| _21_2105 -> begin
None
end)))

# 1207 "FStar.Absyn.Util.fst"
let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _21_25 -> (match (_21_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _21_2109 -> begin
false
end))

# 1211 "FStar.Absyn.Util.fst"
let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _21_2115 _21_2119 -> (match ((_21_2115, _21_2119)) with
| ((fn1, _21_2114), (fn2, _21_2118)) -> begin
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
let b2t_v : FStar_Absyn_Syntax.typ = (let _100_1327 = (let _100_1326 = (let _100_1325 = (let _100_1324 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_100_1324)::[])
in (_100_1325, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1326 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _100_1327))

# 1231 "FStar.Absyn.Util.fst"
let mk_conj_opt : FStar_Absyn_Syntax.typ Prims.option  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _100_1338 = (let _100_1337 = (let _100_1335 = (let _100_1334 = (FStar_Absyn_Syntax.targ phi1)
in (let _100_1333 = (let _100_1332 = (FStar_Absyn_Syntax.targ phi2)
in (_100_1332)::[])
in (_100_1334)::_100_1333))
in (tand, _100_1335))
in (let _100_1336 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _100_1337 None _100_1336)))
in Some (_100_1338))
end))

# 1234 "FStar.Absyn.Util.fst"
let mk_binop : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _100_1350 = (let _100_1348 = (let _100_1347 = (FStar_Absyn_Syntax.targ phi1)
in (let _100_1346 = (let _100_1345 = (FStar_Absyn_Syntax.targ phi2)
in (_100_1345)::[])
in (_100_1347)::_100_1346))
in (op_t, _100_1348))
in (let _100_1349 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _100_1350 None _100_1349))))

# 1235 "FStar.Absyn.Util.fst"
let mk_neg : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _100_1356 = (let _100_1355 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (let _100_1354 = (let _100_1353 = (FStar_Absyn_Syntax.targ phi)
in (_100_1353)::[])
in (_100_1355, _100_1354)))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1356 None phi.FStar_Absyn_Syntax.pos)))

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
let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (match ((let _100_1373 = (compress_typ phi1)
in _100_1373.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _21_2150 -> begin
(match ((let _100_1374 = (compress_typ phi2)
in _100_1374.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _21_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 1254 "FStar.Absyn.Util.fst"
let mk_iff : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 1255 "FStar.Absyn.Util.fst"
let b2t : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _100_1383 = (let _100_1382 = (let _100_1381 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_100_1381)::[])
in (b2t_v, _100_1382))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1383 None e.FStar_Absyn_Syntax.pos)))

# 1257 "FStar.Absyn.Util.fst"
let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (
# 1258 "FStar.Absyn.Util.fst"
let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _21_2194)) -> begin
(mk_conj t1 t2)
end
| _21_2199 -> begin
t
end)))

# 1269 "FStar.Absyn.Util.fst"
let eq_k : FStar_Absyn_Syntax.knd = (
# 1270 "FStar.Absyn.Util.fst"
let a = (let _100_1386 = (new_bvd None)
in (bvd_to_bvar_s _100_1386 FStar_Absyn_Syntax.ktype))
in (
# 1271 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (
# 1272 "FStar.Absyn.Util.fst"
let b = (let _100_1387 = (new_bvd None)
in (bvd_to_bvar_s _100_1387 FStar_Absyn_Syntax.ktype))
in (
# 1273 "FStar.Absyn.Util.fst"
let btyp = (btvar_to_typ b)
in (let _100_1394 = (let _100_1393 = (let _100_1392 = (let _100_1391 = (let _100_1390 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (let _100_1389 = (let _100_1388 = (FStar_Absyn_Syntax.null_v_binder btyp)
in (_100_1388)::[])
in (_100_1390)::_100_1389))
in ((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit (false))))::_100_1391)
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_100_1392)
in (_100_1393, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1394 FStar_Absyn_Syntax.dummyRange))))))

# 1277 "FStar.Absyn.Util.fst"
let teq : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eq2_lid eq_k)

# 1278 "FStar.Absyn.Util.fst"
let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _21_2217 -> begin
(let _100_1412 = (let _100_1410 = (let _100_1409 = (FStar_Absyn_Syntax.itarg t1)
in (let _100_1408 = (let _100_1407 = (FStar_Absyn_Syntax.itarg t2)
in (let _100_1406 = (let _100_1405 = (FStar_Absyn_Syntax.varg e1)
in (let _100_1404 = (let _100_1403 = (FStar_Absyn_Syntax.varg e2)
in (_100_1403)::[])
in (_100_1405)::_100_1404))
in (_100_1407)::_100_1406))
in (_100_1409)::_100_1408))
in (teq, _100_1410))
in (let _100_1411 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _100_1412 None _100_1411)))
end))

# 1282 "FStar.Absyn.Util.fst"
let eq_typ : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

# 1283 "FStar.Absyn.Util.fst"
let mk_eq_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _100_1422 = (let _100_1420 = (let _100_1419 = (FStar_Absyn_Syntax.targ t1)
in (let _100_1418 = (let _100_1417 = (FStar_Absyn_Syntax.targ t2)
in (_100_1417)::[])
in (_100_1419)::_100_1418))
in (eq_typ, _100_1420))
in (let _100_1421 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app _100_1422 None _100_1421))))

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
let lexcons = (let _100_1432 = (let _100_1431 = (let _100_1430 = (let _100_1428 = (FStar_Absyn_Syntax.t_binder a)
in (let _100_1427 = (let _100_1426 = (let _100_1423 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _100_1423))
in (let _100_1425 = (let _100_1424 = (FStar_Absyn_Syntax.null_v_binder lex_t)
in (_100_1424)::[])
in (_100_1426)::_100_1425))
in (_100_1428)::_100_1427))
in (let _100_1429 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_100_1430, _100_1429)))
in (FStar_Absyn_Syntax.mk_Typ_fun _100_1431 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _100_1432 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

# 1295 "FStar.Absyn.Util.fst"
let forall_kind : FStar_Absyn_Syntax.knd = (
# 1296 "FStar.Absyn.Util.fst"
let a = (let _100_1433 = (new_bvd None)
in (bvd_to_bvar_s _100_1433 FStar_Absyn_Syntax.ktype))
in (
# 1297 "FStar.Absyn.Util.fst"
let atyp = (btvar_to_typ a)
in (let _100_1441 = (let _100_1440 = (let _100_1439 = (let _100_1438 = (let _100_1437 = (let _100_1436 = (let _100_1435 = (let _100_1434 = (FStar_Absyn_Syntax.null_v_binder atyp)
in (_100_1434)::[])
in (_100_1435, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1436 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _100_1437))
in (_100_1438)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_100_1439)
in (_100_1440, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1441 FStar_Absyn_Syntax.dummyRange))))

# 1302 "FStar.Absyn.Util.fst"
let tforall : FStar_Absyn_Syntax.typ = (ftv FStar_Absyn_Const.forall_lid forall_kind)

# 1304 "FStar.Absyn.Util.fst"
let allT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _100_1450 = (let _100_1449 = (let _100_1448 = (let _100_1447 = (let _100_1446 = (let _100_1445 = (let _100_1444 = (FStar_Absyn_Syntax.null_t_binder k)
in (_100_1444)::[])
in (_100_1445, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1446 FStar_Absyn_Syntax.dummyRange))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _100_1447))
in (_100_1448)::[])
in (_100_1449, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1450 FStar_Absyn_Syntax.dummyRange)))

# 1305 "FStar.Absyn.Util.fst"
let eqT_k : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _100_1457 = (let _100_1456 = (let _100_1455 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (let _100_1454 = (let _100_1453 = (FStar_Absyn_Syntax.null_t_binder k)
in (_100_1453)::[])
in (_100_1455)::_100_1454))
in (_100_1456, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _100_1457 FStar_Absyn_Syntax.dummyRange)))

# 1307 "FStar.Absyn.Util.fst"
let tforall_typ : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.typ = (fun k -> (let _100_1460 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _100_1460)))

# 1309 "FStar.Absyn.Util.fst"
let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _100_1472 = (let _100_1471 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _100_1470 = (let _100_1469 = (let _100_1468 = (let _100_1467 = (let _100_1466 = (let _100_1465 = (FStar_Absyn_Syntax.t_binder a)
in (_100_1465)::[])
in (_100_1466, b))
in (FStar_Absyn_Syntax.mk_Typ_lam _100_1467 None b.FStar_Absyn_Syntax.pos))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _100_1468))
in (_100_1469)::[])
in (_100_1471, _100_1470)))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1472 None b.FStar_Absyn_Syntax.pos)))

# 1312 "FStar.Absyn.Util.fst"
let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (
# 1313 "FStar.Absyn.Util.fst"
let r = FStar_Absyn_Syntax.dummyRange
in (let _100_1483 = (let _100_1482 = (let _100_1481 = (let _100_1480 = (let _100_1479 = (let _100_1478 = (let _100_1477 = (FStar_Absyn_Syntax.v_binder x)
in (_100_1477)::[])
in (_100_1478, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _100_1479 None r))
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _100_1480))
in (_100_1481)::[])
in (tforall, _100_1482))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1483 None r))))

# 1316 "FStar.Absyn.Util.fst"
let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(
# 1320 "FStar.Absyn.Util.fst"
let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _100_1493 = (let _100_1492 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _100_1491 = (let _100_1490 = (FStar_Absyn_Syntax.targ body)
in (_100_1490)::[])
in (_100_1492, _100_1491)))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1493 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(let _100_1497 = (let _100_1496 = (let _100_1495 = (let _100_1494 = (FStar_Absyn_Syntax.targ body)
in (_100_1494)::[])
in ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit (false))))::_100_1495)
in (tforall, _100_1496))
in (FStar_Absyn_Syntax.mk_Typ_app _100_1497 None f.FStar_Absyn_Syntax.pos))
end))
end) bs f))

# 1325 "FStar.Absyn.Util.fst"
let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_21_2244) -> begin
true
end
| _21_2247 -> begin
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
| _21_2255 -> begin
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
| _21_2263 -> begin
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
| _21_2271 -> begin
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
| QAll (_21_2276) -> begin
_21_2276
end))

# 1373 "FStar.Absyn.Util.fst"
let ___QEx____0 = (fun projectee -> (match (projectee) with
| QEx (_21_2279) -> begin
_21_2279
end))

# 1374 "FStar.Absyn.Util.fst"
let ___BaseConn____0 = (fun projectee -> (match (projectee) with
| BaseConn (_21_2282) -> begin
_21_2282
end))

# 1376 "FStar.Absyn.Util.fst"
let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (
# 1377 "FStar.Absyn.Util.fst"
let destruct_base_conn = (fun f -> (
# 1378 "FStar.Absyn.Util.fst"
let _21_2288 = (true, false)
in (match (_21_2288) with
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
let rec aux = (fun f _21_2298 -> (match (_21_2298) with
| (lid, arity) -> begin
(
# 1396 "FStar.Absyn.Util.fst"
let _21_2301 = (head_and_args f)
in (match (_21_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_21_2305), _21_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_21_2311), _21_2314) -> begin
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
(let _100_1561 = (compress_typ t)
in (pats, _100_1561))
end
| _21_2325 -> begin
(let _100_1562 = (compress_typ t)
in ([], _100_1562))
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
let _21_2335 = (head_and_args t)
in (match (_21_2335) with
| (t, args) -> begin
(let _100_1576 = (FStar_All.pipe_right args (FStar_List.map (fun _21_26 -> (match (_21_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _100_1573 = (let _100_1572 = (compress_typ t)
in FStar_Util.Inl (_100_1572))
in (_100_1573, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _100_1575 = (let _100_1574 = (compress_exp e)
in FStar_Util.Inr (_100_1574))
in (_100_1575, imp))
end))))
in (t, _100_1576))
end)))
in (
# 1418 "FStar.Absyn.Util.fst"
let rec aux = (fun qopt out t -> (match ((let _100_1583 = (flat t)
in (qopt, _100_1583))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _21_2483) -> begin
(
# 1430 "FStar.Absyn.Util.fst"
let _21_2487 = (patterns t)
in (match (_21_2487) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _21_2491) -> begin
(
# 1434 "FStar.Absyn.Util.fst"
let _21_2495 = (patterns t)
in (match (_21_2495) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _21_2497 -> begin
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





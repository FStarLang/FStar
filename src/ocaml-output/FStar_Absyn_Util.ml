
open Prims
# 28 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let handle_err : Prims.bool  ->  Prims.unit  ->  Prims.exn  ->  Prims.unit = (fun warning ret e -> (match (e) with
| FStar_Util.Failure (s) -> begin
(let _130_7 = (FStar_Util.format1 "Fatal: %s" s)
in (FStar_Util.print_string _130_7))
end
| FStar_Absyn_Syntax.Error (msg, r) -> begin
(let _28_36 = (let _130_9 = (let _130_8 = (FStar_Range.string_of_range r)
in (FStar_Util.format3 "%s : %s\n%s\n" _130_8 (if warning then begin
"Warning"
end else begin
"Error"
end) msg))
in (FStar_Util.print_string _130_9))
in ())
end
| FStar_Util.NYI (s) -> begin
(let _28_40 = (let _130_10 = (FStar_Util.format1 "Feature not yet implemented: %s" s)
in (FStar_Util.print_string _130_10))
in ())
end
| FStar_Absyn_Syntax.Err (s) -> begin
(let _130_11 = (FStar_Util.format1 "Error: %s" s)
in (FStar_Util.print_string _130_11))
end
| _28_45 -> begin
(Prims.raise e)
end))

# 42 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let handleable : Prims.exn  ->  Prims.bool = (fun _28_1 -> (match (_28_1) with
| (FStar_Util.Failure (_)) | (FStar_Absyn_Syntax.Error (_)) | (FStar_Util.NYI (_)) | (FStar_Absyn_Syntax.Err (_)) -> begin
true
end
| _28_60 -> begin
false
end))

# 53 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type gensym_t =
{gensym : Prims.unit  ->  Prims.string; reset : Prims.unit  ->  Prims.unit}

# 53 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_Mkgensym_t : gensym_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkgensym_t"))))

# 57 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let gs : gensym_t = (let ctr = (FStar_Util.mk_ref 0)
in (let n_resets = (FStar_Util.mk_ref 0)
in {gensym = (fun _28_66 -> (match (()) with
| () -> begin
(let _130_39 = (let _130_36 = (let _130_35 = (let _130_34 = (FStar_ST.read n_resets)
in (FStar_Util.string_of_int _130_34))
in (Prims.strcat "_" _130_35))
in (Prims.strcat _130_36 "_"))
in (let _130_38 = (let _130_37 = (let _28_67 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
in (FStar_Util.string_of_int _130_37))
in (Prims.strcat _130_39 _130_38)))
end)); reset = (fun _28_69 -> (match (()) with
| () -> begin
(let _28_70 = (FStar_ST.op_Colon_Equals ctr 0)
in (FStar_Util.incr n_resets))
end))}))

# 62 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let gensym : Prims.unit  ->  Prims.string = (fun _28_72 -> (match (()) with
| () -> begin
(gs.gensym ())
end))

# 63 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let reset_gensym : Prims.unit  ->  Prims.unit = (fun _28_73 -> (match (()) with
| () -> begin
(gs.reset ())
end))

# 64 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec gensyms : Prims.int  ->  Prims.string Prims.list = (fun x -> (match (x) with
| 0 -> begin
[]
end
| n -> begin
(let _130_48 = (gensym ())
in (let _130_47 = (gensyms (n - 1))
in (_130_48)::_130_47))
end))

# 68 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let genident : FStar_Range.range Prims.option  ->  FStar_Ident.ident = (fun r -> (let sym = (gensym ())
in (match (r) with
| None -> begin
(FStar_Ident.mk_ident (sym, FStar_Absyn_Syntax.dummyRange))
end
| Some (r) -> begin
(FStar_Ident.mk_ident (sym, r))
end)))

# 74 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvd_eq = (fun bvd1 bvd2 -> (bvd1.FStar_Absyn_Syntax.realname.FStar_Ident.idText = bvd2.FStar_Absyn_Syntax.realname.FStar_Ident.idText))

# 75 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let range_of_bvd = (fun x -> x.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange)

# 76 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mkbvd = (fun _28_87 -> (match (_28_87) with
| (x, y) -> begin
{FStar_Absyn_Syntax.ppname = x; FStar_Absyn_Syntax.realname = y}
end))

# 78 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let setsort = (fun w t -> {FStar_Absyn_Syntax.v = w.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = w.FStar_Absyn_Syntax.p})

# 79 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let withinfo = (fun e s r -> {FStar_Absyn_Syntax.v = e; FStar_Absyn_Syntax.sort = s; FStar_Absyn_Syntax.p = r})

# 80 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let withsort = (fun e s -> (withinfo e s FStar_Absyn_Syntax.dummyRange))

# 81 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvar_ppname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname)

# 82 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvar_realname = (fun bv -> bv.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.realname)

# 83 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvar_eq = (fun bv1 bv2 -> (bvd_eq bv1.FStar_Absyn_Syntax.v bv2.FStar_Absyn_Syntax.v))

# 84 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lbname_eq = (fun l1 l2 -> (match ((l1, l2)) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(bvd_eq x y)
end
| (FStar_Util.Inr (l), FStar_Util.Inr (m)) -> begin
(FStar_Ident.lid_equals l m)
end
| _28_114 -> begin
false
end))

# 88 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let fvar_eq = (fun fv1 fv2 -> (FStar_Ident.lid_equals fv1.FStar_Absyn_Syntax.v fv2.FStar_Absyn_Syntax.v))

# 89 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvd_to_bvar_s = (fun bvd sort -> {FStar_Absyn_Syntax.v = bvd; FStar_Absyn_Syntax.sort = sort; FStar_Absyn_Syntax.p = bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idRange})

# 90 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvar_to_bvd = (fun bv -> bv.FStar_Absyn_Syntax.v)

# 91 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let btvar_to_typ : FStar_Absyn_Syntax.btvar  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun bv -> (FStar_Absyn_Syntax.mk_Typ_btvar bv None bv.FStar_Absyn_Syntax.p))

# 92 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvd_to_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun bvd k -> (btvar_to_typ (bvd_to_bvar_s bvd k)))

# 93 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvar_to_exp : FStar_Absyn_Syntax.bvvar  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun bv -> (FStar_Absyn_Syntax.mk_Exp_bvar bv None bv.FStar_Absyn_Syntax.p))

# 94 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvd_to_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun bvd t -> (bvar_to_exp (bvd_to_bvar_s bvd t)))

# 95 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let new_bvd = (fun ropt -> (let f = (fun ropt -> (let id = (genident ropt)
in (mkbvd (id, id))))
in (f ropt)))

# 98 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freshen_bvd = (fun bvd' -> (let _130_89 = (let _130_88 = (genident (Some ((range_of_bvd bvd'))))
in (bvd'.FStar_Absyn_Syntax.ppname, _130_88))
in (mkbvd _130_89)))

# 99 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freshen_bvar = (fun b -> (let _130_91 = (freshen_bvd b.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _130_91 b.FStar_Absyn_Syntax.sort)))

# 100 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let gen_bvar = (fun sort -> (let bvd = (new_bvd None)
in (bvd_to_bvar_s bvd sort)))

# 101 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let gen_bvar_p = (fun r sort -> (let bvd = (new_bvd (Some (r)))
in (bvd_to_bvar_s bvd sort)))

# 102 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let bvdef_of_str = (fun s -> (let f = (fun s -> (let id = (FStar_Ident.id_of_text s)
in (mkbvd (id, id))))
in (f s)))

# 105 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let set_bvd_range = (fun bvd r -> {FStar_Absyn_Syntax.ppname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.ppname.FStar_Ident.idText, r)); FStar_Absyn_Syntax.realname = (FStar_Ident.mk_ident (bvd.FStar_Absyn_Syntax.realname.FStar_Ident.idText, r))})

# 107 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let set_lid_range : FStar_Ident.lident  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun l r -> (let ids = (FStar_All.pipe_right (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[])) (FStar_List.map (fun i -> (FStar_Ident.mk_ident (i.FStar_Ident.idText, r)))))
in (FStar_Ident.lid_of_ids ids)))

# 110 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let fv : FStar_Ident.lid  ->  (FStar_Ident.lid, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t = (fun l -> (withinfo l FStar_Absyn_Syntax.tun (FStar_Ident.range_of_lid l)))

# 111 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let fvvar_of_lid = (fun l t -> (withinfo l t (FStar_Ident.range_of_lid l)))

# 112 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let fvar : FStar_Absyn_Syntax.fv_qual Prims.option  ->  FStar_Ident.lident  ->  FStar_Range.range  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun dc l r -> (let _130_116 = (let _130_115 = (let _130_114 = (set_lid_range l r)
in (fv _130_114))
in (_130_115, dc))
in (FStar_Absyn_Syntax.mk_Exp_fvar _130_116 None r)))

# 113 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ftv : FStar_Ident.lid  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun l k -> (FStar_Absyn_Syntax.mk_Typ_const (withinfo l k (FStar_Ident.range_of_lid l)) None (FStar_Ident.range_of_lid l)))

# 114 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let order_bvd = (fun x y -> (match ((x, y)) with
| (FStar_Util.Inl (_28_160), FStar_Util.Inr (_28_163)) -> begin
(- (1))
end
| (FStar_Util.Inr (_28_167), FStar_Util.Inl (_28_170)) -> begin
1
end
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_String.compare x.FStar_Absyn_Syntax.ppname.FStar_Ident.idText y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText)
end))

# 119 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let arg_of_non_null_binder = (fun _28_185 -> (match (_28_185) with
| (b, imp) -> begin
(match (b) with
| FStar_Util.Inl (a) -> begin
(let _130_125 = (let _130_124 = (btvar_to_typ a)
in FStar_Util.Inl (_130_124))
in (_130_125, imp))
end
| FStar_Util.Inr (x) -> begin
(let _130_127 = (let _130_126 = (bvar_to_exp x)
in FStar_Util.Inr (_130_126))
in (_130_127, imp))
end)
end))

# 123 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let args_of_non_null_binders : FStar_Absyn_Syntax.binders  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.collect (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
[]
end else begin
(let _130_131 = (arg_of_non_null_binder b)
in (_130_131)::[])
end))))

# 127 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let args_of_binders : FStar_Absyn_Syntax.binders  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun binders -> (let _130_141 = (FStar_All.pipe_right binders (FStar_List.map (fun b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(let b = (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _130_136 = (let _130_135 = (gen_bvar a.FStar_Absyn_Syntax.sort)
in FStar_Util.Inl (_130_135))
in (_130_136, (Prims.snd b)))
end
| FStar_Util.Inr (x) -> begin
(let _130_138 = (let _130_137 = (gen_bvar x.FStar_Absyn_Syntax.sort)
in FStar_Util.Inr (_130_137))
in (_130_138, (Prims.snd b)))
end)
in (let _130_139 = (arg_of_non_null_binder b)
in (b, _130_139)))
end else begin
(let _130_140 = (arg_of_non_null_binder b)
in (b, _130_140))
end)))
in (FStar_All.pipe_right _130_141 FStar_List.unzip)))

# 140 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let name_binders : FStar_Absyn_Syntax.binder Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun binders -> (FStar_All.pipe_right binders (FStar_List.mapi (fun i b -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let b = (let _130_147 = (let _130_146 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _130_146))
in (FStar_Ident.id_of_text _130_147))
in (let b = (bvd_to_bvar_s (mkbvd (b, b)) a.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inl (b), imp)))
end
| (FStar_Util.Inr (y), imp) -> begin
(let x = (let _130_149 = (let _130_148 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _130_148))
in (FStar_Ident.id_of_text _130_149))
in (let x = (bvd_to_bvar_s (mkbvd (x, x)) y.FStar_Absyn_Syntax.sort)
in (FStar_Util.Inr (x), imp)))
end)
end else begin
b
end))))

# 155 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let name_function_binders : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, comp) -> begin
(let _130_153 = (let _130_152 = (name_binders binders)
in (_130_152, comp))
in (FStar_Absyn_Syntax.mk_Typ_fun _130_153 None t.FStar_Absyn_Syntax.pos))
end
| _28_220 -> begin
t
end))

# 158 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let null_binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _28_2 -> (match (_28_2) with
| (FStar_Util.Inl (k), imp) -> begin
(let _130_157 = (FStar_All.pipe_left Prims.fst (FStar_Absyn_Syntax.null_t_binder k))
in (_130_157, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _130_158 = (FStar_All.pipe_left Prims.fst (FStar_Absyn_Syntax.null_v_binder t))
in (_130_158, imp))
end)))))

# 162 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let binders_of_tks : ((FStar_Absyn_Syntax.knd, FStar_Absyn_Syntax.typ) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) Prims.list = (fun tks -> (FStar_All.pipe_right tks (FStar_List.map (fun _28_3 -> (match (_28_3) with
| (FStar_Util.Inl (k), imp) -> begin
(let _130_163 = (let _130_162 = (gen_bvar_p k.FStar_Absyn_Syntax.pos k)
in FStar_Util.Inl (_130_162))
in (_130_163, imp))
end
| (FStar_Util.Inr (t), imp) -> begin
(let _130_165 = (let _130_164 = (gen_bvar_p t.FStar_Absyn_Syntax.pos t)
in FStar_Util.Inr (_130_164))
in (_130_165, imp))
end)))))

# 167 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let binders_of_freevars : FStar_Absyn_Syntax.freevars  ->  ((FStar_Absyn_Syntax.btvar, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun fvs -> (let _130_171 = (let _130_168 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.ftvs)
in (FStar_All.pipe_right _130_168 (FStar_List.map FStar_Absyn_Syntax.t_binder)))
in (let _130_170 = (let _130_169 = (FStar_Util.set_elements fvs.FStar_Absyn_Syntax.fxvs)
in (FStar_All.pipe_right _130_169 (FStar_List.map FStar_Absyn_Syntax.v_binder)))
in (FStar_List.append _130_171 _130_170))))

# 174 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_to_string = (fun s -> (let _130_174 = (FStar_All.pipe_right s (FStar_List.map (fun _28_4 -> (match (_28_4) with
| FStar_Util.Inl (b, _28_246) -> begin
b.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end
| FStar_Util.Inr (x, _28_251) -> begin
x.FStar_Absyn_Syntax.realname.FStar_Ident.idText
end))))
in (FStar_All.pipe_right _130_174 (FStar_String.concat ", "))))

# 177 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_tvar = (fun s a -> (FStar_Util.find_map s (fun _28_5 -> (match (_28_5) with
| FStar_Util.Inl (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _28_262 -> begin
None
end))))

# 178 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_xvar = (fun s a -> (FStar_Util.find_map s (fun _28_6 -> (match (_28_6) with
| FStar_Util.Inr (b, t) when (bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some (t)
end
| _28_271 -> begin
None
end))))

# 179 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec subst_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_typ t)
end
| _28_278 -> begin
(let t0 = (FStar_Absyn_Visit.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _130_199 = (let _130_198 = (compose_subst s' s)
in (let _130_197 = (FStar_Util.mk_ref None)
in (t', _130_198, _130_197)))
in (FStar_Absyn_Syntax.mk_Typ_delayed _130_199 None t.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (mk_t ())
in (let _28_293 = (FStar_ST.op_Colon_Equals m (Some (t)))
in (subst_typ' s t)))
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let rec aux = (fun s' -> (match (s') with
| s0::rest -> begin
(match ((subst_tvar s0 a)) with
| Some (t) -> begin
(subst_typ' rest t)
end
| _28_305 -> begin
(aux rest)
end)
end
| _28_307 -> begin
t0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) -> begin
t0
end
| _28_316 -> begin
(let _130_204 = (let _130_203 = (FStar_Util.mk_ref None)
in (t0, s, _130_203))
in (FStar_Absyn_Syntax.mk_Typ_delayed _130_204 None t.FStar_Absyn_Syntax.pos))
end))
end))
and subst_exp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s e -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_exp e)
end
| _28_323 -> begin
(let e0 = (FStar_Absyn_Visit.compress_exp e)
in (match (e0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e, s', m) -> begin
(let _130_209 = (let _130_208 = (compose_subst s' s)
in (let _130_207 = (FStar_Util.mk_ref None)
in (e, _130_208, _130_207)))
in (FStar_Absyn_Syntax.mk_Exp_delayed _130_209 None e.FStar_Absyn_Syntax.pos))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let rec aux = (fun s -> (match (s) with
| s0::rest -> begin
(match ((subst_xvar s0 x)) with
| Some (e) -> begin
(subst_exp' rest e)
end
| _28_340 -> begin
(aux rest)
end)
end
| _28_342 -> begin
e0
end))
in (aux s))
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_uvar (_)) -> begin
e0
end
| _28_350 -> begin
(let _130_213 = (let _130_212 = (FStar_Util.mk_ref None)
in (e0, s, _130_212))
in (FStar_Absyn_Syntax.mk_Exp_delayed _130_213 None e0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_kind' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s k -> (match (s) with
| ([]) | ([]::[]) -> begin
(FStar_Absyn_Visit.compress_kind k)
end
| _28_357 -> begin
(let k0 = (FStar_Absyn_Visit.compress_kind k)
in (match (k0.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_unknown) -> begin
k0
end
| FStar_Absyn_Syntax.Kind_delayed (k, s', m) -> begin
(let _130_218 = (let _130_217 = (compose_subst s' s)
in (let _130_216 = (FStar_Util.mk_ref None)
in (k, _130_217, _130_216)))
in (FStar_Absyn_Syntax.mk_Kind_delayed _130_218 k0.FStar_Absyn_Syntax.pos))
end
| _28_368 -> begin
(let _130_220 = (let _130_219 = (FStar_Util.mk_ref None)
in (k0, s, _130_219))
in (FStar_Absyn_Syntax.mk_Kind_delayed _130_220 k0.FStar_Absyn_Syntax.pos))
end))
end))
and subst_flags' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _28_7 -> (match (_28_7) with
| FStar_Absyn_Syntax.DECREASES (a) -> begin
(let _130_224 = (subst_exp' s a)
in FStar_Absyn_Syntax.DECREASES (_130_224))
end
| f -> begin
f
end)))))
and subst_comp_typ' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  FStar_Absyn_Syntax.comp_typ  ->  FStar_Absyn_Syntax.comp_typ = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _28_381 -> begin
(let _28_382 = t
in (let _130_234 = (subst_typ' s t.FStar_Absyn_Syntax.result_typ)
in (let _130_233 = (FStar_List.map (fun _28_8 -> (match (_28_8) with
| (FStar_Util.Inl (t), imp) -> begin
(let _130_229 = (let _130_228 = (subst_typ' s t)
in FStar_Util.Inl (_130_228))
in (_130_229, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _130_231 = (let _130_230 = (subst_exp' s e)
in FStar_Util.Inr (_130_230))
in (_130_231, imp))
end)) t.FStar_Absyn_Syntax.effect_args)
in (let _130_232 = (subst_flags' s t.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _28_382.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _130_234; FStar_Absyn_Syntax.effect_args = _130_233; FStar_Absyn_Syntax.flags = _130_232}))))
end))
and subst_comp' : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (match (s) with
| ([]) | ([]::[]) -> begin
t
end
| _28_399 -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _130_237 = (subst_typ' s t)
in (FStar_Absyn_Syntax.mk_Total _130_237))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _130_238 = (subst_comp_typ' s ct)
in (FStar_Absyn_Syntax.mk_Comp _130_238))
end)
end))
and compose_subst : FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t  ->  FStar_Absyn_Syntax.subst_t = (fun s1 s2 -> (FStar_List.append s1 s2))

# 271 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_subst = (fun s -> (s)::[])

# 272 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_kind : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun s t -> (subst_kind' (mk_subst s) t))

# 273 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_typ' (mk_subst s) t))

# 274 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_exp' (mk_subst s) t))

# 275 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_flags : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.cflags Prims.list = (fun s t -> (subst_flags' (mk_subst s) t))

# 276 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_comp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun s t -> (subst_comp' (mk_subst s) t))

# 277 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_binder = (fun s _28_9 -> (match (_28_9) with
| (FStar_Util.Inl (a), imp) -> begin
(let _130_266 = (let _130_265 = (let _28_423 = a
in (let _130_264 = (subst_kind s a.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _28_423.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _130_264; FStar_Absyn_Syntax.p = _28_423.FStar_Absyn_Syntax.p}))
in FStar_Util.Inl (_130_265))
in (_130_266, imp))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _130_269 = (let _130_268 = (let _28_429 = x
in (let _130_267 = (subst_typ s x.FStar_Absyn_Syntax.sort)
in {FStar_Absyn_Syntax.v = _28_429.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = _130_267; FStar_Absyn_Syntax.p = _28_429.FStar_Absyn_Syntax.p}))
in FStar_Util.Inr (_130_268))
in (_130_269, imp))
end))

# 280 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_arg = (fun s _28_10 -> (match (_28_10) with
| (FStar_Util.Inl (t), imp) -> begin
(let _130_273 = (let _130_272 = (subst_typ s t)
in FStar_Util.Inl (_130_272))
in (_130_273, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _130_275 = (let _130_274 = (subst_exp s e)
in FStar_Util.Inr (_130_274))
in (_130_275, imp))
end))

# 283 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_binders = (fun s bs -> (match (s) with
| [] -> begin
bs
end
| _28_445 -> begin
(FStar_List.map (subst_binder s) bs)
end))

# 286 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_args = (fun s args -> (match (s) with
| [] -> begin
args
end
| _28_450 -> begin
(FStar_List.map (subst_arg s) args)
end))

# 289 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_formal : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.arg  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either = (fun f a -> (match ((f, a)) with
| ((FStar_Util.Inl (a), _28_456), (FStar_Util.Inl (t), _28_461)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, t))
end
| ((FStar_Util.Inr (x), _28_467), (FStar_Util.Inr (v), _28_472)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, v))
end
| _28_476 -> begin
(FStar_All.failwith "Ill-formed substitution")
end))

# 293 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_subst_one_binder : FStar_Absyn_Syntax.binder  ->  FStar_Absyn_Syntax.binder  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list = (fun b1 b2 -> if ((FStar_Absyn_Syntax.is_null_binder b1) || (FStar_Absyn_Syntax.is_null_binder b2)) then begin
[]
end else begin
(match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
if (bvar_eq a b) then begin
[]
end else begin
(let _130_290 = (let _130_289 = (let _130_288 = (btvar_to_typ a)
in (b.FStar_Absyn_Syntax.v, _130_288))
in FStar_Util.Inl (_130_289))
in (_130_290)::[])
end
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
if (bvar_eq x y) then begin
[]
end else begin
(let _130_293 = (let _130_292 = (let _130_291 = (bvar_to_exp x)
in (y.FStar_Absyn_Syntax.v, _130_291))
in FStar_Util.Inr (_130_292))
in (_130_293)::[])
end
end
| _28_490 -> begin
[]
end)
end)

# 306 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_subst_binder : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.binder Prims.list  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.option = (fun bs1 bs2 -> (let rec aux = (fun out bs1 bs2 -> (match ((bs1, bs2)) with
| ([], []) -> begin
Some (out)
end
| (b1::bs1, b2::bs2) -> begin
(let _130_305 = (let _130_304 = (mk_subst_one_binder b1 b2)
in (FStar_List.append _130_304 out))
in (aux _130_305 bs1 bs2))
end
| _28_508 -> begin
None
end))
in (aux [] bs1 bs2)))

# 313 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_of_list : FStar_Absyn_Syntax.binders  ->  FStar_Absyn_Syntax.args  ->  FStar_Absyn_Syntax.subst = (fun formals actuals -> if ((FStar_List.length formals) = (FStar_List.length actuals)) then begin
(FStar_List.map2 subst_formal formals actuals)
end else begin
(FStar_All.failwith "Ill-formed substitution")
end)

# 317 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type red_ctrl =
{stop_if_empty_subst : Prims.bool; descend : Prims.bool}

# 317 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_Mkred_ctrl : red_ctrl  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkred_ctrl"))))

# 321 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let alpha_ctrl : red_ctrl = {stop_if_empty_subst = false; descend = true}

# 322 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let subst_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = true}

# 323 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let null_ctrl : red_ctrl = {stop_if_empty_subst = true; descend = false}

# 324 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let extend_subst = (fun e s -> (FStar_List.append (((mk_subst e))::[]) s))

# 326 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let map_knd = (fun s vk mt me descend binders k -> (let _130_326 = (subst_kind' s k)
in (_130_326, descend)))

# 328 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let map_typ = (fun s mk vt me descend binders t -> (let _130_334 = (subst_typ' s t)
in (_130_334, descend)))

# 330 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let map_exp = (fun s mk me ve descend binders e -> (let _130_342 = (subst_exp' s e)
in (_130_342, descend)))

# 332 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let map_flags = (fun s map_exp descend binders flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _28_11 -> (match (_28_11) with
| FStar_Absyn_Syntax.DECREASES (e) -> begin
(let _130_359 = (let _130_358 = (map_exp descend binders e)
in (FStar_All.pipe_right _130_358 Prims.fst))
in FStar_Absyn_Syntax.DECREASES (_130_359))
end
| f -> begin
f
end)))))

# 336 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let map_comp = (fun s mk map_typ map_exp descend binders c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
(let _28_557 = (map_typ descend binders t)
in (match (_28_557) with
| (t, descend) -> begin
(let _130_382 = (FStar_Absyn_Syntax.mk_Total t)
in (_130_382, descend))
end))
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _28_562 = (map_typ descend binders ct.FStar_Absyn_Syntax.result_typ)
in (match (_28_562) with
| (t, descend) -> begin
(let _28_565 = (FStar_Absyn_Visit.map_args map_typ map_exp descend binders ct.FStar_Absyn_Syntax.effect_args)
in (match (_28_565) with
| (args, descend) -> begin
(let _130_385 = (let _130_384 = (let _28_566 = ct
in (let _130_383 = (map_flags s map_exp descend binders ct.FStar_Absyn_Syntax.flags)
in {FStar_Absyn_Syntax.effect_name = _28_566.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = args; FStar_Absyn_Syntax.flags = _130_383}))
in (FStar_Absyn_Syntax.mk_Comp _130_384))
in (_130_385, descend))
end))
end))
end))

# 345 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let visit_knd = (fun s vk mt me ctrl binders k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in if ctrl.descend then begin
(let _28_579 = (vk null_ctrl binders k)
in (match (_28_579) with
| (k, _28_578) -> begin
(k, ctrl)
end))
end else begin
(map_knd s vk mt me null_ctrl binders k)
end))

# 351 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec compress_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (let k = (FStar_Absyn_Visit.compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_delayed (k', s, m) -> begin
(let k' = (let _130_431 = (FStar_Absyn_Visit.reduce_kind (visit_knd s) (map_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] k')
in (FStar_All.pipe_left Prims.fst _130_431))
in (let k' = (compress_kind k')
in (let _28_589 = (FStar_ST.op_Colon_Equals m (Some (k')))
in k')))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, actuals) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (formals, k') -> begin
(let _130_433 = (let _130_432 = (subst_of_list formals actuals)
in (subst_kind _130_432 k'))
in (compress_kind _130_433))
end
| _28_602 -> begin
if ((FStar_List.length actuals) = 0) then begin
k
end else begin
(FStar_All.failwith "Wrong arity for kind unifier")
end
end)
end
| _28_604 -> begin
k
end)
end
| _28_606 -> begin
k
end)))

# 374 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec visit_typ : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  FStar_Absyn_Visit.boundvars  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk vt me ctrl boundvars t -> (let visit_prod = (fun bs tc -> (let _28_667 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _28_620 b -> (match (_28_620) with
| (bs, boundvars, s) -> begin
(match (b) with
| (FStar_Util.Inl (a), imp) -> begin
(let _28_629 = (map_knd s mk vt me null_ctrl boundvars a.FStar_Absyn_Syntax.sort)
in (match (_28_629) with
| (k, _28_628) -> begin
(let a = (let _28_630 = a
in {FStar_Absyn_Syntax.v = _28_630.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _28_630.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inl (a), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inl (a.FStar_Absyn_Syntax.v))::boundvars
in (let _28_642 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inl (a), s, boundvars')
end
| _28_636 -> begin
(let b = (let _130_510 = (freshen_bvd a.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _130_510 k))
in (let s = (let _130_513 = (let _130_512 = (let _130_511 = (btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _130_511))
in FStar_Util.Inl (_130_512))
in (extend_subst _130_513 s))
in (FStar_Util.Inl (b), s, (FStar_Util.Inl (b.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_28_642) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end
| (FStar_Util.Inr (x), imp) -> begin
(let _28_650 = (map_typ s mk vt me null_ctrl boundvars x.FStar_Absyn_Syntax.sort)
in (match (_28_650) with
| (t, _28_649) -> begin
(let x = (let _28_651 = x
in {FStar_Absyn_Syntax.v = _28_651.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _28_651.FStar_Absyn_Syntax.p})
in if (FStar_Absyn_Syntax.is_null_binder b) then begin
(((FStar_Util.Inr (x), imp))::bs, boundvars, s)
end else begin
(let boundvars' = (FStar_Util.Inr (x.FStar_Absyn_Syntax.v))::boundvars
in (let _28_663 = (match (s) with
| [] when ctrl.stop_if_empty_subst -> begin
(FStar_Util.Inr (x), s, boundvars')
end
| _28_657 -> begin
(let y = (let _130_523 = (freshen_bvd x.FStar_Absyn_Syntax.v)
in (bvd_to_bvar_s _130_523 t))
in (let s = (let _130_526 = (let _130_525 = (let _130_524 = (bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _130_524))
in FStar_Util.Inr (_130_525))
in (extend_subst _130_526 s))
in (FStar_Util.Inr (y), s, (FStar_Util.Inr (y.FStar_Absyn_Syntax.v))::boundvars)))
end)
in (match (_28_663) with
| (b, s, boundvars) -> begin
(((b, imp))::bs, boundvars, s)
end)))
end)
end))
end)
end)) ([], boundvars, s)))
in (match (_28_667) with
| (bs, boundvars, s) -> begin
(let tc = (match ((s, tc)) with
| ([], _28_670) -> begin
tc
end
| (_28_673, FStar_Util.Inl (t)) -> begin
(let _130_537 = (let _130_536 = (map_typ s mk vt me null_ctrl boundvars t)
in (FStar_All.pipe_left Prims.fst _130_536))
in FStar_Util.Inl (_130_537))
end
| (_28_678, FStar_Util.Inr (c)) -> begin
(let _130_560 = (let _130_559 = (map_comp s mk (map_typ s mk vt me) (map_exp s mk vt me) null_ctrl boundvars c)
in (FStar_All.pipe_left Prims.fst _130_559))
in FStar_Util.Inr (_130_560))
end)
in ((FStar_List.rev bs), tc))
end)))
in (let t0 = t
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (_28_685) -> begin
(let _130_562 = (let _130_561 = (subst_typ' s t0)
in (FStar_All.pipe_left compress_typ _130_561))
in (_130_562, ctrl))
end
| _28_688 when (not (ctrl.descend)) -> begin
(map_typ s mk vt me null_ctrl boundvars t)
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(match ((visit_prod bs (FStar_Util.Inr (c)))) with
| (bs, FStar_Util.Inr (c)) -> begin
(let _130_572 = (FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t0.FStar_Absyn_Syntax.pos)
in (_130_572, ctrl))
end
| _28_698 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(match ((visit_prod (((FStar_Util.Inr (x), None))::[]) (FStar_Util.Inl (t)))) with
| ((FStar_Util.Inr (x), _28_706)::[], FStar_Util.Inl (t)) -> begin
(let _130_573 = (FStar_Absyn_Syntax.mk_Typ_refine (x, t) None t0.FStar_Absyn_Syntax.pos)
in (_130_573, ctrl))
end
| _28_713 -> begin
(FStar_All.failwith "Impossible")
end)
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(match ((visit_prod bs (FStar_Util.Inl (t)))) with
| (bs, FStar_Util.Inl (t)) -> begin
(let _130_574 = (FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t0.FStar_Absyn_Syntax.pos)
in (_130_574, ctrl))
end
| _28_723 -> begin
(FStar_All.failwith "Impossible")
end)
end
| _28_725 -> begin
(let _28_729 = (vt null_ctrl boundvars t)
in (match (_28_729) with
| (t, _28_728) -> begin
(t, ctrl)
end))
end))))
and compress_typ' : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (let t = (FStar_Absyn_Visit.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inl (t', s), m) -> begin
(let res = (let _130_594 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] t')
in (FStar_All.pipe_left Prims.fst _130_594))
in (let res = (compress_typ' res)
in (let _28_741 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| FStar_Absyn_Syntax.Typ_delayed (FStar_Util.Inr (mk_t), m) -> begin
(let t = (let _130_596 = (mk_t ())
in (compress_typ' _130_596))
in (let _28_749 = (FStar_ST.op_Colon_Equals m (Some (t)))
in t))
end
| _28_752 -> begin
t
end)))
and compress_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (let t = (compress_typ' t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_28_756) -> begin
(FStar_All.failwith "Impossible: compress returned a delayed type")
end
| _28_759 -> begin
t
end)))

# 462 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec visit_exp : (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax), ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef * (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax)) FStar_Util.either Prims.list Prims.list  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  (red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl))  ->  red_ctrl  ->  ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef) FStar_Util.either Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax * red_ctrl) = (fun s mk me ve ctrl binders e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_bvar (_28_769) -> begin
(let _130_662 = (let _130_661 = (subst_exp' s e)
in (FStar_All.pipe_left compress_exp _130_661))
in (_130_662, ctrl))
end
| _28_772 when (not (ctrl.descend)) -> begin
(map_exp s mk me ve ctrl binders e)
end
| _28_774 -> begin
(let _28_778 = (ve null_ctrl binders e)
in (match (_28_778) with
| (e, _28_777) -> begin
(e, ctrl)
end))
end)))
and compress_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (let e = (FStar_Absyn_Visit.compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (e', s, m) -> begin
(let e = (let _130_691 = (FStar_Absyn_Visit.reduce_exp (map_knd s) (map_typ s) (visit_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp subst_ctrl [] e')
in (FStar_All.pipe_left Prims.fst _130_691))
in (let res = (compress_exp e)
in (let _28_788 = (FStar_ST.op_Colon_Equals m (Some (res)))
in res)))
end
| _28_791 -> begin
e
end)))

# 479 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unmeta_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_796)) -> begin
(unmeta_exp e)
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _28_802, _28_804) -> begin
(unmeta_exp e)
end
| _28_808 -> begin
e
end)))

# 486 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let alpha_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (let t = (compress_typ t)
in (let s = (mk_subst [])
in (let doit = (fun t -> (let _130_716 = (FStar_Absyn_Visit.reduce_typ (map_knd s) (visit_typ s) (map_exp s) FStar_Absyn_Visit.combine_kind FStar_Absyn_Visit.combine_typ FStar_Absyn_Visit.combine_exp alpha_ctrl [] t)
in (FStar_All.pipe_left Prims.fst _130_716)))
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_lam (bs, _)) | (FStar_Absyn_Syntax.Typ_fun (bs, _)) -> begin
if (FStar_Util.for_all FStar_Absyn_Syntax.is_null_binder bs) then begin
t
end else begin
(doit t)
end
end
| FStar_Absyn_Syntax.Typ_refine (_28_824) -> begin
(doit t)
end
| _28_827 -> begin
t
end)))))

# 496 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let formals_for_actuals = (fun formals actuals -> (FStar_List.map2 (fun formal actual -> (match (((Prims.fst formal), (Prims.fst actual))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, b))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, y))
end
| _28_843 -> begin
(FStar_All.failwith "Ill-typed substitution")
end)) formals actuals))

# 502 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let compress_typ_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun _28_12 -> (match (_28_12) with
| None -> begin
None
end
| Some (t) -> begin
(let _130_723 = (compress_typ t)
in Some (_130_723))
end))

# 506 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_discriminator : FStar_Ident.lident  ->  FStar_Ident.lident = (fun lid -> (FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns (((FStar_Absyn_Syntax.mk_ident ((Prims.strcat "is_" lid.FStar_Ident.ident.FStar_Ident.idText), lid.FStar_Ident.ident.FStar_Ident.idRange)))::[]))))

# 509 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_name : FStar_Ident.lident  ->  Prims.bool = (fun lid -> (let c = (FStar_Util.char_at lid.FStar_Ident.ident.FStar_Ident.idText 0)
in (FStar_Util.is_upper c)))

# 513 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ml_comp : FStar_Absyn_Syntax.typ  ->  FStar_Range.range  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun t r -> (let _130_733 = (let _130_732 = (set_lid_range FStar_Absyn_Const.effect_ML_lid r)
in {FStar_Absyn_Syntax.effect_name = _130_732; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.MLEFFECT)::[]})
in (FStar_Absyn_Syntax.mk_Comp _130_733)))

# 519 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let total_comp = (fun t r -> (FStar_Absyn_Syntax.mk_Total t))

# 521 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let gtotal_comp : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun t -> (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_GTot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.SOMETRIVIAL)::[]}))

# 529 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let comp_set_flags : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.cflags Prims.list  ->  FStar_Absyn_Syntax.comp = (fun c f -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_28_859) -> begin
c
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(let _28_863 = c
in {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp ((let _28_865 = ct
in {FStar_Absyn_Syntax.effect_name = _28_865.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = _28_865.FStar_Absyn_Syntax.result_typ; FStar_Absyn_Syntax.effect_args = _28_865.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = f})); FStar_Absyn_Syntax.tk = _28_863.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = _28_863.FStar_Absyn_Syntax.pos; FStar_Absyn_Syntax.fvs = _28_863.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _28_863.FStar_Absyn_Syntax.uvs})
end))

# 533 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let comp_flags = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_28_869) -> begin
(FStar_Absyn_Syntax.TOTAL)::[]
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.flags
end))

# 537 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let comp_effect_name = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c.FStar_Absyn_Syntax.effect_name
end
| FStar_Absyn_Syntax.Total (_28_877) -> begin
FStar_Absyn_Const.effect_Tot_lid
end))

# 541 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let comp_to_comp_typ : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.comp_typ = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
c
end
| FStar_Absyn_Syntax.Total (t) -> begin
{FStar_Absyn_Syntax.effect_name = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = []; FStar_Absyn_Syntax.flags = (FStar_Absyn_Syntax.TOTAL)::[]}
end))

# 546 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_total_comp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_13 -> (match (_28_13) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _28_889 -> begin
false
end)))))

# 549 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_total_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> ((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _28_14 -> (match (_28_14) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _28_895 -> begin
false
end))))))

# 551 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_tot_or_gtot_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Tot_lid) || (FStar_Ident.lid_equals c.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_GTot_lid)) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _28_15 -> (match (_28_15) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _28_901 -> begin
false
end))))))

# 555 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_partial_return = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_16 -> (match (_28_16) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _28_907 -> begin
false
end)))))

# 557 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_lcomp_partial_return : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun c -> (FStar_All.pipe_right c.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _28_17 -> (match (_28_17) with
| (FStar_Absyn_Syntax.RETURN) | (FStar_Absyn_Syntax.PARTIAL_RETURN) -> begin
true
end
| _28_913 -> begin
false
end)))))

# 559 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_tot_or_gtot_comp = (fun c -> ((is_total_comp c) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid (comp_effect_name c))))

# 563 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_pure_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_28_917) -> begin
true
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
((((is_tot_or_gtot_comp c) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right ct.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_18 -> (match (_28_18) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _28_924 -> begin
false
end)))))
end))

# 570 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_ghost_effect : FStar_Ident.lident  ->  Prims.bool = (fun l -> (((FStar_Ident.lid_equals FStar_Absyn_Const.effect_GTot_lid l) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_GHOST_lid l)) || (FStar_Ident.lid_equals FStar_Absyn_Const.effect_Ghost_lid l)))

# 575 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_pure_or_ghost_comp = (fun c -> ((is_pure_comp c) || (is_ghost_effect (comp_effect_name c))))

# 577 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_pure_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((((is_total_lcomp lc) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_PURE_lid)) || (FStar_Ident.lid_equals lc.FStar_Absyn_Syntax.eff_name FStar_Absyn_Const.effect_Pure_lid)) || (FStar_All.pipe_right lc.FStar_Absyn_Syntax.cflags (FStar_Util.for_some (fun _28_19 -> (match (_28_19) with
| FStar_Absyn_Syntax.LEMMA -> begin
true
end
| _28_931 -> begin
false
end))))))

# 583 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_pure_or_ghost_lcomp : FStar_Absyn_Syntax.lcomp  ->  Prims.bool = (fun lc -> ((is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Absyn_Syntax.eff_name)))

# 586 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_pure_or_ghost_function : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _130_772 = (compress_typ t)
in _130_772.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_28_935, c) -> begin
(is_pure_or_ghost_comp c)
end
| _28_940 -> begin
true
end))

# 590 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _130_775 = (compress_typ t)
in _130_775.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_28_943, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid)
end
| _28_950 -> begin
false
end)
end
| _28_952 -> begin
false
end))

# 597 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_smt_lemma : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _130_778 = (compress_typ t)
in _130_778.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_28_955, c) -> begin
(match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (ct) when (FStar_Ident.lid_equals ct.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_Lemma_lid) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| _req::_ens::(FStar_Util.Inr (pats), _28_966)::_28_962 -> begin
(match ((let _130_779 = (unmeta_exp pats)
in _130_779.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _28_983); FStar_Absyn_Syntax.tk = _28_980; FStar_Absyn_Syntax.pos = _28_978; FStar_Absyn_Syntax.fvs = _28_976; FStar_Absyn_Syntax.uvs = _28_974}, _28_988) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid)
end
| _28_992 -> begin
false
end)
end
| _28_994 -> begin
false
end)
end
| _28_996 -> begin
false
end)
end
| _28_998 -> begin
false
end))

# 611 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_ml_comp = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Comp (c) -> begin
((FStar_Ident.lid_equals c.FStar_Absyn_Syntax.effect_name FStar_Absyn_Const.effect_ML_lid) || (FStar_All.pipe_right c.FStar_Absyn_Syntax.flags (FStar_Util.for_some (fun _28_20 -> (match (_28_20) with
| FStar_Absyn_Syntax.MLEFFECT -> begin
true
end
| _28_1005 -> begin
false
end)))))
end
| _28_1007 -> begin
false
end))

# 617 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let comp_result = (fun c -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (t) -> begin
t
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
ct.FStar_Absyn_Syntax.result_typ
end))

# 621 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let set_result_typ = (fun c t -> (match (c.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Total (_28_1016) -> begin
(FStar_Absyn_Syntax.mk_Total t)
end
| FStar_Absyn_Syntax.Comp (ct) -> begin
(FStar_Absyn_Syntax.mk_Comp (let _28_1020 = ct
in {FStar_Absyn_Syntax.effect_name = _28_1020.FStar_Absyn_Syntax.effect_name; FStar_Absyn_Syntax.result_typ = t; FStar_Absyn_Syntax.effect_args = _28_1020.FStar_Absyn_Syntax.effect_args; FStar_Absyn_Syntax.flags = _28_1020.FStar_Absyn_Syntax.flags}))
end))

# 625 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_trivial_wp = (fun c -> (FStar_All.pipe_right (comp_flags c) (FStar_Util.for_some (fun _28_21 -> (match (_28_21) with
| (FStar_Absyn_Syntax.TOTAL) | (FStar_Absyn_Syntax.RETURN) -> begin
true
end
| _28_1027 -> begin
false
end)))))

# 631 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec is_atom : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _130_789 = (compress_exp e)
in _130_789.FStar_Absyn_Syntax.n)) with
| (FStar_Absyn_Syntax.Exp_bvar (_)) | (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
true
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_1040)) -> begin
(is_atom e)
end
| _28_1045 -> begin
false
end))

# 638 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let primops : FStar_Ident.lident Prims.list = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]

# 655 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_primop = (fun f -> (match (f.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _28_1049) -> begin
(FStar_All.pipe_right primops (FStar_Util.for_some (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v)))
end
| _28_1053 -> begin
false
end))

# 659 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unascribe : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun e -> (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_ascribed (e, _28_1057, _28_1059) -> begin
(unascribe e)
end
| _28_1063 -> begin
e
end))

# 663 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec ascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t k -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t', _28_1068) -> begin
(ascribe_typ t' k)
end
| _28_1072 -> begin
(FStar_Absyn_Syntax.mk_Typ_ascribed (t, k) t.FStar_Absyn_Syntax.pos)
end))

# 667 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unascribe_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_ascribed (t, _28_1076) -> begin
(unascribe_typ t)
end
| _28_1080 -> begin
t
end))

# 671 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unrefine : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _28_1085) -> begin
(unrefine x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _28_1090) -> begin
(unrefine t)
end
| _28_1094 -> begin
t
end)))

# 678 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_fun : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun e -> (match ((let _130_803 = (compress_exp e)
in _130_803.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_abs (_28_1097) -> begin
true
end
| _28_1100 -> begin
false
end))

# 682 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_function_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun t -> (match ((let _130_806 = (compress_typ t)
in _130_806.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (_28_1103) -> begin
true
end
| _28_1106 -> begin
false
end))

# 686 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec pre_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_refine (x, _28_1111) -> begin
(pre_typ x.FStar_Absyn_Syntax.sort)
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _28_1116) -> begin
(pre_typ t)
end
| _28_1120 -> begin
t
end)))

# 693 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let destruct : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.args Prims.option = (fun typ lid -> (let typ = (compress_typ typ)
in (match (typ.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _28_1131; FStar_Absyn_Syntax.pos = _28_1129; FStar_Absyn_Syntax.fvs = _28_1127; FStar_Absyn_Syntax.uvs = _28_1125}, args) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some (args)
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid) -> begin
Some ([])
end
| _28_1141 -> begin
None
end)))

# 700 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec lids_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.lident Prims.list = (fun se -> (match (se) with
| (FStar_Absyn_Syntax.Sig_let (_, _, lids, _)) | (FStar_Absyn_Syntax.Sig_bundle (_, _, lids, _)) -> begin
lids
end
| (FStar_Absyn_Syntax.Sig_tycon (lid, _, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (lid, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_datacon (lid, _, _, _, _, _)) | (FStar_Absyn_Syntax.Sig_val_decl (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (lid, _, _, _)) | (FStar_Absyn_Syntax.Sig_assume (lid, _, _, _)) -> begin
(lid)::[]
end
| FStar_Absyn_Syntax.Sig_new_effect (n, _28_1235) -> begin
(n.FStar_Absyn_Syntax.mname)::[]
end
| (FStar_Absyn_Syntax.Sig_sub_effect (_)) | (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) -> begin
[]
end))

# 715 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lid_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Ident.lident Prims.option = (fun se -> (match ((lids_of_sigelt se)) with
| l::[] -> begin
Some (l)
end
| _28_1251 -> begin
None
end))

# 719 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let range_of_sigelt : FStar_Absyn_Syntax.sigelt  ->  FStar_Range.range = (fun x -> (match (x) with
| (FStar_Absyn_Syntax.Sig_bundle (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_tycon (_, _, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_typ_abbrev (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_datacon (_, _, _, _, _, r)) | (FStar_Absyn_Syntax.Sig_val_decl (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_assume (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_let (_, r, _, _)) | (FStar_Absyn_Syntax.Sig_main (_, r)) | (FStar_Absyn_Syntax.Sig_pragma (_, r)) | (FStar_Absyn_Syntax.Sig_new_effect (_, r)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_, _, _, r)) | (FStar_Absyn_Syntax.Sig_sub_effect (_, r)) -> begin
r
end))

# 734 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let range_of_lb = (fun _28_22 -> (match (_28_22) with
| (FStar_Util.Inl (x), _28_1362, _28_1364) -> begin
(range_of_bvd x)
end
| (FStar_Util.Inr (l), _28_1369, _28_1371) -> begin
(FStar_Ident.range_of_lid l)
end))

# 738 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let range_of_arg = (fun _28_23 -> (match (_28_23) with
| (FStar_Util.Inl (hd), _28_1377) -> begin
hd.FStar_Absyn_Syntax.pos
end
| (FStar_Util.Inr (hd), _28_1382) -> begin
hd.FStar_Absyn_Syntax.pos
end))

# 742 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let range_of_args = (fun args r -> (FStar_All.pipe_right args (FStar_List.fold_left (fun r a -> (FStar_Range.union_ranges r (range_of_arg a))) r)))

# 745 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_typ_app : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (f, args) None r)))

# 749 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_exp_app : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.exp = (fun f args -> (let r = (range_of_args args f.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Exp_app (f, args) None r)))

# 753 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_data : FStar_Ident.lident  ->  (((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax, (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun l args -> (match (args) with
| [] -> begin
(let _130_839 = (let _130_838 = (let _130_837 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (_130_837, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_130_838))
in (FStar_Absyn_Syntax.mk_Exp_meta _130_839))
end
| _28_1398 -> begin
(let _130_843 = (let _130_842 = (let _130_841 = (let _130_840 = (fvar (Some (FStar_Absyn_Syntax.Data_ctor)) l (FStar_Ident.range_of_lid l))
in (mk_exp_app _130_840 args))
in (_130_841, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_130_842))
in (FStar_Absyn_Syntax.mk_Exp_meta _130_843))
end))

# 760 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> (FStar_Ident.mk_ident ((Prims.strcat "^fname^" x.FStar_Ident.idText), x.FStar_Ident.idRange)))

# 761 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let unmangle_field_name : FStar_Ident.ident  ->  FStar_Ident.ident = (fun x -> if (FStar_Util.starts_with x.FStar_Ident.idText "^fname^") then begin
(let _130_849 = (let _130_848 = (FStar_Util.substring_from x.FStar_Ident.idText 7)
in (_130_848, x.FStar_Ident.idRange))
in (FStar_Ident.mk_ident _130_849))
end else begin
x
end)

# 766 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_field_projector_name = (fun lid x i -> (let nm = if (FStar_Absyn_Syntax.is_null_bvar x) then begin
(let _130_855 = (let _130_854 = (let _130_853 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _130_853))
in (_130_854, x.FStar_Absyn_Syntax.p))
in (FStar_Absyn_Syntax.mk_ident _130_855))
end else begin
x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname
end
in (let y = (let _28_1407 = x.FStar_Absyn_Syntax.v
in {FStar_Absyn_Syntax.ppname = nm; FStar_Absyn_Syntax.realname = _28_1407.FStar_Absyn_Syntax.realname})
in (let _130_859 = (let _130_858 = (let _130_857 = (let _130_856 = (unmangle_field_name nm)
in (_130_856)::[])
in (FStar_List.append (FStar_Ident.ids_of_lid lid) _130_857))
in (FStar_Ident.lid_of_ids _130_858))
in (_130_859, y)))))

# 773 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let unchecked_unify = (fun uv t -> (match ((FStar_Unionfind.find uv)) with
| FStar_Absyn_Syntax.Fixed (_28_1413) -> begin
(let _130_864 = (let _130_863 = (let _130_862 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _130_862))
in (FStar_Util.format1 "Changing a fixed uvar! U%s\n" _130_863))
in (FStar_All.failwith _130_864))
end
| _28_1416 -> begin
(FStar_Unionfind.change uv (FStar_Absyn_Syntax.Fixed (t)))
end))

# 782 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type bvars =
(FStar_Absyn_Syntax.btvar FStar_Util.set * FStar_Absyn_Syntax.bvvar FStar_Util.set)

# 783 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let no_bvars : ((FStar_Absyn_Syntax.btvar Prims.list * (FStar_Absyn_Syntax.btvar  ->  FStar_Absyn_Syntax.btvar  ->  Prims.bool)) * (FStar_Absyn_Syntax.bvvar Prims.list * (FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.bvvar  ->  Prims.bool))) = (FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.ftvs, FStar_Absyn_Syntax.no_fvs.FStar_Absyn_Syntax.fxvs)

# 784 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let fvs_included : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun fvs1 fvs2 -> ((FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs) && (FStar_Util.set_is_subset_of fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)))

# 788 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let eq_fvars = (fun v1 v2 -> (match ((v1, v2)) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(FStar_Absyn_Syntax.bvd_eq a b)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x y)
end
| _28_1432 -> begin
false
end))

# 793 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let eq_binder = (fun b1 b2 -> (match (((Prims.fst b1), (Prims.fst b2))) with
| (FStar_Util.Inl (x), FStar_Util.Inl (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(FStar_Absyn_Syntax.bvd_eq x.FStar_Absyn_Syntax.v y.FStar_Absyn_Syntax.v)
end
| _28_1446 -> begin
false
end))

# 798 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let uv_eq = (fun _28_1450 _28_1454 -> (match ((_28_1450, _28_1454)) with
| ((uv1, _28_1449), (uv2, _28_1453)) -> begin
(FStar_Unionfind.equivalent uv1 uv2)
end))

# 799 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let union_uvs : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun uvs1 uvs2 -> (let _130_893 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_k uvs2.FStar_Absyn_Syntax.uvars_k)
in (let _130_892 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_t uvs2.FStar_Absyn_Syntax.uvars_t)
in (let _130_891 = (FStar_Util.set_union uvs1.FStar_Absyn_Syntax.uvars_e uvs2.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _130_893; FStar_Absyn_Syntax.uvars_t = _130_892; FStar_Absyn_Syntax.uvars_e = _130_891}))))

# 805 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let union_fvs : FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars  ->  FStar_Absyn_Syntax.freevars = (fun fvs1 fvs2 -> (let _130_899 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.ftvs fvs2.FStar_Absyn_Syntax.ftvs)
in (let _130_898 = (FStar_Util.set_union fvs1.FStar_Absyn_Syntax.fxvs fvs2.FStar_Absyn_Syntax.fxvs)
in {FStar_Absyn_Syntax.ftvs = _130_899; FStar_Absyn_Syntax.fxvs = _130_898})))

# 811 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let union_fvs_uvs : (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars)  ->  (FStar_Absyn_Syntax.freevars * FStar_Absyn_Syntax.uvars) = (fun _28_1461 _28_1464 -> (match ((_28_1461, _28_1464)) with
| ((fvs1, uvs1), (fvs2, uvs2)) -> begin
(let _130_905 = (union_fvs fvs1 fvs2)
in (let _130_904 = (union_uvs uvs1 uvs2)
in (_130_905, _130_904)))
end))

# 815 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let sub_fv = (fun _28_1467 _28_1470 -> (match ((_28_1467, _28_1470)) with
| ((fvs, uvs), (tvars, vvars)) -> begin
(let _130_926 = (let _28_1471 = fvs
in (let _130_925 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.ftvs tvars)
in (let _130_924 = (FStar_Util.set_difference fvs.FStar_Absyn_Syntax.fxvs vvars)
in {FStar_Absyn_Syntax.ftvs = _130_925; FStar_Absyn_Syntax.fxvs = _130_924})))
in (_130_926, uvs))
end))

# 820 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let stash = (fun uvonly s _28_1479 -> (match (_28_1479) with
| (fvs, uvs) -> begin
(let _28_1480 = (FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.uvs (Some (uvs)))
in if uvonly then begin
()
end else begin
(FStar_ST.op_Colon_Equals s.FStar_Absyn_Syntax.fvs (Some (fvs)))
end)
end))

# 825 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let single_fv = (fun x -> (let _130_937 = (FStar_Absyn_Syntax.new_ftv_set ())
in (FStar_Util.set_add x _130_937)))

# 826 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let single_uv = (fun u -> (let _130_945 = (FStar_Absyn_Syntax.new_uv_set ())
in (FStar_Util.set_add u _130_945)))

# 827 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let single_uvt = (fun u -> (let _130_953 = (FStar_Absyn_Syntax.new_uvt_set ())
in (FStar_Util.set_add u _130_953)))

# 829 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec vs_typ' = (fun t uvonly cont -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_delayed (_28_1491) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _130_1068 = (let _130_1067 = (let _28_1495 = FStar_Absyn_Syntax.no_fvs
in (let _130_1066 = (single_fv a)
in {FStar_Absyn_Syntax.ftvs = _130_1066; FStar_Absyn_Syntax.fxvs = _28_1495.FStar_Absyn_Syntax.fxvs}))
in (_130_1067, FStar_Absyn_Syntax.no_uvs))
in (cont _130_1068))
end
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let _130_1071 = (let _130_1070 = (let _28_1501 = FStar_Absyn_Syntax.no_uvs
in (let _130_1069 = (single_uvt (uv, k))
in {FStar_Absyn_Syntax.uvars_k = _28_1501.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _130_1069; FStar_Absyn_Syntax.uvars_e = _28_1501.FStar_Absyn_Syntax.uvars_e}))
in (FStar_Absyn_Syntax.no_fvs, _130_1070))
in (cont _130_1071))
end
| (FStar_Absyn_Syntax.Typ_unknown) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
(vs_binders bs uvonly (fun _28_1513 -> (match (_28_1513) with
| (bvs, vs1) -> begin
(vs_comp c uvonly (fun vs2 -> (let _130_1075 = (let _130_1074 = (union_fvs_uvs vs1 vs2)
in (sub_fv _130_1074 bvs))
in (cont _130_1075))))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, t) -> begin
(vs_binders bs uvonly (fun _28_1521 -> (match (_28_1521) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _130_1079 = (let _130_1078 = (union_fvs_uvs vs1 vs2)
in (sub_fv _130_1078 bvs))
in (cont _130_1079))))
end)))
end
| FStar_Absyn_Syntax.Typ_refine (x, t) -> begin
(vs_binders (((FStar_Util.Inr (x), None))::[]) uvonly (fun _28_1529 -> (match (_28_1529) with
| (bvs, vs1) -> begin
(vs_typ t uvonly (fun vs2 -> (let _130_1083 = (let _130_1082 = (union_fvs_uvs vs1 vs2)
in (sub_fv _130_1082 bvs))
in (cont _130_1083))))
end)))
end
| FStar_Absyn_Syntax.Typ_app (t, args) -> begin
(vs_typ t uvonly (fun vs1 -> (vs_args args uvonly (fun vs2 -> (let _130_1086 = (union_fvs_uvs vs1 vs2)
in (cont _130_1086))))))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _28_1539) -> begin
(vs_typ t uvonly cont)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _28_1545)) -> begin
(vs_typ t1 uvonly (fun vs1 -> (vs_typ t2 uvonly (fun vs2 -> (let _130_1089 = (union_fvs_uvs vs1 vs2)
in (cont _130_1089))))))
end
| (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) -> begin
(vs_typ t uvonly cont)
end)))
and vs_binders = (fun bs uvonly cont -> (match (bs) with
| [] -> begin
(cont (no_bvars, (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs)))
end
| (FStar_Util.Inl (a), _28_1587)::rest -> begin
(vs_kind a.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _28_1595 -> (match (_28_1595) with
| ((tvars, vvars), vs2) -> begin
(let _130_1126 = (let _130_1125 = (let _130_1123 = (FStar_Util.set_add a tvars)
in (_130_1123, vvars))
in (let _130_1124 = (union_fvs_uvs vs vs2)
in (_130_1125, _130_1124)))
in (cont _130_1126))
end)))))
end
| (FStar_Util.Inr (x), _28_1600)::rest -> begin
(vs_typ x.FStar_Absyn_Syntax.sort uvonly (fun vs -> (vs_binders rest uvonly (fun _28_1608 -> (match (_28_1608) with
| ((tvars, vvars), vs2) -> begin
(let _130_1150 = (let _130_1149 = (let _130_1147 = (FStar_Util.set_add x vvars)
in (tvars, _130_1147))
in (let _130_1148 = (union_fvs_uvs vs vs2)
in (_130_1149, _130_1148)))
in (cont _130_1150))
end)))))
end))
and vs_args = (fun args uvonly cont -> (match (args) with
| [] -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| (FStar_Util.Inl (t), _28_1618)::tl -> begin
(vs_typ t uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _130_1154 = (union_fvs_uvs ft1 ft2)
in (cont _130_1154))))))
end
| (FStar_Util.Inr (e), _28_1627)::tl -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args tl uvonly (fun ft2 -> (let _130_1157 = (union_fvs_uvs ft1 ft2)
in (cont _130_1157))))))
end))
and vs_typ = (fun t uvonly cont -> (match ((let _130_1160 = (FStar_ST.read t.FStar_Absyn_Syntax.fvs)
in (let _130_1159 = (FStar_ST.read t.FStar_Absyn_Syntax.uvs)
in (_130_1160, _130_1159)))) with
| (Some (_28_1637), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_typ' t uvonly (fun fvs -> (let _28_1645 = (stash uvonly t fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_typ' t uvonly (fun fvs -> (let _28_1652 = (stash uvonly t fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_kind' = (fun k uvonly cont -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_28_1665, k) -> begin
(let _130_1165 = (let _130_1164 = (FStar_Range.string_of_range k.FStar_Absyn_Syntax.pos)
in (FStar_Util.format1 "%s: Impossible ... found a Kind_lam bare" _130_1164))
in (FStar_All.failwith _130_1165))
end
| FStar_Absyn_Syntax.Kind_delayed (_28_1670) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, args) -> begin
(vs_args args uvonly (fun _28_1681 -> (match (_28_1681) with
| (fvs, uvs) -> begin
(let _130_1169 = (let _130_1168 = (let _28_1682 = uvs
in (let _130_1167 = (FStar_Util.set_add uv uvs.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _130_1167; FStar_Absyn_Syntax.uvars_t = _28_1682.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _28_1682.FStar_Absyn_Syntax.uvars_e}))
in (fvs, _130_1168))
in (cont _130_1169))
end)))
end
| FStar_Absyn_Syntax.Kind_abbrev (_28_1685, k) -> begin
(vs_kind k uvonly cont)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(vs_binders bs uvonly (fun _28_1695 -> (match (_28_1695) with
| (bvs, vs1) -> begin
(vs_kind k uvonly (fun vs2 -> (let _130_1173 = (let _130_1172 = (union_fvs_uvs vs1 vs2)
in (sub_fv _130_1172 bvs))
in (cont _130_1173))))
end)))
end)))
and vs_kind = (fun k uvonly cont -> (match ((let _130_1176 = (FStar_ST.read k.FStar_Absyn_Syntax.fvs)
in (let _130_1175 = (FStar_ST.read k.FStar_Absyn_Syntax.uvs)
in (_130_1176, _130_1175)))) with
| (Some (_28_1702), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_kind' k uvonly (fun fvs -> (let _28_1710 = (stash uvonly k fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_kind' k uvonly (fun fvs -> (let _28_1717 = (stash uvonly k fvs)
in (cont fvs))))
end
end
| (Some (fvs), Some (uvs)) -> begin
(cont (fvs, uvs))
end))
and vs_exp' = (fun e uvonly cont -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_28_1730) -> begin
(FStar_All.failwith "impossible")
end
| (FStar_Absyn_Syntax.Exp_fvar (_)) | (FStar_Absyn_Syntax.Exp_constant (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_uvar (uv, t) -> begin
(let _130_1182 = (let _130_1181 = (let _28_1742 = FStar_Absyn_Syntax.no_uvs
in (let _130_1180 = (single_uvt (uv, t))
in {FStar_Absyn_Syntax.uvars_k = _28_1742.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _28_1742.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _130_1180}))
in (FStar_Absyn_Syntax.no_fvs, _130_1181))
in (cont _130_1182))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end else begin
(let _130_1185 = (let _130_1184 = (let _28_1746 = FStar_Absyn_Syntax.no_fvs
in (let _130_1183 = (single_fv x)
in {FStar_Absyn_Syntax.ftvs = _28_1746.FStar_Absyn_Syntax.ftvs; FStar_Absyn_Syntax.fxvs = _130_1183}))
in (_130_1184, FStar_Absyn_Syntax.no_uvs))
in (cont _130_1185))
end
end
| FStar_Absyn_Syntax.Exp_ascribed (e, _28_1750, _28_1752) -> begin
(vs_exp e uvonly cont)
end
| FStar_Absyn_Syntax.Exp_abs (bs, e) -> begin
(vs_binders bs uvonly (fun _28_1761 -> (match (_28_1761) with
| (bvs, vs1) -> begin
(vs_exp e uvonly (fun vs2 -> (let _130_1189 = (let _130_1188 = (union_fvs_uvs vs1 vs2)
in (sub_fv _130_1188 bvs))
in (cont _130_1189))))
end)))
end
| FStar_Absyn_Syntax.Exp_app (e, args) -> begin
(vs_exp e uvonly (fun ft1 -> (vs_args args uvonly (fun ft2 -> (let _130_1192 = (union_fvs_uvs ft1 ft2)
in (cont _130_1192))))))
end
| (FStar_Absyn_Syntax.Exp_match (_)) | (FStar_Absyn_Syntax.Exp_let (_)) -> begin
(cont (FStar_Absyn_Syntax.no_fvs, FStar_Absyn_Syntax.no_uvs))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _28_1777)) -> begin
(vs_exp e uvonly cont)
end)))
and vs_exp = (fun e uvonly cont -> (match ((let _130_1195 = (FStar_ST.read e.FStar_Absyn_Syntax.fvs)
in (let _130_1194 = (FStar_ST.read e.FStar_Absyn_Syntax.uvs)
in (_130_1195, _130_1194)))) with
| (Some (_28_1786), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_exp' e uvonly (fun fvs -> (let _28_1794 = (stash uvonly e fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_exp' e uvonly (fun fvs -> (let _28_1801 = (stash uvonly e fvs)
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
(vs_typ ct.FStar_Absyn_Syntax.result_typ uvonly (fun vs1 -> (vs_args ct.FStar_Absyn_Syntax.effect_args uvonly (fun vs2 -> (let _130_1201 = (union_fvs_uvs vs1 vs2)
in (k _130_1201))))))
end
end))
and vs_comp = (fun c uvonly cont -> (match ((let _130_1204 = (FStar_ST.read c.FStar_Absyn_Syntax.fvs)
in (let _130_1203 = (FStar_ST.read c.FStar_Absyn_Syntax.uvs)
in (_130_1204, _130_1203)))) with
| (Some (_28_1823), None) -> begin
(FStar_All.failwith "Impossible")
end
| (None, None) -> begin
(vs_comp' c uvonly (fun fvs -> (let _28_1831 = (stash uvonly c fvs)
in (cont fvs))))
end
| (None, Some (uvs)) -> begin
if uvonly then begin
(cont (FStar_Absyn_Syntax.no_fvs, uvs))
end else begin
(vs_comp' c uvonly (fun fvs -> (let _28_1838 = (stash uvonly c fvs)
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
(vs_either hd uvonly (fun ft1 -> (vs_either_l tl uvonly (fun ft2 -> (let _130_1211 = (union_fvs_uvs ft1 ft2)
in (cont _130_1211))))))
end))

# 1027 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freevars_kind : FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.freevars = (fun k -> (vs_kind k false (fun _28_1867 -> (match (_28_1867) with
| (x, _28_1866) -> begin
x
end))))

# 1030 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freevars_typ : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.freevars = (fun t -> (vs_typ t false (fun _28_1872 -> (match (_28_1872) with
| (x, _28_1871) -> begin
x
end))))

# 1033 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freevars_exp : FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.freevars = (fun e -> (vs_exp e false (fun _28_1877 -> (match (_28_1877) with
| (x, _28_1876) -> begin
x
end))))

# 1036 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freevars_comp : FStar_Absyn_Syntax.comp  ->  FStar_Absyn_Syntax.freevars = (fun c -> (vs_comp c false (fun _28_1882 -> (match (_28_1882) with
| (x, _28_1881) -> begin
x
end))))

# 1039 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let freevars_args = (fun args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (t) -> begin
(let _130_1227 = (freevars_typ t)
in (FStar_All.pipe_left (union_fvs out) _130_1227))
end
| FStar_Util.Inr (e) -> begin
(let _130_1228 = (freevars_exp e)
in (FStar_All.pipe_left (union_fvs out) _130_1228))
end)) FStar_Absyn_Syntax.no_fvs)))

# 1044 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_free : (FStar_Absyn_Syntax.btvar, FStar_Absyn_Syntax.bvvar) FStar_Util.either Prims.list  ->  FStar_Absyn_Syntax.freevars  ->  Prims.bool = (fun axs fvs -> (FStar_All.pipe_right axs (FStar_Util.for_some (fun _28_24 -> (match (_28_24) with
| FStar_Util.Inl (a) -> begin
(FStar_Util.set_mem a fvs.FStar_Absyn_Syntax.ftvs)
end
| FStar_Util.Inr (x) -> begin
(FStar_Util.set_mem x fvs.FStar_Absyn_Syntax.fxvs)
end)))))

# 1049 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type syntax_sum =
| SynSumKind of FStar_Absyn_Syntax.knd
| SynSumType of FStar_Absyn_Syntax.typ
| SynSumExp of FStar_Absyn_Syntax.exp
| SynSumComp of (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax

# 1050 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_SynSumKind = (fun _discr_ -> (match (_discr_) with
| SynSumKind (_) -> begin
true
end
| _ -> begin
false
end))

# 1051 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_SynSumType = (fun _discr_ -> (match (_discr_) with
| SynSumType (_) -> begin
true
end
| _ -> begin
false
end))

# 1052 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_SynSumExp = (fun _discr_ -> (match (_discr_) with
| SynSumExp (_) -> begin
true
end
| _ -> begin
false
end))

# 1053 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_SynSumComp = (fun _discr_ -> (match (_discr_) with
| SynSumComp (_) -> begin
true
end
| _ -> begin
false
end))

# 1050 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___SynSumKind____0 : syntax_sum  ->  FStar_Absyn_Syntax.knd = (fun projectee -> (match (projectee) with
| SynSumKind (_28_1899) -> begin
_28_1899
end))

# 1051 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___SynSumType____0 : syntax_sum  ->  FStar_Absyn_Syntax.typ = (fun projectee -> (match (projectee) with
| SynSumType (_28_1902) -> begin
_28_1902
end))

# 1052 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___SynSumExp____0 : syntax_sum  ->  FStar_Absyn_Syntax.exp = (fun projectee -> (match (projectee) with
| SynSumExp (_28_1905) -> begin
_28_1905
end))

# 1053 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___SynSumComp____0 : syntax_sum  ->  (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax = (fun projectee -> (match (projectee) with
| SynSumComp (_28_1908) -> begin
_28_1908
end))

# 1055 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec update_uvars : syntax_sum  ->  FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars = (fun s uvs -> (let out = (let _130_1302 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_k)
in (FStar_All.pipe_right _130_1302 (FStar_List.fold_left (fun out u -> (match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (k) -> begin
(let _130_1300 = (uvars_in_kind k)
in (union_uvs _130_1300 out))
end
| _28_1916 -> begin
(let _28_1917 = out
in (let _130_1301 = (FStar_Util.set_add u out.FStar_Absyn_Syntax.uvars_k)
in {FStar_Absyn_Syntax.uvars_k = _130_1301; FStar_Absyn_Syntax.uvars_t = _28_1917.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _28_1917.FStar_Absyn_Syntax.uvars_e}))
end)) FStar_Absyn_Syntax.no_uvs)))
in (let out = (let _130_1307 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_t)
in (FStar_All.pipe_right _130_1307 (FStar_List.fold_left (fun out _28_1923 -> (match (_28_1923) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (t) -> begin
(let _130_1305 = (uvars_in_typ t)
in (union_uvs _130_1305 out))
end
| _28_1927 -> begin
(let _28_1928 = out
in (let _130_1306 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_t)
in {FStar_Absyn_Syntax.uvars_k = _28_1928.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _130_1306; FStar_Absyn_Syntax.uvars_e = _28_1928.FStar_Absyn_Syntax.uvars_e}))
end)
end)) out)))
in (let out = (let _130_1312 = (FStar_Util.set_elements uvs.FStar_Absyn_Syntax.uvars_e)
in (FStar_All.pipe_right _130_1312 (FStar_List.fold_left (fun out _28_1934 -> (match (_28_1934) with
| (u, t) -> begin
(match ((FStar_Unionfind.find u)) with
| FStar_Absyn_Syntax.Fixed (e) -> begin
(let _130_1310 = (uvars_in_exp e)
in (union_uvs _130_1310 out))
end
| _28_1938 -> begin
(let _28_1939 = out
in (let _130_1311 = (FStar_Util.set_add (u, t) out.FStar_Absyn_Syntax.uvars_e)
in {FStar_Absyn_Syntax.uvars_k = _28_1939.FStar_Absyn_Syntax.uvars_k; FStar_Absyn_Syntax.uvars_t = _28_1939.FStar_Absyn_Syntax.uvars_t; FStar_Absyn_Syntax.uvars_e = _130_1311}))
end)
end)) out)))
in (let _28_1950 = (match (s) with
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
and uvars_in_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun k -> (let _130_1315 = (vs_kind k true (fun _28_1956 -> (match (_28_1956) with
| (_28_1954, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumKind (k))) _130_1315)))
and uvars_in_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun t -> (let _130_1318 = (vs_typ t true (fun _28_1961 -> (match (_28_1961) with
| (_28_1959, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumType (t))) _130_1318)))
and uvars_in_exp : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun e -> (let _130_1321 = (vs_exp e true (fun _28_1966 -> (match (_28_1966) with
| (_28_1964, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumExp (e))) _130_1321)))
and uvars_in_comp : (FStar_Absyn_Syntax.comp', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.uvars = (fun c -> (let _130_1324 = (vs_comp c true (fun _28_1971 -> (match (_28_1971) with
| (_28_1969, x) -> begin
x
end)))
in (FStar_All.pipe_left (update_uvars (SynSumComp (c))) _130_1324)))

# 1087 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let uvars_included_in : FStar_Absyn_Syntax.uvars  ->  FStar_Absyn_Syntax.uvars  ->  Prims.bool = (fun u1 u2 -> (((FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_k u2.FStar_Absyn_Syntax.uvars_k) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_t u2.FStar_Absyn_Syntax.uvars_t)) && (FStar_Util.set_is_subset_of u1.FStar_Absyn_Syntax.uvars_e u2.FStar_Absyn_Syntax.uvars_e)))

# 1095 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec kind_formals : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list * (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_lam (_28_1977) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Kind_unknown) | (FStar_Absyn_Syntax.Kind_type) | (FStar_Absyn_Syntax.Kind_effect) | (FStar_Absyn_Syntax.Kind_uvar (_)) -> begin
([], k)
end
| FStar_Absyn_Syntax.Kind_arrow (bs, k) -> begin
(let _28_1991 = (kind_formals k)
in (match (_28_1991) with
| (bs', k) -> begin
((FStar_List.append bs bs'), k)
end))
end
| FStar_Absyn_Syntax.Kind_abbrev (_28_1993, k) -> begin
(kind_formals k)
end
| FStar_Absyn_Syntax.Kind_delayed (_28_1998) -> begin
(FStar_All.failwith "Impossible")
end)))

# 1109 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let close_for_kind : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t k -> (let _28_2005 = (kind_formals k)
in (match (_28_2005) with
| (bs, _28_2004) -> begin
(match (bs) with
| [] -> begin
t
end
| _28_2008 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (bs, t) None t.FStar_Absyn_Syntax.pos)
end)
end)))

# 1115 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unabbreviate_kind : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax = (fun k -> (let k = (compress_kind k)
in (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_abbrev (_28_2012, k) -> begin
(unabbreviate_kind k)
end
| _28_2017 -> begin
k
end)))

# 1121 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let close_with_lam : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _28_2022 -> begin
(FStar_Absyn_Syntax.mk_Typ_lam (tps, t) None t.FStar_Absyn_Syntax.pos)
end))

# 1126 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let close_with_arrow : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun tps t -> (match (tps) with
| [] -> begin
t
end
| _28_2027 -> begin
(let _28_2036 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
((FStar_List.append tps bs'), c)
end
| _28_2033 -> begin
(let _130_1345 = (FStar_Absyn_Syntax.mk_Total t)
in (tps, _130_1345))
end)
in (match (_28_2036) with
| (bs, c) -> begin
(FStar_Absyn_Syntax.mk_Typ_fun (bs, c) None t.FStar_Absyn_Syntax.pos)
end))
end))

# 1135 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let close_typ : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = close_with_arrow

# 1137 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let close_kind : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun tps k -> (match (tps) with
| [] -> begin
k
end
| _28_2041 -> begin
(FStar_Absyn_Syntax.mk_Kind_arrow' (tps, k) k.FStar_Absyn_Syntax.pos)
end))

# 1145 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_tuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.Tuple")
end
| _28_2046 -> begin
false
end))

# 1149 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_tuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (let t = (let _130_1358 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "Tuple%s" _130_1358))
in (let _130_1359 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _130_1359 r))))

# 1153 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_tuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (let t = (let _130_1364 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkTuple%s" _130_1364))
in (let _130_1365 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _130_1365 r))))

# 1157 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_tuple_data_lid : FStar_Ident.lident  ->  Prims.int  ->  Prims.bool = (fun f n -> (let _130_1370 = (mk_tuple_data_lid n FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.lid_equals f _130_1370)))

# 1160 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_dtuple_constructor : FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun t -> (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (l) -> begin
(FStar_Util.starts_with l.FStar_Absyn_Syntax.v.FStar_Ident.str "Prims.DTuple")
end
| _28_2059 -> begin
false
end))

# 1164 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_dtuple_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (let t = (let _130_1377 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "DTuple%s" _130_1377))
in (let _130_1378 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _130_1378 r))))

# 1168 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_dtuple_data_lid : Prims.int  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n r -> (let t = (let _130_1383 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 "MkDTuple%s" _130_1383))
in (let _130_1384 = (FStar_Absyn_Const.pconst t)
in (set_lid_range _130_1384 r))))

# 1173 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_lid_equality : FStar_Ident.lident  ->  Prims.bool = (fun x -> ((((FStar_Ident.lid_equals x FStar_Absyn_Const.eq_lid) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eq2_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqA_lid)) || (FStar_Ident.lid_equals x FStar_Absyn_Const.eqT_lid)))

# 1179 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_forall : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.forall_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.allTyp_lid)))

# 1180 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_exists : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((FStar_Ident.lid_equals lid FStar_Absyn_Const.exists_lid) || (FStar_Ident.lid_equals lid FStar_Absyn_Const.exTyp_lid)))

# 1181 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_qlid : FStar_Ident.lident  ->  Prims.bool = (fun lid -> ((is_forall lid) || (is_exists lid)))

# 1182 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_equality = (fun x -> (is_lid_equality x.FStar_Absyn_Syntax.v))

# 1184 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lid_is_connective : FStar_Ident.lident  ->  Prims.bool = (let lst = (FStar_Absyn_Const.and_lid)::(FStar_Absyn_Const.or_lid)::(FStar_Absyn_Const.not_lid)::(FStar_Absyn_Const.iff_lid)::(FStar_Absyn_Const.imp_lid)::[]
in (fun lid -> (FStar_Util.for_some (FStar_Ident.lid_equals lid) lst)))

# 1189 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_constructor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _130_1400 = (pre_typ t)
in _130_1400.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) -> begin
(FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v lid)
end
| _28_2078 -> begin
false
end))

# 1194 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec is_constructed_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident  ->  Prims.bool = (fun t lid -> (match ((let _130_1405 = (pre_typ t)
in _130_1405.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (_28_2082) -> begin
(is_constructor t lid)
end
| FStar_Absyn_Syntax.Typ_app (t, _28_2086) -> begin
(is_constructed_typ t lid)
end
| _28_2090 -> begin
false
end))

# 1199 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec get_tycon : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun t -> (let t = (pre_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_const (_)) -> begin
Some (t)
end
| FStar_Absyn_Syntax.Typ_app (t, _28_2101) -> begin
(get_tycon t)
end
| _28_2105 -> begin
None
end)))

# 1207 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let base_kind : FStar_Absyn_Syntax.knd'  ->  Prims.bool = (fun _28_25 -> (match (_28_25) with
| FStar_Absyn_Syntax.Kind_type -> begin
true
end
| _28_2109 -> begin
false
end))

# 1211 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let sortByFieldName = (fun fn_a_l -> (FStar_All.pipe_right fn_a_l (FStar_List.sortWith (fun _28_2115 _28_2119 -> (match ((_28_2115, _28_2119)) with
| ((fn1, _28_2114), (fn2, _28_2118)) -> begin
(FStar_String.compare (FStar_Ident.text_of_lid fn1) (FStar_Ident.text_of_lid fn2))
end)))))

# 1219 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kunary FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1220 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let kt_kt_kt : FStar_Absyn_Syntax.knd = (FStar_Absyn_Const.kbin FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype FStar_Absyn_Syntax.ktype)

# 1222 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let tand : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.and_lid kt_kt_kt)

# 1223 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let tor : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.or_lid kt_kt_kt)

# 1224 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let timp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.imp_lid kt_kt_kt)

# 1225 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let tiff : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.iff_lid kt_kt_kt)

# 1226 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let t_bool : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)

# 1227 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let t_false : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)

# 1228 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let t_true : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)

# 1229 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let b2t_v : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (let _130_1416 = (let _130_1415 = (let _130_1414 = (let _130_1413 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder t_bool)
in (_130_1413)::[])
in (_130_1414, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_1415 FStar_Absyn_Syntax.dummyRange))
in (ftv FStar_Absyn_Const.b2t_lid _130_1416))

# 1231 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_conj_opt : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.option = (fun phi1 phi2 -> (match (phi1) with
| None -> begin
Some (phi2)
end
| Some (phi1) -> begin
(let _130_1422 = (let _130_1421 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (tand, ((FStar_Absyn_Syntax.targ phi1))::((FStar_Absyn_Syntax.targ phi2))::[]) None _130_1421))
in Some (_130_1422))
end))

# 1234 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_binop : FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun op_t phi1 phi2 -> (let _130_1429 = (FStar_Range.union_ranges phi1.FStar_Absyn_Syntax.pos phi2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (op_t, ((FStar_Absyn_Syntax.targ phi1))::((FStar_Absyn_Syntax.targ phi2))::[]) None _130_1429)))

# 1235 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_neg : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun phi -> (let _130_1433 = (let _130_1432 = (ftv FStar_Absyn_Const.not_lid kt_kt)
in (_130_1432, ((FStar_Absyn_Syntax.targ phi))::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1433 None phi.FStar_Absyn_Syntax.pos)))

# 1236 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_conj : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tand phi1 phi2))

# 1237 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_conj_l : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_conj tl hd)
end))

# 1240 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_disj : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tor phi1 phi2))

# 1241 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_disj_l : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax Prims.list  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun phi -> (match (phi) with
| [] -> begin
(ftv FStar_Absyn_Const.false_lid FStar_Absyn_Syntax.ktype)
end
| hd::tl -> begin
(FStar_List.fold_right mk_disj tl hd)
end))

# 1244 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_imp : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun phi1 phi2 -> (match ((let _130_1450 = (compress_typ phi1)
in _130_1450.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid) -> begin
t_true
end
| FStar_Absyn_Syntax.Typ_const (tc) when (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) -> begin
phi2
end
| _28_2150 -> begin
(match ((let _130_1451 = (compress_typ phi2)
in _130_1451.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (tc) when ((FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.true_lid) || (FStar_Ident.lid_equals tc.FStar_Absyn_Syntax.v FStar_Absyn_Const.false_lid)) -> begin
phi2
end
| _28_2154 -> begin
(mk_binop timp phi1 phi2)
end)
end))

# 1254 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_iff : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun phi1 phi2 -> (mk_binop tiff phi1 phi2))

# 1255 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let b2t : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun e -> (let _130_1460 = (let _130_1459 = (let _130_1458 = (FStar_All.pipe_left FStar_Absyn_Syntax.varg e)
in (_130_1458)::[])
in (b2t_v, _130_1459))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1460 None e.FStar_Absyn_Syntax.pos)))

# 1257 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec unmeta_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_ascribed (t, _)) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_named (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (t, _, _, _))) | (FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_refresh_label (t, _, _))) -> begin
(unmeta_typ t)
end
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_slack_formula (t1, t2, _28_2194)) -> begin
(mk_conj t1 t2)
end
| _28_2199 -> begin
t
end)))

# 1269 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let eq_k : FStar_Absyn_Syntax.knd = (let a = (let _130_1463 = (new_bvd None)
in (bvd_to_bvar_s _130_1463 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let b = (let _130_1464 = (new_bvd None)
in (bvd_to_bvar_s _130_1464 FStar_Absyn_Syntax.ktype))
in (let btyp = (btvar_to_typ b)
in (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::((FStar_Util.Inl (b), Some (FStar_Absyn_Syntax.Implicit (false))))::((FStar_Absyn_Syntax.null_v_binder atyp))::((FStar_Absyn_Syntax.null_v_binder btyp))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)))))

# 1277 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let teq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.eq2_lid eq_k)

# 1278 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_eq : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 e1 e2 -> (match ((t1.FStar_Absyn_Syntax.n, t2.FStar_Absyn_Syntax.n)) with
| ((FStar_Absyn_Syntax.Typ_unknown, _)) | ((_, FStar_Absyn_Syntax.Typ_unknown)) -> begin
(FStar_All.failwith "DIE! mk_eq with tun")
end
| _28_2217 -> begin
(let _130_1473 = (FStar_Range.union_ranges e1.FStar_Absyn_Syntax.pos e2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (teq, ((FStar_Absyn_Syntax.itarg t1))::((FStar_Absyn_Syntax.itarg t2))::((FStar_Absyn_Syntax.varg e1))::((FStar_Absyn_Syntax.varg e2))::[]) None _130_1473))
end))

# 1282 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let eq_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.eqT_lid FStar_Absyn_Syntax.kun)

# 1283 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_eq_typ : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t1 t2 -> (let _130_1478 = (FStar_Range.union_ranges t1.FStar_Absyn_Syntax.pos t2.FStar_Absyn_Syntax.pos)
in (FStar_Absyn_Syntax.mk_Typ_app (eq_typ, ((FStar_Absyn_Syntax.targ t1))::((FStar_Absyn_Syntax.targ t2))::[]) None _130_1478)))

# 1285 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lex_t : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.lex_t_lid FStar_Absyn_Syntax.ktype)

# 1286 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lex_top : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (let lexnil = (withinfo FStar_Absyn_Const.lextop_lid lex_t FStar_Absyn_Syntax.dummyRange)
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexnil, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange))

# 1290 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let lex_pair : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (let a = (gen_bvar FStar_Absyn_Syntax.ktype)
in (let lexcons = (let _130_1485 = (let _130_1484 = (let _130_1483 = (let _130_1481 = (let _130_1480 = (let _130_1479 = (btvar_to_typ a)
in (FStar_Absyn_Syntax.null_v_binder _130_1479))
in (_130_1480)::((FStar_Absyn_Syntax.null_v_binder lex_t))::[])
in ((FStar_Absyn_Syntax.t_binder a))::_130_1481)
in (let _130_1482 = (FStar_Absyn_Syntax.mk_Total lex_t)
in (_130_1483, _130_1482)))
in (FStar_Absyn_Syntax.mk_Typ_fun _130_1484 None FStar_Absyn_Syntax.dummyRange))
in (withinfo FStar_Absyn_Const.lexcons_lid _130_1485 FStar_Absyn_Syntax.dummyRange))
in (FStar_Absyn_Syntax.mk_Exp_fvar (lexcons, Some (FStar_Absyn_Syntax.Data_ctor)) None FStar_Absyn_Syntax.dummyRange)))

# 1295 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let forall_kind : FStar_Absyn_Syntax.knd = (let a = (let _130_1486 = (new_bvd None)
in (bvd_to_bvar_s _130_1486 FStar_Absyn_Syntax.ktype))
in (let atyp = (btvar_to_typ a)
in (let _130_1491 = (let _130_1490 = (let _130_1489 = (let _130_1488 = (let _130_1487 = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_v_binder atyp))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _130_1487))
in (_130_1488)::[])
in ((FStar_Util.Inl (a), Some (FStar_Absyn_Syntax.Implicit (false))))::_130_1489)
in (_130_1490, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_1491 FStar_Absyn_Syntax.dummyRange))))

# 1302 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let tforall : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (ftv FStar_Absyn_Const.forall_lid forall_kind)

# 1304 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let allT_k : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _130_1497 = (let _130_1496 = (let _130_1495 = (let _130_1494 = (FStar_Absyn_Syntax.mk_Kind_arrow (((FStar_Absyn_Syntax.null_t_binder k))::[], FStar_Absyn_Syntax.ktype) FStar_Absyn_Syntax.dummyRange)
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder _130_1494))
in (_130_1495)::[])
in (_130_1496, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_1497 FStar_Absyn_Syntax.dummyRange)))

# 1305 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let eqT_k : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.knd = (fun k -> (let _130_1502 = (let _130_1501 = (let _130_1500 = (FStar_All.pipe_left FStar_Absyn_Syntax.null_t_binder k)
in (_130_1500)::((FStar_Absyn_Syntax.null_t_binder k))::[])
in (_130_1501, FStar_Absyn_Syntax.ktype))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_1502 FStar_Absyn_Syntax.dummyRange)))

# 1307 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let tforall_typ : (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun k -> (let _130_1505 = (allT_k k)
in (ftv FStar_Absyn_Const.allTyp_lid _130_1505)))

# 1309 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_forallT : ((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun a b -> (let _130_1514 = (let _130_1513 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (let _130_1512 = (let _130_1511 = (let _130_1510 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.t_binder a))::[], b) None b.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_1510))
in (_130_1511)::[])
in (_130_1513, _130_1512)))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1514 None b.FStar_Absyn_Syntax.pos)))

# 1312 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let mk_forall : FStar_Absyn_Syntax.bvvar  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun x body -> (let r = FStar_Absyn_Syntax.dummyRange
in (let _130_1522 = (let _130_1521 = (let _130_1520 = (let _130_1519 = (FStar_Absyn_Syntax.mk_Typ_lam (((FStar_Absyn_Syntax.v_binder x))::[], body) None r)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_1519))
in (_130_1520)::[])
in (tforall, _130_1521))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1522 None r))))

# 1316 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec close_forall : FStar_Absyn_Syntax.binder Prims.list  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun bs f -> (FStar_List.fold_right (fun b f -> if (FStar_Absyn_Syntax.is_null_binder b) then begin
f
end else begin
(let body = (FStar_Absyn_Syntax.mk_Typ_lam ((b)::[], f) None f.FStar_Absyn_Syntax.pos)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(let _130_1530 = (let _130_1529 = (tforall_typ a.FStar_Absyn_Syntax.sort)
in (_130_1529, ((FStar_Absyn_Syntax.targ body))::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _130_1530 None f.FStar_Absyn_Syntax.pos))
end
| FStar_Util.Inr (x) -> begin
(FStar_Absyn_Syntax.mk_Typ_app (tforall, ((FStar_Util.Inl (x.FStar_Absyn_Syntax.sort), Some (FStar_Absyn_Syntax.Implicit (false))))::((FStar_Absyn_Syntax.targ body))::[]) None f.FStar_Absyn_Syntax.pos)
end))
end) bs f))

# 1325 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let rec is_wild_pat = (fun p -> (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_wild (_28_2244) -> begin
true
end
| _28_2247 -> begin
false
end))

# 1330 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let head_and_args : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.args) = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(head, args)
end
| _28_2255 -> begin
(t, [])
end)))

# 1336 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let head_and_args_e : (FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.exp * FStar_Absyn_Syntax.args) = (fun e -> (let e = (compress_exp e)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_app (head, args) -> begin
(head, args)
end
| _28_2263 -> begin
(e, [])
end)))

# 1342 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let function_formals : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.binders * FStar_Absyn_Syntax.comp) Prims.option = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs, c) -> begin
Some ((bs, c))
end
| _28_2271 -> begin
None
end)))

# 1348 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_interpreted : FStar_Ident.lident  ->  Prims.bool = (fun l -> (let theory_syms = (FStar_Absyn_Const.op_Eq)::(FStar_Absyn_Const.op_notEq)::(FStar_Absyn_Const.op_LT)::(FStar_Absyn_Const.op_LTE)::(FStar_Absyn_Const.op_GT)::(FStar_Absyn_Const.op_GTE)::(FStar_Absyn_Const.op_Subtraction)::(FStar_Absyn_Const.op_Minus)::(FStar_Absyn_Const.op_Addition)::(FStar_Absyn_Const.op_Multiply)::(FStar_Absyn_Const.op_Division)::(FStar_Absyn_Const.op_Modulus)::(FStar_Absyn_Const.op_And)::(FStar_Absyn_Const.op_Or)::(FStar_Absyn_Const.op_Negation)::[]
in (FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms)))

# 1370 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type qpats =
FStar_Absyn_Syntax.args Prims.list

# 1371 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

type connective =
| QAll of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| QEx of (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ)
| BaseConn of (FStar_Ident.lident * FStar_Absyn_Syntax.args)

# 1372 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_QAll = (fun _discr_ -> (match (_discr_) with
| QAll (_) -> begin
true
end
| _ -> begin
false
end))

# 1373 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_QEx = (fun _discr_ -> (match (_discr_) with
| QEx (_) -> begin
true
end
| _ -> begin
false
end))

# 1374 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let is_BaseConn = (fun _discr_ -> (match (_discr_) with
| BaseConn (_) -> begin
true
end
| _ -> begin
false
end))

# 1372 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___QAll____0 : connective  ->  (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| QAll (_28_2276) -> begin
_28_2276
end))

# 1373 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___QEx____0 : connective  ->  (FStar_Absyn_Syntax.binders * qpats * FStar_Absyn_Syntax.typ) = (fun projectee -> (match (projectee) with
| QEx (_28_2279) -> begin
_28_2279
end))

# 1374 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let ___BaseConn____0 : connective  ->  (FStar_Ident.lident * FStar_Absyn_Syntax.args) = (fun projectee -> (match (projectee) with
| BaseConn (_28_2282) -> begin
_28_2282
end))

# 1376 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\absyn\\util.fs"

let destruct_typ_as_formula : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  connective Prims.option = (fun f -> (let destruct_base_conn = (fun f -> (let _28_2288 = (true, false)
in (match (_28_2288) with
| (type_sort, term_sort) -> begin
(let oneType = (type_sort)::[]
in (let twoTypes = (type_sort)::(type_sort)::[]
in (let threeTys = (type_sort)::(type_sort)::(type_sort)::[]
in (let twoTerms = (term_sort)::(term_sort)::[]
in (let connectives = ((FStar_Absyn_Const.true_lid, []))::((FStar_Absyn_Const.false_lid, []))::((FStar_Absyn_Const.and_lid, twoTypes))::((FStar_Absyn_Const.or_lid, twoTypes))::((FStar_Absyn_Const.imp_lid, twoTypes))::((FStar_Absyn_Const.iff_lid, twoTypes))::((FStar_Absyn_Const.ite_lid, threeTys))::((FStar_Absyn_Const.not_lid, oneType))::((FStar_Absyn_Const.eqT_lid, twoTypes))::((FStar_Absyn_Const.eq2_lid, twoTerms))::((FStar_Absyn_Const.eq2_lid, (FStar_List.append twoTypes twoTerms)))::[]
in (let rec aux = (fun f _28_2298 -> (match (_28_2298) with
| (lid, arity) -> begin
(let _28_2301 = (head_and_args f)
in (match (_28_2301) with
| (t, args) -> begin
if (((is_constructor t lid) && ((FStar_List.length args) = (FStar_List.length arity))) && (FStar_List.forall2 (fun arg flag -> (match (arg) with
| (FStar_Util.Inl (_28_2305), _28_2308) -> begin
(flag = type_sort)
end
| (FStar_Util.Inr (_28_2311), _28_2314) -> begin
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
in (let patterns = (fun t -> (let t = (compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_pattern (t, pats)) -> begin
(let _130_1594 = (compress_typ t)
in (pats, _130_1594))
end
| _28_2325 -> begin
(let _130_1595 = (compress_typ t)
in ([], _130_1595))
end)))
in (let destruct_q_conn = (fun t -> (let is_q = (fun fa l -> if fa then begin
(is_forall l)
end else begin
(is_exists l)
end)
in (let flat = (fun t -> (let _28_2335 = (head_and_args t)
in (match (_28_2335) with
| (t, args) -> begin
(let _130_1609 = (FStar_All.pipe_right args (FStar_List.map (fun _28_26 -> (match (_28_26) with
| (FStar_Util.Inl (t), imp) -> begin
(let _130_1606 = (let _130_1605 = (compress_typ t)
in FStar_Util.Inl (_130_1605))
in (_130_1606, imp))
end
| (FStar_Util.Inr (e), imp) -> begin
(let _130_1608 = (let _130_1607 = (compress_exp e)
in FStar_Util.Inr (_130_1607))
in (_130_1608, imp))
end))))
in (t, _130_1609))
end)))
in (let rec aux = (fun qopt out t -> (match ((let _130_1616 = (flat t)
in (qopt, _130_1616))) with
| ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((Some (fa), ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_q fa tc.FStar_Absyn_Syntax.v) -> begin
(aux qopt ((b)::out) t2)
end
| ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, (FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) | ((None, ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (tc); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _::(FStar_Util.Inl ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_lam (b::[], t2); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}), _)::[]))) when (is_qlid tc.FStar_Absyn_Syntax.v) -> begin
(aux (Some ((is_forall tc.FStar_Absyn_Syntax.v))) ((b)::out) t2)
end
| (Some (true), _28_2483) -> begin
(let _28_2487 = (patterns t)
in (match (_28_2487) with
| (pats, body) -> begin
Some (QAll (((FStar_List.rev out), pats, body)))
end))
end
| (Some (false), _28_2491) -> begin
(let _28_2495 = (patterns t)
in (match (_28_2495) with
| (pats, body) -> begin
Some (QEx (((FStar_List.rev out), pats, body)))
end))
end
| _28_2497 -> begin
None
end))
in (aux None [] t)))))
in (let phi = (compress_typ f)
in (match ((destruct_base_conn phi)) with
| Some (b) -> begin
Some (b)
end
| None -> begin
(destruct_q_conn phi)
end))))))





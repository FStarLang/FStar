
open Prims

let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _35_21) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _35_27 -> begin
t
end)
end
| _35_29 -> begin
t
end))


let rec force_delayed_thunk : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (f, m) -> begin
(match ((FStar_ST.read m)) with
| None -> begin
(match (f) with
| FStar_Util.Inr (c) -> begin
(

let t' = (let _124_8 = (c ())
in (force_delayed_thunk _124_8))
in (

let _35_39 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_42 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _35_46 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_49 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _35_56 -> begin
u
end)
end
| _35_58 -> begin
u
end))


let bv_to_string' : (FStar_Syntax_Syntax.bv  ->  Prims.string) FStar_ST.ref = (FStar_ST.alloc (fun x -> (FStar_All.failwith "Not initialized!")))


let print_term' : (FStar_Syntax_Syntax.term  ->  Prims.string) FStar_ST.ref = (FStar_ST.alloc (fun t -> (FStar_All.failwith "Not initialized!")))


let print_univ' : (FStar_Syntax_Syntax.universe  ->  Prims.string) FStar_ST.ref = (FStar_ST.alloc (fun u -> (FStar_All.failwith "Not initialized!")))


let bv_to_string : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun x -> (FStar_ST.read bv_to_string' x))


let print_term : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  Prims.string = (fun t -> (FStar_ST.read print_term' t))


let print_univ : FStar_Syntax_Syntax.universe  ->  Prims.string = (fun u -> (FStar_ST.read print_univ' u))


let renaming_elt_to_string : FStar_Syntax_Syntax.renaming_subst  ->  Prims.string = (fun _35_1 -> (match (_35_1) with
| FStar_Syntax_Syntax.Index2Name (i, x) -> begin
(let _124_40 = (FStar_Util.string_of_int i)
in (let _124_39 = (bv_to_string x)
in (FStar_Util.format2 "Index2Name (%s, %s)" _124_40 _124_39)))
end
| FStar_Syntax_Syntax.Name2Index (x, i) -> begin
(let _124_42 = (bv_to_string x)
in (let _124_41 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Name2Index (%s, %s)" _124_42 _124_41)))
end
| FStar_Syntax_Syntax.Name2Name (x, y) -> begin
(let _124_44 = (bv_to_string x)
in (let _124_43 = (bv_to_string y)
in (FStar_Util.format2 "Name2Name(%s, %s)" _124_44 _124_43)))
end
| FStar_Syntax_Syntax.Index2Index (i, j) -> begin
(let _124_46 = (FStar_Util.string_of_int i)
in (let _124_45 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "Index2Index (%d, %d)" _124_46 _124_45)))
end
| FStar_Syntax_Syntax.UIndex2UName (i, u) -> begin
(let _124_47 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UIndex2Uname(%d, %s)" _124_47 u.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.UName2UIndex (u, i) -> begin
(let _124_48 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UName2UIndex (%s, %s)" u.FStar_Ident.idText _124_48))
end
| FStar_Syntax_Syntax.UIndex2UIndex (i, j) -> begin
(let _124_50 = (FStar_Util.string_of_int i)
in (let _124_49 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "UIndex2UIndex (%d, %d)" _124_50 _124_49)))
end
| FStar_Syntax_Syntax.UName2UName (u, v) -> begin
(FStar_Util.format2 "UName2UName(%s, %s)" u.FStar_Ident.idText v.FStar_Ident.idText)
end))


let renaming_to_string : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  Prims.string = (fun r -> (let _124_54 = (let _124_53 = (FStar_All.pipe_right r (FStar_List.map renaming_elt_to_string))
in (FStar_All.pipe_right _124_53 (FStar_String.concat "; ")))
in (FStar_Util.format1 "Renaming[%s]" _124_54)))


let instantiation_elt_to_string : FStar_Syntax_Syntax.inst_subst  ->  Prims.string = (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.Name2Term (x, t) -> begin
(let _124_58 = (bv_to_string x)
in (let _124_57 = (print_term t)
in (FStar_Util.format2 "Name2Term(%s, %s)" _124_58 _124_57)))
end
| FStar_Syntax_Syntax.UName2Univ (un, u) -> begin
(let _124_59 = (print_univ u)
in (FStar_Util.format2 "UName2Univ(%s, %s)" un.FStar_Ident.idText _124_59))
end))


let instantiation_to_string : FStar_Syntax_Syntax.inst_subst Prims.list  ->  Prims.string = (fun i -> (let _124_63 = (let _124_62 = (FStar_All.pipe_right i (FStar_List.map instantiation_elt_to_string))
in (FStar_All.pipe_right _124_62 (FStar_String.concat "; ")))
in (FStar_Util.format1 "Instantiation[%s]" _124_63)))


let subst_to_string : FStar_Syntax_Syntax.subst_ts  ->  Prims.string = (fun s -> (let _124_67 = (FStar_All.pipe_right s (FStar_List.map (fun _35_3 -> (match (_35_3) with
| FStar_Syntax_Syntax.Renaming (r) -> begin
(renaming_to_string r)
end
| FStar_Syntax_Syntax.Instantiation (i) -> begin
(instantiation_to_string i)
end))))
in (FStar_All.pipe_right _124_67 (FStar_String.concat "; "))))


type renaming =
FStar_Syntax_Syntax.renaming_subst Prims.list


type inst =
FStar_Syntax_Syntax.inst_subst Prims.list


let subst_index : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.term Prims.option = (fun i s -> (

let rename_index = (fun a renaming -> (FStar_Util.find_map renaming (fun _35_4 -> (match (_35_4) with
| FStar_Syntax_Syntax.Index2Name (i, x) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _124_79 = (let _124_78 = (let _124_77 = (FStar_Syntax_Syntax.range_of_bv a)
in (FStar_Syntax_Syntax.set_range_of_bv x _124_77))
in (FStar_Syntax_Syntax.bv_to_name _124_78))
in Some (_124_79))
end
| FStar_Syntax_Syntax.Index2Index (i, j) when (i = a.FStar_Syntax_Syntax.index) -> begin
(let _124_80 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_129 = a
in {FStar_Syntax_Syntax.ppname = _35_129.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = j; FStar_Syntax_Syntax.sort = _35_129.FStar_Syntax_Syntax.sort}))
in Some (_124_80))
end
| _35_132 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_index i renaming)
end
| _35_136 -> begin
None
end)))


let subst_name : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.term Prims.option = (fun x s -> (

let rename_name = (fun a renaming -> (FStar_Util.find_map renaming (fun _35_5 -> (match (_35_5) with
| FStar_Syntax_Syntax.Name2Index (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_90 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_147 = a
in {FStar_Syntax_Syntax.ppname = _35_147.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_147.FStar_Syntax_Syntax.sort}))
in Some (_124_90))
end
| FStar_Syntax_Syntax.Name2Name (x, y) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_91 = (FStar_Syntax_Syntax.bv_to_name y)
in Some (_124_91))
end
| _35_154 -> begin
None
end))))
in (

let instantiate = (fun x inst -> (FStar_Util.find_map inst (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.Name2Term (y, t) when (FStar_Syntax_Syntax.bv_eq x y) -> begin
Some (t)
end
| _35_164 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_name x renaming)
end
| FStar_Syntax_Syntax.Instantiation (inst) -> begin
(instantiate x inst)
end))))


let subst_uindex : Prims.int  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.universe Prims.option = (fun i s -> (

let rename_uindex = (fun i renaming -> (FStar_Util.find_map renaming (fun _35_7 -> (match (_35_7) with
| FStar_Syntax_Syntax.UIndex2UName (j, t) when (i = j) -> begin
Some (FStar_Syntax_Syntax.U_name (t))
end
| FStar_Syntax_Syntax.UIndex2UIndex (j, k) when (i = j) -> begin
Some (FStar_Syntax_Syntax.U_bvar (k))
end
| _35_184 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_uindex i renaming)
end
| _35_188 -> begin
None
end)))


let subst_uname : FStar_Syntax_Syntax.univ_name  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.universe Prims.option = (fun x s -> (

let rename_uname = (fun x renaming -> (FStar_Util.find_map renaming (fun _35_8 -> (match (_35_8) with
| FStar_Syntax_Syntax.UName2UIndex (y, i) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_bvar (i))
end
| FStar_Syntax_Syntax.UName2UName (y, z) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (FStar_Syntax_Syntax.U_name (z))
end
| _35_204 -> begin
None
end))))
in (

let instantiate_uname = (fun x inst -> (FStar_Util.find_map inst (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.UName2Univ (y, t) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (t)
end
| _35_214 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_uname x renaming)
end
| FStar_Syntax_Syntax.Instantiation (inst) -> begin
(instantiate_uname x inst)
end))))


let rec apply_until_some = (fun f s -> (match (s) with
| [] -> begin
None
end
| s0::rest -> begin
(match ((f s0)) with
| None -> begin
(apply_until_some f rest)
end
| Some (st) -> begin
Some ((rest, st))
end)
end))


let map_some_curry = (fun f x _35_10 -> (match (_35_10) with
| None -> begin
x
end
| Some (a, b) -> begin
(f a b)
end))


let apply_until_some_then_map = (fun f s g t -> (let _124_147 = (apply_until_some f s)
in (FStar_All.pipe_right _124_147 (map_some_curry g t))))


let rec subst_univ : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun s u -> (

let u = (compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_bvar (x) -> begin
(apply_until_some_then_map (subst_uindex x) s subst_univ u)
end
| FStar_Syntax_Syntax.U_name (x) -> begin
(apply_until_some_then_map (subst_uname x) s subst_univ u)
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _124_152 = (subst_univ s u)
in FStar_Syntax_Syntax.U_succ (_124_152))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _124_153 = (FStar_List.map (subst_univ s) us)
in FStar_Syntax_Syntax.U_max (_124_153))
end)))


let compose_renamings : renaming  ->  renaming  ->  renaming = (fun s1 s2 -> (

let find_and_remove = (fun f s -> (

let rec aux = (fun out s -> (match (s) with
| [] -> begin
(None, out)
end
| hd::tl -> begin
if (f hd) then begin
(Some (hd), (FStar_List.append out tl))
end else begin
(aux ((hd)::out) tl)
end
end))
in (aux [] s)))
in (

let find_name = (fun s x -> (FStar_All.pipe_right s (find_and_remove (fun _35_11 -> (match (_35_11) with
| (FStar_Syntax_Syntax.Name2Index (y, _)) | (FStar_Syntax_Syntax.Name2Name (y, _)) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| _35_282 -> begin
false
end)))))
in (

let find_index = (fun s i -> (FStar_All.pipe_right s (find_and_remove (fun _35_12 -> (match (_35_12) with
| (FStar_Syntax_Syntax.Index2Name (j, _)) | (FStar_Syntax_Syntax.Index2Index (j, _)) -> begin
(i = j)
end
| _35_297 -> begin
false
end)))))
in (

let find_uindex = (fun s2 i -> (FStar_All.pipe_right s2 (find_and_remove (fun _35_13 -> (match (_35_13) with
| (FStar_Syntax_Syntax.UIndex2UName (j, _)) | (FStar_Syntax_Syntax.UIndex2UIndex (j, _)) -> begin
(i = j)
end
| _35_312 -> begin
false
end)))))
in (

let find_uname = (fun s2 n -> (FStar_All.pipe_right s2 (find_and_remove (fun _35_14 -> (match (_35_14) with
| (FStar_Syntax_Syntax.UName2UIndex (m, _)) | (FStar_Syntax_Syntax.UName2UName (m, _)) -> begin
(n.FStar_Ident.idText = m.FStar_Ident.idText)
end
| _35_327 -> begin
false
end)))))
in (

let s2_orig = s2
in (

let comp = (FStar_All.pipe_right s1 (FStar_List.fold_left (fun s2 s1_elt -> (match (s1_elt) with
| FStar_Syntax_Syntax.Index2Name (i, x) -> begin
(

let _35_337 = (find_name s2 x)
in (match (_35_337) with
| (s2_x, s2_remainder) -> begin
(match (s2_x) with
| Some (FStar_Syntax_Syntax.Name2Index (_35_339, j)) -> begin
if (i = j) then begin
s2_remainder
end else begin
(FStar_Syntax_Syntax.Index2Index ((i, j)))::s2_remainder
end
end
| Some (FStar_Syntax_Syntax.Name2Name (_35_345, y)) -> begin
(FStar_Syntax_Syntax.Index2Name ((i, y)))::s2_remainder
end
| _35_351 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.Name2Index (x, i) -> begin
(

let _35_358 = (find_index s2 i)
in (match (_35_358) with
| (s2_i, s2_remainder) -> begin
(match (s2_i) with
| Some (FStar_Syntax_Syntax.Index2Name (_35_360, y)) -> begin
(FStar_Syntax_Syntax.Name2Name ((x, y)))::s2_remainder
end
| Some (FStar_Syntax_Syntax.Index2Index (_35_366, j)) -> begin
(FStar_Syntax_Syntax.Name2Index ((x, j)))::s2_remainder
end
| _35_372 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.Index2Index (i, j) -> begin
(

let _35_379 = (find_index s2 i)
in (match (_35_379) with
| (s2_i, s2_remainder) -> begin
(match (s2_i) with
| Some (FStar_Syntax_Syntax.Index2Name (_35_381, y)) -> begin
(FStar_Syntax_Syntax.Index2Name ((i, y)))::s2_remainder
end
| Some (FStar_Syntax_Syntax.Index2Index (_35_387, k)) -> begin
(FStar_Syntax_Syntax.Index2Index ((i, k)))::s2_remainder
end
| _35_393 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.Name2Name (x, y) -> begin
(

let _35_401 = (find_name s2 y)
in (match (_35_401) with
| (s2_y, _35_400) -> begin
(match (s2_y) with
| Some (FStar_Syntax_Syntax.Name2Index (_35_403, j)) -> begin
(FStar_Syntax_Syntax.Name2Index ((x, j)))::s2
end
| _35_409 -> begin
(s1_elt)::s2
end)
end))
end
| FStar_Syntax_Syntax.UIndex2UName (i, n) -> begin
(

let _35_416 = (find_uname s2 n)
in (match (_35_416) with
| (u_n, s2_remainder) -> begin
(match (u_n) with
| Some (FStar_Syntax_Syntax.UName2UIndex (_35_418, j)) -> begin
if (i = j) then begin
s2_remainder
end else begin
(FStar_Syntax_Syntax.UIndex2UIndex ((i, j)))::s2_remainder
end
end
| Some (FStar_Syntax_Syntax.UName2UName (_35_424, u)) -> begin
(FStar_Syntax_Syntax.UIndex2UName ((i, u)))::s2_remainder
end
| _35_430 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.UName2UIndex (u, i) -> begin
(

let _35_437 = (find_uindex s2 i)
in (match (_35_437) with
| (u_i, s2_remainder) -> begin
(match (u_i) with
| Some (FStar_Syntax_Syntax.UIndex2UName (_35_439, v)) -> begin
(FStar_Syntax_Syntax.UName2UName ((u, v)))::s2_remainder
end
| Some (FStar_Syntax_Syntax.UIndex2UIndex (_35_445, k)) -> begin
(FStar_Syntax_Syntax.UName2UIndex ((u, k)))::s2_remainder
end
| _35_451 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.UName2UName (u, v) -> begin
(

let _35_458 = (find_uname s2 v)
in (match (_35_458) with
| (u_i, s2_remainder) -> begin
(match (u_i) with
| Some (FStar_Syntax_Syntax.UName2UIndex (_35_460, i)) -> begin
(FStar_Syntax_Syntax.UName2UIndex ((u, i)))::s2
end
| Some (FStar_Syntax_Syntax.UName2UName (_35_466, w)) -> begin
(FStar_Syntax_Syntax.UName2UName ((u, w)))::s2
end
| _35_472 -> begin
(s1_elt)::s2_remainder
end)
end))
end
| FStar_Syntax_Syntax.UIndex2UIndex (i, j) -> begin
(

let _35_479 = (find_uindex s2 i)
in (match (_35_479) with
| (s2_i, s2_remainder) -> begin
(match (s2_i) with
| Some (FStar_Syntax_Syntax.UIndex2UName (_35_481, y)) -> begin
(FStar_Syntax_Syntax.UIndex2UName ((i, y)))::s2_remainder
end
| Some (FStar_Syntax_Syntax.UIndex2UIndex (_35_487, k)) -> begin
(FStar_Syntax_Syntax.UIndex2UIndex ((i, k)))::s2_remainder
end
| _35_493 -> begin
(s1_elt)::s2_remainder
end)
end))
end)) s2))
in comp))))))))


let compose_subst : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun s1 s2 -> (

let composed = (FStar_List.append s1 s2)
in (FStar_List.fold_right (fun ri out -> (match ((ri, out)) with
| (FStar_Syntax_Syntax.Renaming (re1), FStar_Syntax_Syntax.Renaming (re2)::tl) -> begin
(let _124_200 = (let _124_199 = (compose_renamings re1 re2)
in FStar_Syntax_Syntax.Renaming (_124_199))
in (_124_200)::tl)
end
| _35_508 -> begin
(ri)::out
end)) [] composed)))


let shift : Prims.int  ->  FStar_Syntax_Syntax.renaming_subst  ->  FStar_Syntax_Syntax.renaming_subst = (fun n s -> (match (s) with
| FStar_Syntax_Syntax.Index2Name (i, t) -> begin
FStar_Syntax_Syntax.Index2Name (((i + n), t))
end
| FStar_Syntax_Syntax.Index2Index (i, j) -> begin
FStar_Syntax_Syntax.Index2Index (((i + n), (j + n)))
end
| FStar_Syntax_Syntax.Name2Index (x, i) -> begin
FStar_Syntax_Syntax.Name2Index ((x, (i + n)))
end
| FStar_Syntax_Syntax.UName2UIndex (x, i) -> begin
FStar_Syntax_Syntax.UName2UIndex ((x, (i + n)))
end
| FStar_Syntax_Syntax.UIndex2UName (i, x) -> begin
FStar_Syntax_Syntax.UIndex2UName (((i + n), x))
end
| FStar_Syntax_Syntax.UIndex2UIndex (i, j) -> begin
FStar_Syntax_Syntax.UIndex2UIndex (((i + n), (j + n)))
end
| (FStar_Syntax_Syntax.UName2UName (_)) | (FStar_Syntax_Syntax.Name2Name (_)) -> begin
s
end))


let shift_renaming : Prims.int  ->  FStar_Syntax_Syntax.renaming  ->  FStar_Syntax_Syntax.renaming = (fun n s -> (FStar_List.map (shift n) s))


let shift_subst : Prims.int  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_ts = (fun n s -> (FStar_List.map (fun _35_15 -> (match (_35_15) with
| FStar_Syntax_Syntax.Renaming (s) -> begin
(let _124_214 = (shift_renaming n s)
in FStar_Syntax_Syntax.Renaming (_124_214))
end
| x -> begin
x
end)) s))


let rec subst' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| [] -> begin
t
end
| _35_553 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _124_228 = (let _124_227 = (let _124_226 = (compose_subst s' s)
in (t', _124_226))
in FStar_Util.Inl (_124_227))
in (FStar_Syntax_Syntax.mk_Tm_delayed _124_228 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_572), _35_575) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(apply_until_some_then_map (subst_index a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(apply_until_some_then_map (subst_name a) s subst' t0)
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _124_231 = (let _124_230 = (subst_univ s u)
in FStar_Syntax_Syntax.Tm_type (_124_230))
in (FStar_Syntax_Syntax.mk _124_231 None t0.FStar_Syntax_Syntax.pos))
end
| _35_585 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, s))) t.FStar_Syntax_Syntax.pos)
end))
end))
and subst_flags' : FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.cflags Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_16 -> (match (_35_16) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _124_236 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_124_236))
end
| f -> begin
f
end)))))
and subst_comp_typ' : FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.comp_typ  ->  FStar_Syntax_Syntax.comp_typ = (fun s t -> (match (s) with
| [] -> begin
t
end
| _35_596 -> begin
(

let _35_597 = t
in (let _124_243 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _124_242 = (FStar_List.map (fun _35_601 -> (match (_35_601) with
| (t, imp) -> begin
(let _124_240 = (subst' s t)
in (_124_240, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _124_241 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_597.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _124_243; FStar_Syntax_Syntax.effect_args = _124_242; FStar_Syntax_Syntax.flags = _124_241}))))
end))
and subst_comp' : FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s t -> (match (s) with
| [] -> begin
t
end
| _35_606 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _124_246 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _124_246))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _124_247 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _124_247))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _124_248 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _124_248))
end)
end))


let subst_binder' = (fun s _35_616 -> (match (_35_616) with
| (x, imp) -> begin
(let _124_252 = (

let _35_617 = x
in (let _124_251 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_617.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_617.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_251}))
in (_124_252, imp))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _124_257 = (shift_subst i s)
in (subst_binder' _124_257 b))
end))))


let subst_arg' = (fun s _35_626 -> (match (_35_626) with
| (t, imp) -> begin
(let _124_260 = (subst' s t)
in (_124_260, imp))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_636) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_644 = (aux n p)
in (match (_35_644) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _124_273 = (aux n p)
in (Prims.fst _124_273))) ps)
in ((

let _35_647 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_647.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_647.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_664 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_655 _35_658 -> (match ((_35_655, _35_658)) with
| ((pats, n), (p, imp)) -> begin
(

let _35_661 = (aux n p)
in (match (_35_661) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_664) with
| (pats, n) -> begin
((

let _35_665 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_665.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_665.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_670 = x
in (let _124_276 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_670.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_670.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_276}))
in ((

let _35_673 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_673.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_673.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_678 = x
in (let _124_277 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_678.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_678.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_277}))
in ((

let _35_681 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_681.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_681.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_688 = x
in (let _124_278 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_688.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_688.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_278}))
in (

let t0 = (subst' s t0)
in ((

let _35_692 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_692.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_692.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _124_285 = (let _124_284 = (

let _35_704 = l
in (let _124_283 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_704.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_283; FStar_Syntax_Syntax.cflags = _35_704.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_706 -> (match (()) with
| () -> begin
(let _124_282 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _124_282))
end))}))
in FStar_Util.Inl (_124_284))
in Some (_124_285))
end))


let push_subst : FStar_Syntax_Syntax.subst_ts  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_710) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(subst' s t)
end
| FStar_Syntax_Syntax.Tm_uinst (t', us) -> begin
(

let us = (FStar_List.map (subst_univ s) us)
in (FStar_Syntax_Syntax.mk_Tm_uinst t' us))
end
| FStar_Syntax_Syntax.Tm_app (t0, args) -> begin
(let _124_296 = (let _124_295 = (let _124_294 = (subst' s t0)
in (let _124_293 = (subst_args' s args)
in (_124_294, _124_293)))
in FStar_Syntax_Syntax.Tm_app (_124_295))
in (FStar_Syntax_Syntax.mk _124_296 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _124_301 = (let _124_300 = (let _124_299 = (subst' s t0)
in (let _124_298 = (let _124_297 = (subst' s t1)
in FStar_Util.Inl (_124_297))
in (_124_299, _124_298, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_300))
in (FStar_Syntax_Syntax.mk _124_301 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _124_306 = (let _124_305 = (let _124_304 = (subst' s t0)
in (let _124_303 = (let _124_302 = (subst_comp' s c)
in FStar_Util.Inr (_124_302))
in (_124_304, _124_303, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_305))
in (FStar_Syntax_Syntax.mk _124_306 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst n s)
in (let _124_311 = (let _124_310 = (let _124_309 = (subst_binders' s bs)
in (let _124_308 = (subst' s' body)
in (let _124_307 = (push_subst_lcomp s' lopt)
in (_124_309, _124_308, _124_307))))
in FStar_Syntax_Syntax.Tm_abs (_124_310))
in (FStar_Syntax_Syntax.mk _124_311 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _124_316 = (let _124_315 = (let _124_314 = (subst_binders' s bs)
in (let _124_313 = (let _124_312 = (shift_subst n s)
in (subst_comp' _124_312 comp))
in (_124_314, _124_313)))
in FStar_Syntax_Syntax.Tm_arrow (_124_315))
in (FStar_Syntax_Syntax.mk _124_316 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_768 = x
in (let _124_317 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_768.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_768.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_317}))
in (

let phi = (let _124_318 = (shift_subst 1 s)
in (subst' _124_318 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_780 -> (match (_35_780) with
| (pat, wopt, branch) -> begin
(

let _35_783 = (subst_pat' s pat)
in (match (_35_783) with
| (pat, n) -> begin
(

let s = (shift_subst n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_320 = (subst' s w)
in Some (_124_320))
end)
in (

let branch = (subst' s branch)
in (pat, wopt, branch))))
end))
end))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((t0, pats))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_let ((is_rec, lbs), body) -> begin
(

let n = (FStar_List.length lbs)
in (

let sn = (shift_subst n s)
in (

let body = (subst' sn body)
in (

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let lbt = (subst' s lb.FStar_Syntax_Syntax.lbtyp)
in (

let lbd = if (is_rec && (FStar_Util.is_left lb.FStar_Syntax_Syntax.lbname)) then begin
(subst' sn lb.FStar_Syntax_Syntax.lbdef)
end else begin
(subst' s lb.FStar_Syntax_Syntax.lbdef)
end
in (

let lbname = (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl ((

let _35_805 = x
in {FStar_Syntax_Syntax.ppname = _35_805.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_805.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _35_809 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _35_811 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_811.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_811.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_809.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_809.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _35_814 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_814.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_814.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _124_326 = (let _124_325 = (let _124_324 = (subst' s t0)
in (let _124_323 = (let _124_322 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_124_322))
in (_124_324, _124_323)))
in FStar_Syntax_Syntax.Tm_meta (_124_325))
in (FStar_Syntax_Syntax.mk _124_326 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _124_329 = (let _124_328 = (let _124_327 = (subst' s t)
in (_124_327, m))
in FStar_Syntax_Syntax.Tm_meta (_124_328))
in (FStar_Syntax_Syntax.mk _124_329 None t.FStar_Syntax_Syntax.pos))
end))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _124_332 = (push_subst s t)
in (compress _124_332))
in (

let _35_836 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_839 -> begin
(force_uvar t)
end)))


let rename : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (subst' ((FStar_Syntax_Syntax.Renaming (s))::[]) t))


let rename_comp : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun s c -> (subst_comp' ((FStar_Syntax_Syntax.Renaming (s))::[]) c))


let subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[]) t))


let subst_comp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[]) t))


let closing_subst = (fun bs -> (let _124_352 = (FStar_List.fold_right (fun _35_852 _35_855 -> (match ((_35_852, _35_855)) with
| ((x, _35_851), (subst, n)) -> begin
((FStar_Syntax_Syntax.Name2Index ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _124_352 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(

let x' = (

let _35_866 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_358 = (rename o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_866.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_866.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_358}))
in (

let o = (

let o' = (shift_renaming 1 o)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::o')
in (

let _35_873 = (aux bs' o)
in (match (_35_873) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _124_361 = (open_binders' bs)
in (Prims.fst _124_361)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_879 = (open_binders' bs)
in (match (_35_879) with
| (bs', opening) -> begin
(let _124_366 = (rename opening t)
in (bs', _124_366, FStar_Syntax_Syntax.Renaming (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_886 = (open_term' bs t)
in (match (_35_886) with
| (b, t, _35_885) -> begin
(b, t)
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_891 = (open_binders' bs)
in (match (_35_891) with
| (bs', opening) -> begin
(let _124_375 = (rename_comp opening t)
in (bs', _124_375))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * renaming) = (fun p -> (

let rec aux_disj = (fun sub pat_var_renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_898) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_901) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_907 = p
in (let _124_388 = (let _124_387 = (let _124_386 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_911 -> (match (_35_911) with
| (p, b) -> begin
(let _124_385 = (aux_disj sub pat_var_renaming p)
in (_124_385, b))
end))))
in (fv, _124_386))
in FStar_Syntax_Syntax.Pat_cons (_124_387))
in {FStar_Syntax_Syntax.v = _124_388; FStar_Syntax_Syntax.ty = _35_907.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_907.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map pat_var_renaming (fun _35_17 -> (match (_35_17) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_919 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_922 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_390 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_922.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_922.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_390}))
end
| Some (y) -> begin
y
end)
in (

let _35_927 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_927.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_927.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_931 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_391 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_931.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_931.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_391}))
in (

let _35_934 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_934.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_934.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_940 = x
in (let _124_392 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_940.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_940.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_392}))
in (

let t0 = (rename sub t0)
in (

let _35_944 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_944.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_944.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub pat_var_renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_953) -> begin
(p, sub, pat_var_renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_962 = (aux sub pat_var_renaming p)
in (match (_35_962) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((

let _35_964 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_964.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_964.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_984 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_973 _35_976 -> (match ((_35_973, _35_976)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_980 = (aux sub renaming p)
in (match (_35_980) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, pat_var_renaming)))
in (match (_35_984) with
| (pats, sub, renaming) -> begin
((

let _35_985 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_985.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_985.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_989 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_401 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_989.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_401}))
in (

let sub = (

let sub' = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::sub')
in ((

let _35_994 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_994.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_994.FStar_Syntax_Syntax.p}), sub, ((x, x'))::pat_var_renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_998 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_402 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_998.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_998.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_402}))
in (

let sub = (

let sub' = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::sub')
in ((

let _35_1003 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_1003.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1003.FStar_Syntax_Syntax.p}), sub, ((x, x'))::pat_var_renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_1009 = x
in (let _124_403 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1009.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1009.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_403}))
in (

let t0 = (rename sub t0)
in ((

let _35_1013 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_1013.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1013.FStar_Syntax_Syntax.p}), sub, pat_var_renaming)))
end))
in (

let _35_1019 = (aux [] [] p)
in (match (_35_1019) with
| (p, sub, _35_1018) -> begin
(p, sub)
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_1023 -> (match (_35_1023) with
| (p, wopt, e) -> begin
(

let _35_1026 = (open_pat p)
in (match (_35_1026) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_406 = (rename opening w)
in Some (_124_406))
end)
in (

let e = (rename opening e)
in (p, wopt, e)))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _124_411 = (closing_subst bs)
in (rename _124_411 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _124_416 = (closing_subst bs)
in (rename_comp _124_416 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(

let x = (

let _35_1046 = x
in (let _124_423 = (rename s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1046.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1046.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_423}))
in (

let s' = (let _124_424 = (shift_renaming 1 s)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_424)
in (let _124_425 = (aux s' tl)
in ((x, imp))::_124_425)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_1053 = lc
in (let _124_432 = (rename s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_1053.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_432; FStar_Syntax_Syntax.cflags = _35_1053.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_1055 -> (match (()) with
| () -> begin
(let _124_431 = (lc.FStar_Syntax_Syntax.comp ())
in (rename_comp s _124_431))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * renaming) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_1063) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_1071 = (aux sub p)
in (match (_35_1071) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _124_440 = (aux sub p)
in (Prims.fst _124_440))) ps)
in ((

let _35_1074 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_1074.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1074.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_1091 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_1082 _35_1085 -> (match ((_35_1082, _35_1085)) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_1088 = (aux sub p)
in (match (_35_1088) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_1091) with
| (pats, sub) -> begin
((

let _35_1092 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_1092.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1092.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_1096 = x
in (let _124_443 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1096.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1096.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_443}))
in (

let sub = (let _124_444 = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_444)
in ((

let _35_1100 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_1100.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1100.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_1104 = x
in (let _124_445 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1104.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1104.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_445}))
in (

let sub = (let _124_446 = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_446)
in ((

let _35_1108 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_1108.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1108.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_1114 = x
in (let _124_447 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1114.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1114.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_447}))
in (

let t0 = (rename sub t0)
in ((

let _35_1118 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_1118.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1118.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_1123 -> (match (_35_1123) with
| (p, wopt, e) -> begin
(

let _35_1126 = (close_pat p)
in (match (_35_1126) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_450 = (rename closing w)
in Some (_124_450))
end)
in (

let e = (rename closing e)
in (p, wopt, e)))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.renaming_subst Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - 1)
in (

let _35_1139 = (let _124_455 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UIndex2UName (((n - i), u')), u')))))
in (FStar_All.pipe_right _124_455 FStar_List.unzip))
in (match (_35_1139) with
| (s, us') -> begin
(s, us')
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_1144 = (univ_var_opening us)
in (match (_35_1144) with
| (s, us') -> begin
(

let t = (rename s t)
in (us', t))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_1150 = (univ_var_opening us)
in (match (_35_1150) with
| (s, us') -> begin
(let _124_464 = (rename_comp s c)
in (us', _124_464))
end)))


let close_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun us t -> (

let n = ((FStar_List.length us) - 1)
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UName2UIndex ((u, (n - i))))))
in (rename s t))))


let close_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun us c -> (

let n = ((FStar_List.length us) - 1)
in (

let s = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UName2UIndex ((u, (n - i))))))
in (rename_comp s c))))


let open_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(

let _35_1176 = (FStar_List.fold_right (fun lb _35_1169 -> (match (_35_1169) with
| (i, lbs, out) -> begin
(

let x = (let _124_483 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _124_483))
in ((i + 1), ((

let _35_1171 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_1171.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_1171.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1171.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_1171.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.Index2Name ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_35_1176) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_1188 = (FStar_List.fold_right (fun u _35_1182 -> (match (_35_1182) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UIndex2UName ((i, u)))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_35_1188) with
| (_35_1185, us, u_let_rec_opening) -> begin
(

let _35_1189 = lb
in (let _124_487 = (rename u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_1189.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_1189.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1189.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_487}))
end)))))
in (

let t = (rename let_rec_opening t)
in (lbs, t)))
end))
end)


let close_let_rec : FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.letbinding Prims.list * FStar_Syntax_Syntax.term) = (fun lbs t -> if (FStar_Syntax_Syntax.is_top_level lbs) then begin
(lbs, t)
end else begin
(

let _35_1201 = (FStar_List.fold_right (fun lb _35_1198 -> (match (_35_1198) with
| (i, out) -> begin
(let _124_497 = (let _124_496 = (let _124_495 = (let _124_494 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_124_494, i))
in FStar_Syntax_Syntax.Name2Index (_124_495))
in (_124_496)::out)
in ((i + 1), _124_497))
end)) lbs (0, []))
in (match (_35_1201) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_1210 = (FStar_List.fold_right (fun u _35_1206 -> (match (_35_1206) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UName2UIndex ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_35_1210) with
| (_35_1208, u_let_rec_closing) -> begin
(

let _35_1211 = lb
in (let _124_501 = (rename u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_1211.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_1211.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_1211.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1211.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_501}))
end)))))
in (

let t = (rename let_rec_closing t)
in (lbs, t)))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_1218 -> (match (_35_1218) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - 1)
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_1225 -> (match (_35_1225) with
| (x, _35_1224) -> begin
FStar_Syntax_Syntax.Name2Index ((x, (k + (n - i))))
end)) binders)
in (

let t = (rename s t)
in (us, t)))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_1231 -> (match (_35_1231) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - 1)
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UName2UIndex ((x, (k + (n - i))))) us)
in (let _124_514 = (rename s t)
in (us', _124_514)))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - 1)
in (let _124_519 = (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_1243 -> (match (_35_1243) with
| (x, _35_1242) -> begin
FStar_Syntax_Syntax.Index2Name (((n - i), x))
end))))
in FStar_Syntax_Syntax.Renaming (_124_519))))





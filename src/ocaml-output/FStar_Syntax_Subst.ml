
open Prims

let rec force_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _35_22) -> begin
(match ((FStar_Unionfind.find uv)) with
| FStar_Syntax_Syntax.Fixed (t') -> begin
(force_uvar t')
end
| _35_28 -> begin
t
end)
end
| _35_30 -> begin
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

let _35_40 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end
| _35_43 -> begin
t
end)
end
| Some (t') -> begin
(

let t' = (force_delayed_thunk t')
in (

let _35_47 = (FStar_ST.op_Colon_Equals m (Some (t')))
in t'))
end)
end
| _35_50 -> begin
t
end))


let rec compress_univ : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun u -> (match (u) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(match ((FStar_Unionfind.find u')) with
| Some (u) -> begin
(compress_univ u)
end
| _35_57 -> begin
u
end)
end
| _35_59 -> begin
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
in (FStar_Util.format2 "Index2Name   (%s, %s)" _124_40 _124_39)))
end
| FStar_Syntax_Syntax.Name2Index (x, i) -> begin
(let _124_42 = (bv_to_string x)
in (let _124_41 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Name2Index   (%s, %s)" _124_42 _124_41)))
end
| FStar_Syntax_Syntax.Name2Name (x, y) -> begin
(let _124_44 = (bv_to_string x)
in (let _124_43 = (bv_to_string y)
in (FStar_Util.format2 "Name2Name    (%s, %s)" _124_44 _124_43)))
end
| FStar_Syntax_Syntax.Index2Index (i, j) -> begin
(let _124_46 = (FStar_Util.string_of_int i)
in (let _124_45 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "Index2Index  (%s, %s)" _124_46 _124_45)))
end
| FStar_Syntax_Syntax.UIndex2UName (i, u) -> begin
(let _124_47 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UIndex2Uname (%s, %s)" _124_47 u.FStar_Ident.idText))
end
| FStar_Syntax_Syntax.UName2UIndex (u, i) -> begin
(let _124_48 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "UName2UIndex (%s, %s)" u.FStar_Ident.idText _124_48))
end
| FStar_Syntax_Syntax.UIndex2UIndex (i, j) -> begin
(let _124_50 = (FStar_Util.string_of_int i)
in (let _124_49 = (FStar_Util.string_of_int j)
in (FStar_Util.format2 "UIndex2UIndex(%s, %s)" _124_50 _124_49)))
end
| FStar_Syntax_Syntax.UName2UName (u, v) -> begin
(FStar_Util.format2 "UName2UName  (%s, %s)" u.FStar_Ident.idText v.FStar_Ident.idText)
end))


let renaming_to_string : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  Prims.string = (fun r -> (let _124_54 = (let _124_53 = (FStar_All.pipe_right r (FStar_List.map renaming_elt_to_string))
in (FStar_All.pipe_right _124_53 (FStar_String.concat "; ")))
in (FStar_Util.format1 "Renaming[%s]" _124_54)))


let instantiation_elt_to_string : FStar_Syntax_Syntax.inst_subst  ->  Prims.string = (fun _35_2 -> (match (_35_2) with
| FStar_Syntax_Syntax.Name2Term (x, t) -> begin
(let _124_58 = (bv_to_string x)
in (let _124_57 = (print_term t)
in (FStar_Util.format2 "Name2Term (%s, %s)" _124_58 _124_57)))
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
in (FStar_All.pipe_right _124_67 (FStar_String.concat ";\n"))))


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

let _35_130 = a
in {FStar_Syntax_Syntax.ppname = _35_130.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = j; FStar_Syntax_Syntax.sort = _35_130.FStar_Syntax_Syntax.sort}))
in Some (_124_80))
end
| _35_133 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_index i renaming)
end
| _35_137 -> begin
None
end)))


let subst_name : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.term Prims.option = (fun x s -> (

let rename_name = (fun a renaming -> (FStar_Util.find_map renaming (fun _35_5 -> (match (_35_5) with
| FStar_Syntax_Syntax.Name2Index (x, i) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_90 = (FStar_Syntax_Syntax.bv_to_tm (

let _35_148 = a
in {FStar_Syntax_Syntax.ppname = _35_148.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = i; FStar_Syntax_Syntax.sort = _35_148.FStar_Syntax_Syntax.sort}))
in Some (_124_90))
end
| FStar_Syntax_Syntax.Name2Name (x, y) when (FStar_Syntax_Syntax.bv_eq a x) -> begin
(let _124_91 = (FStar_Syntax_Syntax.bv_to_name y)
in Some (_124_91))
end
| _35_155 -> begin
None
end))))
in (

let instantiate = (fun x inst -> (FStar_Util.find_map inst (fun _35_6 -> (match (_35_6) with
| FStar_Syntax_Syntax.Name2Term (y, t) when (FStar_Syntax_Syntax.bv_eq x y) -> begin
Some (t)
end
| _35_165 -> begin
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
| _35_185 -> begin
None
end))))
in (match (s) with
| FStar_Syntax_Syntax.Renaming (renaming) -> begin
(rename_uindex i renaming)
end
| _35_189 -> begin
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
| _35_205 -> begin
None
end))))
in (

let instantiate_uname = (fun x inst -> (FStar_Util.find_map inst (fun _35_9 -> (match (_35_9) with
| FStar_Syntax_Syntax.UName2Univ (y, t) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
Some (t)
end
| _35_215 -> begin
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

let s2_orig = s2
in (

let find_name = (fun x -> (FStar_All.pipe_right s2 (FStar_Util.find_opt (fun _35_11 -> (match (_35_11) with
| (FStar_Syntax_Syntax.Name2Index (y, _)) | (FStar_Syntax_Syntax.Name2Name (y, _)) -> begin
(FStar_Syntax_Syntax.bv_eq x y)
end
| _35_267 -> begin
false
end)))))
in (

let find_index = (fun i -> (FStar_All.pipe_right s2 (FStar_Util.find_opt (fun _35_12 -> (match (_35_12) with
| (FStar_Syntax_Syntax.Index2Name (j, _)) | (FStar_Syntax_Syntax.Index2Index (j, _)) -> begin
(i = j)
end
| _35_281 -> begin
false
end)))))
in (

let find_uindex = (fun i -> (FStar_All.pipe_right s2 (FStar_Util.find_opt (fun _35_13 -> (match (_35_13) with
| (FStar_Syntax_Syntax.UIndex2UName (j, _)) | (FStar_Syntax_Syntax.UIndex2UIndex (j, _)) -> begin
(i = j)
end
| _35_295 -> begin
false
end)))))
in (

let find_uname = (fun n -> (FStar_All.pipe_right s2 (FStar_Util.find_opt (fun _35_14 -> (match (_35_14) with
| (FStar_Syntax_Syntax.UName2UIndex (m, _)) | (FStar_Syntax_Syntax.UName2UName (m, _)) -> begin
(n.FStar_Ident.idText = m.FStar_Ident.idText)
end
| _35_309 -> begin
false
end)))))
in (

let _35_468 = (FStar_All.pipe_right s1 (FStar_List.fold_left (fun _35_312 s1_elt -> (match (_35_312) with
| (s1_elts, s2_removes) -> begin
(match (s1_elt) with
| FStar_Syntax_Syntax.Index2Name (i, x) -> begin
(

let s2_x = (find_name x)
in (match (s2_x) with
| Some (FStar_Syntax_Syntax.Name2Index (_35_320, j)) -> begin
if (i = j) then begin
(s1_elts, (s2_x)::s2_removes)
end else begin
((FStar_Syntax_Syntax.Index2Index ((i, j)))::s1_elts, (s2_x)::s2_removes)
end
end
| Some (FStar_Syntax_Syntax.Name2Name (_35_326, y)) -> begin
((FStar_Syntax_Syntax.Index2Name ((i, y)))::s1_elts, (s2_x)::s2_removes)
end
| _35_332 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.Name2Index (x, i) -> begin
(

let s2_i = (find_index i)
in (match (s2_i) with
| Some (FStar_Syntax_Syntax.Index2Name (_35_339, y)) -> begin
((FStar_Syntax_Syntax.Name2Name ((x, y)))::s1_elts, (s2_i)::s2_removes)
end
| Some (FStar_Syntax_Syntax.Index2Index (_35_345, j)) -> begin
((FStar_Syntax_Syntax.Name2Index ((x, j)))::s1_elts, (s2_i)::s2_removes)
end
| _35_351 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.Index2Index (i, j) -> begin
(

let s2_j = (find_index j)
in (match (s2_j) with
| Some (FStar_Syntax_Syntax.Index2Name (_35_358, y)) -> begin
((FStar_Syntax_Syntax.Index2Name ((i, y)))::s1_elts, (s2_j)::s2_removes)
end
| Some (FStar_Syntax_Syntax.Index2Index (_35_364, k)) -> begin
((FStar_Syntax_Syntax.Index2Index ((i, k)))::s1_elts, (s2_j)::s2_removes)
end
| _35_370 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.Name2Name (x, y) -> begin
(

let s2_y = (find_name y)
in (match (s2_y) with
| Some (FStar_Syntax_Syntax.Name2Index (_35_377, j)) -> begin
((FStar_Syntax_Syntax.Name2Index ((x, j)))::s1_elts, s2_removes)
end
| Some (FStar_Syntax_Syntax.Name2Name (_35_383, z)) -> begin
((FStar_Syntax_Syntax.Name2Name ((x, z)))::s1_elts, s2_removes)
end
| _35_389 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.UIndex2UName (i, n) -> begin
(

let u_n = (find_uname n)
in (match (u_n) with
| Some (FStar_Syntax_Syntax.UName2UIndex (_35_396, j)) -> begin
if (i = j) then begin
(s1_elts, (u_n)::s2_removes)
end else begin
((FStar_Syntax_Syntax.UIndex2UIndex ((i, j)))::s1_elts, (u_n)::s2_removes)
end
end
| Some (FStar_Syntax_Syntax.UName2UName (_35_402, u)) -> begin
((FStar_Syntax_Syntax.UIndex2UName ((i, u)))::s1_elts, (u_n)::s2_removes)
end
| _35_408 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.UName2UIndex (u, i) -> begin
(

let u_i = (find_uindex i)
in (match (u_i) with
| Some (FStar_Syntax_Syntax.UIndex2UName (_35_415, v)) -> begin
((FStar_Syntax_Syntax.UName2UName ((u, v)))::s1_elts, (u_i)::s2_removes)
end
| Some (FStar_Syntax_Syntax.UIndex2UIndex (_35_421, k)) -> begin
((FStar_Syntax_Syntax.UName2UIndex ((u, k)))::s1_elts, (u_i)::s2_removes)
end
| _35_427 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.UName2UName (u, v) -> begin
(

let u_i = (find_uname v)
in (match (u_i) with
| Some (FStar_Syntax_Syntax.UName2UIndex (_35_434, i)) -> begin
((FStar_Syntax_Syntax.UName2UIndex ((u, i)))::s1_elts, s2_removes)
end
| Some (FStar_Syntax_Syntax.UName2UName (_35_440, w)) -> begin
((FStar_Syntax_Syntax.UName2UName ((u, w)))::s1_elts, s2_removes)
end
| _35_446 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end
| FStar_Syntax_Syntax.UIndex2UIndex (i, j) -> begin
(

let s2_j = (find_uindex j)
in (match (s2_j) with
| Some (FStar_Syntax_Syntax.UIndex2UName (_35_453, y)) -> begin
((FStar_Syntax_Syntax.UIndex2UName ((i, y)))::s1_elts, (s2_j)::s2_removes)
end
| Some (FStar_Syntax_Syntax.UIndex2UIndex (_35_459, k)) -> begin
((FStar_Syntax_Syntax.UIndex2UIndex ((i, k)))::s1_elts, (s2_j)::s2_removes)
end
| _35_465 -> begin
((s1_elt)::s1_elts, s2_removes)
end))
end)
end)) ([], [])))
in (match (_35_468) with
| (s1_elts, s2_removes) -> begin
(

let s2_remainder = (FStar_All.pipe_right s2 (FStar_List.filter (fun x -> (not ((FStar_All.pipe_right s2_removes (FStar_Util.for_some (fun _35_15 -> (match (_35_15) with
| None -> begin
false
end
| Some (y) -> begin
(FStar_Util.physical_equality x y)
end)))))))))
in (FStar_List.append s1_elts s2_remainder))
end)))))))))


let collapse_subst : FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun s -> (FStar_List.fold_right (fun ri out -> (match ((ri, out)) with
| (FStar_Syntax_Syntax.Renaming (re1), FStar_Syntax_Syntax.Renaming (re2)::tl) -> begin
(let _124_186 = (let _124_185 = (compose_renamings re1 re2)
in FStar_Syntax_Syntax.Renaming (_124_185))
in (_124_186)::tl)
end
| _35_486 -> begin
(ri)::out
end)) s []))


let compose_subst = (fun _35_489 _35_492 -> (match ((_35_489, _35_492)) with
| ((s1, s1_new), (s2, s2_new)) -> begin
(

let composed = []
in (

let composed_new = (collapse_subst (FStar_List.append s1_new s2_new)) in
    if FStar_Options.debug_at_level "" (FStar_Options.Other "Substitutions")
    then FStar_Util.print1 "Length of composed substs is %s\n" (FStar_Util.string_of_int (FStar_List.length composed_new));


  (composed, composed_new)))
end))


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


let shift_subst' : Prims.int  ->  FStar_Syntax_Syntax.subst_ts  ->  FStar_Syntax_Syntax.subst_t Prims.list = (fun n s -> (FStar_List.map (fun _35_16 -> (match (_35_16) with
| FStar_Syntax_Syntax.Renaming (s) -> begin
(let _124_202 = (shift_renaming n s)
in FStar_Syntax_Syntax.Renaming (_124_202))
end
| x -> begin
x
end)) s))


let shift_subst : Prims.int  ->  (FStar_Syntax_Syntax.subst_ts * FStar_Syntax_Syntax.subst_ts)  ->  (FStar_Syntax_Syntax.subst_t Prims.list * FStar_Syntax_Syntax.subst_t Prims.list) = (fun n _35_538 -> (match (_35_538) with
| (s, s_new) -> begin
(let _124_208 = (shift_subst' n s)
in (let _124_207 = (shift_subst' n s_new)
in (_124_208, _124_207)))
end))


let print_subst_detail : FStar_Syntax_Syntax.subst_ts  ->  Prims.string = (fun s -> (match (s) with
| ([]) | (_::[]) -> begin
(subst_to_string s)
end
| hd::tl -> begin
(

let str = (subst_to_string ((hd)::[]))
in (

let rec aux = (fun str prev rest -> (match (rest) with
| [] -> begin
str
end
| FStar_Syntax_Syntax.Renaming (r)::rest -> begin
(match (prev) with
| FStar_Syntax_Syntax.Renaming (r0) -> begin
(

let next = (let _124_218 = (compose_renamings r0 r)
in (FStar_All.pipe_left (fun _124_217 -> FStar_Syntax_Syntax.Renaming (_124_217)) _124_218))
in (

let str = (let _124_220 = (subst_to_string ((FStar_Syntax_Syntax.Renaming (r))::[]))
in (let _124_219 = (subst_to_string ((next)::[]))
in (FStar_Util.format3 "%s\n+%s\n=%s" str _124_220 _124_219)))
in (aux str next rest)))
end
| FStar_Syntax_Syntax.Instantiation (_35_562) -> begin
(

let str = (let _124_221 = (subst_to_string ((FStar_Syntax_Syntax.Renaming (r))::[]))
in (FStar_Util.format2 "%s\n;%s" str _124_221))
in (aux str (FStar_Syntax_Syntax.Renaming (r)) rest))
end)
end
| FStar_Syntax_Syntax.Instantiation (i)::rest -> begin
(

let str = (let _124_222 = (subst_to_string ((FStar_Syntax_Syntax.Instantiation (i))::[]))
in (FStar_Util.format2 "%s\n;%s" str _124_222))
in (aux str (FStar_Syntax_Syntax.Instantiation (i)) rest))
end))
in (aux str hd tl)))
end))


let check = (fun tm0 tm tm' _35_579 -> (match (_35_579) with
| ((s, rest), (s_new, rest_new)) -> begin
(

let rec cmp = (fun tm tm' -> (match ((tm.FStar_Syntax_Syntax.n, tm'.FStar_Syntax_Syntax.n)) with
| ((FStar_Syntax_Syntax.Tm_bvar (a), FStar_Syntax_Syntax.Tm_bvar (b))) | ((FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b))) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| _35_592 -> begin
true
end))
in if (cmp tm tm') then begin
()
end else begin
(let _124_236 = (let _124_235 = (print_subst_detail s)
in (let _124_234 = (subst_to_string s_new)
in (let _124_233 = (print_term tm0)
in (let _124_232 = (print_term tm)
in (let _124_231 = (print_term tm')
in (FStar_Util.format5 "%s composed to\n %s\nmapped %s to %s <> %s\n" _124_235 _124_234 _124_233 _124_232 _124_231))))))
in (FStar_All.failwith _124_236))
end)
end))


let ucheck = (fun u0 u u' _35_602 -> (match (_35_602) with
| ((s, rest), (s_new, rest_new)) -> begin
(

let rec cmp = (fun u u' -> (match ((u, u')) with
| (FStar_Syntax_Syntax.U_bvar (a), FStar_Syntax_Syntax.U_bvar (b)) -> begin
(a = b)
end
| (FStar_Syntax_Syntax.U_name (a), FStar_Syntax_Syntax.U_name (b)) -> begin
(a.FStar_Ident.idText = b.FStar_Ident.idText)
end
| _35_617 -> begin
true
end))
in if (cmp u u') then begin
()
end else begin
(let _124_250 = (let _124_249 = (print_subst_detail s)
in (let _124_248 = (subst_to_string s_new)
in (let _124_247 = (print_univ u0)
in (let _124_246 = (print_univ u)
in (let _124_245 = (print_univ u')
in (FStar_Util.format5 "%s composed to\n %s\nmapped %s to %s <> %s\n" _124_249 _124_248 _124_247 _124_246 _124_245))))))
in (FStar_All.failwith _124_250))
end)
end))


let rec rename_aux : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  ((FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.subst_t Prims.list) = (fun t s -> (match (s) with
| FStar_Syntax_Syntax.Renaming (r)::rest -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(match ((subst_index a (FStar_Syntax_Syntax.Renaming (r)))) with
| None -> begin
(rename_aux t rest)
end
| Some (t') -> begin
(rename_aux t' rest)
end)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(match ((subst_name a (FStar_Syntax_Syntax.Renaming (r)))) with
| None -> begin
(rename_aux t rest)
end
| Some (t') -> begin
(rename_aux t' rest)
end)
end
| _35_635 -> begin
(FStar_All.failwith "impos")
end)
end
| _35_637 -> begin
(t, s)
end))


let rec inst_aux : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t Prims.list) = (fun t s -> (match (s) with
| FStar_Syntax_Syntax.Instantiation (i)::rest -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_bvar (a) -> begin
(match ((subst_index a (FStar_Syntax_Syntax.Instantiation (i)))) with
| None -> begin
(inst_aux t rest)
end
| Some (t') -> begin
(t', rest)
end)
end
| FStar_Syntax_Syntax.Tm_name (a) -> begin
(match ((subst_name a (FStar_Syntax_Syntax.Instantiation (i)))) with
| None -> begin
(inst_aux t rest)
end
| Some (t') -> begin
(t', rest)
end)
end
| _35_655 -> begin
(FStar_All.failwith "impos")
end)
end
| _35_657 -> begin
(t, s)
end))


let eq_subst : FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  Prims.bool = (fun s1 s2 -> (

let cmp_renaming_elt = (fun r1 r2 -> (let _124_268 = (renaming_elt_to_string r1)
in (let _124_267 = (renaming_elt_to_string r2)
in (FStar_Util.compare _124_268 _124_267))))
in (

let eq_renaming_elt = (fun r1 r2 -> (match ((r1, r2)) with
| ((FStar_Syntax_Syntax.Index2Name (i, x), FStar_Syntax_Syntax.Index2Name (j, y))) | ((FStar_Syntax_Syntax.Name2Index (x, i), FStar_Syntax_Syntax.Name2Index (y, j))) -> begin
((i = j) && (FStar_Syntax_Syntax.bv_eq x y))
end
| (FStar_Syntax_Syntax.Name2Name (x, y), FStar_Syntax_Syntax.Name2Name (w, z)) -> begin
((FStar_Syntax_Syntax.bv_eq w x) && (FStar_Syntax_Syntax.bv_eq y z))
end
| ((FStar_Syntax_Syntax.Index2Index (i, k), FStar_Syntax_Syntax.Index2Index (j, l))) | ((FStar_Syntax_Syntax.UIndex2UIndex (i, k), FStar_Syntax_Syntax.UIndex2UIndex (j, l))) -> begin
((i = j) && (k = l))
end
| ((FStar_Syntax_Syntax.UIndex2UName (i, u), FStar_Syntax_Syntax.UIndex2UName (j, v))) | ((FStar_Syntax_Syntax.UName2UIndex (u, i), FStar_Syntax_Syntax.UName2UIndex (v, j))) -> begin
((i = j) && (u.FStar_Ident.idText = v.FStar_Ident.idText))
end
| (FStar_Syntax_Syntax.UName2UName (u, v), FStar_Syntax_Syntax.UName2UName (u', v')) -> begin
((u.FStar_Ident.idText = u'.FStar_Ident.idText) && (v.FStar_Ident.idText = v'.FStar_Ident.idText))
end
| _35_727 -> begin
false
end))
in (

let eq_renaming = (fun r1 r2 -> if ((FStar_List.length r1) = (FStar_List.length r2)) then begin
(

let r1 = (FStar_Util.sort_with cmp_renaming_elt r1)
in (

let r2 = (FStar_Util.sort_with cmp_renaming_elt r2)
in (FStar_List.forall2 eq_renaming_elt r1 r2)))
end else begin
false
end)
in if ((FStar_List.length s1) = (FStar_List.length s2)) then begin
(FStar_List.forall2 (fun s1 s2 -> (match ((s1, s2)) with
| (FStar_Syntax_Syntax.Renaming (r1), FStar_Syntax_Syntax.Renaming (r2)) -> begin
(eq_renaming r1 r2)
end
| (FStar_Syntax_Syntax.Instantiation (_35_741), FStar_Syntax_Syntax.Instantiation (_35_744)) -> begin
true
end
| _35_748 -> begin
false
end)) s1 s2)
end else begin
false
end))))


let check_subst_inv : FStar_Syntax_Syntax.subst_t Prims.list  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  Prims.unit = (fun s s_new -> (

let rec collapse_subst = (fun out s -> (match ((out, s)) with
| (FStar_Syntax_Syntax.Renaming (r1)::out, FStar_Syntax_Syntax.Renaming (r2)::s) -> begin
(

let r = (compose_renamings r1 r2)
in (collapse_subst ((FStar_Syntax_Syntax.Renaming (r))::out) s))
end
| (_35_765, hd::s) -> begin
(collapse_subst ((hd)::out) s)
end
| (_35_771, []) -> begin
(FStar_List.rev out)
end))
in (

let s' = (collapse_subst [] s)
in if (eq_subst s' s_new) then begin
()
end else begin
(let _124_290 = (let _124_289 = (subst_to_string s)
in (let _124_288 = (subst_to_string s')
in (let _124_287 = (subst_to_string s_new)
in (FStar_Util.format3 "%s should be collapsed to\n%s instead of\n%s\n" _124_289 _124_288 _124_287))))
in (FStar_All.failwith _124_290))
end)))


let rec rename_uaux : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.subst_t Prims.list) = (fun u s -> (match (s) with
| FStar_Syntax_Syntax.Renaming (r)::rest -> begin
(match (u) with
| FStar_Syntax_Syntax.U_bvar (a) -> begin
(match ((subst_uindex a (FStar_Syntax_Syntax.Renaming (r)))) with
| None -> begin
(rename_uaux u rest)
end
| Some (u') -> begin
(rename_uaux u' rest)
end)
end
| FStar_Syntax_Syntax.U_name (a) -> begin
(match ((subst_uname a (FStar_Syntax_Syntax.Renaming (r)))) with
| None -> begin
(rename_uaux u rest)
end
| Some (u') -> begin
(rename_uaux u' rest)
end)
end
| _35_792 -> begin
(FStar_All.failwith "impos")
end)
end
| _35_794 -> begin
(u, s)
end))


let rec inst_uaux : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.subst_t Prims.list  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.subst_t Prims.list) = (fun u s -> (match (s) with
| FStar_Syntax_Syntax.Instantiation (i)::rest -> begin
(match (u) with
| FStar_Syntax_Syntax.U_bvar (a) -> begin
(match ((subst_uindex a (FStar_Syntax_Syntax.Instantiation (i)))) with
| None -> begin
(inst_uaux u rest)
end
| Some (u') -> begin
(u', rest)
end)
end
| FStar_Syntax_Syntax.U_name (a) -> begin
(match ((subst_uname a (FStar_Syntax_Syntax.Instantiation (i)))) with
| None -> begin
(inst_uaux u rest)
end
| Some (u') -> begin
(u', rest)
end)
end
| _35_812 -> begin
(FStar_All.failwith "impos")
end)
end
| _35_814 -> begin
(u, s)
end))


let rec subst_univ = (fun _35_818 u -> (match (_35_818) with
| (_35_816, s_new) -> begin
(match (s_new) with
| [] -> begin
u
end
| _35_822 -> begin
(

let u = (compress_univ u)
in (match (u) with
| (FStar_Syntax_Syntax.U_bvar (_)) | (FStar_Syntax_Syntax.U_name (_)) -> begin
(

let _35_832 = (rename_uaux u s_new)
in (match (_35_832) with
| (tm_new, rest_new) -> begin
(

let _35_835 = (inst_uaux tm_new rest_new)
in (match (_35_835) with
| (tm_new, rest_new) -> begin
(subst_univ ([], rest_new) tm_new)
end))
end))
end
| (FStar_Syntax_Syntax.U_zero) | (FStar_Syntax_Syntax.U_unknown) | (FStar_Syntax_Syntax.U_unif (_)) -> begin
u
end
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _124_301 = (subst_univ ([], s_new) u)
in FStar_Syntax_Syntax.U_succ (_124_301))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _124_302 = (FStar_List.map (subst_univ ([], s_new)) us)
in FStar_Syntax_Syntax.U_max (_124_302))
end))
end)
end))


let rec subst' = (fun _35_848 t -> (match (_35_848) with
| (_35_846, s_new) -> begin
(match (s_new) with
| [] -> begin
t
end
| _35_852 -> begin
(

let t0 = (force_delayed_thunk t)
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
t0
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t', s'), m) -> begin
(let _124_314 = (let _124_313 = (let _124_312 = (compose_subst s' ([], s_new))
in (t', _124_312))
in FStar_Util.Inl (_124_313))
in (FStar_Syntax_Syntax.mk_Tm_delayed _124_314 t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inr (_35_871), _35_874) -> begin
(FStar_All.failwith "Impossible: force_delayed_thunk removes lazy delayed nodes")
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) -> begin
(

let _35_885 = (rename_aux t0 s_new)
in (match (_35_885) with
| (tm_new, rest_new) -> begin
(

let _35_888 = (inst_aux tm_new rest_new)
in (match (_35_888) with
| (tm_new, rest_new) -> begin
(subst' ([], rest_new) tm_new)
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (u) -> begin
(let _124_317 = (let _124_316 = (subst_univ ([], s_new) u)
in FStar_Syntax_Syntax.Tm_type (_124_316))
in (FStar_Syntax_Syntax.mk _124_317 None t0.FStar_Syntax_Syntax.pos))
end
| _35_892 -> begin
(FStar_Syntax_Syntax.mk_Tm_delayed (FStar_Util.Inl ((t0, ([], s_new)))) t.FStar_Syntax_Syntax.pos)
end))
end)
end))
and subst_flags' = (fun s flags -> (FStar_All.pipe_right flags (FStar_List.map (fun _35_17 -> (match (_35_17) with
| FStar_Syntax_Syntax.DECREASES (a) -> begin
(let _124_320 = (subst' s a)
in FStar_Syntax_Syntax.DECREASES (_124_320))
end
| f -> begin
f
end)))))
and subst_comp_typ' = (fun s t -> (match ((Prims.snd s)) with
| [] -> begin
t
end
| _35_903 -> begin
(

let _35_904 = t
in (let _124_325 = (subst' s t.FStar_Syntax_Syntax.result_typ)
in (let _124_324 = (FStar_List.map (fun _35_908 -> (match (_35_908) with
| (t, imp) -> begin
(let _124_322 = (subst' s t)
in (_124_322, imp))
end)) t.FStar_Syntax_Syntax.effect_args)
in (let _124_323 = (subst_flags' s t.FStar_Syntax_Syntax.flags)
in {FStar_Syntax_Syntax.effect_name = _35_904.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _124_325; FStar_Syntax_Syntax.effect_args = _124_324; FStar_Syntax_Syntax.flags = _124_323}))))
end))
and subst_comp' = (fun s t -> (match ((Prims.snd s)) with
| [] -> begin
t
end
| _35_913 -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t) -> begin
(let _124_326 = (subst' s t)
in (FStar_Syntax_Syntax.mk_Total _124_326))
end
| FStar_Syntax_Syntax.GTotal (t) -> begin
(let _124_327 = (subst' s t)
in (FStar_Syntax_Syntax.mk_GTotal _124_327))
end
| FStar_Syntax_Syntax.Comp (ct) -> begin
(let _124_328 = (subst_comp_typ' s ct)
in (FStar_Syntax_Syntax.mk_Comp _124_328))
end)
end))


let subst_binder' = (fun s _35_923 -> (match (_35_923) with
| (x, imp) -> begin
(let _124_332 = (

let _35_924 = x
in (let _124_331 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_924.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_924.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_331}))
in (_124_332, imp))
end))


let subst_binders' = (fun s bs -> (FStar_All.pipe_right bs (FStar_List.mapi (fun i b -> if (i = 0) then begin
(subst_binder' s b)
end else begin
(let _124_337 = (shift_subst i s)
in (subst_binder' _124_337 b))
end))))


let subst_arg' = (fun s _35_933 -> (match (_35_933) with
| (t, imp) -> begin
(let _124_340 = (subst' s t)
in (_124_340, imp))
end))


let subst_args' = (fun s -> (FStar_List.map (subst_arg' s)))


let subst_pat' : (FStar_Syntax_Syntax.subst_ts * FStar_Syntax_Syntax.subst_ts)  ->  (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  (FStar_Syntax_Syntax.pat * Prims.int) = (fun s p -> (

let rec aux = (fun n p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_943) -> begin
(p, n)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_951 = (aux n p)
in (match (_35_951) with
| (p, m) -> begin
(

let ps = (FStar_List.map (fun p -> (let _124_353 = (aux n p)
in (Prims.fst _124_353))) ps)
in ((

let _35_954 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_954.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_954.FStar_Syntax_Syntax.p}), m))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_971 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_962 _35_965 -> (match ((_35_962, _35_965)) with
| ((pats, n), (p, imp)) -> begin
(

let _35_968 = (aux n p)
in (match (_35_968) with
| (p, m) -> begin
(((p, imp))::pats, m)
end))
end)) ([], n)))
in (match (_35_971) with
| (pats, n) -> begin
((

let _35_972 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_972.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_972.FStar_Syntax_Syntax.p}), n)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_977 = x
in (let _124_356 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_977.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_977.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_356}))
in ((

let _35_980 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_980.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_980.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_985 = x
in (let _124_357 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_985.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_985.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_357}))
in ((

let _35_988 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_988.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_988.FStar_Syntax_Syntax.p}), (n + 1))))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let s = (shift_subst n s)
in (

let x = (

let _35_995 = x
in (let _124_358 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_995.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_995.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_358}))
in (

let t0 = (subst' s t0)
in ((

let _35_999 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_999.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_999.FStar_Syntax_Syntax.p}), n))))
end))
in (aux 0 p)))


let push_subst_lcomp = (fun s lopt -> (match (lopt) with
| (None) | (Some (FStar_Util.Inr (_))) -> begin
lopt
end
| Some (FStar_Util.Inl (l)) -> begin
(let _124_365 = (let _124_364 = (

let _35_1011 = l
in (let _124_363 = (subst' s l.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_1011.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_363; FStar_Syntax_Syntax.cflags = _35_1011.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_1013 -> (match (()) with
| () -> begin
(let _124_362 = (l.FStar_Syntax_Syntax.comp ())
in (subst_comp' s _124_362))
end))}))
in FStar_Util.Inl (_124_364))
in Some (_124_365))
end))


let push_subst : (FStar_Syntax_Syntax.subst_ts * FStar_Syntax_Syntax.subst_ts)  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun s t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_35_1017) -> begin
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
(let _124_376 = (let _124_375 = (let _124_374 = (subst' s t0)
in (let _124_373 = (subst_args' s args)
in (_124_374, _124_373)))
in FStar_Syntax_Syntax.Tm_app (_124_375))
in (FStar_Syntax_Syntax.mk _124_376 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inl (t1), lopt) -> begin
(let _124_381 = (let _124_380 = (let _124_379 = (subst' s t0)
in (let _124_378 = (let _124_377 = (subst' s t1)
in FStar_Util.Inl (_124_377))
in (_124_379, _124_378, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_380))
in (FStar_Syntax_Syntax.mk _124_381 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_ascribed (t0, FStar_Util.Inr (c), lopt) -> begin
(let _124_386 = (let _124_385 = (let _124_384 = (subst' s t0)
in (let _124_383 = (let _124_382 = (subst_comp' s c)
in FStar_Util.Inr (_124_382))
in (_124_384, _124_383, lopt)))
in FStar_Syntax_Syntax.Tm_ascribed (_124_385))
in (FStar_Syntax_Syntax.mk _124_386 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let n = (FStar_List.length bs)
in (

let s' = (shift_subst n s)
in (let _124_391 = (let _124_390 = (let _124_389 = (subst_binders' s bs)
in (let _124_388 = (subst' s' body)
in (let _124_387 = (push_subst_lcomp s' lopt)
in (_124_389, _124_388, _124_387))))
in FStar_Syntax_Syntax.Tm_abs (_124_390))
in (FStar_Syntax_Syntax.mk _124_391 None t.FStar_Syntax_Syntax.pos))))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, comp) -> begin
(

let n = (FStar_List.length bs)
in (let _124_396 = (let _124_395 = (let _124_394 = (subst_binders' s bs)
in (let _124_393 = (let _124_392 = (shift_subst n s)
in (subst_comp' _124_392 comp))
in (_124_394, _124_393)))
in FStar_Syntax_Syntax.Tm_arrow (_124_395))
in (FStar_Syntax_Syntax.mk _124_396 None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
(

let x = (

let _35_1075 = x
in (let _124_397 = (subst' s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1075.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1075.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_397}))
in (

let phi = (let _124_398 = (shift_subst 1 s)
in (subst' _124_398 phi))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((x, phi))) None t.FStar_Syntax_Syntax.pos)))
end
| FStar_Syntax_Syntax.Tm_match (t0, pats) -> begin
(

let t0 = (subst' s t0)
in (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _35_1087 -> (match (_35_1087) with
| (pat, wopt, branch) -> begin
(

let _35_1090 = (subst_pat' s pat)
in (match (_35_1090) with
| (pat, n) -> begin
(

let s = (shift_subst n s)
in (

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_400 = (subst' s w)
in Some (_124_400))
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

let _35_1112 = x
in {FStar_Syntax_Syntax.ppname = _35_1112.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1112.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = lbt}))
end
| FStar_Util.Inr (fv) -> begin
FStar_Util.Inr ((

let _35_1116 = fv
in {FStar_Syntax_Syntax.fv_name = (

let _35_1118 = fv.FStar_Syntax_Syntax.fv_name
in {FStar_Syntax_Syntax.v = _35_1118.FStar_Syntax_Syntax.v; FStar_Syntax_Syntax.ty = lbt; FStar_Syntax_Syntax.p = _35_1118.FStar_Syntax_Syntax.p}); FStar_Syntax_Syntax.fv_delta = _35_1116.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _35_1116.FStar_Syntax_Syntax.fv_qual}))
end)
in (

let _35_1121 = lb
in {FStar_Syntax_Syntax.lbname = lbname; FStar_Syntax_Syntax.lbunivs = _35_1121.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lbt; FStar_Syntax_Syntax.lbeff = _35_1121.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = lbd})))))))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((is_rec, lbs), body))) None t.FStar_Syntax_Syntax.pos)))))
end
| FStar_Syntax_Syntax.Tm_meta (t0, FStar_Syntax_Syntax.Meta_pattern (ps)) -> begin
(let _124_406 = (let _124_405 = (let _124_404 = (subst' s t0)
in (let _124_403 = (let _124_402 = (FStar_All.pipe_right ps (FStar_List.map (subst_args' s)))
in FStar_Syntax_Syntax.Meta_pattern (_124_402))
in (_124_404, _124_403)))
in FStar_Syntax_Syntax.Tm_meta (_124_405))
in (FStar_Syntax_Syntax.mk _124_406 None t.FStar_Syntax_Syntax.pos))
end
| FStar_Syntax_Syntax.Tm_meta (t, m) -> begin
(let _124_409 = (let _124_408 = (let _124_407 = (subst' s t)
in (_124_407, m))
in FStar_Syntax_Syntax.Tm_meta (_124_408))
in (FStar_Syntax_Syntax.mk _124_409 None t.FStar_Syntax_Syntax.pos))
end))


let rec compress : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let t = (force_delayed_thunk t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (FStar_Util.Inl (t, s), memo) -> begin
(

let t' = (let _124_412 = (push_subst s t)
in (compress _124_412))
in (

let _35_1143 = (FStar_Unionfind.update_in_tx memo (Some (t')))
in t'))
end
| _35_1146 -> begin
(force_uvar t)
end)))


let rename : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun r t -> (

let s = (FStar_Syntax_Syntax.Renaming (r))::[]
in (subst' (s, s) t)))


let rename_comp : FStar_Syntax_Syntax.renaming_subst Prims.list  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun r c -> (

let s = (FStar_Syntax_Syntax.Renaming (r))::[]
in (subst_comp' (s, s) c)))


let subst : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun s t -> (subst' ((s)::[], (s)::[]) t))


let subst_comp : FStar_Syntax_Syntax.subst_t  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun s t -> (subst_comp' ((s)::[], (s)::[]) t))


let closing_subst = (fun bs -> (let _124_432 = (FStar_List.fold_right (fun _35_1161 _35_1164 -> (match ((_35_1161, _35_1164)) with
| ((x, _35_1160), (subst, n)) -> begin
((FStar_Syntax_Syntax.Name2Index ((x, n)))::subst, (n + 1))
end)) bs ([], 0))
in (FStar_All.pipe_right _124_432 Prims.fst)))


let open_binders' = (fun bs -> (

let rec aux = (fun bs o -> (match (bs) with
| [] -> begin
([], o)
end
| (x, imp)::bs' -> begin
(

let x' = (

let _35_1175 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_438 = (rename o x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1175.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_438}))
in (

let o = (

let o' = (shift_renaming 1 o)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::o')
in (

let _35_1182 = (aux bs' o)
in (match (_35_1182) with
| (bs', o) -> begin
(((x', imp))::bs', o)
end))))
end))
in (aux bs [])))


let open_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (let _124_441 = (open_binders' bs)
in (Prims.fst _124_441)))


let open_term' : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.subst_t) = (fun bs t -> (

let _35_1188 = (open_binders' bs)
in (match (_35_1188) with
| (bs', opening) -> begin
(let _124_446 = (rename opening t)
in (bs', _124_446, FStar_Syntax_Syntax.Renaming (opening)))
end)))


let open_term : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term) = (fun bs t -> (

let _35_1195 = (open_term' bs t)
in (match (_35_1195) with
| (b, t, _35_1194) -> begin
(b, t)
end)))


let open_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun bs t -> (

let _35_1200 = (open_binders' bs)
in (match (_35_1200) with
| (bs', opening) -> begin
(let _124_455 = (rename_comp opening t)
in (bs', _124_455))
end)))


let open_pat : FStar_Syntax_Syntax.pat  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * renaming) = (fun p -> (

let rec aux_disj = (fun sub pat_var_renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_35_1207) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Syntax_Syntax.Pat_constant (_35_1210) -> begin
p
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_1216 = p
in (let _124_468 = (let _124_467 = (let _124_466 = (FStar_All.pipe_right pats (FStar_List.map (fun _35_1220 -> (match (_35_1220) with
| (p, b) -> begin
(let _124_465 = (aux_disj sub pat_var_renaming p)
in (_124_465, b))
end))))
in (fv, _124_466))
in FStar_Syntax_Syntax.Pat_cons (_124_467))
in {FStar_Syntax_Syntax.v = _124_468; FStar_Syntax_Syntax.ty = _35_1216.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1216.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let yopt = (FStar_Util.find_map pat_var_renaming (fun _35_18 -> (match (_35_18) with
| (x', y) when (x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x'.FStar_Syntax_Syntax.ppname.FStar_Ident.idText) -> begin
Some (y)
end
| _35_1228 -> begin
None
end)))
in (

let y = (match (yopt) with
| None -> begin
(

let _35_1231 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_470 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_470}))
end
| Some (y) -> begin
y
end)
in (

let _35_1236 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (y); FStar_Syntax_Syntax.ty = _35_1236.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1236.FStar_Syntax_Syntax.p})))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_1240 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_471 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1240.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1240.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_471}))
in (

let _35_1243 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_1243.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1243.FStar_Syntax_Syntax.p}))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_1249 = x
in (let _124_472 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1249.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_472}))
in (

let t0 = (rename sub t0)
in (

let _35_1253 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_1253.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1253.FStar_Syntax_Syntax.p})))
end))
in (

let rec aux = (fun sub pat_var_renaming p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_1262) -> begin
(p, sub, pat_var_renaming)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_1271 = (aux sub pat_var_renaming p)
in (match (_35_1271) with
| (p, sub, renaming) -> begin
(

let ps = (FStar_List.map (aux_disj sub renaming) ps)
in ((

let _35_1273 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_1273.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1273.FStar_Syntax_Syntax.p}), sub, renaming))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_1293 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_1282 _35_1285 -> (match ((_35_1282, _35_1285)) with
| ((pats, sub, renaming), (p, imp)) -> begin
(

let _35_1289 = (aux sub renaming p)
in (match (_35_1289) with
| (p, sub, renaming) -> begin
(((p, imp))::pats, sub, renaming)
end))
end)) ([], sub, pat_var_renaming)))
in (match (_35_1293) with
| (pats, sub, renaming) -> begin
((

let _35_1294 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_1294.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1294.FStar_Syntax_Syntax.p}), sub, renaming)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x' = (

let _35_1298 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_481 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1298.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1298.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_481}))
in (

let sub = (

let sub' = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::sub')
in ((

let _35_1303 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x'); FStar_Syntax_Syntax.ty = _35_1303.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1303.FStar_Syntax_Syntax.p}), sub, ((x, x'))::pat_var_renaming)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x' = (

let _35_1307 = (FStar_Syntax_Syntax.freshen_bv x)
in (let _124_482 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1307.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1307.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_482}))
in (

let sub = (

let sub' = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Index2Name ((0, x')))::sub')
in ((

let _35_1312 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x'); FStar_Syntax_Syntax.ty = _35_1312.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1312.FStar_Syntax_Syntax.p}), sub, ((x, x'))::pat_var_renaming)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_1318 = x
in (let _124_483 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1318.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1318.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_483}))
in (

let t0 = (rename sub t0)
in ((

let _35_1322 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_1322.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1322.FStar_Syntax_Syntax.p}), sub, pat_var_renaming)))
end))
in (

let _35_1328 = (aux [] [] p)
in (match (_35_1328) with
| (p, sub, _35_1327) -> begin
(p, sub)
end)))))


let open_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_1332 -> (match (_35_1332) with
| (p, wopt, e) -> begin
(

let _35_1335 = (open_pat p)
in (match (_35_1335) with
| (p, opening) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_486 = (rename opening w)
in Some (_124_486))
end)
in (

let e = (rename opening e)
in (p, wopt, e)))
end))
end))


let close : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (let _124_491 = (closing_subst bs)
in (rename _124_491 t)))


let close_comp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp = (fun bs c -> (let _124_496 = (closing_subst bs)
in (rename_comp _124_496 c)))


let close_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let rec aux = (fun s bs -> (match (bs) with
| [] -> begin
[]
end
| (x, imp)::tl -> begin
(

let x = (

let _35_1355 = x
in (let _124_503 = (rename s x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1355.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1355.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_503}))
in (

let s' = (let _124_504 = (shift_renaming 1 s)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_504)
in (let _124_505 = (aux s' tl)
in ((x, imp))::_124_505)))
end))
in (aux [] bs)))


let close_lcomp : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.lcomp  ->  FStar_Syntax_Syntax.lcomp = (fun bs lc -> (

let s = (closing_subst bs)
in (

let _35_1362 = lc
in (let _124_512 = (rename s lc.FStar_Syntax_Syntax.res_typ)
in {FStar_Syntax_Syntax.eff_name = _35_1362.FStar_Syntax_Syntax.eff_name; FStar_Syntax_Syntax.res_typ = _124_512; FStar_Syntax_Syntax.cflags = _35_1362.FStar_Syntax_Syntax.cflags; FStar_Syntax_Syntax.comp = (fun _35_1364 -> (match (()) with
| () -> begin
(let _124_511 = (lc.FStar_Syntax_Syntax.comp ())
in (rename_comp s _124_511))
end))}))))


let close_pat : (FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_Syntax_Syntax.pat', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.withinfo_t * renaming) = (fun p -> (

let rec aux = (fun sub p -> (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible: empty disjunction")
end
| FStar_Syntax_Syntax.Pat_constant (_35_1372) -> begin
(p, sub)
end
| FStar_Syntax_Syntax.Pat_disj (p::ps) -> begin
(

let _35_1380 = (aux sub p)
in (match (_35_1380) with
| (p, sub) -> begin
(

let ps = (FStar_List.map (fun p -> (let _124_520 = (aux sub p)
in (Prims.fst _124_520))) ps)
in ((

let _35_1383 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_disj ((p)::ps); FStar_Syntax_Syntax.ty = _35_1383.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1383.FStar_Syntax_Syntax.p}), sub))
end))
end
| FStar_Syntax_Syntax.Pat_cons (fv, pats) -> begin
(

let _35_1400 = (FStar_All.pipe_right pats (FStar_List.fold_left (fun _35_1391 _35_1394 -> (match ((_35_1391, _35_1394)) with
| ((pats, sub), (p, imp)) -> begin
(

let _35_1397 = (aux sub p)
in (match (_35_1397) with
| (p, sub) -> begin
(((p, imp))::pats, sub)
end))
end)) ([], sub)))
in (match (_35_1400) with
| (pats, sub) -> begin
((

let _35_1401 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_cons ((fv, (FStar_List.rev pats))); FStar_Syntax_Syntax.ty = _35_1401.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1401.FStar_Syntax_Syntax.p}), sub)
end))
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let x = (

let _35_1405 = x
in (let _124_523 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1405.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1405.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_523}))
in (

let sub = (let _124_524 = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_524)
in ((

let _35_1409 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (x); FStar_Syntax_Syntax.ty = _35_1409.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1409.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let x = (

let _35_1413 = x
in (let _124_525 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1413.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1413.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_525}))
in (

let sub = (let _124_526 = (shift_renaming 1 sub)
in (FStar_Syntax_Syntax.Name2Index ((x, 0)))::_124_526)
in ((

let _35_1417 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (x); FStar_Syntax_Syntax.ty = _35_1417.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1417.FStar_Syntax_Syntax.p}), sub)))
end
| FStar_Syntax_Syntax.Pat_dot_term (x, t0) -> begin
(

let x = (

let _35_1423 = x
in (let _124_527 = (rename sub x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _35_1423.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _35_1423.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _124_527}))
in (

let t0 = (rename sub t0)
in ((

let _35_1427 = p
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_dot_term ((x, t0)); FStar_Syntax_Syntax.ty = _35_1427.FStar_Syntax_Syntax.ty; FStar_Syntax_Syntax.p = _35_1427.FStar_Syntax_Syntax.p}), sub)))
end))
in (aux [] p)))


let close_branch : FStar_Syntax_Syntax.branch  ->  FStar_Syntax_Syntax.branch = (fun _35_1432 -> (match (_35_1432) with
| (p, wopt, e) -> begin
(

let _35_1435 = (close_pat p)
in (match (_35_1435) with
| (p, closing) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (w) -> begin
(let _124_530 = (rename closing w)
in Some (_124_530))
end)
in (

let e = (rename closing e)
in (p, wopt, e)))
end))
end))


let univ_var_opening : FStar_Syntax_Syntax.univ_names  ->  (FStar_Syntax_Syntax.renaming_subst Prims.list * FStar_Syntax_Syntax.univ_name Prims.list) = (fun us -> (

let n = ((FStar_List.length us) - 1)
in (

let _35_1448 = (let _124_535 = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> (

let u' = (FStar_Syntax_Syntax.new_univ_name (Some (u.FStar_Ident.idRange)))
in (FStar_Syntax_Syntax.UIndex2UName (((n - i), u')), u')))))
in (FStar_All.pipe_right _124_535 FStar_List.unzip))
in (match (_35_1448) with
| (s, us') -> begin
(s, us')
end))))


let open_univ_vars : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) = (fun us t -> (

let _35_1453 = (univ_var_opening us)
in (match (_35_1453) with
| (s, us') -> begin
(

let t = (rename s t)
in (us', t))
end)))


let open_univ_vars_comp : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.comp  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.comp) = (fun us c -> (

let _35_1459 = (univ_var_opening us)
in (match (_35_1459) with
| (s, us') -> begin
(let _124_544 = (rename_comp s c)
in (us', _124_544))
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

let _35_1485 = (FStar_List.fold_right (fun lb _35_1478 -> (match (_35_1478) with
| (i, lbs, out) -> begin
(

let x = (let _124_563 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (FStar_Syntax_Syntax.freshen_bv _124_563))
in ((i + 1), ((

let _35_1480 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _35_1480.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_1480.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1480.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _35_1480.FStar_Syntax_Syntax.lbdef}))::lbs, (FStar_Syntax_Syntax.Index2Name ((i, x)))::out))
end)) lbs (0, [], []))
in (match (_35_1485) with
| (n_let_recs, lbs, let_rec_opening) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_1497 = (FStar_List.fold_right (fun u _35_1491 -> (match (_35_1491) with
| (i, us, out) -> begin
(

let u = (FStar_Syntax_Syntax.new_univ_name None)
in ((i + 1), (u)::us, (FStar_Syntax_Syntax.UIndex2UName ((i, u)))::out))
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, [], let_rec_opening))
in (match (_35_1497) with
| (_35_1494, us, u_let_rec_opening) -> begin
(

let _35_1498 = lb
in (let _124_567 = (rename u_let_rec_opening lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_1498.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = us; FStar_Syntax_Syntax.lbtyp = _35_1498.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1498.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_567}))
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

let _35_1510 = (FStar_List.fold_right (fun lb _35_1507 -> (match (_35_1507) with
| (i, out) -> begin
(let _124_577 = (let _124_576 = (let _124_575 = (let _124_574 = (FStar_Util.left lb.FStar_Syntax_Syntax.lbname)
in (_124_574, i))
in FStar_Syntax_Syntax.Name2Index (_124_575))
in (_124_576)::out)
in ((i + 1), _124_577))
end)) lbs (0, []))
in (match (_35_1510) with
| (n_let_recs, let_rec_closing) -> begin
(

let lbs = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let _35_1519 = (FStar_List.fold_right (fun u _35_1515 -> (match (_35_1515) with
| (i, out) -> begin
((i + 1), (FStar_Syntax_Syntax.UName2UIndex ((u, i)))::out)
end)) lb.FStar_Syntax_Syntax.lbunivs (n_let_recs, let_rec_closing))
in (match (_35_1519) with
| (_35_1517, u_let_rec_closing) -> begin
(

let _35_1520 = lb
in (let _124_581 = (rename u_let_rec_closing lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = _35_1520.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _35_1520.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _35_1520.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _35_1520.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _124_581}))
end)))))
in (

let t = (rename let_rec_closing t)
in (lbs, t)))
end))
end)


let close_tscheme : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun binders _35_1527 -> (match (_35_1527) with
| (us, t) -> begin
(

let n = ((FStar_List.length binders) - 1)
in (

let k = (FStar_List.length us)
in (

let s = (FStar_List.mapi (fun i _35_1534 -> (match (_35_1534) with
| (x, _35_1533) -> begin
FStar_Syntax_Syntax.Name2Index ((x, (k + (n - i))))
end)) binders)
in (

let t = (rename s t)
in (us, t)))))
end))


let close_univ_vars_tscheme : FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.tscheme = (fun us _35_1540 -> (match (_35_1540) with
| (us', t) -> begin
(

let n = ((FStar_List.length us) - 1)
in (

let k = (FStar_List.length us')
in (

let s = (FStar_List.mapi (fun i x -> FStar_Syntax_Syntax.UName2UIndex ((x, (k + (n - i))))) us)
in (let _124_594 = (rename s t)
in (us', _124_594)))))
end))


let opening_of_binders : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.subst_t = (fun bs -> (

let n = ((FStar_List.length bs) - 1)
in (let _124_599 = (FStar_All.pipe_right bs (FStar_List.mapi (fun i _35_1552 -> (match (_35_1552) with
| (x, _35_1551) -> begin
FStar_Syntax_Syntax.Index2Name (((n - i), x))
end))))
in FStar_Syntax_Syntax.Renaming (_124_599))))





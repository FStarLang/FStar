
open Prims
# 34 "FStar.Parser.Dep.fst"
type map =
Prims.string FStar_Util.smap

# 36 "FStar.Parser.Dep.fst"
let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (
# 39 "FStar.Parser.Dep.fst"
let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (
# 40 "FStar.Parser.Dep.fst"
let matches = (FStar_List.map (fun ext -> (
# 41 "FStar.Parser.Dep.fst"
let lext = (FStar_String.length ext)
in (
# 42 "FStar.Parser.Dep.fst"
let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _142_4 = (FStar_String.substring f 0 (l - lext))
in Some (_142_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_57_17 -> begin
Some (m)
end
| _57_22 -> begin
None
end))))

# 52 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 56 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _142_13 = (let _142_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _142_12))
in (FStar_List.iter (fun k -> (let _142_11 = (let _142_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _142_10))
in (FStar_Util.print2 "%s: %s\n" k _142_11))) _142_13)))

# 61 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _142_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _142_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _142_18 = (let _142_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_142_17))
in (Prims.raise _142_18))
end))

# 69 "FStar.Parser.Dep.fst"
let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (
# 75 "FStar.Parser.Dep.fst"
let include_directories = (FStar_Options.get_include_path ())
in (
# 76 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (
# 77 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.unique include_directories)
in (
# 78 "FStar.Parser.Dep.fst"
let cwd = (let _142_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _142_21))
in (
# 79 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 80 "FStar.Parser.Dep.fst"
let _57_48 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(
# 82 "FStar.Parser.Dep.fst"
let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (
# 84 "FStar.Parser.Dep.fst"
let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(
# 87 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase longname)
in (
# 88 "FStar.Parser.Dep.fst"
let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
if ((not ((is_interface existing_file))) || (is_interface f)) then begin
(FStar_Util.smap_add map key full_path)
end else begin
()
end
end
| None -> begin
(FStar_Util.smap_add map key full_path)
end)))
end
| None -> begin
()
end))) files))
end else begin
(let _142_25 = (let _142_24 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_142_24))
in (Prims.raise _142_25))
end) include_directories)
in (
# 109 "FStar.Parser.Dep.fst"
let _57_51 = (FStar_List.iter (fun f -> (let _142_27 = (lowercase_module_name f)
in (FStar_Util.smap_add map _142_27 f))) filenames)
in map))))))))

# 112 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 119 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 120 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 121 "FStar.Parser.Dep.fst"
let _57_63 = (let _142_37 = (let _142_36 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _142_36))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 123 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 126 "FStar.Parser.Dep.fst"
let filename = (let _142_35 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _142_35))
in (
# 127 "FStar.Parser.Dep.fst"
let _57_61 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _142_37))
in (FStar_ST.read found)))))

# 130 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 134 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 135 "FStar.Parser.Dep.fst"
let names = (let _142_43 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _142_43 suffix))
in (FStar_String.concat "." names))))

# 136 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _142_48 = (string_of_lid l last)
in (FStar_String.lowercase _142_48)))

# 141 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 145 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _142_55 = (let _142_54 = (let _142_53 = (FStar_Util.basename filename)
in (check_and_strip_suffix _142_53))
in (FStar_Util.must _142_54))
in (FStar_String.lowercase _142_55)) <> k') then begin
(let _142_57 = (let _142_56 = (string_of_lid lid true)
in (_142_56)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _142_57))
end else begin
()
end))

# 151 "FStar.Parser.Dep.fst"
exception Exit

# 151 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 151 "FStar.Parser.Dep.fst"
let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (
# 156 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 157 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _142_66 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _142_66)))) then begin
(let _142_68 = (let _142_67 = (FStar_ST.read deps)
in (d)::_142_67)
in (FStar_ST.op_Colon_Equals deps _142_68))
end else begin
()
end)
in (
# 161 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 163 "FStar.Parser.Dep.fst"
let record_open = (fun lid -> (
# 164 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _142_71 = (lowercase_module_name filename)
in (add_dep _142_71))
end
| None -> begin
(
# 169 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _142_73 = (let _142_72 = (string_of_lid lid true)
in (_142_72)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _142_73))
end else begin
()
end)
end)))
in (
# 178 "FStar.Parser.Dep.fst"
let auto_open = (
# 179 "FStar.Parser.Dep.fst"
let index_of = (fun s l -> (
# 180 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc (- (1)))
in (FStar_All.try_with (fun _57_94 -> (match (()) with
| () -> begin
(
# 182 "FStar.Parser.Dep.fst"
let _57_103 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(
# 184 "FStar.Parser.Dep.fst"
let _57_101 = (FStar_ST.op_Colon_Equals found i)
in (Prims.raise Exit))
end else begin
()
end) l)
in (- (1)))
end)) (fun _57_93 -> (match (_57_93) with
| Exit -> begin
(FStar_ST.read found)
end)))))
in (
# 193 "FStar.Parser.Dep.fst"
let ordered = ("fstar")::("prims")::("fstar.list.tot")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.map")::("fstar.hyperheap")::("fstar.st")::("fstar.all")::[]
in (
# 198 "FStar.Parser.Dep.fst"
let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (
# 199 "FStar.Parser.Dep.fst"
let me = (let _142_84 = (let _142_83 = (let _142_82 = (FStar_Util.basename filename)
in (check_and_strip_suffix _142_82))
in (FStar_Util.must _142_83))
in (FStar_String.lowercase _142_84))
in (
# 200 "FStar.Parser.Dep.fst"
let index_or_length = (fun s l -> (
# 201 "FStar.Parser.Dep.fst"
let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (
# 204 "FStar.Parser.Dep.fst"
let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _142_90 = (lowercase_join_longident lid true)
in (index_or_length _142_90 ordered)) < my_index)) desired_opens)))))))
in (
# 207 "FStar.Parser.Dep.fst"
let _57_115 = (FStar_List.iter record_open auto_open)
in (
# 209 "FStar.Parser.Dep.fst"
let rec collect_fragment = (fun _57_1 -> (match (_57_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _57_2 -> (match (_57_2) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(
# 219 "FStar.Parser.Dep.fst"
let _57_142 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _57_3 -> (match (_57_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 225 "FStar.Parser.Dep.fst"
let _57_153 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _57_4 -> (match (_57_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_57_161, _57_163, patterms) -> begin
(FStar_List.iter (fun _57_170 -> (match (_57_170) with
| (_57_168, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_57_172, binders, t) -> begin
(
# 237 "FStar.Parser.Dep.fst"
let _57_177 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_57_200, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_57_205, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_57_210, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_57_215) -> begin
()
end))
and collect_tycon = (fun _57_5 -> (match (_57_5) with
| FStar_Parser_AST.TyconAbstract (_57_219, binders, k) -> begin
(
# 255 "FStar.Parser.Dep.fst"
let _57_224 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_57_227, binders, k, t) -> begin
(
# 258 "FStar.Parser.Dep.fst"
let _57_233 = (collect_binders binders)
in (
# 259 "FStar.Parser.Dep.fst"
let _57_235 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_57_238, binders, k, identterms) -> begin
(
# 262 "FStar.Parser.Dep.fst"
let _57_244 = (collect_binders binders)
in (
# 263 "FStar.Parser.Dep.fst"
let _57_246 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _57_251 -> (match (_57_251) with
| (_57_249, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_57_253, binders, k, identterms) -> begin
(
# 266 "FStar.Parser.Dep.fst"
let _57_259 = (collect_binders binders)
in (
# 267 "FStar.Parser.Dep.fst"
let _57_261 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _57_268 -> (match (_57_268) with
| (_57_264, t, _57_267) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _57_6 -> (match (_57_6) with
| FStar_Parser_AST.DefineEffect (_57_271, binders, t, decls) -> begin
(
# 272 "FStar.Parser.Dep.fst"
let _57_277 = (collect_binders binders)
in (
# 273 "FStar.Parser.Dep.fst"
let _57_279 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_57_282, binders, t) -> begin
(
# 276 "FStar.Parser.Dep.fst"
let _57_287 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _57_7 -> (match (_57_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _57_315 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _57_8 -> (match (_57_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_57_320) -> begin
()
end
| FStar_Parser_AST.Op (_57_323, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_57_328) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(
# 304 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _142_122 = (lowercase_module_name filename)
in (add_dep _142_122))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _142_124 = (let _142_123 = (string_of_lid lid false)
in (_142_123)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _142_124))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_57_338, termimps) -> begin
(FStar_List.iter (fun _57_345 -> (match (_57_345) with
| (t, _57_344) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 316 "FStar.Parser.Dep.fst"
let _57_350 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _57_355) -> begin
(
# 319 "FStar.Parser.Dep.fst"
let _57_358 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_57_361, patterms, t) -> begin
(
# 322 "FStar.Parser.Dep.fst"
let _57_370 = (FStar_List.iter (fun _57_369 -> (match (_57_369) with
| (_57_367, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 325 "FStar.Parser.Dep.fst"
let _57_376 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 328 "FStar.Parser.Dep.fst"
let _57_383 = (collect_term t1)
in (
# 329 "FStar.Parser.Dep.fst"
let _57_385 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 333 "FStar.Parser.Dep.fst"
let _57_393 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 336 "FStar.Parser.Dep.fst"
let _57_399 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _57_407) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 344 "FStar.Parser.Dep.fst"
let _57_416 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 348 "FStar.Parser.Dep.fst"
let _57_425 = (collect_binders binders)
in (
# 349 "FStar.Parser.Dep.fst"
let _57_427 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 352 "FStar.Parser.Dep.fst"
let _57_433 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_57_436, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) -> begin
(collect_term t)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun _57_9 -> (match (_57_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_57_462) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(
# 375 "FStar.Parser.Dep.fst"
let _57_468 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _57_491 -> (match (_57_491) with
| (_57_489, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 388 "FStar.Parser.Dep.fst"
let _57_496 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _57_502 -> (match (_57_502) with
| (pat, t1, t2) -> begin
(
# 396 "FStar.Parser.Dep.fst"
let _57_503 = (collect_pattern pat)
in (
# 397 "FStar.Parser.Dep.fst"
let _57_505 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 401 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file filename)
in (
# 402 "FStar.Parser.Dep.fst"
let _57_508 = (collect_file ast)
in (FStar_ST.read deps)))))))))))

# 403 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 405 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 405 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 405 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 405 "FStar.Parser.Dep.fst"
let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (
# 411 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 416 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 419 "FStar.Parser.Dep.fst"
let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 421 "FStar.Parser.Dep.fst"
let filename = (let _142_140 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _142_140))
in (
# 422 "FStar.Parser.Dep.fst"
let deps = (collect_one m filename)
in (
# 423 "FStar.Parser.Dep.fst"
let _57_517 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (
# 426 "FStar.Parser.Dep.fst"
let _57_519 = (let _142_141 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _142_141))
in (
# 429 "FStar.Parser.Dep.fst"
let print_graph = (fun _57_522 -> (match (()) with
| () -> begin
(let _142_150 = (let _142_149 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _142_149))
in (FStar_List.iter (fun k -> (let _142_148 = (let _142_147 = (let _142_146 = (let _142_145 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _142_145))
in (Prims.fst _142_146))
in (FStar_String.concat " " _142_147))
in (FStar_Util.print2 "%s: %s\n" k _142_148))) _142_150))
end))
in (
# 435 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 438 "FStar.Parser.Dep.fst"
let rec discover = (fun key -> (
# 439 "FStar.Parser.Dep.fst"
let _57_529 = (let _142_153 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _142_153))
in (match (_57_529) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 442 "FStar.Parser.Dep.fst"
let _57_531 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 443 "FStar.Parser.Dep.fst"
let _57_533 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (
# 444 "FStar.Parser.Dep.fst"
let _57_535 = (print_graph ())
in (
# 445 "FStar.Parser.Dep.fst"
let _57_537 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 453 "FStar.Parser.Dep.fst"
let _57_541 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (
# 454 "FStar.Parser.Dep.fst"
let all_deps = (let _142_157 = (let _142_156 = (FStar_List.map (fun dep -> (let _142_155 = (discover dep)
in (dep)::_142_155)) direct_deps)
in (FStar_List.flatten _142_156))
in (FStar_List.unique _142_157))
in (
# 458 "FStar.Parser.Dep.fst"
let _57_545 = (FStar_Util.smap_add graph key (all_deps, Black))
in (
# 460 "FStar.Parser.Dep.fst"
let _57_547 = (let _142_159 = (let _142_158 = (FStar_ST.read topologically_sorted)
in (key)::_142_158)
in (FStar_ST.op_Colon_Equals topologically_sorted _142_159))
in all_deps))))
end)
end)))
in (
# 465 "FStar.Parser.Dep.fst"
let must_find = (fun k -> (let _142_162 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _142_162)))
in (
# 468 "FStar.Parser.Dep.fst"
let by_target = (let _142_167 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (
# 469 "FStar.Parser.Dep.fst"
let deps = (let _142_164 = (discover k)
in (FStar_List.rev _142_164))
in (let _142_166 = (must_find k)
in (let _142_165 = (FStar_List.map must_find deps)
in (_142_166, _142_165))))) _142_167))
in (
# 472 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _142_168 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _142_168))
in (by_target, topologically_sorted))))))))))))

# 474 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _57_558 -> (match (_57_558) with
| (f, deps) -> begin
(
# 481 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 483 "FStar.Parser.Dep.fst"
let print_nubuild : Prims.string Prims.list  ->  Prims.unit = (fun l -> (FStar_List.iter FStar_Util.print_endline (FStar_List.rev l)))

# 486 "FStar.Parser.Dep.fst"
let print : ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list)  ->  Prims.unit = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("nubuild") -> begin
(print_nubuild (Prims.snd deps))
end
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_57_568) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))





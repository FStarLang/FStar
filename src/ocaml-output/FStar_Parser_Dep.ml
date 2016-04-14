
open Prims
# 36 "FStar.Parser.Dep.fst"
type map =
Prims.string FStar_Util.smap

# 38 "FStar.Parser.Dep.fst"
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
(let _150_4 = (FStar_String.substring f 0 (l - lext))
in Some (_150_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_61_17 -> begin
Some (m)
end
| _61_22 -> begin
None
end))))

# 55 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 58 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _150_13 = (let _150_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _150_12))
in (FStar_List.iter (fun k -> (let _150_11 = (let _150_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _150_10))
in (FStar_Util.print2 "%s: %s\n" k _150_11))) _150_13)))

# 64 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _150_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _150_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _150_18 = (let _150_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_150_17))
in (Prims.raise _150_18))
end))

# 74 "FStar.Parser.Dep.fst"
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
let cwd = (let _150_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _150_21))
in (
# 79 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 80 "FStar.Parser.Dep.fst"
let _61_48 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
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
(let _150_25 = (let _150_24 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_150_24))
in (Prims.raise _150_25))
end) include_directories)
in (
# 109 "FStar.Parser.Dep.fst"
let _61_51 = (FStar_List.iter (fun f -> (let _150_27 = (lowercase_module_name f)
in (FStar_Util.smap_add map _150_27 f))) filenames)
in map))))))))

# 118 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 119 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 120 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 121 "FStar.Parser.Dep.fst"
let _61_63 = (let _150_37 = (let _150_36 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _150_36))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 123 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 126 "FStar.Parser.Dep.fst"
let filename = (let _150_35 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _150_35))
in (
# 127 "FStar.Parser.Dep.fst"
let _61_61 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _150_37))
in (FStar_ST.read found)))))

# 133 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 134 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 135 "FStar.Parser.Dep.fst"
let names = (let _150_43 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _150_43 suffix))
in (FStar_String.concat "." names))))

# 141 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _150_48 = (string_of_lid l last)
in (FStar_String.lowercase _150_48)))

# 145 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 146 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _150_55 = (let _150_54 = (let _150_53 = (FStar_Util.basename filename)
in (check_and_strip_suffix _150_53))
in (FStar_Util.must _150_54))
in (FStar_String.lowercase _150_55)) <> k') then begin
(let _150_57 = (let _150_56 = (string_of_lid lid true)
in (_150_56)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _150_57))
end else begin
()
end))

# 152 "FStar.Parser.Dep.fst"
exception Exit

# 152 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 156 "FStar.Parser.Dep.fst"
let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (
# 157 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 158 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _150_66 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _150_66)))) then begin
(let _150_68 = (let _150_67 = (FStar_ST.read deps)
in (d)::_150_67)
in (FStar_ST.op_Colon_Equals deps _150_68))
end else begin
()
end)
in (
# 162 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 164 "FStar.Parser.Dep.fst"
let record_open = (fun lid -> (
# 165 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _150_71 = (lowercase_module_name filename)
in (add_dep _150_71))
end
| None -> begin
(
# 170 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _150_73 = (let _150_72 = (string_of_lid lid true)
in (_150_72)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _150_73))
end else begin
()
end)
end)))
in (
# 176 "FStar.Parser.Dep.fst"
let record_module_alias = (fun ident lid -> (
# 177 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (
# 178 "FStar.Parser.Dep.fst"
let alias = (lowercase_join_longident lid true)
in (
# 179 "FStar.Parser.Dep.fst"
let deps_of_aliased_module = (let _150_78 = (FStar_Util.smap_try_find working_map alias)
in (FStar_Util.must _150_78))
in (FStar_Util.smap_add working_map key deps_of_aliased_module)))))
in (
# 185 "FStar.Parser.Dep.fst"
let auto_open = (
# 186 "FStar.Parser.Dep.fst"
let index_of = (fun s l -> (
# 187 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc (- (1)))
in try
(match (()) with
| () -> begin
(
# 189 "FStar.Parser.Dep.fst"
let _61_109 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(
# 191 "FStar.Parser.Dep.fst"
let _61_107 = (FStar_ST.op_Colon_Equals found i)
in (Prims.raise Exit))
end else begin
()
end) l)
in (- (1)))
end)
with
| Exit -> begin
(FStar_ST.read found)
end))
in (
# 200 "FStar.Parser.Dep.fst"
let ordered = ("fstar")::("prims")::("fstar.list.tot")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.map")::("fstar.hyperheap")::("fstar.st")::("fstar.all")::[]
in (
# 205 "FStar.Parser.Dep.fst"
let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (
# 206 "FStar.Parser.Dep.fst"
let me = (let _150_89 = (let _150_88 = (let _150_87 = (FStar_Util.basename filename)
in (check_and_strip_suffix _150_87))
in (FStar_Util.must _150_88))
in (FStar_String.lowercase _150_89))
in (
# 207 "FStar.Parser.Dep.fst"
let index_or_length = (fun s l -> (
# 208 "FStar.Parser.Dep.fst"
let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (
# 211 "FStar.Parser.Dep.fst"
let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _150_95 = (lowercase_join_longident lid true)
in (index_or_length _150_95 ordered)) < my_index)) desired_opens)))))))
in (
# 214 "FStar.Parser.Dep.fst"
let _61_121 = (FStar_List.iter record_open auto_open)
in (
# 216 "FStar.Parser.Dep.fst"
let rec collect_fragment = (fun _61_1 -> (match (_61_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _61_2 -> (match (_61_2) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(
# 226 "FStar.Parser.Dep.fst"
let _61_148 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _61_3 -> (match (_61_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 232 "FStar.Parser.Dep.fst"
let _61_159 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _61_4 -> (match (_61_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(record_module_alias ident lid)
end
| FStar_Parser_AST.ToplevelLet (_61_171, _61_173, patterms) -> begin
(FStar_List.iter (fun _61_180 -> (match (_61_180) with
| (_61_178, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_61_182, binders, t) -> begin
(
# 246 "FStar.Parser.Dep.fst"
let _61_187 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_61_210, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_61_215, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_61_220, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_61_225) -> begin
()
end))
and collect_tycon = (fun _61_5 -> (match (_61_5) with
| FStar_Parser_AST.TyconAbstract (_61_229, binders, k) -> begin
(
# 264 "FStar.Parser.Dep.fst"
let _61_234 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_61_237, binders, k, t) -> begin
(
# 267 "FStar.Parser.Dep.fst"
let _61_243 = (collect_binders binders)
in (
# 268 "FStar.Parser.Dep.fst"
let _61_245 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_61_248, binders, k, identterms) -> begin
(
# 271 "FStar.Parser.Dep.fst"
let _61_254 = (collect_binders binders)
in (
# 272 "FStar.Parser.Dep.fst"
let _61_256 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _61_261 -> (match (_61_261) with
| (_61_259, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_61_263, binders, k, identterms) -> begin
(
# 275 "FStar.Parser.Dep.fst"
let _61_269 = (collect_binders binders)
in (
# 276 "FStar.Parser.Dep.fst"
let _61_271 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _61_278 -> (match (_61_278) with
| (_61_274, t, _61_277) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _61_6 -> (match (_61_6) with
| FStar_Parser_AST.DefineEffect (_61_281, binders, t, decls) -> begin
(
# 281 "FStar.Parser.Dep.fst"
let _61_287 = (collect_binders binders)
in (
# 282 "FStar.Parser.Dep.fst"
let _61_289 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_61_292, binders, t) -> begin
(
# 285 "FStar.Parser.Dep.fst"
let _61_297 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _61_7 -> (match (_61_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _61_325 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _61_8 -> (match (_61_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_61_330) -> begin
()
end
| FStar_Parser_AST.Op (_61_333, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_61_338) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(
# 313 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _150_127 = (lowercase_module_name filename)
in (add_dep _150_127))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _150_129 = (let _150_128 = (string_of_lid lid false)
in (_150_128)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _150_129))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_61_348, termimps) -> begin
(FStar_List.iter (fun _61_355 -> (match (_61_355) with
| (t, _61_354) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 325 "FStar.Parser.Dep.fst"
let _61_360 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _61_365) -> begin
(
# 328 "FStar.Parser.Dep.fst"
let _61_368 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_61_371, patterms, t) -> begin
(
# 331 "FStar.Parser.Dep.fst"
let _61_380 = (FStar_List.iter (fun _61_379 -> (match (_61_379) with
| (_61_377, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 334 "FStar.Parser.Dep.fst"
let _61_386 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 337 "FStar.Parser.Dep.fst"
let _61_393 = (collect_term t1)
in (
# 338 "FStar.Parser.Dep.fst"
let _61_395 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 342 "FStar.Parser.Dep.fst"
let _61_403 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 345 "FStar.Parser.Dep.fst"
let _61_409 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _61_417) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 353 "FStar.Parser.Dep.fst"
let _61_426 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 357 "FStar.Parser.Dep.fst"
let _61_435 = (collect_binders binders)
in (
# 358 "FStar.Parser.Dep.fst"
let _61_437 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 361 "FStar.Parser.Dep.fst"
let _61_443 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_61_446, t) -> begin
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
and collect_pattern' = (fun _61_9 -> (match (_61_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_61_472) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(
# 384 "FStar.Parser.Dep.fst"
let _61_478 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _61_501 -> (match (_61_501) with
| (_61_499, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 397 "FStar.Parser.Dep.fst"
let _61_506 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _61_512 -> (match (_61_512) with
| (pat, t1, t2) -> begin
(
# 405 "FStar.Parser.Dep.fst"
let _61_513 = (collect_pattern pat)
in (
# 406 "FStar.Parser.Dep.fst"
let _61_515 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 410 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file filename)
in (
# 411 "FStar.Parser.Dep.fst"
let _61_518 = (collect_file ast)
in (FStar_ST.read deps))))))))))))

# 414 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 414 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 414 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 414 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 417 "FStar.Parser.Dep.fst"
let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (
# 420 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 425 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 428 "FStar.Parser.Dep.fst"
let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 430 "FStar.Parser.Dep.fst"
let filename = (let _150_145 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _150_145))
in (
# 431 "FStar.Parser.Dep.fst"
let deps = (collect_one m filename)
in (
# 432 "FStar.Parser.Dep.fst"
let _61_527 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (
# 435 "FStar.Parser.Dep.fst"
let _61_529 = (let _150_146 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _150_146))
in (
# 438 "FStar.Parser.Dep.fst"
let print_graph = (fun _61_532 -> (match (()) with
| () -> begin
(let _150_155 = (let _150_154 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _150_154))
in (FStar_List.iter (fun k -> (let _150_153 = (let _150_152 = (let _150_151 = (let _150_150 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _150_150))
in (Prims.fst _150_151))
in (FStar_String.concat " " _150_152))
in (FStar_Util.print2 "%s: %s\n" k _150_153))) _150_155))
end))
in (
# 444 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 447 "FStar.Parser.Dep.fst"
let rec discover = (fun key -> (
# 448 "FStar.Parser.Dep.fst"
let _61_539 = (let _150_158 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _150_158))
in (match (_61_539) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 451 "FStar.Parser.Dep.fst"
let _61_541 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 452 "FStar.Parser.Dep.fst"
let _61_543 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (
# 453 "FStar.Parser.Dep.fst"
let _61_545 = (print_graph ())
in (
# 454 "FStar.Parser.Dep.fst"
let _61_547 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 462 "FStar.Parser.Dep.fst"
let _61_551 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (
# 463 "FStar.Parser.Dep.fst"
let all_deps = (let _150_162 = (let _150_161 = (FStar_List.map (fun dep -> (let _150_160 = (discover dep)
in (dep)::_150_160)) direct_deps)
in (FStar_List.flatten _150_161))
in (FStar_List.unique _150_162))
in (
# 467 "FStar.Parser.Dep.fst"
let _61_555 = (FStar_Util.smap_add graph key (all_deps, Black))
in (
# 469 "FStar.Parser.Dep.fst"
let _61_557 = (let _150_164 = (let _150_163 = (FStar_ST.read topologically_sorted)
in (key)::_150_163)
in (FStar_ST.op_Colon_Equals topologically_sorted _150_164))
in all_deps))))
end)
end)))
in (
# 474 "FStar.Parser.Dep.fst"
let must_find = (fun k -> (let _150_167 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _150_167)))
in (
# 477 "FStar.Parser.Dep.fst"
let by_target = (let _150_172 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (
# 478 "FStar.Parser.Dep.fst"
let deps = (let _150_169 = (discover k)
in (FStar_List.rev _150_169))
in (let _150_171 = (must_find k)
in (let _150_170 = (FStar_List.map must_find deps)
in (_150_171, _150_170))))) _150_172))
in (
# 481 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _150_173 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _150_173))
in (by_target, topologically_sorted))))))))))))

# 488 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _61_568 -> (match (_61_568) with
| (f, deps) -> begin
(
# 490 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 494 "FStar.Parser.Dep.fst"
let print = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_61_575) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))





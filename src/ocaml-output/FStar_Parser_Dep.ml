
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
(let _157_4 = (FStar_String.substring f 0 (l - lext))
in Some (_157_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_68_17 -> begin
Some (m)
end
| _68_22 -> begin
None
end))))

# 55 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 58 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _157_13 = (let _157_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _157_12))
in (FStar_List.iter (fun k -> (let _157_11 = (let _157_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _157_10))
in (FStar_Util.print2 "%s: %s\n" k _157_11))) _157_13)))

# 64 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _157_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _157_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _157_18 = (let _157_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_157_17))
in (Prims.raise _157_18))
end))

# 74 "FStar.Parser.Dep.fst"
let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (
# 76 "FStar.Parser.Dep.fst"
let include_directories = (FStar_Options.get_include_path ())
in (
# 77 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (
# 78 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.unique include_directories)
in (
# 79 "FStar.Parser.Dep.fst"
let cwd = (let _157_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _157_21))
in (
# 80 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 81 "FStar.Parser.Dep.fst"
let _68_48 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(
# 83 "FStar.Parser.Dep.fst"
let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (
# 85 "FStar.Parser.Dep.fst"
let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(
# 88 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase longname)
in (
# 89 "FStar.Parser.Dep.fst"
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
(let _157_25 = (let _157_24 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_157_24))
in (Prims.raise _157_25))
end) include_directories)
in (
# 110 "FStar.Parser.Dep.fst"
let _68_51 = (FStar_List.iter (fun f -> (let _157_27 = (lowercase_module_name f)
in (FStar_Util.smap_add map _157_27 f))) filenames)
in map))))))))

# 119 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 120 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 121 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 122 "FStar.Parser.Dep.fst"
let _68_63 = (let _157_37 = (let _157_36 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _157_36))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 124 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 127 "FStar.Parser.Dep.fst"
let filename = (let _157_35 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _157_35))
in (
# 128 "FStar.Parser.Dep.fst"
let _68_61 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _157_37))
in (FStar_ST.read found)))))

# 134 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 135 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 136 "FStar.Parser.Dep.fst"
let names = (let _157_43 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _157_43 suffix))
in (FStar_String.concat "." names))))

# 142 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _157_48 = (string_of_lid l last)
in (FStar_String.lowercase _157_48)))

# 146 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 147 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _157_55 = (let _157_54 = (let _157_53 = (FStar_Util.basename filename)
in (check_and_strip_suffix _157_53))
in (FStar_Util.must _157_54))
in (FStar_String.lowercase _157_55)) <> k') then begin
(let _157_57 = (let _157_56 = (string_of_lid lid true)
in (_157_56)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _157_57))
end else begin
()
end))

# 153 "FStar.Parser.Dep.fst"
exception Exit

# 153 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 157 "FStar.Parser.Dep.fst"
let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (
# 158 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 159 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _157_66 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _157_66)))) then begin
(let _157_68 = (let _157_67 = (FStar_ST.read deps)
in (d)::_157_67)
in (FStar_ST.op_Colon_Equals deps _157_68))
end else begin
()
end)
in (
# 163 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 165 "FStar.Parser.Dep.fst"
let record_open = (fun lid -> (
# 166 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _157_71 = (lowercase_module_name filename)
in (add_dep _157_71))
end
| None -> begin
(
# 171 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _157_73 = (let _157_72 = (string_of_lid lid true)
in (_157_72)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _157_73))
end else begin
()
end)
end)))
in (
# 177 "FStar.Parser.Dep.fst"
let record_module_alias = (fun ident lid -> (
# 178 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (
# 179 "FStar.Parser.Dep.fst"
let alias = (lowercase_join_longident lid true)
in (
# 180 "FStar.Parser.Dep.fst"
let deps_of_aliased_module = (let _157_78 = (FStar_Util.smap_try_find working_map alias)
in (FStar_Util.must _157_78))
in (FStar_Util.smap_add working_map key deps_of_aliased_module)))))
in (
# 186 "FStar.Parser.Dep.fst"
let auto_open = (
# 187 "FStar.Parser.Dep.fst"
let index_of = (fun s l -> (
# 188 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc (- (1)))
in try
(match (()) with
| () -> begin
(
# 190 "FStar.Parser.Dep.fst"
let _68_109 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(
# 192 "FStar.Parser.Dep.fst"
let _68_107 = (FStar_ST.op_Colon_Equals found i)
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
# 201 "FStar.Parser.Dep.fst"
let ordered = ("fstar")::("prims")::("fstar.list.tot")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.map")::("fstar.hyperheap")::("fstar.st")::("fstar.all")::[]
in (
# 206 "FStar.Parser.Dep.fst"
let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (
# 207 "FStar.Parser.Dep.fst"
let me = (let _157_89 = (let _157_88 = (let _157_87 = (FStar_Util.basename filename)
in (check_and_strip_suffix _157_87))
in (FStar_Util.must _157_88))
in (FStar_String.lowercase _157_89))
in (
# 208 "FStar.Parser.Dep.fst"
let index_or_length = (fun s l -> (
# 209 "FStar.Parser.Dep.fst"
let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (
# 212 "FStar.Parser.Dep.fst"
let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _157_95 = (lowercase_join_longident lid true)
in (index_or_length _157_95 ordered)) < my_index)) desired_opens)))))))
in (
# 215 "FStar.Parser.Dep.fst"
let _68_121 = (FStar_List.iter record_open auto_open)
in (
# 217 "FStar.Parser.Dep.fst"
let rec collect_fragment = (fun _68_1 -> (match (_68_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _68_2 -> (match (_68_2) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(
# 227 "FStar.Parser.Dep.fst"
let _68_148 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _68_3 -> (match (_68_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 233 "FStar.Parser.Dep.fst"
let _68_159 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _68_4 -> (match (_68_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(record_module_alias ident lid)
end
| FStar_Parser_AST.ToplevelLet (_68_171, _68_173, patterms) -> begin
(FStar_List.iter (fun _68_180 -> (match (_68_180) with
| (_68_178, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_68_182, binders, t) -> begin
(
# 247 "FStar.Parser.Dep.fst"
let _68_187 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_68_210, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_68_215, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (ed)) | (FStar_Parser_AST.NewEffect (_, ed)) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_68_226) -> begin
()
end))
and collect_tycon = (fun _68_5 -> (match (_68_5) with
| FStar_Parser_AST.TyconAbstract (_68_230, binders, k) -> begin
(
# 266 "FStar.Parser.Dep.fst"
let _68_235 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_68_238, binders, k, t) -> begin
(
# 269 "FStar.Parser.Dep.fst"
let _68_244 = (collect_binders binders)
in (
# 270 "FStar.Parser.Dep.fst"
let _68_246 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_68_249, binders, k, identterms) -> begin
(
# 273 "FStar.Parser.Dep.fst"
let _68_255 = (collect_binders binders)
in (
# 274 "FStar.Parser.Dep.fst"
let _68_257 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _68_262 -> (match (_68_262) with
| (_68_260, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_68_264, binders, k, identterms) -> begin
(
# 277 "FStar.Parser.Dep.fst"
let _68_270 = (collect_binders binders)
in (
# 278 "FStar.Parser.Dep.fst"
let _68_272 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _68_279 -> (match (_68_279) with
| (_68_275, t, _68_278) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _68_6 -> (match (_68_6) with
| FStar_Parser_AST.DefineEffect (_68_282, binders, t, decls) -> begin
(
# 283 "FStar.Parser.Dep.fst"
let _68_288 = (collect_binders binders)
in (
# 284 "FStar.Parser.Dep.fst"
let _68_290 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_68_293, binders, t) -> begin
(
# 287 "FStar.Parser.Dep.fst"
let _68_298 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _68_7 -> (match (_68_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _68_326 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _68_8 -> (match (_68_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_68_331) -> begin
()
end
| FStar_Parser_AST.Op (_68_334, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_68_339) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(
# 315 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _157_127 = (lowercase_module_name filename)
in (add_dep _157_127))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _157_129 = (let _157_128 = (string_of_lid lid false)
in (_157_128)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _157_129))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_68_349, termimps) -> begin
(FStar_List.iter (fun _68_356 -> (match (_68_356) with
| (t, _68_355) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 327 "FStar.Parser.Dep.fst"
let _68_361 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _68_366) -> begin
(
# 330 "FStar.Parser.Dep.fst"
let _68_369 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_68_372, patterms, t) -> begin
(
# 333 "FStar.Parser.Dep.fst"
let _68_381 = (FStar_List.iter (fun _68_380 -> (match (_68_380) with
| (_68_378, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 336 "FStar.Parser.Dep.fst"
let _68_387 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 339 "FStar.Parser.Dep.fst"
let _68_394 = (collect_term t1)
in (
# 340 "FStar.Parser.Dep.fst"
let _68_396 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 344 "FStar.Parser.Dep.fst"
let _68_404 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 347 "FStar.Parser.Dep.fst"
let _68_410 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _68_418) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 355 "FStar.Parser.Dep.fst"
let _68_427 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 359 "FStar.Parser.Dep.fst"
let _68_436 = (collect_binders binders)
in (
# 360 "FStar.Parser.Dep.fst"
let _68_438 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 363 "FStar.Parser.Dep.fst"
let _68_444 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_68_447, t) -> begin
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
and collect_pattern' = (fun _68_9 -> (match (_68_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_68_473) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(
# 386 "FStar.Parser.Dep.fst"
let _68_479 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _68_502 -> (match (_68_502) with
| (_68_500, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 399 "FStar.Parser.Dep.fst"
let _68_507 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _68_513 -> (match (_68_513) with
| (pat, t1, t2) -> begin
(
# 407 "FStar.Parser.Dep.fst"
let _68_514 = (collect_pattern pat)
in (
# 408 "FStar.Parser.Dep.fst"
let _68_516 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 412 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file filename)
in (
# 413 "FStar.Parser.Dep.fst"
let _68_519 = (collect_file ast)
in (FStar_ST.read deps))))))))))))

# 416 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 416 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 416 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 416 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 419 "FStar.Parser.Dep.fst"
let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (
# 422 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 427 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 430 "FStar.Parser.Dep.fst"
let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 432 "FStar.Parser.Dep.fst"
let filename = (let _157_145 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _157_145))
in (
# 433 "FStar.Parser.Dep.fst"
let deps = (collect_one m filename)
in (
# 434 "FStar.Parser.Dep.fst"
let _68_528 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (
# 437 "FStar.Parser.Dep.fst"
let _68_530 = (let _157_146 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _157_146))
in (
# 440 "FStar.Parser.Dep.fst"
let print_graph = (fun _68_533 -> (match (()) with
| () -> begin
(let _157_155 = (let _157_154 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _157_154))
in (FStar_List.iter (fun k -> (let _157_153 = (let _157_152 = (let _157_151 = (let _157_150 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _157_150))
in (Prims.fst _157_151))
in (FStar_String.concat " " _157_152))
in (FStar_Util.print2 "%s: %s\n" k _157_153))) _157_155))
end))
in (
# 446 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 449 "FStar.Parser.Dep.fst"
let rec discover = (fun key -> (
# 450 "FStar.Parser.Dep.fst"
let _68_540 = (let _157_158 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _157_158))
in (match (_68_540) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 453 "FStar.Parser.Dep.fst"
let _68_542 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 454 "FStar.Parser.Dep.fst"
let _68_544 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (
# 455 "FStar.Parser.Dep.fst"
let _68_546 = (print_graph ())
in (
# 456 "FStar.Parser.Dep.fst"
let _68_548 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 464 "FStar.Parser.Dep.fst"
let _68_552 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (
# 465 "FStar.Parser.Dep.fst"
let all_deps = (let _157_162 = (let _157_161 = (FStar_List.map (fun dep -> (let _157_160 = (discover dep)
in (dep)::_157_160)) direct_deps)
in (FStar_List.flatten _157_161))
in (FStar_List.unique _157_162))
in (
# 469 "FStar.Parser.Dep.fst"
let _68_556 = (FStar_Util.smap_add graph key (all_deps, Black))
in (
# 471 "FStar.Parser.Dep.fst"
let _68_558 = (let _157_164 = (let _157_163 = (FStar_ST.read topologically_sorted)
in (key)::_157_163)
in (FStar_ST.op_Colon_Equals topologically_sorted _157_164))
in all_deps))))
end)
end)))
in (
# 476 "FStar.Parser.Dep.fst"
let must_find = (fun k -> (let _157_167 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _157_167)))
in (
# 479 "FStar.Parser.Dep.fst"
let by_target = (let _157_172 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (
# 480 "FStar.Parser.Dep.fst"
let deps = (let _157_169 = (discover k)
in (FStar_List.rev _157_169))
in (let _157_171 = (must_find k)
in (let _157_170 = (FStar_List.map must_find deps)
in (_157_171, _157_170))))) _157_172))
in (
# 483 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _157_173 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _157_173))
in (by_target, topologically_sorted))))))))))))

# 490 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _68_569 -> (match (_68_569) with
| (f, deps) -> begin
(
# 492 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 496 "FStar.Parser.Dep.fst"
let print = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_68_576) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))





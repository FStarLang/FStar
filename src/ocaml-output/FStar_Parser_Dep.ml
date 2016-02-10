
open Prims
# 36 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

type map =
Prims.string FStar_Util.smap

# 38 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (let matches = (FStar_List.map (fun ext -> (let lext = (FStar_String.length ext)
in (let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _174_4 = (FStar_String.substring f 0 (l - lext))
in Some (_174_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_72_17 -> begin
Some (m)
end
| _72_22 -> begin
None
end))))

# 55 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 58 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let print_map : map  ->  Prims.unit = (fun m -> (let _174_13 = (let _174_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _174_12))
in (FStar_List.iter (fun k -> (let _174_11 = (let _174_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _174_10))
in (FStar_Util.print2 "%s: %s\n" k _174_11))) _174_13)))

# 64 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _174_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _174_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _174_18 = (let _174_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_174_17))
in (Prims.raise _174_18))
end))

# 74 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (let include_directories = (FStar_Options.get_include_path ())
in (let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (let include_directories = (FStar_List.unique include_directories)
in (let cwd = (let _174_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _174_21))
in (let map = (FStar_Util.smap_create 41)
in (let _72_52 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(let key = (FStar_String.lowercase longname)
in (let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
(let _72_46 = if ((FStar_String.lowercase existing_file) = (FStar_String.lowercase f)) then begin
(let _174_25 = (let _174_24 = (FStar_Util.format1 "I\'m case insensitive, and I found the same file twice (%s)\n" f)
in FStar_Absyn_Syntax.Err (_174_24))
in (Prims.raise _174_25))
end else begin
()
end
in (let _72_48 = if ((is_interface existing_file) = (is_interface f)) then begin
(let _174_27 = (let _174_26 = (FStar_Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)\n" f)
in FStar_Absyn_Syntax.Err (_174_26))
in (Prims.raise _174_27))
end else begin
()
end
in if (not ((is_interface existing_file))) then begin
(FStar_Util.smap_add map key full_path)
end else begin
()
end))
end
| None -> begin
(FStar_Util.smap_add map key full_path)
end)))
end
| None -> begin
()
end))) files))
end else begin
()
end) include_directories)
in (let _72_55 = (FStar_List.iter (fun f -> (let _174_29 = (lowercase_module_name f)
in (FStar_Util.smap_add map _174_29 f))) filenames)
in map))))))))

# 115 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (let found = (FStar_ST.alloc false)
in (let prefix = (Prims.strcat prefix ".")
in (let _72_67 = (let _174_39 = (let _174_38 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _174_38))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (let filename = (let _174_37 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _174_37))
in (let _72_65 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _174_39))
in (FStar_ST.read found)))))

# 130 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (let names = (let _174_45 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _174_45 suffix))
in (FStar_String.concat "." names))))

# 137 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _174_50 = (string_of_lid l last)
in (FStar_String.lowercase _174_50)))

# 141 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (let k' = (lowercase_join_longident lid true)
in if ((let _174_57 = (let _174_56 = (let _174_55 = (FStar_Util.basename filename)
in (check_and_strip_suffix _174_55))
in (FStar_Util.must _174_56))
in (FStar_String.lowercase _174_57)) <> k') then begin
(let _174_59 = (let _174_58 = (string_of_lid lid true)
in (_174_58)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _174_59))
end else begin
()
end))

# 148 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

exception Exit

# 148 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (let deps = (FStar_ST.alloc [])
in (let add_dep = (fun d -> if (not ((let _174_68 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _174_68)))) then begin
(let _174_70 = (let _174_69 = (FStar_ST.read deps)
in (d)::_174_69)
in (FStar_ST.op_Colon_Equals deps _174_70))
end else begin
()
end)
in (let working_map = (FStar_Util.smap_copy original_map)
in (let record_open = (fun lid -> (let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _174_73 = (lowercase_module_name filename)
in (add_dep _174_73))
end
| None -> begin
(let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _174_75 = (let _174_74 = (string_of_lid lid true)
in (_174_74)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _174_75))
end else begin
()
end)
end)))
in (let auto_open = (let index_of = (fun s l -> (let found = (FStar_ST.alloc (- (1)))
in (FStar_All.try_with (fun _72_98 -> (match (()) with
| () -> begin
(let _72_107 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(let _72_105 = (FStar_ST.op_Colon_Equals found i)
in (Prims.raise Exit))
end else begin
()
end) l)
in (- (1)))
end)) (fun _72_97 -> (match (_72_97) with
| Exit -> begin
(FStar_ST.read found)
end)))))
in (let ordered = ("fstar")::("prims")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.st")::("fstar.all")::[]
in (let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (let me = (let _174_86 = (let _174_85 = (let _174_84 = (FStar_Util.basename filename)
in (check_and_strip_suffix _174_84))
in (FStar_Util.must _174_85))
in (FStar_String.lowercase _174_86))
in (let index_or_length = (fun s l -> (let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _174_92 = (lowercase_join_longident lid true)
in (index_or_length _174_92 ordered)) < my_index)) desired_opens)))))))
in (let _72_119 = (FStar_List.iter record_open auto_open)
in (let rec collect_fragment = (fun _72_1 -> (match (_72_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _72_2 -> (match (_72_2) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(let _72_146 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _72_3 -> (match (_72_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(let _72_157 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _72_4 -> (match (_72_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_72_165, _72_167, patterms) -> begin
(FStar_List.iter (fun _72_174 -> (match (_72_174) with
| (_72_172, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_72_176, binders, t) -> begin
(let _72_181 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_72_204, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_72_209, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_72_214, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_72_219) -> begin
()
end))
and collect_tycon = (fun _72_5 -> (match (_72_5) with
| FStar_Parser_AST.TyconAbstract (_72_223, binders, k) -> begin
(let _72_228 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_72_231, binders, k, t) -> begin
(let _72_237 = (collect_binders binders)
in (let _72_239 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_72_242, binders, k, identterms) -> begin
(let _72_248 = (collect_binders binders)
in (let _72_250 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _72_255 -> (match (_72_255) with
| (_72_253, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_72_257, binders, k, identterms) -> begin
(let _72_263 = (collect_binders binders)
in (let _72_265 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _72_272 -> (match (_72_272) with
| (_72_268, t, _72_271) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _72_6 -> (match (_72_6) with
| FStar_Parser_AST.DefineEffect (_72_275, binders, t, decls) -> begin
(let _72_281 = (collect_binders binders)
in (let _72_283 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_72_286, binders, t) -> begin
(let _72_291 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _72_7 -> (match (_72_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _72_319 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _72_8 -> (match (_72_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_72_324) -> begin
()
end
| FStar_Parser_AST.Op (_72_327, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_72_332) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _174_124 = (lowercase_module_name filename)
in (add_dep _174_124))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _174_126 = (let _174_125 = (string_of_lid lid false)
in (_174_125)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _174_126))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_72_342, termimps) -> begin
(FStar_List.iter (fun _72_349 -> (match (_72_349) with
| (t, _72_348) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _72_354 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _72_359) -> begin
(let _72_362 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_72_365, patterms, t) -> begin
(let _72_374 = (FStar_List.iter (fun _72_373 -> (match (_72_373) with
| (_72_371, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _72_380 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _72_387 = (collect_term t1)
in (let _72_389 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(let _72_397 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _72_403 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _72_411) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(let _72_420 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(let _72_429 = (collect_binders binders)
in (let _72_431 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(let _72_437 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_72_440, t) -> begin
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
and collect_pattern' = (fun _72_9 -> (match (_72_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_72_466) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(let _72_472 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _72_495 -> (match (_72_495) with
| (_72_493, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _72_500 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _72_506 -> (match (_72_506) with
| (pat, t1, t2) -> begin
(let _72_507 = (collect_pattern pat)
in (let _72_509 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (let ast = (FStar_Parser_Driver.parse_file_raw filename)
in (let _72_512 = (collect_file ast)
in (FStar_ST.read deps)))))))))))

# 399 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

type color =
| White
| Gray
| Black

# 399 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 399 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 399 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 402 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (let graph = (FStar_Util.smap_create 41)
in (let m = (build_map filenames)
in (let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(let filename = (let _174_142 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _174_142))
in (let deps = (collect_one m filename)
in (let _72_521 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (let _72_523 = (let _174_143 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _174_143))
in (let print_graph = (fun _72_526 -> (match (()) with
| () -> begin
(let _174_152 = (let _174_151 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _174_151))
in (FStar_List.iter (fun k -> (let _174_150 = (let _174_149 = (let _174_148 = (let _174_147 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _174_147))
in (Prims.fst _174_148))
in (FStar_String.concat " " _174_149))
in (FStar_Util.print2 "%s: %s\n" k _174_150))) _174_152))
end))
in (let topologically_sorted = (FStar_ST.alloc [])
in (let rec discover = (fun key -> (let _72_533 = (let _174_155 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _174_155))
in (match (_72_533) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(let _72_535 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (let _72_537 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (let _72_539 = (print_graph ())
in (let _72_541 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(let _72_545 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (let all_deps = (let _174_159 = (let _174_158 = (FStar_List.map (fun dep -> (let _174_157 = (discover dep)
in (dep)::_174_157)) direct_deps)
in (FStar_List.flatten _174_158))
in (FStar_List.unique _174_159))
in (let _72_549 = (FStar_Util.smap_add graph key (all_deps, Black))
in (let _72_551 = (let _174_161 = (let _174_160 = (FStar_ST.read topologically_sorted)
in (key)::_174_160)
in (FStar_ST.op_Colon_Equals topologically_sorted _174_161))
in all_deps))))
end)
end)))
in (let must_find = (fun k -> (let _174_164 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _174_164)))
in (let by_target = (let _174_169 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (let deps = (let _174_166 = (discover k)
in (FStar_List.rev _174_166))
in (let _174_168 = (must_find k)
in (let _174_167 = (FStar_List.map must_find deps)
in (_174_168, _174_167))))) _174_169))
in (let topologically_sorted = (let _174_170 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _174_170))
in (by_target, topologically_sorted))))))))))))

# 473 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _72_562 -> (match (_72_562) with
| (f, deps) -> begin
(let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 479 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let print_nubuild : Prims.string Prims.list  ->  Prims.unit = (fun l -> (FStar_List.iter FStar_Util.print_endline (FStar_List.rev l)))

# 482 "C:\\Users\\nswamy\\workspace\\universes\\FStar\\src\\parser\\dep.fs"

let print : ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list)  ->  Prims.unit = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("nubuild") -> begin
(print_nubuild (Prims.snd deps))
end
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_72_572) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))





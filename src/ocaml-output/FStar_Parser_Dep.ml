
open Prims
type map =
Prims.string FStar_Util.smap

let check_and_strip_suffix = (fun f -> (let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (let matches = (FStar_List.map (fun ext -> (let lext = (FStar_String.length ext)
in (let l = (FStar_String.length f)
in if ((l > lext) && ((let _115_4 = (FStar_String.substring f (l - lext) lext)
in (FStar_Util.compare _115_4 ext)) = 0)) then begin
(let _115_5 = (FStar_String.substring f 0 (l - lext))
in Some (_115_5))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_49_17 -> begin
Some (m)
end
| _49_22 -> begin
None
end))))

let is_interface = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

let print_map = (fun m -> (let _115_13 = (FStar_Util.smap_keys m)
in (FStar_List.iter (fun k -> (let _115_12 = (let _115_11 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _115_11))
in (FStar_Util.fprint2 "%s: %s\n" k _115_12))) _115_13)))

let build_map = (fun _49_26 -> (match (()) with
| () -> begin
(let include_directories = (let _115_16 = (FStar_Util.getcwd ())
in (FStar_Options.get_include_path _115_16))
in (let map = (FStar_Util.smap_create 41)
in (let _49_44 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(let key = (FStar_String.lowercase longname)
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
(let _49_38 = if ((FStar_String.lowercase existing_file) = (FStar_String.lowercase f)) then begin
(let _115_20 = (let _115_19 = (FStar_Util.format1 "I\'m case insensitive, and I found the same file twice (%s)" f)
in FStar_Absyn_Syntax.Err (_115_19))
in (Prims.raise _115_20))
end else begin
()
end
in (let _49_40 = if ((is_interface existing_file) = (is_interface f)) then begin
(let _115_22 = (let _115_21 = (FStar_Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)" f)
in FStar_Absyn_Syntax.Err (_115_21))
in (Prims.raise _115_22))
end else begin
()
end
in if (not ((is_interface existing_file))) then begin
(FStar_Util.smap_add map key f)
end else begin
()
end))
end
| None -> begin
(FStar_Util.smap_add map key f)
end))
end
| None -> begin
()
end))) files))
end else begin
()
end) include_directories)
in map)))
end))

let enter_namespace = (fun original_map working_map prefix -> (let found = (FStar_ST.alloc false)
in (let prefix = (Prims.strcat prefix ".")
in (let _49_56 = (let _115_31 = (FStar_Util.smap_keys original_map)
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (let filename = (let _115_30 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _115_30))
in (let _49_54 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _115_31))
in (FStar_ST.read found)))))

let string_of_lid = (fun l last -> (let suffix = if last then begin
(l.FStar_Absyn_Syntax.ident.FStar_Absyn_Syntax.idText)::[]
end else begin
[]
end
in (let names = (let _115_37 = (FStar_List.map (fun x -> x.FStar_Absyn_Syntax.idText) l.FStar_Absyn_Syntax.ns)
in (FStar_List.append _115_37 suffix))
in (FStar_String.concat "." names))))

let lowercase_join_longident = (fun l last -> (let _115_42 = (string_of_lid l last)
in (FStar_String.lowercase _115_42)))

let check_module_declaration_against_filename = (fun lid filename -> (let k' = (lowercase_join_longident lid true)
in if ((let _115_49 = (let _115_48 = (let _115_47 = (FStar_Util.basename filename)
in (check_and_strip_suffix _115_47))
in (FStar_Util.must _115_48))
in (FStar_String.lowercase _115_49)) <> k') then begin
(let _115_50 = (string_of_lid lid true)
in (FStar_Util.fprint2 "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _115_50 filename))
end else begin
()
end))

let collect_one = (fun original_map filename -> (let deps = (FStar_ST.alloc [])
in (let add_dep = (fun d -> if (not ((let _115_58 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _115_58)))) then begin
(let _115_60 = (let _115_59 = (FStar_ST.read deps)
in (d)::_115_59)
in (FStar_ST.op_Colon_Equals deps _115_60))
end else begin
()
end)
in (let working_map = (FStar_Util.smap_copy original_map)
in (let record_open = (fun lid -> (let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(add_dep filename)
end
| None -> begin
(let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _115_63 = (string_of_lid lid true)
in (FStar_Util.fprint1 "Warning: no modules in namespace %s and no file with that name either\n" _115_63))
end else begin
()
end)
end)))
in (let auto_open = (let me = (let _115_65 = (let _115_64 = (check_and_strip_suffix filename)
in (FStar_Util.must _115_64))
in (FStar_String.lowercase _115_65))
in if (me = (lowercase_join_longident FStar_Absyn_Const.prims_lid true)) then begin
[]
end else begin
if (me = (lowercase_join_longident FStar_Absyn_Const.st_lid true)) then begin
(FStar_Absyn_Const.prims_lid)::[]
end else begin
if (me = (lowercase_join_longident FStar_Absyn_Const.all_lid true)) then begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::[]
end else begin
(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::(FStar_Absyn_Const.fstar_ns_lid)::[]
end
end
end)
in (let _49_84 = (FStar_List.iter record_open auto_open)
in (let rec collect_fragment = (fun _49_1 -> (match (_49_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _49_2 -> (match (_49_2) with
| modul::[] -> begin
(collect_module modul)
end
| _49_111 -> begin
(let _115_85 = (let _115_84 = (FStar_Util.format1 "File %s does not respect the one module per file convention" filename)
in FStar_Absyn_Syntax.Err (_115_84))
in (Prims.raise _115_85))
end))
and collect_module = (fun _49_3 -> (match (_49_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(let _49_121 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _49_4 -> (match (_49_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_49_129, patterms) -> begin
(FStar_List.iter (fun _49_136 -> (match (_49_136) with
| (_49_134, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_49_138, binders, t) -> begin
(let _49_143 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_49_166, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_49_171, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_49_176, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_49_181) -> begin
()
end))
and collect_tycon = (fun _49_5 -> (match (_49_5) with
| FStar_Parser_AST.TyconAbstract (_49_185, binders, k) -> begin
(let _49_190 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_49_193, binders, k, t) -> begin
(let _49_199 = (collect_binders binders)
in (let _49_201 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_49_204, binders, k, identterms) -> begin
(let _49_210 = (collect_binders binders)
in (let _49_212 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _49_217 -> (match (_49_217) with
| (_49_215, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_49_219, binders, k, identterms) -> begin
(let _49_225 = (collect_binders binders)
in (let _49_227 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _49_234 -> (match (_49_234) with
| (_49_230, t, _49_233) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _49_6 -> (match (_49_6) with
| FStar_Parser_AST.DefineEffect (_49_237, binders, t, decls) -> begin
(let _49_243 = (collect_binders binders)
in (let _49_245 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_49_248, binders, t) -> begin
(let _49_253 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _49_7 -> (match (_49_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _49_281 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _49_8 -> (match (_49_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_49_286) -> begin
()
end
| FStar_Parser_AST.Op (_49_289, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_49_294) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(add_dep filename)
end
| None -> begin
if ((FStar_List.length lid.FStar_Absyn_Syntax.ns) > 0) then begin
(let _115_99 = (string_of_lid lid false)
in (FStar_Util.fprint1 "Warning: unbound module reference %s\n" _115_99))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_49_304, termimps) -> begin
(FStar_List.iter (fun _49_311 -> (match (_49_311) with
| (t, _49_310) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _49_316 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _49_321) -> begin
(let _49_324 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_49_327, patterms, t) -> begin
(let _49_336 = (FStar_List.iter (fun _49_335 -> (match (_49_335) with
| (_49_333, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _49_342 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _49_349 = (collect_term t1)
in (let _49_351 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(let _49_359 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _49_365 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _49_373) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(let _49_382 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(let _49_391 = (collect_binders binders)
in (let _49_393 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(let _49_399 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_49_402, t) -> begin
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
and collect_pattern' = (fun _49_9 -> (match (_49_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_49_428) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(let _49_434 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _49_457 -> (match (_49_457) with
| (_49_455, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _49_462 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _49_468 -> (match (_49_468) with
| (pat, t1, t2) -> begin
(let _49_469 = (collect_pattern pat)
in (let _49_471 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (let ast = (FStar_Parser_Driver.parse_file_raw filename)
in (let _49_474 = (collect_file ast)
in (FStar_ST.read deps)))))))))))

type t =
(Prims.string * Prims.string Prims.list) Prims.list

type color =
| White
| Gray
| Black

let is_White = (fun _discr_ -> (match (_discr_) with
| White -> begin
true
end
| _ -> begin
false
end))

let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray -> begin
true
end
| _ -> begin
false
end))

let is_Black = (fun _discr_ -> (match (_discr_) with
| Black -> begin
true
end
| _ -> begin
false
end))

let collect = (fun filenames -> (let graph = (FStar_Util.smap_create 41)
in (let m = (build_map ())
in (let rec discover_one = (fun f -> (let short = (FStar_Util.basename f)
in if ((FStar_Util.smap_try_find graph short) = None) then begin
(let deps = (collect_one m f)
in (let _49_483 = (FStar_Util.smap_add graph short (deps, White))
in (FStar_List.iter discover_one deps)))
end else begin
()
end))
in (let _49_485 = (FStar_List.iter discover_one filenames)
in (let print_graph = (fun _49_488 -> (match (()) with
| () -> begin
(let _115_122 = (FStar_Util.smap_keys graph)
in (FStar_List.iter (fun k -> (let _115_121 = (let _115_120 = (let _115_119 = (let _115_118 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _115_118))
in (Prims.fst _115_119))
in (FStar_String.concat " " _115_120))
in (FStar_Util.fprint2 "%s: %s\n" k _115_121))) _115_122))
end))
in (let rec discover = (fun f -> (let short = (FStar_Util.basename f)
in (let _49_495 = (let _115_125 = (FStar_Util.smap_try_find graph short)
in (FStar_Util.must _115_125))
in (match (_49_495) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(let _49_497 = (FStar_Util.fprint1 "Recursive dependency on file %s\n" f)
in (let _49_499 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (let _49_501 = (print_graph ())
in (let _49_503 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(let _49_507 = (FStar_Util.smap_add graph short (direct_deps, Gray))
in (let transitive_deps = (let _115_126 = (FStar_List.map discover direct_deps)
in (FStar_List.flatten _115_126))
in (let all_deps = (FStar_List.unique (FStar_List.append direct_deps transitive_deps))
in (let _49_511 = (FStar_Util.smap_add graph short (all_deps, Black))
in all_deps))))
end)
end))))
in (FStar_List.map (fun f -> (let _115_128 = (discover f)
in (f, _115_128))) filenames))))))))

let print = (fun deps -> (FStar_List.iter (fun _49_517 -> (match (_49_517) with
| (f, deps) -> begin
(let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.fprint2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))





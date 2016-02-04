
open Prims
type map =
Prims.string FStar_Util.smap

let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (let matches = (FStar_List.map (fun ext -> (let lext = (FStar_String.length ext)
in (let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _176_4 = (FStar_String.substring f 0 (l - lext))
in Some (_176_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_73_17 -> begin
Some (m)
end
| _73_22 -> begin
None
end))))

let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

let print_map : map  ->  Prims.unit = (fun m -> (let _176_13 = (let _176_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _176_12))
in (FStar_List.iter (fun k -> (let _176_11 = (let _176_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _176_10))
in (FStar_Util.print2 "%s: %s\n" k _176_11))) _176_13)))

let build_map : Prims.unit  ->  map = (fun _73_26 -> (match (()) with
| () -> begin
(let include_directories = (let _176_16 = (FStar_Util.getcwd ())
in (FStar_Options.get_include_path _176_16))
in (let map = (FStar_Util.smap_create 41)
in (let _73_44 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(let key = (FStar_String.lowercase longname)
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
(let _73_38 = if ((FStar_String.lowercase existing_file) = (FStar_String.lowercase f)) then begin
(let _176_20 = (let _176_19 = (FStar_Util.format1 "I\'m case insensitive, and I found the same file twice (%s)\n" f)
in FStar_Absyn_Syntax.Err (_176_19))
in (Prims.raise _176_20))
end else begin
()
end
in (let _73_40 = if ((is_interface existing_file) = (is_interface f)) then begin
(let _176_22 = (let _176_21 = (FStar_Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)\n" f)
in FStar_Absyn_Syntax.Err (_176_21))
in (Prims.raise _176_22))
end else begin
()
end
in if (not ((is_interface existing_file))) then begin
(let _176_23 = (FStar_Util.join_paths d f)
in (FStar_Util.smap_add map key _176_23))
end else begin
()
end))
end
| None -> begin
(let _176_24 = (FStar_Util.join_paths d f)
in (FStar_Util.smap_add map key _176_24))
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

let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (let found = (FStar_ST.alloc false)
in (let prefix = (Prims.strcat prefix ".")
in (let _73_56 = (let _176_34 = (let _176_33 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _176_33))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (let filename = (let _176_32 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _176_32))
in (let _73_54 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _176_34))
in (FStar_ST.read found)))))

let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (let names = (let _176_40 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _176_40 suffix))
in (FStar_String.concat "." names))))

let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _176_45 = (string_of_lid l last)
in (FStar_String.lowercase _176_45)))

let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (let k' = (lowercase_join_longident lid true)
in if ((let _176_52 = (let _176_51 = (let _176_50 = (FStar_Util.basename filename)
in (check_and_strip_suffix _176_50))
in (FStar_Util.must _176_51))
in (FStar_String.lowercase _176_52)) <> k') then begin
(let _176_54 = (let _176_53 = (string_of_lid lid true)
in (_176_53)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _176_54))
end else begin
()
end))

exception Exit

let is_Exit : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Exit -> begin
true
end
| _ -> begin
false
end))

let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (let deps = (FStar_ST.alloc [])
in (let add_dep = (fun d -> if (not ((let _176_63 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _176_63)))) then begin
(let _176_65 = (let _176_64 = (FStar_ST.read deps)
in (d)::_176_64)
in (FStar_ST.op_Colon_Equals deps _176_65))
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
(let _176_69 = (let _176_68 = (string_of_lid lid true)
in (_176_68)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _176_69))
end else begin
()
end)
end)))
in (let auto_open = (let index_of = (fun s l -> (let found = (FStar_ST.alloc (- (1)))
in (FStar_All.try_with (fun _73_87 -> (match (()) with
| () -> begin
(let _73_96 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(let _73_94 = (FStar_ST.op_Colon_Equals found i)
in (Prims.raise Exit))
end else begin
()
end) l)
in (- (1)))
end)) (fun _73_86 -> (match (_73_86) with
| Exit -> begin
(FStar_ST.read found)
end)))))
in (let ordered = ("fstar")::("prims")::("fstar.set")::("fstar.heap")::("fstar.st")::("fstar.all")::[]
in (let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (let me = (let _176_80 = (let _176_79 = (let _176_78 = (FStar_Util.basename filename)
in (check_and_strip_suffix _176_78))
in (FStar_Util.must _176_79))
in (FStar_String.lowercase _176_80))
in (let index_or_length = (fun s l -> (let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _176_86 = (lowercase_join_longident lid true)
in (index_or_length _176_86 ordered)) < my_index)) desired_opens)))))))
in (let _73_108 = (FStar_List.iter record_open auto_open)
in (let rec collect_fragment = (fun _73_1 -> (match (_73_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _73_2 -> (match (_73_2) with
| modul::[] -> begin
(collect_module modul)
end
| _73_135 -> begin
(let _176_106 = (let _176_105 = (FStar_Util.format1 "File %s does not respect the one module per file convention" filename)
in FStar_Absyn_Syntax.Err (_176_105))
in (Prims.raise _176_106))
end))
and collect_module = (fun _73_3 -> (match (_73_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(let _73_145 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _73_4 -> (match (_73_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_73_153, _73_155, patterms) -> begin
(FStar_List.iter (fun _73_162 -> (match (_73_162) with
| (_73_160, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_73_164, binders, t) -> begin
(let _73_169 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_73_192, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_73_197, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_73_202, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_73_207) -> begin
()
end))
and collect_tycon = (fun _73_5 -> (match (_73_5) with
| FStar_Parser_AST.TyconAbstract (_73_211, binders, k) -> begin
(let _73_216 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_73_219, binders, k, t) -> begin
(let _73_225 = (collect_binders binders)
in (let _73_227 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_73_230, binders, k, identterms) -> begin
(let _73_236 = (collect_binders binders)
in (let _73_238 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _73_243 -> (match (_73_243) with
| (_73_241, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_73_245, binders, k, identterms) -> begin
(let _73_251 = (collect_binders binders)
in (let _73_253 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _73_260 -> (match (_73_260) with
| (_73_256, t, _73_259) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _73_6 -> (match (_73_6) with
| FStar_Parser_AST.DefineEffect (_73_263, binders, t, decls) -> begin
(let _73_269 = (collect_binders binders)
in (let _73_271 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_73_274, binders, t) -> begin
(let _73_279 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _73_7 -> (match (_73_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _73_307 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _73_8 -> (match (_73_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_73_312) -> begin
()
end
| FStar_Parser_AST.Op (_73_315, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_73_320) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(add_dep filename)
end
| None -> begin
if ((FStar_List.length lid.FStar_Ident.ns) > 0) then begin
(let _176_121 = (let _176_120 = (string_of_lid lid false)
in (_176_120)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _176_121))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_73_330, termimps) -> begin
(FStar_List.iter (fun _73_337 -> (match (_73_337) with
| (t, _73_336) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(let _73_342 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _73_347) -> begin
(let _73_350 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_73_353, patterms, t) -> begin
(let _73_362 = (FStar_List.iter (fun _73_361 -> (match (_73_361) with
| (_73_359, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _73_368 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _73_375 = (collect_term t1)
in (let _73_377 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(let _73_385 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(let _73_391 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _73_399) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(let _73_408 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(let _73_417 = (collect_binders binders)
in (let _73_419 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(let _73_425 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_73_428, t) -> begin
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
and collect_pattern' = (fun _73_9 -> (match (_73_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_73_454) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(let _73_460 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _73_483 -> (match (_73_483) with
| (_73_481, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(let _73_488 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _73_494 -> (match (_73_494) with
| (pat, t1, t2) -> begin
(let _73_495 = (collect_pattern pat)
in (let _73_497 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (let ast = (FStar_Parser_Driver.parse_file_raw filename)
in (let _73_500 = (collect_file ast)
in (FStar_ST.read deps)))))))))))

type t =
(Prims.string * Prims.string Prims.list) Prims.list

type color =
| White
| Gray
| Black

let is_White : color  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| White -> begin
true
end
| _ -> begin
false
end))

let is_Gray : color  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Gray -> begin
true
end
| _ -> begin
false
end))

let is_Black : color  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Black -> begin
true
end
| _ -> begin
false
end))

let collect : Prims.string Prims.list  ->  (Prims.string * Prims.string Prims.list) Prims.list = (fun filenames -> (let graph = (FStar_Util.smap_create 41)
in (let m = (build_map ())
in (let rec discover_one = (fun f -> (let short = (FStar_Util.basename f)
in if ((FStar_Util.smap_try_find graph short) = None) then begin
(let deps = (collect_one m f)
in (let _73_509 = (FStar_Util.smap_add graph short (deps, White))
in (FStar_List.iter discover_one deps)))
end else begin
()
end))
in (let _73_511 = (FStar_List.iter discover_one filenames)
in (let print_graph = (fun _73_514 -> (match (()) with
| () -> begin
(let _176_145 = (let _176_144 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _176_144))
in (FStar_List.iter (fun k -> (let _176_143 = (let _176_142 = (let _176_141 = (let _176_140 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _176_140))
in (Prims.fst _176_141))
in (FStar_String.concat " " _176_142))
in (FStar_Util.print2 "%s: %s\n" k _176_143))) _176_145))
end))
in (let rec discover = (fun f -> (let short = (FStar_Util.basename f)
in (let _73_521 = (let _176_148 = (FStar_Util.smap_try_find graph short)
in (FStar_Util.must _176_148))
in (match (_73_521) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(let _73_523 = (FStar_Util.print1 "Recursive dependency on file %s\n" f)
in (let _73_525 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (let _73_527 = (print_graph ())
in (let _73_529 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(let _73_533 = (FStar_Util.smap_add graph short (direct_deps, Gray))
in (let all_deps = (let _176_152 = (let _176_151 = (FStar_List.map (fun dep -> (let _176_150 = (discover dep)
in (dep)::_176_150)) direct_deps)
in (FStar_List.flatten _176_151))
in (FStar_List.unique _176_152))
in (let _73_537 = (FStar_Util.smap_add graph short (all_deps, Black))
in all_deps)))
end)
end))))
in (FStar_List.map (fun f -> (let _176_155 = (let _176_154 = (discover f)
in (FStar_List.rev _176_154))
in (f, _176_155))) filenames))))))))

let print_make : t  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _73_543 -> (match (_73_543) with
| (f, deps) -> begin
(let deps = (FStar_List.map (fun s -> (FStar_All.pipe_right (FStar_Util.replace_string s " " "\\ ") FStar_Util.basename)) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

let print_nubuild : t  ->  Prims.unit = (fun deps -> (let _73_549 = (FStar_List.hd (FStar_List.rev deps))
in (match (_73_549) with
| (f, deps) -> begin
(FStar_List.iter FStar_Util.print_endline deps)
end)))

let print : t  ->  Prims.unit = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("nubuild") -> begin
(print_nubuild deps)
end
| Some ("make") -> begin
(print_make deps)
end
| Some (_73_556) -> begin
(FStar_All.failwith "Unknown tool for --dep")
end
| None -> begin
()
end))





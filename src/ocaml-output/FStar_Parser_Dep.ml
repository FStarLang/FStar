
open Prims

type map =
Prims.string FStar_Util.smap


let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let matches = (FStar_List.map (fun ext -> (

let lext = (FStar_String.length ext)
in (

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


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))


let print_map : map  ->  Prims.unit = (fun m -> (let _150_13 = (let _150_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _150_12))
in (FStar_List.iter (fun k -> (let _150_11 = (let _150_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _150_10))
in (FStar_Util.print2 "%s: %s\n" k _150_11))) _150_13)))


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


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.get_include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _150_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _150_21))
in (

let map = (FStar_Util.smap_create 41)
in (

let _61_48 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (

let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(

let key = (FStar_String.lowercase longname)
in (

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

let _61_51 = (FStar_List.iter (fun f -> (let _150_27 = (lowercase_module_name f)
in (FStar_Util.smap_add map _150_27 f))) filenames)
in map))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_ST.alloc false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _61_63 = (let _150_37 = (let _150_36 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _150_36))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _150_35 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _150_35))
in (

let _61_61 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _150_37))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _150_43 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _150_43 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _150_48 = (string_of_lid l last)
in (FStar_String.lowercase _150_48)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

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


exception Exit


let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))


let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (

let deps = (FStar_ST.alloc [])
in (

let add_dep = (fun d -> if (not ((let _150_66 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _150_66)))) then begin
(let _150_68 = (let _150_67 = (FStar_ST.read deps)
in (d)::_150_67)
in (FStar_ST.op_Colon_Equals deps _150_68))
end else begin
()
end)
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun lid -> (

let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _150_71 = (lowercase_module_name filename)
in (add_dep _150_71))
end
| None -> begin
(

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

let auto_open = (

let index_of = (fun s l -> (

let found = (FStar_ST.alloc (- (1)))
in try
(match (()) with
| () -> begin
(

let _61_103 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(

let _61_101 = (FStar_ST.op_Colon_Equals found i)
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

let ordered = ("fstar")::("prims")::("fstar.list.tot")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.map")::("fstar.hyperheap")::("fstar.st")::("fstar.all")::[]
in (

let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (

let me = (let _150_84 = (let _150_83 = (let _150_82 = (FStar_Util.basename filename)
in (check_and_strip_suffix _150_82))
in (FStar_Util.must _150_83))
in (FStar_String.lowercase _150_84))
in (

let index_or_length = (fun s l -> (

let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (

let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _150_90 = (lowercase_join_longident lid true)
in (index_or_length _150_90 ordered)) < my_index)) desired_opens)))))))
in (

let _61_115 = (FStar_List.iter record_open auto_open)
in (

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

let _61_142 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _61_3 -> (match (_61_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _61_153 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _61_4 -> (match (_61_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_61_161, _61_163, patterms) -> begin
(FStar_List.iter (fun _61_170 -> (match (_61_170) with
| (_61_168, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_61_172, binders, t) -> begin
(

let _61_177 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_61_200, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_61_205, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_61_210, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_61_215) -> begin
()
end))
and collect_tycon = (fun _61_5 -> (match (_61_5) with
| FStar_Parser_AST.TyconAbstract (_61_219, binders, k) -> begin
(

let _61_224 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_61_227, binders, k, t) -> begin
(

let _61_233 = (collect_binders binders)
in (

let _61_235 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_61_238, binders, k, identterms) -> begin
(

let _61_244 = (collect_binders binders)
in (

let _61_246 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _61_251 -> (match (_61_251) with
| (_61_249, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_61_253, binders, k, identterms) -> begin
(

let _61_259 = (collect_binders binders)
in (

let _61_261 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _61_268 -> (match (_61_268) with
| (_61_264, t, _61_267) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _61_6 -> (match (_61_6) with
| FStar_Parser_AST.DefineEffect (_61_271, binders, t, decls) -> begin
(

let _61_277 = (collect_binders binders)
in (

let _61_279 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_61_282, binders, t) -> begin
(

let _61_287 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _61_7 -> (match (_61_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _61_315 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _61_8 -> (match (_61_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_61_320) -> begin
()
end
| FStar_Parser_AST.Op (_61_323, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_61_328) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(

let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _150_122 = (lowercase_module_name filename)
in (add_dep _150_122))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _150_124 = (let _150_123 = (string_of_lid lid false)
in (_150_123)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _150_124))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_61_338, termimps) -> begin
(FStar_List.iter (fun _61_345 -> (match (_61_345) with
| (t, _61_344) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _61_350 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _61_355) -> begin
(

let _61_358 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_61_361, patterms, t) -> begin
(

let _61_370 = (FStar_List.iter (fun _61_369 -> (match (_61_369) with
| (_61_367, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _61_376 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _61_383 = (collect_term t1)
in (

let _61_385 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _61_393 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _61_399 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _61_407) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _61_416 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _61_425 = (collect_binders binders)
in (

let _61_427 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _61_433 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_61_436, t) -> begin
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
| FStar_Parser_AST.PatConst (_61_462) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _61_468 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _61_491 -> (match (_61_491) with
| (_61_489, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _61_496 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _61_502 -> (match (_61_502) with
| (pat, t1, t2) -> begin
(

let _61_503 = (collect_pattern pat)
in (

let _61_505 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let ast = (FStar_Parser_Driver.parse_file filename)
in (

let _61_508 = (collect_file ast)
in (FStar_ST.read deps)))))))))))


type color =
| White
| Gray
| Black


let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))


let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))


let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))


let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (

let graph = (FStar_Util.smap_create 41)
in (

let m = (build_map filenames)
in (

let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let filename = (let _150_140 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _150_140))
in (

let deps = (collect_one m filename)
in (

let _61_517 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (

let _61_519 = (let _150_141 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _150_141))
in (

let print_graph = (fun _61_522 -> (match (()) with
| () -> begin
(let _150_150 = (let _150_149 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _150_149))
in (FStar_List.iter (fun k -> (let _150_148 = (let _150_147 = (let _150_146 = (let _150_145 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _150_145))
in (Prims.fst _150_146))
in (FStar_String.concat " " _150_147))
in (FStar_Util.print2 "%s: %s\n" k _150_148))) _150_150))
end))
in (

let topologically_sorted = (FStar_ST.alloc [])
in (

let rec discover = (fun key -> (

let _61_529 = (let _150_153 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _150_153))
in (match (_61_529) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(

let _61_531 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (

let _61_533 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (

let _61_535 = (print_graph ())
in (

let _61_537 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(

let _61_541 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (

let all_deps = (let _150_157 = (let _150_156 = (FStar_List.map (fun dep -> (let _150_155 = (discover dep)
in (dep)::_150_155)) direct_deps)
in (FStar_List.flatten _150_156))
in (FStar_List.unique _150_157))
in (

let _61_545 = (FStar_Util.smap_add graph key (all_deps, Black))
in (

let _61_547 = (let _150_159 = (let _150_158 = (FStar_ST.read topologically_sorted)
in (key)::_150_158)
in (FStar_ST.op_Colon_Equals topologically_sorted _150_159))
in all_deps))))
end)
end)))
in (

let must_find = (fun k -> (let _150_162 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _150_162)))
in (

let by_target = (let _150_167 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (

let deps = (let _150_164 = (discover k)
in (FStar_List.rev _150_164))
in (let _150_166 = (must_find k)
in (let _150_165 = (FStar_List.map must_find deps)
in (_150_166, _150_165))))) _150_167))
in (

let topologically_sorted = (let _150_168 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _150_168))
in (by_target, topologically_sorted))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _61_558 -> (match (_61_558) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print_nubuild : Prims.string Prims.list  ->  Prims.unit = (fun l -> (FStar_List.iter FStar_Util.print_endline (FStar_List.rev l)))


let print : ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list)  ->  Prims.unit = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("nubuild") -> begin
(print_nubuild (Prims.snd deps))
end
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_61_568) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))





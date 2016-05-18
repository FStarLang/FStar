
open Prims

type map =
(Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap


let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let matches = (FStar_List.map (fun ext -> (

let lext = (FStar_String.length ext)
in (

let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _157_4 = (FStar_String.substring f 0 (l - lext))
in Some (_157_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_68_18 -> begin
Some (m)
end
| _68_23 -> begin
None
end))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))


let list_of_option = (fun _68_1 -> (match (_68_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun _68_32 -> (match (_68_32) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let must_find_stratified = (fun m k -> (match ((let _157_13 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _157_13))) with
| (Some (intf), _68_38) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))


let must_find_universes = (fun m k -> (let _157_17 = (let _157_16 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _157_16))
in (list_of_pair _157_17)))


let must_find = (fun m k -> if (FStar_Options.universes ()) then begin
(must_find_universes m k)
end else begin
(must_find_stratified m k)
end)


let print_map : map  ->  Prims.unit = (fun m -> (let _157_26 = (let _157_25 = (FStar_Util.smap_keys m)
in (FStar_List.unique _157_25))
in (FStar_List.iter (fun k -> (let _157_24 = (must_find m k)
in (FStar_List.iter (fun f -> (FStar_Util.print2 "%s: %s\n" k f)) _157_24))) _157_26)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _157_29 = (FStar_Util.basename f)
in (check_and_strip_suffix _157_29))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _157_31 = (let _157_30 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_157_30))
in (Prims.raise _157_31))
end))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _157_34 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _157_34))
in (

let map = (FStar_Util.smap_create 41)
in (

let add_entry = (fun key full_path -> (match ((FStar_Util.smap_try_find map key)) with
| Some (intf, impl) -> begin
if (is_interface full_path) then begin
(FStar_Util.smap_add map key (Some (full_path), impl))
end else begin
(FStar_Util.smap_add map key (intf, Some (full_path)))
end
end
| None -> begin
if (is_interface full_path) then begin
(FStar_Util.smap_add map key (Some (full_path), None))
end else begin
(FStar_Util.smap_add map key (None, Some (full_path)))
end
end))
in (

let _68_81 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (

let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(

let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (

let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| None -> begin
()
end))) files))
end else begin
(let _157_42 = (let _157_41 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_157_41))
in (Prims.raise _157_42))
end) include_directories)
in (

let _68_84 = (FStar_List.iter (fun f -> (let _157_44 = (lowercase_module_name f)
in (add_entry _157_44 f))) filenames)
in map)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_ST.alloc false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _68_96 = (let _157_54 = (let _157_53 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _157_53))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _157_52 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _157_52))
in (

let _68_94 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _157_54))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _157_60 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _157_60 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _157_65 = (string_of_lid l last)
in (FStar_String.lowercase _157_65)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in if ((let _157_72 = (let _157_71 = (let _157_70 = (FStar_Util.basename filename)
in (check_and_strip_suffix _157_70))
in (FStar_Util.must _157_71))
in (FStar_String.lowercase _157_72)) <> k') then begin
(let _157_74 = (let _157_73 = (string_of_lid lid true)
in (_157_73)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _157_74))
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


let collect_one : map  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (

let deps = (FStar_ST.alloc [])
in (

let add_dep = (fun d -> if (not ((let _157_83 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _157_83)))) then begin
(let _157_85 = (let _157_84 = (FStar_ST.read deps)
in (d)::_157_84)
in (FStar_ST.op_Colon_Equals deps _157_85))
end else begin
()
end)
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun lid -> (

let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _157_89 = (lowercase_module_name f)
in (add_dep _157_89))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _157_91 = (let _157_90 = (string_of_lid lid true)
in (_157_90)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _157_91))
end else begin
()
end)
end)))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let deps_of_aliased_module = (let _157_96 = (FStar_Util.smap_try_find working_map alias)
in (FStar_Util.must _157_96))
in (FStar_Util.smap_add working_map key deps_of_aliased_module)))))
in (

let auto_open = (

let index_of = (fun s l -> (

let found = (FStar_ST.alloc (- (1)))
in try
(match (()) with
| () -> begin
(

let _68_143 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(

let _68_141 = (FStar_ST.op_Colon_Equals found i)
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

let me = (let _157_107 = (let _157_106 = (let _157_105 = (FStar_Util.basename filename)
in (check_and_strip_suffix _157_105))
in (FStar_Util.must _157_106))
in (FStar_String.lowercase _157_107))
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
in (FStar_List.filter (fun lid -> ((let _157_113 = (lowercase_join_longident lid true)
in (index_or_length _157_113 ordered)) < my_index)) desired_opens)))))))
in (

let _68_155 = (FStar_List.iter record_open auto_open)
in (

let rec collect_fragment = (fun _68_2 -> (match (_68_2) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _68_3 -> (match (_68_3) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(

let _68_182 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _68_4 -> (match (_68_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _68_193 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _68_5 -> (match (_68_5) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(record_module_alias ident lid)
end
| FStar_Parser_AST.ToplevelLet (_68_205, _68_207, patterms) -> begin
(FStar_List.iter (fun _68_214 -> (match (_68_214) with
| (_68_212, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_68_216, binders, t) -> begin
(

let _68_221 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_68_244, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_68_249, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (ed)) | (FStar_Parser_AST.NewEffect (_, ed)) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_68_260) -> begin
()
end))
and collect_tycon = (fun _68_6 -> (match (_68_6) with
| FStar_Parser_AST.TyconAbstract (_68_264, binders, k) -> begin
(

let _68_269 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_68_272, binders, k, t) -> begin
(

let _68_278 = (collect_binders binders)
in (

let _68_280 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_68_283, binders, k, identterms) -> begin
(

let _68_289 = (collect_binders binders)
in (

let _68_291 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _68_296 -> (match (_68_296) with
| (_68_294, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_68_298, binders, k, identterms) -> begin
(

let _68_304 = (collect_binders binders)
in (

let _68_306 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _68_313 -> (match (_68_313) with
| (_68_309, t, _68_312) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _68_7 -> (match (_68_7) with
| FStar_Parser_AST.DefineEffect (_68_316, binders, t, decls) -> begin
(

let _68_322 = (collect_binders binders)
in (

let _68_324 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_68_327, binders, t) -> begin
(

let _68_332 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _68_8 -> (match (_68_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _68_360 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _68_9 -> (match (_68_9) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_68_365) -> begin
()
end
| FStar_Parser_AST.Op (_68_368, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_68_373) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(

let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _157_146 = (lowercase_module_name f)
in (add_dep _157_146))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && (FStar_Options.debug_any ())) then begin
(let _157_148 = (let _157_147 = (string_of_lid lid false)
in (_157_147)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _157_148))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_68_384, termimps) -> begin
(FStar_List.iter (fun _68_391 -> (match (_68_391) with
| (t, _68_390) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _68_396 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _68_401) -> begin
(

let _68_404 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_68_407, patterms, t) -> begin
(

let _68_416 = (FStar_List.iter (fun _68_415 -> (match (_68_415) with
| (_68_413, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _68_422 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _68_429 = (collect_term t1)
in (

let _68_431 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _68_439 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _68_445 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(

let _68_451 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _68_456 -> (match (_68_456) with
| (_68_454, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _68_459) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _68_468 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _68_477 = (collect_binders binders)
in (

let _68_479 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _68_485 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_68_488, t) -> begin
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
and collect_pattern' = (fun _68_10 -> (match (_68_10) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_68_514) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _68_520 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _68_543 -> (match (_68_543) with
| (_68_541, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _68_548 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _68_554 -> (match (_68_554) with
| (pat, t1, t2) -> begin
(

let _68_555 = (collect_pattern pat)
in (

let _68_557 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let ast = (FStar_Parser_Driver.parse_file filename)
in (

let _68_560 = (collect_file ast)
in (FStar_ST.read deps))))))))))))


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


let print_graph = (fun graph -> (

let _68_563 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (

let _68_565 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (

let _68_567 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _157_173 = (let _157_172 = (let _157_171 = (let _157_170 = (let _157_169 = (let _157_168 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _157_168))
in (FStar_List.map_flatten (fun k -> (

let deps = (let _157_164 = (let _157_163 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _157_163))
in (Prims.fst _157_164))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _157_169))
in (FStar_String.concat "\n" _157_170))
in (Prims.strcat "digraph {\n" _157_171))
in (Prims.strcat _157_172 "\n}\n"))
in (FStar_Util.write_file "dep.graph" _157_173))))))


let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun filenames -> (

let graph = (FStar_Util.smap_create 41)
in (

let m = (build_map filenames)
in (

let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let _68_581 = (let _157_178 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _157_178))
in (match (_68_581) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| None -> begin
[]
end
| Some (intf) -> begin
(collect_one m intf)
end)
in (

let impl_deps = (match (impl) with
| None -> begin
[]
end
| Some (impl) -> begin
(collect_one m impl)
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (

let _68_591 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps)))))
end))
end else begin
()
end)
in (

let _68_593 = (let _157_179 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _157_179))
in (

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_ST.alloc [])
in (

let rec discover = (fun cycle key -> (

let _68_602 = (let _157_184 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _157_184))
in (match (_68_602) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(

let _68_604 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (

let _68_606 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (

let _68_608 = (print_graph immediate_graph)
in (

let _68_610 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(

let _68_614 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (

let all_deps = (let _157_188 = (let _157_187 = (FStar_List.map (fun dep -> (let _157_186 = (discover ((key)::cycle) dep)
in (dep)::_157_186)) direct_deps)
in (FStar_List.flatten _157_187))
in (FStar_List.unique _157_188))
in (

let _68_618 = (FStar_Util.smap_add graph key (all_deps, Black))
in (

let _68_620 = (let _157_190 = (let _157_189 = (FStar_ST.read topologically_sorted)
in (key)::_157_189)
in (FStar_ST.op_Colon_Equals topologically_sorted _157_190))
in all_deps))))
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (must_find m)
in (

let must_find_r = (fun f -> (let _157_195 = (must_find f)
in (FStar_List.rev _157_195)))
in (

let by_target = (let _157_200 = (FStar_Util.smap_keys graph)
in (FStar_List.map_flatten (fun k -> (

let as_list = (must_find k)
in (

let is_interleaved = ((FStar_List.length as_list) = 2)
in (FStar_List.map (fun f -> (

let should_append_fsti = ((is_implementation f) && is_interleaved)
in (

let suffix = if should_append_fsti then begin
((Prims.strcat f "i"))::[]
end else begin
[]
end
in (

let k = (lowercase_module_name f)
in (

let deps = (let _157_198 = (discover k)
in (FStar_List.rev _157_198))
in (

let deps_as_filenames = (let _157_199 = (FStar_List.map_flatten must_find deps)
in (FStar_List.append _157_199 suffix))
in (f, deps_as_filenames))))))) as_list)))) _157_200))
in (

let topologically_sorted = (let _157_201 = (FStar_ST.read topologically_sorted)
in (FStar_List.map_flatten must_find_r _157_201))
in (by_target, topologically_sorted, immediate_graph))))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _68_640 -> (match (_68_640) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun _68_647 -> (match (_68_647) with
| (make_deps, _68_645, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_68_653) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





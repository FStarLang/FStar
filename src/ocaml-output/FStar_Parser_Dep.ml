
open Prims

type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut


let is_VerifyAll = (fun _discr_ -> (match (_discr_) with
| VerifyAll (_) -> begin
true
end
| _ -> begin
false
end))


let is_VerifyUserList = (fun _discr_ -> (match (_discr_) with
| VerifyUserList (_) -> begin
true
end
| _ -> begin
false
end))


let is_VerifyFigureItOut = (fun _discr_ -> (match (_discr_) with
| VerifyFigureItOut (_) -> begin
true
end
| _ -> begin
false
end))


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
(let _171_7 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in Some (_171_7))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| (Some (m))::_73_19 -> begin
Some (m)
end
| _73_24 -> begin
None
end))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))) = 'i'))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))


let list_of_option = (fun _73_1 -> (match (_73_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun _73_33 -> (match (_73_33) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let must_find_stratified = (fun m k -> (match ((let _171_16 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _171_16))) with
| (Some (intf), _73_39) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))


let must_find_universes = (fun m k -> (let _171_20 = (let _171_19 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _171_19))
in (list_of_pair _171_20)))


let must_find = (fun m k -> if (FStar_Options.universes ()) then begin
(must_find_universes m k)
end else begin
(must_find_stratified m k)
end)


let print_map : map  ->  Prims.unit = (fun m -> (let _171_29 = (let _171_28 = (FStar_Util.smap_keys m)
in (FStar_List.unique _171_28))
in (FStar_List.iter (fun k -> (let _171_27 = (must_find m k)
in (FStar_List.iter (fun f -> (FStar_Util.print2 "%s: %s\n" k f)) _171_27))) _171_29)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _171_32 = (FStar_Util.basename f)
in (check_and_strip_suffix _171_32))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _171_34 = (let _171_33 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_171_33))
in (Prims.raise _171_34))
end))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _171_37 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _171_37))
in (

let map = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (match ((FStar_Util.smap_try_find map key)) with
| Some (intf, impl) -> begin
if (is_interface full_path) then begin
(FStar_Util.smap_add map key ((Some (full_path)), (impl)))
end else begin
(FStar_Util.smap_add map key ((intf), (Some (full_path))))
end
end
| None -> begin
if (is_interface full_path) then begin
(FStar_Util.smap_add map key ((Some (full_path)), (None)))
end else begin
(FStar_Util.smap_add map key ((None), (Some (full_path))))
end
end))
in (

let _73_82 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
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
(let _171_45 = (let _171_44 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_171_44))
in (Prims.raise _171_45))
end) include_directories)
in (

let _73_85 = (FStar_List.iter (fun f -> (let _171_47 = (lowercase_module_name f)
in (add_entry _171_47 f))) filenames)
in map)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_ST.alloc false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _73_97 = (let _171_57 = (let _171_56 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _171_56))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _171_55 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _171_55))
in (

let _73_95 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _171_57))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _171_63 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _171_63 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _171_68 = (string_of_lid l last)
in (FStar_String.lowercase _171_68)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in if ((let _171_75 = (let _171_74 = (let _171_73 = (FStar_Util.basename filename)
in (check_and_strip_suffix _171_73))
in (FStar_Util.must _171_74))
in (FStar_String.lowercase _171_75)) <> k') then begin
(let _171_77 = (let _171_76 = (string_of_lid lid true)
in (_171_76)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _171_77))
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


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_ST.alloc [])
in (

let add_dep = (fun d -> if (not ((let _171_92 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _171_92)))) then begin
(let _171_94 = (let _171_93 = (FStar_ST.read deps)
in (d)::_171_93)
in (FStar_ST.op_Colon_Equals deps _171_94))
end else begin
()
end)
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _171_100 = (lowercase_module_name f)
in (add_dep _171_100))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Absyn_Syntax.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _171_102 = (let _171_101 = (string_of_lid lid true)
in (_171_101)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _171_102))
end
end else begin
()
end)
end)))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map alias)) with
| Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| None -> begin
(let _171_108 = (let _171_107 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Absyn_Syntax.Err (_171_107))
in (Prims.raise _171_108))
end))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _171_114 = (lowercase_module_name f)
in (add_dep _171_114))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ())) then begin
(let _171_116 = (let _171_115 = (string_of_lid lid false)
in (_171_115)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _171_116))
end else begin
()
end
end))
in (

let _73_144 = (let _171_117 = (lowercase_join_longident lid false)
in (try_key _171_117))
in ())))
in (

let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _171_119 = (let _171_118 = (FStar_Util.basename filename)
in (FStar_String.lowercase _171_118))
in (FStar_Util.starts_with _171_119 "fstar.")) then begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::[]
end else begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
end
end
in (

let _73_147 = (FStar_List.iter (record_open false) auto_open)
in (

let num_of_toplevelmods = (FStar_ST.alloc (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun _73_2 -> (match (_73_2) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _73_3 -> (match (_73_3) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
(

let _73_176 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _73_4 -> (match (_73_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _73_187 = (check_module_declaration_against_filename lid filename)
in (

let _73_195 = (match (verify_mode) with
| VerifyAll -> begin
(let _171_140 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _171_140))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _171_141 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _171_141))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _73_194 -> (match (_73_194) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _171_143 = (string_of_lid lid true)
in (FStar_String.lowercase _171_143))) then begin
(FStar_ST.op_Colon_Equals r true)
end else begin
()
end
end)) verify_flags)
end)
in (collect_decls decls)))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (

let _73_199 = (collect_decl x.FStar_Parser_AST.d)
in (FStar_List.iter collect_term x.FStar_Parser_AST.attrs))) decls))
and collect_decl = (fun _73_5 -> (match (_73_5) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let _73_208 = (let _171_147 = (lowercase_join_longident lid true)
in (add_dep _171_147))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.TopLevelLet (_73_211, patterms) -> begin
(FStar_List.iter (fun _73_217 -> (match (_73_217) with
| (pat, t) -> begin
(

let _73_218 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_73_221, binders, t) -> begin
(

let _73_226 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)})) | (FStar_Parser_AST.Val (_, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _73_259; FStar_Parser_AST.mdest = _73_257; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(

let _73_262 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_73_265, ts) -> begin
(

let ts = (FStar_List.map (fun _73_271 -> (match (_73_271) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (_73_274, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (ed)) | (FStar_Parser_AST.NewEffect (ed)) -> begin
(collect_effect_decl ed)
end
| (FStar_Parser_AST.Fsdoc (_)) | (FStar_Parser_AST.Pragma (_)) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
(

let _73_289 = (FStar_Util.incr num_of_toplevelmods)
in if ((FStar_ST.read num_of_toplevelmods) > (Prims.parse_int "1")) then begin
(let _171_152 = (let _171_151 = (let _171_150 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" _171_150))
in FStar_Absyn_Syntax.Err (_171_151))
in (Prims.raise _171_152))
end else begin
()
end)
end))
and collect_tycon = (fun _73_6 -> (match (_73_6) with
| FStar_Parser_AST.TyconAbstract (_73_293, binders, k) -> begin
(

let _73_298 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_73_301, binders, k, t) -> begin
(

let _73_307 = (collect_binders binders)
in (

let _73_309 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_73_312, binders, k, identterms) -> begin
(

let _73_318 = (collect_binders binders)
in (

let _73_320 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _73_327 -> (match (_73_327) with
| (_73_323, t, _73_326) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_73_329, binders, k, identterms) -> begin
(

let _73_335 = (collect_binders binders)
in (

let _73_337 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _73_346 -> (match (_73_346) with
| (_73_340, t, _73_343, _73_345) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _73_7 -> (match (_73_7) with
| FStar_Parser_AST.DefineEffect (_73_349, binders, t, decls, actions) -> begin
(

let _73_356 = (collect_binders binders)
in (

let _73_358 = (collect_term t)
in (

let _73_360 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_73_363, binders, t) -> begin
(

let _73_368 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _73_8 -> (match (_73_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _73_404 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun _73_9 -> (match (_73_9) with
| FStar_Const.Const_int (_73_408, Some (signedness, width)) -> begin
(

let u = (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)
in (

let w = (match (width) with
| FStar_Const.Int8 -> begin
"8"
end
| FStar_Const.Int16 -> begin
"16"
end
| FStar_Const.Int32 -> begin
"32"
end
| FStar_Const.Int64 -> begin
"64"
end)
in (let _171_161 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _171_161))))
end
| _73_424 -> begin
()
end))
and collect_term' = (fun _73_10 -> (match (_73_10) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
(

let _73_433 = if (s = "@") then begin
(let _171_164 = (let _171_163 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_171_163))
in (collect_term' _171_164))
end else begin
()
end
in (FStar_List.iter collect_term ts))
end
| (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Projector (lid, _)) | (FStar_Parser_AST.Discrim (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
(

let _73_453 = if (((FStar_List.length termimps) = (Prims.parse_int "1")) && (FStar_Options.universes ())) then begin
(record_lid lid)
end else begin
()
end
in (FStar_List.iter (fun _73_458 -> (match (_73_458) with
| (t, _73_457) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _73_463 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _73_468) -> begin
(

let _73_471 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_73_474, patterms, t) -> begin
(

let _73_484 = (FStar_List.iter (fun _73_481 -> (match (_73_481) with
| (pat, t) -> begin
(

let _73_482 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(

let _73_490 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _73_496 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _73_503 = (collect_term t1)
in (

let _73_505 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _73_513 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _73_519 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(

let _73_525 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _73_530 -> (match (_73_530) with
| (_73_528, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _73_533) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _73_542 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _73_551 = (collect_binders binders)
in (

let _73_553 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _73_559 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_73_562, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun _73_11 -> (match (_73_11) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _73_603 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _73_626 -> (match (_73_626) with
| (_73_624, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _73_631 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _73_637 -> (match (_73_637) with
| (pat, t1, t2) -> begin
(

let _73_638 = (collect_pattern pat)
in (

let _73_640 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let ast = (FStar_Parser_Driver.parse_file filename)
in (

let _73_643 = (collect_file ast)
in (FStar_ST.read deps))))))))))))))


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

let _73_646 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (

let _73_648 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (

let _73_650 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _171_189 = (let _171_188 = (let _171_187 = (let _171_186 = (let _171_185 = (let _171_184 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _171_184))
in (FStar_List.collect (fun k -> (

let deps = (let _171_180 = (let _171_179 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _171_179))
in (Prims.fst _171_180))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _171_185))
in (FStar_String.concat "\n" _171_186))
in (Prims.strcat _171_187 "\n}\n"))
in (Prims.strcat "digraph {\n" _171_188))
in (FStar_Util.write_file "dep.graph" _171_189))))))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (let _171_196 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _171_195 = (FStar_ST.alloc false)
in ((f), (_171_195)))) _171_196))
in (

let m = (build_map filenames)
in (

let collect_one = (collect_one verify_flags verify_mode)
in (

let rec discover_one = (fun is_user_provided_filename key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let _73_669 = (let _171_204 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _171_204))
in (match (_73_669) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| None -> begin
[]
end
| Some (intf) -> begin
(collect_one is_user_provided_filename m intf)
end)
in (

let impl_deps = (match (impl) with
| None -> begin
[]
end
| Some (impl) -> begin
(collect_one is_user_provided_filename m impl)
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (

let _73_679 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one false) deps)))))
end))
end else begin
()
end)
in (

let _73_681 = (let _171_205 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter (discover_one true) _171_205))
in (

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_ST.alloc [])
in (

let rec discover = (fun cycle key -> (

let _73_690 = (let _171_210 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _171_210))
in (match (_73_690) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(

let _73_692 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (

let _73_694 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (

let _73_696 = (print_graph immediate_graph)
in (

let _73_698 = (FStar_Util.print_string "\n")
in (FStar_All.exit (Prims.parse_int "1"))))))
end
| Black -> begin
direct_deps
end
| White -> begin
(

let _73_702 = (FStar_Util.smap_add graph key ((direct_deps), (Gray)))
in (

let all_deps = (let _171_214 = (let _171_213 = (FStar_List.map (fun dep -> (let _171_212 = (discover ((key)::cycle) dep)
in (dep)::_171_212)) direct_deps)
in (FStar_List.flatten _171_213))
in (FStar_List.unique _171_214))
in (

let _73_706 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (

let _73_708 = (let _171_216 = (let _171_215 = (FStar_ST.read topologically_sorted)
in (key)::_171_215)
in (FStar_ST.op_Colon_Equals topologically_sorted _171_216))
in all_deps))))
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (must_find m)
in (

let must_find_r = (fun f -> (let _171_221 = (must_find f)
in (FStar_List.rev _171_221)))
in (

let by_target = (let _171_226 = (FStar_Util.smap_keys graph)
in (FStar_List.collect (fun k -> (

let as_list = (must_find k)
in (

let is_interleaved = ((FStar_List.length as_list) = (Prims.parse_int "2"))
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

let deps = (let _171_224 = (discover k)
in (FStar_List.rev _171_224))
in (

let deps_as_filenames = (let _171_225 = (FStar_List.collect must_find deps)
in (FStar_List.append _171_225 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _171_226))
in (

let topologically_sorted = (let _171_227 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _171_227))
in (

let _73_728 = (FStar_List.iter (fun _73_727 -> (match (_73_727) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(let _171_230 = (let _171_229 = (FStar_Util.format2 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph\n" m m)
in FStar_Absyn_Syntax.Err (_171_229))
in (Prims.raise _171_230))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _73_733 -> (match (_73_733) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun _73_740 -> (match (_73_740) with
| (make_deps, _73_738, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_73_746) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





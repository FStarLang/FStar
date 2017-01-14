
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


let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let matches = (FStar_List.map (fun ext -> (

let lext = (FStar_String.length ext)
in (

let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _171_10 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in Some (_171_10))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| (Some (m))::_70_10 -> begin
Some (m)
end
| _70_15 -> begin
None
end))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))) = 'i'))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))


let list_of_option = (fun uu___382 -> (match (uu___382) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun _70_24 -> (match (_70_24) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _171_19 = (FStar_Util.basename f)
in (check_and_strip_suffix _171_19))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _171_21 = (let _171_20 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Errors.Err (_171_20))
in (Prims.raise _171_21))
end))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _171_24 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _171_24))
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

let _70_52 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
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
(let _171_32 = (let _171_31 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (_171_31))
in (Prims.raise _171_32))
end) include_directories)
in (

let _70_55 = (FStar_List.iter (fun f -> (let _171_34 = (lowercase_module_name f)
in (add_entry _171_34 f))) filenames)
in map)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _70_67 = (let _171_44 = (let _171_43 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _171_43))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _171_42 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _171_42))
in (

let _70_65 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _171_44))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _171_50 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _171_50 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _171_55 = (string_of_lid l last)
in (FStar_String.lowercase _171_55)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in if ((let _171_62 = (let _171_61 = (let _171_60 = (FStar_Util.basename filename)
in (check_and_strip_suffix _171_60))
in (FStar_Util.must _171_61))
in (FStar_String.lowercase _171_62)) <> k') then begin
(let _171_64 = (let _171_63 = (string_of_lid lid true)
in (_171_63)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _171_64))
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

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> if (not ((let _171_79 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _171_79)))) then begin
(let _171_81 = (let _171_80 = (FStar_ST.read deps)
in (d)::_171_80)
in (FStar_ST.op_Colon_Equals deps _171_81))
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
(FStar_List.iter (fun f -> (let _171_87 = (lowercase_module_name f)
in (add_dep _171_87))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Errors.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _171_89 = (let _171_88 = (string_of_lid lid true)
in (_171_88)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _171_89))
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
(let _171_95 = (let _171_94 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (_171_94))
in (Prims.raise _171_95))
end))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _171_101 = (lowercase_module_name f)
in (add_dep _171_101))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ())) then begin
(let _171_103 = (let _171_102 = (string_of_lid lid false)
in (_171_102)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _171_103))
end else begin
()
end
end))
in (

let _70_114 = (let _171_104 = (lowercase_join_longident lid false)
in (try_key _171_104))
in ())))
in (

let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _171_106 = (let _171_105 = (FStar_Util.basename filename)
in (FStar_String.lowercase _171_105))
in (FStar_Util.starts_with _171_106 "fstar.")) then begin
(FStar_Syntax_Const.fstar_ns_lid)::(FStar_Syntax_Const.prims_lid)::[]
end else begin
(FStar_Syntax_Const.fstar_ns_lid)::(FStar_Syntax_Const.prims_lid)::(FStar_Syntax_Const.st_lid)::(FStar_Syntax_Const.all_lid)::[]
end
end
in (

let _70_117 = (FStar_List.iter (record_open false) auto_open)
in (

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun uu___383 -> (match (uu___383) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun uu___384 -> (match (uu___384) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
(

let _70_146 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun uu___385 -> (match (uu___385) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _70_157 = (check_module_declaration_against_filename lid filename)
in (

let _70_165 = (match (verify_mode) with
| VerifyAll -> begin
(let _171_127 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _171_127))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _171_128 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _171_128))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _70_164 -> (match (_70_164) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _171_130 = (string_of_lid lid true)
in (FStar_String.lowercase _171_130))) then begin
(FStar_ST.op_Colon_Equals r true)
end else begin
()
end
end)) verify_flags)
end)
in (collect_decls decls)))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (

let _70_169 = (collect_decl x.FStar_Parser_AST.d)
in (FStar_List.iter collect_term x.FStar_Parser_AST.attrs))) decls))
and collect_decl = (fun uu___386 -> (match (uu___386) with
| (FStar_Parser_AST.Include (lid)) | (FStar_Parser_AST.Open (lid)) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let _70_179 = (let _171_134 = (lowercase_join_longident lid true)
in (add_dep _171_134))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.TopLevelLet (_70_182, patterms) -> begin
(FStar_List.iter (fun _70_188 -> (match (_70_188) with
| (pat, t) -> begin
(

let _70_189 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_70_192, binders, t) -> begin
(

let _70_197 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)})) | (FStar_Parser_AST.Val (_, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _70_230; FStar_Parser_AST.mdest = _70_228; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(

let _70_233 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_70_236, ts) -> begin
(

let ts = (FStar_List.map (fun _70_242 -> (match (_70_242) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (_70_245, t) -> begin
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

let _70_260 = (FStar_Util.incr num_of_toplevelmods)
in if ((FStar_ST.read num_of_toplevelmods) > (Prims.parse_int "1")) then begin
(let _171_139 = (let _171_138 = (let _171_137 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" _171_137))
in FStar_Errors.Err (_171_138))
in (Prims.raise _171_139))
end else begin
()
end)
end))
and collect_tycon = (fun uu___387 -> (match (uu___387) with
| FStar_Parser_AST.TyconAbstract (_70_264, binders, k) -> begin
(

let _70_269 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_70_272, binders, k, t) -> begin
(

let _70_278 = (collect_binders binders)
in (

let _70_280 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_70_283, binders, k, identterms) -> begin
(

let _70_289 = (collect_binders binders)
in (

let _70_291 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _70_298 -> (match (_70_298) with
| (_70_294, t, _70_297) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_70_300, binders, k, identterms) -> begin
(

let _70_306 = (collect_binders binders)
in (

let _70_308 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _70_317 -> (match (_70_317) with
| (_70_311, t, _70_314, _70_316) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun uu___388 -> (match (uu___388) with
| FStar_Parser_AST.DefineEffect (_70_320, binders, t, decls, actions) -> begin
(

let _70_327 = (collect_binders binders)
in (

let _70_329 = (collect_term t)
in (

let _70_331 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_70_334, binders, t) -> begin
(

let _70_339 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___389 -> (match (uu___389) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _70_375 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___390 -> (match (uu___390) with
| FStar_Const.Const_int (_70_379, Some (signedness, width)) -> begin
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
in (let _171_148 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _171_148))))
end
| _70_395 -> begin
()
end))
and collect_term' = (fun uu___391 -> (match (uu___391) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
(

let _70_404 = if (s = "@") then begin
(let _171_151 = (let _171_150 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_171_150))
in (collect_term' _171_151))
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

let _70_424 = if (((FStar_List.length termimps) = (Prims.parse_int "1")) && (FStar_Options.universes ())) then begin
(record_lid lid)
end else begin
()
end
in (FStar_List.iter (fun _70_429 -> (match (_70_429) with
| (t, _70_428) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _70_434 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _70_439) -> begin
(

let _70_442 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_70_445, patterms, t) -> begin
(

let _70_455 = (FStar_List.iter (fun _70_452 -> (match (_70_452) with
| (pat, t) -> begin
(

let _70_453 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(

let _70_461 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _70_467 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _70_474 = (collect_term t1)
in (

let _70_476 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _70_484 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _70_490 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(

let _70_496 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _70_501 -> (match (_70_501) with
| (_70_499, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _70_504) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _70_513 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _70_522 = (collect_binders binders)
in (

let _70_524 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _70_530 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_70_533, t) -> begin
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
and collect_pattern' = (fun uu___392 -> (match (uu___392) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _70_574 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _70_597 -> (match (_70_597) with
| (_70_595, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _70_602 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _70_608 -> (match (_70_608) with
| (pat, t1, t2) -> begin
(

let _70_609 = (collect_pattern pat)
in (

let _70_611 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let _70_616 = (FStar_Parser_Driver.parse_file filename)
in (match (_70_616) with
| (ast, _70_615) -> begin
(

let _70_617 = (collect_file ast)
in (FStar_ST.read deps))
end)))))))))))))


let print_graph = (fun graph -> (

let _70_620 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (

let _70_622 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (

let _70_624 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _171_173 = (let _171_172 = (let _171_171 = (let _171_170 = (let _171_169 = (let _171_168 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _171_168))
in (FStar_List.collect (fun k -> (

let deps = (let _171_164 = (let _171_163 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _171_163))
in (Prims.fst _171_164))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _171_169))
in (FStar_String.concat "\n" _171_170))
in (Prims.strcat _171_171 "\n}\n"))
in (Prims.strcat "digraph {\n" _171_172))
in (FStar_Util.write_file "dep.graph" _171_173))))))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (let _171_180 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _171_179 = (FStar_Util.mk_ref false)
in ((f), (_171_179)))) _171_180))
in (

let m = (build_map filenames)
in (

let collect_one = (collect_one verify_flags verify_mode)
in (

let partial_discovery = ((FStar_Options.universes ()) && (not (((FStar_Options.verify_all ()) || (FStar_Options.extract_all ())))))
in (

let rec discover_one = (fun is_user_provided_filename interface_only key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let _70_645 = (let _171_190 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _171_190))
in (match (_70_645) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| Some (intf) -> begin
(collect_one is_user_provided_filename m intf)
end
| None -> begin
[]
end)
in (

let impl_deps = (match (((impl), (intf))) with
| (Some (impl), Some (_70_653)) when interface_only -> begin
[]
end
| (Some (impl), _70_659) -> begin
(collect_one is_user_provided_filename m impl)
end
| (None, _70_663) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (

let _70_667 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one false partial_discovery) deps)))))
end))
end else begin
()
end)
in (

let discover_command_line_argument = (fun f -> (

let m = (lowercase_module_name f)
in if (is_interface f) then begin
(discover_one true true m)
end else begin
(discover_one true false m)
end))
in (

let _70_672 = (FStar_List.iter discover_command_line_argument filenames)
in (

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let _70_681 = (let _171_197 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _171_197))
in (match (_70_681) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(

let _70_683 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (

let _70_685 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (

let _70_687 = (print_graph immediate_graph)
in (

let _70_689 = (FStar_Util.print_string "\n")
in (FStar_All.exit (Prims.parse_int "1"))))))
end
| Black -> begin
direct_deps
end
| White -> begin
(

let _70_693 = (FStar_Util.smap_add graph key ((direct_deps), (Gray)))
in (

let all_deps = (let _171_201 = (let _171_200 = (FStar_List.map (fun dep -> (let _171_199 = (discover ((key)::cycle) dep)
in (dep)::_171_199)) direct_deps)
in (FStar_List.flatten _171_200))
in (FStar_List.unique _171_201))
in (

let _70_697 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (

let _70_699 = (let _171_203 = (let _171_202 = (FStar_ST.read topologically_sorted)
in (key)::_171_202)
in (FStar_ST.op_Colon_Equals topologically_sorted _171_203))
in all_deps))))
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (fun k -> (match ((let _171_207 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _171_207))) with
| (Some (intf), Some (impl)) when ((not (partial_discovery)) && (not ((FStar_List.existsML (fun f -> ((lowercase_module_name f) = k)) filenames)))) -> begin
(intf)::(impl)::[]
end
| (Some (intf), Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && ((lowercase_module_name f) = k))) filenames) -> begin
(intf)::(impl)::[]
end
| (Some (intf), _70_719) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))
in (

let must_find_r = (fun f -> (let _171_212 = (must_find f)
in (FStar_List.rev _171_212)))
in (

let by_target = (let _171_217 = (FStar_Util.smap_keys graph)
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

let deps = (let _171_215 = (discover k)
in (FStar_List.rev _171_215))
in (

let deps_as_filenames = (let _171_216 = (FStar_List.collect must_find deps)
in (FStar_List.append _171_216 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _171_217))
in (

let topologically_sorted = (let _171_218 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _171_218))
in (

let _70_746 = (FStar_List.iter (fun _70_743 -> (match (_70_743) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(

let maybe_fst = (

let k = (FStar_String.length m)
in if ((k > (Prims.parse_int "4")) && ((FStar_String.substring m (k - (Prims.parse_int "4")) (Prims.parse_int "4")) = ".fst")) then begin
(let _171_220 = (FStar_String.substring m (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" _171_220))
end else begin
""
end)
in (let _171_222 = (let _171_221 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m m maybe_fst)
in FStar_Errors.Err (_171_221))
in (Prims.raise _171_222)))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _70_751 -> (match (_70_751) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun _70_758 -> (match (_70_758) with
| (make_deps, _70_756, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_70_764) -> begin
(Prims.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





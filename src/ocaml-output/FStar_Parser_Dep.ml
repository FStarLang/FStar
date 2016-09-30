
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
(let _164_7 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in Some (_164_7))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| (Some (m))::_70_19 -> begin
Some (m)
end
| _70_24 -> begin
None
end))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))) = 'i'))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))


let list_of_option = (fun _70_1 -> (match (_70_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun _70_33 -> (match (_70_33) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let must_find_stratified = (fun m k -> (match ((let _164_16 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _164_16))) with
| (Some (intf), _70_39) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))


let must_find_universes = (fun m k -> (let _164_20 = (let _164_19 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _164_19))
in (list_of_pair _164_20)))


let must_find = (fun m k -> if (FStar_Options.universes ()) then begin
(must_find_universes m k)
end else begin
(must_find_stratified m k)
end)


let print_map : map  ->  Prims.unit = (fun m -> (let _164_29 = (let _164_28 = (FStar_Util.smap_keys m)
in (FStar_List.unique _164_28))
in (FStar_List.iter (fun k -> (let _164_27 = (must_find m k)
in (FStar_List.iter (fun f -> (FStar_Util.print2 "%s: %s\n" k f)) _164_27))) _164_29)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _164_32 = (FStar_Util.basename f)
in (check_and_strip_suffix _164_32))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _164_34 = (let _164_33 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_164_33))
in (Prims.raise _164_34))
end))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _164_37 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _164_37))
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

let _70_82 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
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
(let _164_45 = (let _164_44 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_164_44))
in (Prims.raise _164_45))
end) include_directories)
in (

let _70_85 = (FStar_List.iter (fun f -> (let _164_47 = (lowercase_module_name f)
in (add_entry _164_47 f))) filenames)
in map)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_ST.alloc false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _70_97 = (let _164_57 = (let _164_56 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _164_56))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _164_55 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _164_55))
in (

let _70_95 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _164_57))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _164_63 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _164_63 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _164_68 = (string_of_lid l last)
in (FStar_String.lowercase _164_68)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in if ((let _164_75 = (let _164_74 = (let _164_73 = (FStar_Util.basename filename)
in (check_and_strip_suffix _164_73))
in (FStar_Util.must _164_74))
in (FStar_String.lowercase _164_75)) <> k') then begin
(let _164_77 = (let _164_76 = (string_of_lid lid true)
in (_164_76)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _164_77))
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

let add_dep = (fun d -> if (not ((let _164_92 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _164_92)))) then begin
(let _164_94 = (let _164_93 = (FStar_ST.read deps)
in (d)::_164_93)
in (FStar_ST.op_Colon_Equals deps _164_94))
end else begin
()
end)
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _164_100 = (lowercase_module_name f)
in (add_dep _164_100))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Absyn_Syntax.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _164_102 = (let _164_101 = (string_of_lid lid true)
in (_164_101)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _164_102))
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
(let _164_108 = (let _164_107 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Absyn_Syntax.Err (_164_107))
in (Prims.raise _164_108))
end))))
in (

let record_lid = (fun is_constructor lid -> if (lid.FStar_Ident.ident.FStar_Ident.idText <> "reflect") then begin
(

let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _164_116 = (lowercase_module_name f)
in (add_dep _164_116))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ())) then begin
(let _164_118 = (let _164_117 = (string_of_lid lid false)
in (_164_117)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _164_118))
end else begin
()
end
end))
in (

let _70_145 = (let _164_119 = (lowercase_join_longident lid false)
in (try_key _164_119))
in if is_constructor then begin
(let _164_120 = (lowercase_join_longident lid true)
in (try_key _164_120))
end else begin
()
end))
end else begin
()
end)
in (

let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _164_122 = (let _164_121 = (FStar_Util.basename filename)
in (FStar_String.lowercase _164_121))
in (FStar_Util.starts_with _164_122 "fstar.")) then begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::[]
end else begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
end
end
in (

let _70_148 = (FStar_List.iter (record_open false) auto_open)
in (

let rec collect_fragment = (fun _70_2 -> (match (_70_2) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _70_3 -> (match (_70_3) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
(

let _70_176 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _70_4 -> (match (_70_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _70_187 = (check_module_declaration_against_filename lid filename)
in (

let _70_195 = (match (verify_mode) with
| VerifyAll -> begin
(let _164_143 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _164_143))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _164_144 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _164_144))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _70_194 -> (match (_70_194) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _164_146 = (string_of_lid lid true)
in (FStar_String.lowercase _164_146))) then begin
(FStar_ST.op_Colon_Equals r true)
end else begin
()
end
end)) verify_flags)
end)
in (collect_decls decls)))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _70_5 -> (match (_70_5) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let _70_206 = (let _164_150 = (lowercase_join_longident lid true)
in (add_dep _164_150))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.ToplevelLet (_70_209, _70_211, patterms) -> begin
(FStar_List.iter (fun _70_217 -> (match (_70_217) with
| (pat, t) -> begin
(

let _70_218 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_70_221, binders, t) -> begin
(

let _70_226 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _70_256; FStar_Parser_AST.mdest = _70_254; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(

let _70_259 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_70_262, ts) -> begin
(

let ts = (FStar_List.map (fun _70_268 -> (match (_70_268) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (_70_271, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (_, ed)) | (FStar_Parser_AST.NewEffect (_, ed)) -> begin
(collect_effect_decl ed)
end
| (FStar_Parser_AST.Fsdoc (_)) | (FStar_Parser_AST.Pragma (_)) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
()
end))
and collect_tycon = (fun _70_6 -> (match (_70_6) with
| FStar_Parser_AST.TyconAbstract (_70_294, binders, k) -> begin
(

let _70_299 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_70_302, binders, k, t) -> begin
(

let _70_308 = (collect_binders binders)
in (

let _70_310 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_70_313, binders, k, identterms) -> begin
(

let _70_319 = (collect_binders binders)
in (

let _70_321 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _70_328 -> (match (_70_328) with
| (_70_324, t, _70_327) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_70_330, binders, k, identterms) -> begin
(

let _70_336 = (collect_binders binders)
in (

let _70_338 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _70_347 -> (match (_70_347) with
| (_70_341, t, _70_344, _70_346) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _70_7 -> (match (_70_7) with
| FStar_Parser_AST.DefineEffect (_70_350, binders, t, decls, actions) -> begin
(

let _70_357 = (collect_binders binders)
in (

let _70_359 = (collect_term t)
in (

let _70_361 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_70_364, binders, t) -> begin
(

let _70_369 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _70_8 -> (match (_70_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _70_405 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun _70_9 -> (match (_70_9) with
| FStar_Const.Const_int (_70_409, Some (signedness, width)) -> begin
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
in (let _162_161 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _162_161))))
end
| _70_425 -> begin
()
end))
and collect_term' = (fun _70_10 -> (match (_70_10) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
(

let _69_434 = if (s = "@") then begin
(let _162_164 = (let _162_163 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_162_163))
in (collect_term' _162_164))
end else begin
()
end
in (FStar_List.iter collect_term ts))
end
| FStar_Parser_AST.Tvar (_70_437) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(record_lid false lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
(

let _70_446 = if (((FStar_List.length termimps) = (Prims.parse_int "1")) && (FStar_Options.universes ())) then begin
(record_lid true lid)
end else begin
()
end
in (FStar_List.iter (fun _70_451 -> (match (_70_451) with
| (t, _70_450) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _70_456 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _70_461) -> begin
(

let _70_464 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_70_467, patterms, t) -> begin
(

let _70_477 = (FStar_List.iter (fun _70_474 -> (match (_70_474) with
| (pat, t) -> begin
(

let _70_475 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(

let _70_483 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _70_489 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _70_496 = (collect_term t1)
in (

let _70_498 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _70_506 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _70_512 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(

let _70_518 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _70_523 -> (match (_70_523) with
| (_70_521, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _70_526) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _70_535 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _70_544 = (collect_binders binders)
in (

let _70_546 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _70_552 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_70_555, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) -> begin
(collect_term t)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun _70_11 -> (match (_70_11) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _70_594 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _70_617 -> (match (_70_617) with
| (_70_615, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _70_622 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _70_628 -> (match (_70_628) with
| (pat, t1, t2) -> begin
(

let _70_629 = (collect_pattern pat)
in (

let _70_631 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let ast = (FStar_Parser_Driver.parse_file filename)
in (

let _70_634 = (collect_file ast)
in (FStar_ST.read deps)))))))))))))


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

let _70_637 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (

let _70_639 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (

let _69_641 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _162_189 = (let _162_188 = (let _162_187 = (let _162_186 = (let _162_185 = (let _162_184 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _162_184))
in (FStar_List.collect (fun k -> (

let deps = (let _162_180 = (let _162_179 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _162_179))
in (Prims.fst _162_180))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _162_185))
in (FStar_String.concat "\n" _162_186))
in (Prims.strcat _162_187 "\n}\n"))
in (Prims.strcat "digraph {\n" _162_188))
in (FStar_Util.write_file "dep.graph" _162_189))))))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (let _162_196 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _162_195 = (FStar_ST.alloc false)
in ((f), (_162_195)))) _162_196))
in (

let m = (build_map filenames)
in (

let collect_one = (collect_one verify_flags verify_mode)
in (

let rec discover_one = (fun is_user_provided_filename key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let _69_660 = (let _162_204 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _162_204))
in (match (_69_660) with
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

let _70_670 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one false) deps)))))
end))
end else begin
()
end)
in (

let _69_672 = (let _162_205 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter (discover_one true) _162_205))
in (

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_ST.alloc [])
in (

let rec discover = (fun cycle key -> (

let _69_681 = (let _162_210 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _162_210))
in (match (_69_681) with
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

let all_deps = (let _162_214 = (let _162_213 = (FStar_List.map (fun dep -> (let _162_212 = (discover ((key)::cycle) dep)
in (dep)::_162_212)) direct_deps)
in (FStar_List.flatten _162_213))
in (FStar_List.unique _162_214))
in (

let _70_697 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (

let _69_699 = (let _162_216 = (let _162_215 = (FStar_ST.read topologically_sorted)
in (key)::_162_215)
in (FStar_ST.op_Colon_Equals topologically_sorted _162_216))
in all_deps))))
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (must_find m)
in (

let must_find_r = (fun f -> (let _162_221 = (must_find f)
in (FStar_List.rev _162_221)))
in (

let by_target = (let _162_226 = (FStar_Util.smap_keys graph)
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

let deps = (let _162_224 = (discover k)
in (FStar_List.rev _162_224))
in (

let deps_as_filenames = (let _162_225 = (FStar_List.collect must_find deps)
in (FStar_List.append _162_225 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _162_226))
in (

let topologically_sorted = (let _162_227 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _162_227))
in (

let _70_719 = (FStar_List.iter (fun _70_718 -> (match (_70_718) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(let _162_230 = (let _162_229 = (FStar_Util.format2 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph\n" m m)
in FStar_Absyn_Syntax.Err (_162_229))
in (Prims.raise _162_230))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _70_724 -> (match (_70_724) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun _70_731 -> (match (_70_731) with
| (make_deps, _70_729, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_70_737) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))






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
(let _170_7 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in Some (_170_7))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| (Some (m))::_72_19 -> begin
Some (m)
end
| _72_24 -> begin
None
end))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1"))) = 'i'))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))


let list_of_option = (fun _72_1 -> (match (_72_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun _72_33 -> (match (_72_33) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _170_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _170_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _170_18 = (let _170_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_170_17))
in (Prims.raise _170_18))
end))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (let _170_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _170_21))
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

let _72_61 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
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
(let _170_29 = (let _170_28 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_170_28))
in (Prims.raise _170_29))
end) include_directories)
in (

let _72_64 = (FStar_List.iter (fun f -> (let _170_31 = (lowercase_module_name f)
in (add_entry _170_31 f))) filenames)
in map)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_ST.alloc false)
in (

let prefix = (Prims.strcat prefix ".")
in (

let _72_76 = (let _170_41 = (let _170_40 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _170_40))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (let _170_39 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _170_39))
in (

let _72_74 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _170_41))
in (FStar_ST.read found)))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (

let names = (let _170_47 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _170_47 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _170_52 = (string_of_lid l last)
in (FStar_String.lowercase _170_52)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in if ((let _170_59 = (let _170_58 = (let _170_57 = (FStar_Util.basename filename)
in (check_and_strip_suffix _170_57))
in (FStar_Util.must _170_58))
in (FStar_String.lowercase _170_59)) <> k') then begin
(let _170_61 = (let _170_60 = (string_of_lid lid true)
in (_170_60)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _170_61))
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

let add_dep = (fun d -> if (not ((let _170_76 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _170_76)))) then begin
(let _170_78 = (let _170_77 = (FStar_ST.read deps)
in (d)::_170_77)
in (FStar_ST.op_Colon_Equals deps _170_78))
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
(FStar_List.iter (fun f -> (let _170_84 = (lowercase_module_name f)
in (add_dep _170_84))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Absyn_Syntax.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _170_86 = (let _170_85 = (string_of_lid lid true)
in (_170_85)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _170_86))
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
(let _170_92 = (let _170_91 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Absyn_Syntax.Err (_170_91))
in (Prims.raise _170_92))
end))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _170_98 = (lowercase_module_name f)
in (add_dep _170_98))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ())) then begin
(let _170_100 = (let _170_99 = (string_of_lid lid false)
in (_170_99)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _170_100))
end else begin
()
end
end))
in (

let _72_123 = (let _170_101 = (lowercase_join_longident lid false)
in (try_key _170_101))
in ())))
in (

let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _170_103 = (let _170_102 = (FStar_Util.basename filename)
in (FStar_String.lowercase _170_102))
in (FStar_Util.starts_with _170_103 "fstar.")) then begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::[]
end else begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
end
end
in (

let _72_126 = (FStar_List.iter (record_open false) auto_open)
in (

let num_of_toplevelmods = (FStar_ST.alloc (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun _72_2 -> (match (_72_2) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _72_3 -> (match (_72_3) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
(

let _72_155 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _72_4 -> (match (_72_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(

let _72_166 = (check_module_declaration_against_filename lid filename)
in (

let _72_174 = (match (verify_mode) with
| VerifyAll -> begin
(let _170_124 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _170_124))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _170_125 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _170_125))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _72_173 -> (match (_72_173) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _170_127 = (string_of_lid lid true)
in (FStar_String.lowercase _170_127))) then begin
(FStar_ST.op_Colon_Equals r true)
end else begin
()
end
end)) verify_flags)
end)
in (collect_decls decls)))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (

let _72_178 = (collect_decl x.FStar_Parser_AST.d)
in (FStar_List.iter collect_term x.FStar_Parser_AST.attrs))) decls))
and collect_decl = (fun _72_5 -> (match (_72_5) with
| (FStar_Parser_AST.Include (lid)) | (FStar_Parser_AST.Open (lid)) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let _72_188 = (let _170_131 = (lowercase_join_longident lid true)
in (add_dep _170_131))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.TopLevelLet (_72_191, patterms) -> begin
(FStar_List.iter (fun _72_197 -> (match (_72_197) with
| (pat, t) -> begin
(

let _72_198 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_72_201, binders, t) -> begin
(

let _72_206 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)})) | (FStar_Parser_AST.Val (_, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _72_239; FStar_Parser_AST.mdest = _72_237; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(

let _72_242 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_72_245, ts) -> begin
(

let ts = (FStar_List.map (fun _72_251 -> (match (_72_251) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (_72_254, t) -> begin
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

let _72_269 = (FStar_Util.incr num_of_toplevelmods)
in if ((FStar_ST.read num_of_toplevelmods) > (Prims.parse_int "1")) then begin
(let _170_136 = (let _170_135 = (let _170_134 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" _170_134))
in FStar_Absyn_Syntax.Err (_170_135))
in (Prims.raise _170_136))
end else begin
()
end)
end))
and collect_tycon = (fun _72_6 -> (match (_72_6) with
| FStar_Parser_AST.TyconAbstract (_72_273, binders, k) -> begin
(

let _72_278 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_72_281, binders, k, t) -> begin
(

let _72_287 = (collect_binders binders)
in (

let _72_289 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_72_292, binders, k, identterms) -> begin
(

let _72_298 = (collect_binders binders)
in (

let _72_300 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _72_307 -> (match (_72_307) with
| (_72_303, t, _72_306) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_72_309, binders, k, identterms) -> begin
(

let _72_315 = (collect_binders binders)
in (

let _72_317 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _72_326 -> (match (_72_326) with
| (_72_320, t, _72_323, _72_325) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _72_7 -> (match (_72_7) with
| FStar_Parser_AST.DefineEffect (_72_329, binders, t, decls, actions) -> begin
(

let _72_336 = (collect_binders binders)
in (

let _72_338 = (collect_term t)
in (

let _72_340 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_72_343, binders, t) -> begin
(

let _72_348 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _72_8 -> (match (_72_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _72_384 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun _72_9 -> (match (_72_9) with
| FStar_Const.Const_int (_72_388, Some (signedness, width)) -> begin
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
in (let _170_145 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _170_145))))
end
| _72_404 -> begin
()
end))
and collect_term' = (fun _72_10 -> (match (_72_10) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
(

let _72_413 = if (s = "@") then begin
(let _170_148 = (let _170_147 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_170_147))
in (collect_term' _170_148))
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

let _72_433 = if (((FStar_List.length termimps) = (Prims.parse_int "1")) && (FStar_Options.universes ())) then begin
(record_lid lid)
end else begin
()
end
in (FStar_List.iter (fun _72_438 -> (match (_72_438) with
| (t, _72_437) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(

let _72_443 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _72_448) -> begin
(

let _72_451 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_72_454, patterms, t) -> begin
(

let _72_464 = (FStar_List.iter (fun _72_461 -> (match (_72_461) with
| (pat, t) -> begin
(

let _72_462 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(

let _72_470 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let _72_476 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let _72_483 = (collect_term t1)
in (

let _72_485 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(

let _72_493 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(

let _72_499 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(

let _72_505 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _72_510 -> (match (_72_510) with
| (_72_508, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _72_513) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(

let _72_522 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(

let _72_531 = (collect_binders binders)
in (

let _72_533 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(

let _72_539 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_72_542, t) -> begin
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
and collect_pattern' = (fun _72_11 -> (match (_72_11) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(

let _72_583 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _72_606 -> (match (_72_606) with
| (_72_604, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _72_611 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _72_617 -> (match (_72_617) with
| (pat, t1, t2) -> begin
(

let _72_618 = (collect_pattern pat)
in (

let _72_620 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (

let _72_625 = (FStar_Parser_Driver.parse_file filename)
in (match (_72_625) with
| (ast, _72_624) -> begin
(

let _72_626 = (collect_file ast)
in (FStar_ST.read deps))
end)))))))))))))


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

let _72_629 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (

let _72_631 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (

let _72_633 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _170_173 = (let _170_172 = (let _170_171 = (let _170_170 = (let _170_169 = (let _170_168 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _170_168))
in (FStar_List.collect (fun k -> (

let deps = (let _170_164 = (let _170_163 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _170_163))
in (Prims.fst _170_164))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _170_169))
in (FStar_String.concat "\n" _170_170))
in (Prims.strcat _170_171 "\n}\n"))
in (Prims.strcat "digraph {\n" _170_172))
in (FStar_Util.write_file "dep.graph" _170_173))))))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (let _170_180 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _170_179 = (FStar_ST.alloc false)
in ((f), (_170_179)))) _170_180))
in (

let m = (build_map filenames)
in (

let collect_one = (collect_one verify_flags verify_mode)
in (

let partial_discovery = ((FStar_Options.universes ()) && (not ((FStar_Options.verify_all ()))))
in (

let rec discover_one = (fun interface_only key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(

let _72_653 = (let _170_188 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _170_188))
in (match (_72_653) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| Some (intf) -> begin
(collect_one false m intf)
end
| None -> begin
[]
end)
in (

let impl_deps = (match (((impl), (intf))) with
| (Some (impl), Some (_72_661)) when interface_only -> begin
[]
end
| (Some (impl), _72_667) -> begin
(collect_one false m impl)
end
| (None, _72_671) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (

let _72_675 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one partial_discovery) deps)))))
end))
end else begin
()
end)
in (

let discover_command_line_argument = (fun f -> (

let m = (lowercase_module_name f)
in if (is_interface f) then begin
(discover_one true m)
end else begin
(discover_one false m)
end))
in (

let _72_680 = (FStar_List.iter discover_command_line_argument filenames)
in (

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_ST.alloc [])
in (

let rec discover = (fun cycle key -> (

let _72_689 = (let _170_195 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _170_195))
in (match (_72_689) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(

let _72_691 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (

let _72_693 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (

let _72_695 = (print_graph immediate_graph)
in (

let _72_697 = (FStar_Util.print_string "\n")
in (FStar_All.exit (Prims.parse_int "1"))))))
end
| Black -> begin
direct_deps
end
| White -> begin
(

let _72_701 = (FStar_Util.smap_add graph key ((direct_deps), (Gray)))
in (

let all_deps = (let _170_199 = (let _170_198 = (FStar_List.map (fun dep -> (let _170_197 = (discover ((key)::cycle) dep)
in (dep)::_170_197)) direct_deps)
in (FStar_List.flatten _170_198))
in (FStar_List.unique _170_199))
in (

let _72_705 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (

let _72_707 = (let _170_201 = (let _170_200 = (FStar_ST.read topologically_sorted)
in (key)::_170_200)
in (FStar_ST.op_Colon_Equals topologically_sorted _170_201))
in all_deps))))
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (fun k -> (match ((let _170_205 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _170_205))) with
| (Some (intf), Some (impl)) when ((not (partial_discovery)) && (not ((FStar_List.existsML (fun f -> ((lowercase_module_name f) = k)) filenames)))) -> begin
(intf)::(impl)::[]
end
| (Some (intf), Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && ((lowercase_module_name f) = k))) filenames) -> begin
(intf)::(impl)::[]
end
| (Some (intf), _72_727) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))
in (

let must_find_r = (fun f -> (let _170_210 = (must_find f)
in (FStar_List.rev _170_210)))
in (

let by_target = (let _170_215 = (FStar_Util.smap_keys graph)
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

let deps = (let _170_213 = (discover k)
in (FStar_List.rev _170_213))
in (

let deps_as_filenames = (let _170_214 = (FStar_List.collect must_find deps)
in (FStar_List.append _170_214 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _170_215))
in (

let topologically_sorted = (let _170_216 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _170_216))
in (

let _72_754 = (FStar_List.iter (fun _72_751 -> (match (_72_751) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(

let maybe_fst = (

let k = (FStar_String.length m)
in if ((k > (Prims.parse_int "4")) && ((FStar_String.substring m (k - (Prims.parse_int "4")) (Prims.parse_int "4")) = ".fst")) then begin
(let _170_218 = (FStar_String.substring m (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" _170_218))
end else begin
""
end)
in (let _170_220 = (let _170_219 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m m maybe_fst)
in FStar_Absyn_Syntax.Err (_170_219))
in (Prims.raise _170_220)))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _72_759 -> (match (_72_759) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun _72_766 -> (match (_72_766) with
| (make_deps, _72_764, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_72_772) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





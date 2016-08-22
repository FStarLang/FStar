
open Prims
# 35 "FStar.Parser.Dep.fst"
type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut

# 45 "FStar.Parser.Dep.fst"
let is_VerifyAll = (fun _discr_ -> (match (_discr_) with
| VerifyAll (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Parser.Dep.fst"
let is_VerifyUserList = (fun _discr_ -> (match (_discr_) with
| VerifyUserList (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Parser.Dep.fst"
let is_VerifyFigureItOut = (fun _discr_ -> (match (_discr_) with
| VerifyFigureItOut (_) -> begin
true
end
| _ -> begin
false
end))

# 47 "FStar.Parser.Dep.fst"
type map =
(Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap

# 49 "FStar.Parser.Dep.fst"
let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (
# 52 "FStar.Parser.Dep.fst"
let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (
# 53 "FStar.Parser.Dep.fst"
let matches = (FStar_List.map (fun ext -> (
# 54 "FStar.Parser.Dep.fst"
let lext = (FStar_String.length ext)
in (
# 55 "FStar.Parser.Dep.fst"
let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _161_7 = (FStar_String.substring f 0 (l - lext))
in Some (_161_7))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| (Some (m))::_69_19 -> begin
Some (m)
end
| _69_24 -> begin
None
end))))

# 65 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 69 "FStar.Parser.Dep.fst"
let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))

# 72 "FStar.Parser.Dep.fst"
let list_of_option = (fun _69_1 -> (match (_69_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))

# 74 "FStar.Parser.Dep.fst"
let list_of_pair = (fun _69_33 -> (match (_69_33) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))

# 77 "FStar.Parser.Dep.fst"
let must_find_stratified = (fun m k -> (match ((let _161_16 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _161_16))) with
| (Some (intf), _69_39) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))

# 88 "FStar.Parser.Dep.fst"
let must_find_universes = (fun m k -> (let _161_20 = (let _161_19 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _161_19))
in (list_of_pair _161_20)))

# 91 "FStar.Parser.Dep.fst"
let must_find = (fun m k -> if (FStar_Options.universes ()) then begin
(must_find_universes m k)
end else begin
(must_find_stratified m k)
end)

# 97 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _161_29 = (let _161_28 = (FStar_Util.smap_keys m)
in (FStar_List.unique _161_28))
in (FStar_List.iter (fun k -> (let _161_27 = (must_find m k)
in (FStar_List.iter (fun f -> (FStar_Util.print2 "%s: %s\n" k f)) _161_27))) _161_29)))

# 104 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _161_32 = (FStar_Util.basename f)
in (check_and_strip_suffix _161_32))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _161_34 = (let _161_33 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_161_33))
in (Prims.raise _161_34))
end))

# 112 "FStar.Parser.Dep.fst"
let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (
# 120 "FStar.Parser.Dep.fst"
let include_directories = (FStar_Options.include_path ())
in (
# 121 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (
# 124 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.unique include_directories)
in (
# 125 "FStar.Parser.Dep.fst"
let cwd = (let _161_37 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _161_37))
in (
# 126 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 127 "FStar.Parser.Dep.fst"
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
# 140 "FStar.Parser.Dep.fst"
let _69_82 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(
# 142 "FStar.Parser.Dep.fst"
let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (
# 144 "FStar.Parser.Dep.fst"
let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(
# 147 "FStar.Parser.Dep.fst"
let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (
# 148 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| None -> begin
()
end))) files))
end else begin
(let _161_45 = (let _161_44 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_161_44))
in (Prims.raise _161_45))
end) include_directories)
in (
# 157 "FStar.Parser.Dep.fst"
let _69_85 = (FStar_List.iter (fun f -> (let _161_47 = (lowercase_module_name f)
in (add_entry _161_47 f))) filenames)
in map)))))))))

# 160 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 167 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 168 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 169 "FStar.Parser.Dep.fst"
let _69_97 = (let _161_57 = (let _161_56 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _161_56))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 171 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 174 "FStar.Parser.Dep.fst"
let filename = (let _161_55 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _161_55))
in (
# 175 "FStar.Parser.Dep.fst"
let _69_95 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _161_57))
in (FStar_ST.read found)))))

# 178 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 182 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 183 "FStar.Parser.Dep.fst"
let names = (let _161_63 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _161_63 suffix))
in (FStar_String.concat "." names))))

# 184 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _161_68 = (string_of_lid l last)
in (FStar_String.lowercase _161_68)))

# 190 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 194 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _161_75 = (let _161_74 = (let _161_73 = (FStar_Util.basename filename)
in (check_and_strip_suffix _161_73))
in (FStar_Util.must _161_74))
in (FStar_String.lowercase _161_75)) <> k') then begin
(let _161_77 = (let _161_76 = (string_of_lid lid true)
in (_161_76)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _161_77))
end else begin
()
end))

# 200 "FStar.Parser.Dep.fst"
exception Exit

# 200 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 200 "FStar.Parser.Dep.fst"
let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (
# 205 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 206 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _161_92 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _161_92)))) then begin
(let _161_94 = (let _161_93 = (FStar_ST.read deps)
in (d)::_161_93)
in (FStar_ST.op_Colon_Equals deps _161_94))
end else begin
()
end)
in (
# 210 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 212 "FStar.Parser.Dep.fst"
let record_open = (fun let_open lid -> (
# 213 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _161_100 = (lowercase_module_name f)
in (add_dep _161_100))) (list_of_pair pair))
end
| None -> begin
(
# 218 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Absyn_Syntax.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _161_102 = (let _161_101 = (string_of_lid lid true)
in (_161_101)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _161_102))
end
end else begin
()
end)
end)))
in (
# 228 "FStar.Parser.Dep.fst"
let record_module_alias = (fun ident lid -> (
# 229 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (
# 230 "FStar.Parser.Dep.fst"
let alias = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map alias)) with
| Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| None -> begin
(let _161_108 = (let _161_107 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Absyn_Syntax.Err (_161_107))
in (Prims.raise _161_108))
end))))
in (
# 238 "FStar.Parser.Dep.fst"
let record_lid = (fun is_constructor lid -> if (lid.FStar_Ident.ident.FStar_Ident.idText <> "reflect") then begin
(
# 240 "FStar.Parser.Dep.fst"
let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _161_116 = (lowercase_module_name f)
in (add_dep _161_116))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && (FStar_Options.debug_any ())) then begin
(let _161_118 = (let _161_117 = (string_of_lid lid false)
in (_161_117)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _161_118))
end else begin
()
end
end))
in (
# 250 "FStar.Parser.Dep.fst"
let _69_145 = (let _161_119 = (lowercase_join_longident lid false)
in (try_key _161_119))
in if is_constructor then begin
(let _161_120 = (lowercase_join_longident lid true)
in (try_key _161_120))
end else begin
()
end))
end else begin
()
end)
in (
# 259 "FStar.Parser.Dep.fst"
let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _161_122 = (let _161_121 = (FStar_Util.basename filename)
in (FStar_String.lowercase _161_121))
in (FStar_Util.starts_with _161_122 "fstar.")) then begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::[]
end else begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
end
end
in (
# 267 "FStar.Parser.Dep.fst"
let _69_148 = (FStar_List.iter (record_open false) auto_open)
in (
# 269 "FStar.Parser.Dep.fst"
let rec collect_fragment = (fun _69_2 -> (match (_69_2) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _69_3 -> (match (_69_3) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
(
# 279 "FStar.Parser.Dep.fst"
let _69_176 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _69_4 -> (match (_69_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 285 "FStar.Parser.Dep.fst"
let _69_187 = (check_module_declaration_against_filename lid filename)
in (
# 286 "FStar.Parser.Dep.fst"
let _69_195 = (match (verify_mode) with
| VerifyAll -> begin
(let _161_143 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _161_143))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _161_144 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _161_144))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _69_194 -> (match (_69_194) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _161_146 = (string_of_lid lid true)
in (FStar_String.lowercase _161_146))) then begin
(FStar_ST.op_Colon_Equals r true)
end else begin
()
end
end)) verify_flags)
end)
in (collect_decls decls)))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _69_5 -> (match (_69_5) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(
# 307 "FStar.Parser.Dep.fst"
let _69_206 = (let _161_150 = (lowercase_join_longident lid true)
in (add_dep _161_150))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.ToplevelLet (_69_209, _69_211, patterms) -> begin
(FStar_List.iter (fun _69_217 -> (match (_69_217) with
| (pat, t) -> begin
(
# 310 "FStar.Parser.Dep.fst"
let _69_218 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_69_221, binders, t) -> begin
(
# 312 "FStar.Parser.Dep.fst"
let _69_226 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _69_256; FStar_Parser_AST.mdest = _69_254; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(
# 320 "FStar.Parser.Dep.fst"
let _69_259 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_69_262, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_69_267, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (_, ed)) | (FStar_Parser_AST.NewEffect (_, ed)) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_69_281) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
(let _161_154 = (let _161_153 = (let _161_152 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" _161_152))
in FStar_Absyn_Syntax.Err (_161_153))
in (Prims.raise _161_154))
end))
and collect_tycon = (fun _69_6 -> (match (_69_6) with
| FStar_Parser_AST.TyconAbstract (_69_287, binders, k) -> begin
(
# 337 "FStar.Parser.Dep.fst"
let _69_292 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_69_295, binders, k, t) -> begin
(
# 340 "FStar.Parser.Dep.fst"
let _69_301 = (collect_binders binders)
in (
# 341 "FStar.Parser.Dep.fst"
let _69_303 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_69_306, binders, k, identterms) -> begin
(
# 344 "FStar.Parser.Dep.fst"
let _69_312 = (collect_binders binders)
in (
# 345 "FStar.Parser.Dep.fst"
let _69_314 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _69_319 -> (match (_69_319) with
| (_69_317, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_69_321, binders, k, identterms) -> begin
(
# 348 "FStar.Parser.Dep.fst"
let _69_327 = (collect_binders binders)
in (
# 349 "FStar.Parser.Dep.fst"
let _69_329 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _69_336 -> (match (_69_336) with
| (_69_332, t, _69_335) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _69_7 -> (match (_69_7) with
| FStar_Parser_AST.DefineEffect (_69_339, binders, t, decls, actions) -> begin
(
# 354 "FStar.Parser.Dep.fst"
let _69_346 = (collect_binders binders)
in (
# 355 "FStar.Parser.Dep.fst"
let _69_348 = (collect_term t)
in (
# 356 "FStar.Parser.Dep.fst"
let _69_350 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_69_353, binders, t) -> begin
(
# 359 "FStar.Parser.Dep.fst"
let _69_358 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _69_8 -> (match (_69_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _69_394 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun _69_9 -> (match (_69_9) with
| FStar_Const.Const_int (_69_398, Some (signedness, width)) -> begin
(
# 378 "FStar.Parser.Dep.fst"
let u = (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)
in (
# 379 "FStar.Parser.Dep.fst"
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
in (let _161_163 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _161_163))))
end
| _69_414 -> begin
()
end))
and collect_term' = (fun _69_10 -> (match (_69_10) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
(
# 390 "FStar.Parser.Dep.fst"
let _69_423 = if (s = "@") then begin
(let _161_166 = (let _161_165 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_161_165))
in (collect_term' _161_166))
end else begin
()
end
in (FStar_List.iter collect_term ts))
end
| FStar_Parser_AST.Tvar (_69_426) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(record_lid false lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
(
# 399 "FStar.Parser.Dep.fst"
let _69_435 = if (((FStar_List.length termimps) = 1) && (FStar_Options.universes ())) then begin
(record_lid true lid)
end else begin
()
end
in (FStar_List.iter (fun _69_440 -> (match (_69_440) with
| (t, _69_439) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 403 "FStar.Parser.Dep.fst"
let _69_445 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _69_450) -> begin
(
# 406 "FStar.Parser.Dep.fst"
let _69_453 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_69_456, patterms, t) -> begin
(
# 409 "FStar.Parser.Dep.fst"
let _69_466 = (FStar_List.iter (fun _69_463 -> (match (_69_463) with
| (pat, t) -> begin
(
# 409 "FStar.Parser.Dep.fst"
let _69_464 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(
# 412 "FStar.Parser.Dep.fst"
let _69_472 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 415 "FStar.Parser.Dep.fst"
let _69_478 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 418 "FStar.Parser.Dep.fst"
let _69_485 = (collect_term t1)
in (
# 419 "FStar.Parser.Dep.fst"
let _69_487 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 423 "FStar.Parser.Dep.fst"
let _69_495 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 426 "FStar.Parser.Dep.fst"
let _69_501 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(
# 429 "FStar.Parser.Dep.fst"
let _69_507 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _69_512 -> (match (_69_512) with
| (_69_510, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _69_515) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 435 "FStar.Parser.Dep.fst"
let _69_524 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 439 "FStar.Parser.Dep.fst"
let _69_533 = (collect_binders binders)
in (
# 440 "FStar.Parser.Dep.fst"
let _69_535 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 443 "FStar.Parser.Dep.fst"
let _69_541 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_69_544, t) -> begin
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
and collect_pattern' = (fun _69_11 -> (match (_69_11) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(
# 467 "FStar.Parser.Dep.fst"
let _69_583 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _69_606 -> (match (_69_606) with
| (_69_604, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 480 "FStar.Parser.Dep.fst"
let _69_611 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _69_617 -> (match (_69_617) with
| (pat, t1, t2) -> begin
(
# 488 "FStar.Parser.Dep.fst"
let _69_618 = (collect_pattern pat)
in (
# 489 "FStar.Parser.Dep.fst"
let _69_620 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 493 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file filename)
in (
# 494 "FStar.Parser.Dep.fst"
let _69_623 = (collect_file ast)
in (FStar_ST.read deps)))))))))))))

# 496 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 498 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 498 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 498 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 498 "FStar.Parser.Dep.fst"
let print_graph = (fun graph -> (
# 501 "FStar.Parser.Dep.fst"
let _69_626 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (
# 502 "FStar.Parser.Dep.fst"
let _69_628 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (
# 503 "FStar.Parser.Dep.fst"
let _69_630 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _161_191 = (let _161_190 = (let _161_189 = (let _161_188 = (let _161_187 = (let _161_186 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _161_186))
in (FStar_List.collect (fun k -> (
# 507 "FStar.Parser.Dep.fst"
let deps = (let _161_182 = (let _161_181 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _161_181))
in (Prims.fst _161_182))
in (
# 508 "FStar.Parser.Dep.fst"
let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _161_187))
in (FStar_String.concat "\n" _161_188))
in (Prims.strcat _161_189 "\n}\n"))
in (Prims.strcat "digraph {\n" _161_190))
in (FStar_Util.write_file "dep.graph" _161_191))))))

# 512 "FStar.Parser.Dep.fst"
let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (
# 518 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 522 "FStar.Parser.Dep.fst"
let verify_flags = (let _161_198 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _161_197 = (FStar_ST.alloc false)
in ((f), (_161_197)))) _161_198))
in (
# 527 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 538 "FStar.Parser.Dep.fst"
let collect_one = (collect_one verify_flags verify_mode)
in (
# 541 "FStar.Parser.Dep.fst"
let rec discover_one = (fun is_user_provided_filename key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 544 "FStar.Parser.Dep.fst"
let _69_649 = (let _161_206 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _161_206))
in (match (_69_649) with
| (intf, impl) -> begin
(
# 545 "FStar.Parser.Dep.fst"
let intf_deps = (match (intf) with
| None -> begin
[]
end
| Some (intf) -> begin
(collect_one is_user_provided_filename m intf)
end)
in (
# 550 "FStar.Parser.Dep.fst"
let impl_deps = (match (impl) with
| None -> begin
[]
end
| Some (impl) -> begin
(collect_one is_user_provided_filename m impl)
end)
in (
# 555 "FStar.Parser.Dep.fst"
let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (
# 556 "FStar.Parser.Dep.fst"
let _69_659 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one false) deps)))))
end))
end else begin
()
end)
in (
# 559 "FStar.Parser.Dep.fst"
let _69_661 = (let _161_207 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter (discover_one true) _161_207))
in (
# 562 "FStar.Parser.Dep.fst"
let immediate_graph = (FStar_Util.smap_copy graph)
in (
# 564 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 567 "FStar.Parser.Dep.fst"
let rec discover = (fun cycle key -> (
# 568 "FStar.Parser.Dep.fst"
let _69_670 = (let _161_212 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _161_212))
in (match (_69_670) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 571 "FStar.Parser.Dep.fst"
let _69_672 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 572 "FStar.Parser.Dep.fst"
let _69_674 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (
# 573 "FStar.Parser.Dep.fst"
let _69_676 = (print_graph immediate_graph)
in (
# 574 "FStar.Parser.Dep.fst"
let _69_678 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 582 "FStar.Parser.Dep.fst"
let _69_682 = (FStar_Util.smap_add graph key ((direct_deps), (Gray)))
in (
# 583 "FStar.Parser.Dep.fst"
let all_deps = (let _161_216 = (let _161_215 = (FStar_List.map (fun dep -> (let _161_214 = (discover ((key)::cycle) dep)
in (dep)::_161_214)) direct_deps)
in (FStar_List.flatten _161_215))
in (FStar_List.unique _161_216))
in (
# 587 "FStar.Parser.Dep.fst"
let _69_686 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (
# 589 "FStar.Parser.Dep.fst"
let _69_688 = (let _161_218 = (let _161_217 = (FStar_ST.read topologically_sorted)
in (key)::_161_217)
in (FStar_ST.op_Colon_Equals topologically_sorted _161_218))
in all_deps))))
end)
end)))
in (
# 593 "FStar.Parser.Dep.fst"
let discover = (discover [])
in (
# 595 "FStar.Parser.Dep.fst"
let must_find = (must_find m)
in (
# 596 "FStar.Parser.Dep.fst"
let must_find_r = (fun f -> (let _161_223 = (must_find f)
in (FStar_List.rev _161_223)))
in (
# 597 "FStar.Parser.Dep.fst"
let by_target = (let _161_228 = (FStar_Util.smap_keys graph)
in (FStar_List.collect (fun k -> (
# 598 "FStar.Parser.Dep.fst"
let as_list = (must_find k)
in (
# 599 "FStar.Parser.Dep.fst"
let is_interleaved = ((FStar_List.length as_list) = 2)
in (FStar_List.map (fun f -> (
# 601 "FStar.Parser.Dep.fst"
let should_append_fsti = ((is_implementation f) && is_interleaved)
in (
# 602 "FStar.Parser.Dep.fst"
let suffix = if should_append_fsti then begin
((Prims.strcat f "i"))::[]
end else begin
[]
end
in (
# 603 "FStar.Parser.Dep.fst"
let k = (lowercase_module_name f)
in (
# 604 "FStar.Parser.Dep.fst"
let deps = (let _161_226 = (discover k)
in (FStar_List.rev _161_226))
in (
# 605 "FStar.Parser.Dep.fst"
let deps_as_filenames = (let _161_227 = (FStar_List.collect must_find deps)
in (FStar_List.append _161_227 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _161_228))
in (
# 610 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _161_229 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _161_229))
in (
# 612 "FStar.Parser.Dep.fst"
let _69_708 = (FStar_List.iter (fun _69_707 -> (match (_69_707) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(let _161_232 = (let _161_231 = (FStar_Util.format2 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph\n" m m)
in FStar_Absyn_Syntax.Err (_161_231))
in (Prims.raise _161_232))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))

# 621 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _69_713 -> (match (_69_713) with
| (f, deps) -> begin
(
# 628 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 630 "FStar.Parser.Dep.fst"
let print = (fun _69_720 -> (match (_69_720) with
| (make_deps, _69_718, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_69_726) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





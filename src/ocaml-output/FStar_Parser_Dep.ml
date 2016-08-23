
open Prims
# 34 "FStar.Parser.Dep.fst"
type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut

# 44 "FStar.Parser.Dep.fst"
let is_VerifyAll = (fun _discr_ -> (match (_discr_) with
| VerifyAll (_) -> begin
true
end
| _ -> begin
false
end))

# 45 "FStar.Parser.Dep.fst"
let is_VerifyUserList = (fun _discr_ -> (match (_discr_) with
| VerifyUserList (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Parser.Dep.fst"
let is_VerifyFigureItOut = (fun _discr_ -> (match (_discr_) with
| VerifyFigureItOut (_) -> begin
true
end
| _ -> begin
false
end))

# 46 "FStar.Parser.Dep.fst"
type map =
(Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap

# 48 "FStar.Parser.Dep.fst"
let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (
# 51 "FStar.Parser.Dep.fst"
let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (
# 52 "FStar.Parser.Dep.fst"
let matches = (FStar_List.map (fun ext -> (
# 53 "FStar.Parser.Dep.fst"
let lext = (FStar_String.length ext)
in (
# 54 "FStar.Parser.Dep.fst"
let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _162_7 = (FStar_String.substring f 0 (l - lext))
in Some (_162_7))
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

# 64 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 68 "FStar.Parser.Dep.fst"
let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (not ((is_interface f))))

# 71 "FStar.Parser.Dep.fst"
let list_of_option = (fun _69_1 -> (match (_69_1) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))

# 73 "FStar.Parser.Dep.fst"
let list_of_pair = (fun _69_33 -> (match (_69_33) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))

# 76 "FStar.Parser.Dep.fst"
let must_find_stratified = (fun m k -> (match ((let _162_16 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _162_16))) with
| (Some (intf), _69_39) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end))

# 87 "FStar.Parser.Dep.fst"
let must_find_universes = (fun m k -> (let _162_20 = (let _162_19 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _162_19))
in (list_of_pair _162_20)))

# 90 "FStar.Parser.Dep.fst"
let must_find = (fun m k -> if (FStar_Options.universes ()) then begin
(must_find_universes m k)
end else begin
(must_find_stratified m k)
end)

# 96 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _162_29 = (let _162_28 = (FStar_Util.smap_keys m)
in (FStar_List.unique _162_28))
in (FStar_List.iter (fun k -> (let _162_27 = (must_find m k)
in (FStar_List.iter (fun f -> (FStar_Util.print2 "%s: %s\n" k f)) _162_27))) _162_29)))

# 103 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _162_32 = (FStar_Util.basename f)
in (check_and_strip_suffix _162_32))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _162_34 = (let _162_33 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_162_33))
in (Prims.raise _162_34))
end))

# 118 "FStar.Parser.Dep.fst"
let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (
# 119 "FStar.Parser.Dep.fst"
let include_directories = (FStar_Options.include_path ())
in (
# 120 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (
# 123 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.unique include_directories)
in (
# 124 "FStar.Parser.Dep.fst"
let cwd = (let _162_37 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _162_37))
in (
# 125 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 126 "FStar.Parser.Dep.fst"
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
# 139 "FStar.Parser.Dep.fst"
let _69_82 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(
# 141 "FStar.Parser.Dep.fst"
let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (
# 143 "FStar.Parser.Dep.fst"
let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(
# 146 "FStar.Parser.Dep.fst"
let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (
# 147 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| None -> begin
()
end))) files))
end else begin
(let _162_45 = (let _162_44 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Absyn_Syntax.Err (_162_44))
in (Prims.raise _162_45))
end) include_directories)
in (
# 156 "FStar.Parser.Dep.fst"
let _69_85 = (FStar_List.iter (fun f -> (let _162_47 = (lowercase_module_name f)
in (add_entry _162_47 f))) filenames)
in map)))))))))

# 165 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 166 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 167 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 168 "FStar.Parser.Dep.fst"
let _69_97 = (let _162_57 = (let _162_56 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _162_56))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 170 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 173 "FStar.Parser.Dep.fst"
let filename = (let _162_55 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _162_55))
in (
# 174 "FStar.Parser.Dep.fst"
let _69_95 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _162_57))
in (FStar_ST.read found)))))

# 177 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 181 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 182 "FStar.Parser.Dep.fst"
let names = (let _162_63 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _162_63 suffix))
in (FStar_String.concat "." names))))

# 188 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _162_68 = (string_of_lid l last)
in (FStar_String.lowercase _162_68)))

# 189 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 193 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _162_75 = (let _162_74 = (let _162_73 = (FStar_Util.basename filename)
in (check_and_strip_suffix _162_73))
in (FStar_Util.must _162_74))
in (FStar_String.lowercase _162_75)) <> k') then begin
(let _162_77 = (let _162_76 = (string_of_lid lid true)
in (_162_76)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _162_77))
end else begin
()
end))

# 199 "FStar.Parser.Dep.fst"
exception Exit

# 199 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 203 "FStar.Parser.Dep.fst"
let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (
# 204 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 205 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _162_92 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _162_92)))) then begin
(let _162_94 = (let _162_93 = (FStar_ST.read deps)
in (d)::_162_93)
in (FStar_ST.op_Colon_Equals deps _162_94))
end else begin
()
end)
in (
# 209 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 211 "FStar.Parser.Dep.fst"
let record_open = (fun let_open lid -> (
# 212 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _162_100 = (lowercase_module_name f)
in (add_dep _162_100))) (list_of_pair pair))
end
| None -> begin
(
# 217 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
if let_open then begin
(Prims.raise (FStar_Absyn_Syntax.Err ("let-open only supported for modules, not namespaces")))
end else begin
(let _162_102 = (let _162_101 = (string_of_lid lid true)
in (_162_101)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _162_102))
end
end else begin
()
end)
end)))
in (
# 227 "FStar.Parser.Dep.fst"
let record_module_alias = (fun ident lid -> (
# 228 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (
# 229 "FStar.Parser.Dep.fst"
let alias = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map alias)) with
| Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| None -> begin
(let _162_108 = (let _162_107 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Absyn_Syntax.Err (_162_107))
in (Prims.raise _162_108))
end))))
in (
# 237 "FStar.Parser.Dep.fst"
let record_lid = (fun is_constructor lid -> if (lid.FStar_Ident.ident.FStar_Ident.idText <> "reflect") then begin
(
# 239 "FStar.Parser.Dep.fst"
let try_key = (fun key -> (match ((FStar_Util.smap_try_find working_map key)) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (let _162_116 = (lowercase_module_name f)
in (add_dep _162_116))) (list_of_pair pair))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && (FStar_Options.debug_any ())) then begin
(let _162_118 = (let _162_117 = (string_of_lid lid false)
in (_162_117)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _162_118))
end else begin
()
end
end))
in (
# 249 "FStar.Parser.Dep.fst"
let _69_145 = (let _162_119 = (lowercase_join_longident lid false)
in (try_key _162_119))
in if is_constructor then begin
(let _162_120 = (lowercase_join_longident lid true)
in (try_key _162_120))
end else begin
()
end))
end else begin
()
end)
in (
# 258 "FStar.Parser.Dep.fst"
let auto_open = if ((FStar_Util.basename filename) = "prims.fst") then begin
[]
end else begin
if (let _162_122 = (let _162_121 = (FStar_Util.basename filename)
in (FStar_String.lowercase _162_121))
in (FStar_Util.starts_with _162_122 "fstar.")) then begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::[]
end else begin
(FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
end
end
in (
# 266 "FStar.Parser.Dep.fst"
let _69_148 = (FStar_List.iter (record_open false) auto_open)
in (
# 268 "FStar.Parser.Dep.fst"
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
# 278 "FStar.Parser.Dep.fst"
let _69_176 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _69_4 -> (match (_69_4) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 284 "FStar.Parser.Dep.fst"
let _69_187 = (check_module_declaration_against_filename lid filename)
in (
# 285 "FStar.Parser.Dep.fst"
let _69_195 = (match (verify_mode) with
| VerifyAll -> begin
(let _162_143 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _162_143))
end
| VerifyFigureItOut -> begin
if is_user_provided_filename then begin
(let _162_144 = (string_of_lid lid true)
in (FStar_Options.add_verify_module _162_144))
end else begin
()
end
end
| VerifyUserList -> begin
(FStar_List.iter (fun _69_194 -> (match (_69_194) with
| (m, r) -> begin
if ((FStar_String.lowercase m) = (let _162_146 = (string_of_lid lid true)
in (FStar_String.lowercase _162_146))) then begin
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
# 306 "FStar.Parser.Dep.fst"
let _69_206 = (let _162_150 = (lowercase_join_longident lid true)
in (add_dep _162_150))
in (record_module_alias ident lid))
end
| FStar_Parser_AST.ToplevelLet (_69_209, _69_211, patterms) -> begin
(FStar_List.iter (fun _69_217 -> (match (_69_217) with
| (pat, t) -> begin
(
# 309 "FStar.Parser.Dep.fst"
let _69_218 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_69_221, binders, t) -> begin
(
# 311 "FStar.Parser.Dep.fst"
let _69_226 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _69_256; FStar_Parser_AST.mdest = _69_254; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
(
# 319 "FStar.Parser.Dep.fst"
let _69_259 = (collect_term t0)
in (collect_term t1))
end
| FStar_Parser_AST.Tycon (_69_262, ts) -> begin
(
# 322 "FStar.Parser.Dep.fst"
let ts = (FStar_List.map (fun _69_268 -> (match (_69_268) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (_69_271, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (_, ed)) | (FStar_Parser_AST.NewEffect (_, ed)) -> begin
(collect_effect_decl ed)
end
| (FStar_Parser_AST.Fsdoc (_)) | (FStar_Parser_AST.Pragma (_)) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
(let _162_155 = (let _162_154 = (let _162_153 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" _162_153))
in FStar_Absyn_Syntax.Err (_162_154))
in (Prims.raise _162_155))
end))
and collect_tycon = (fun _69_6 -> (match (_69_6) with
| FStar_Parser_AST.TyconAbstract (_69_294, binders, k) -> begin
(
# 338 "FStar.Parser.Dep.fst"
let _69_299 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_69_302, binders, k, t) -> begin
(
# 341 "FStar.Parser.Dep.fst"
let _69_308 = (collect_binders binders)
in (
# 342 "FStar.Parser.Dep.fst"
let _69_310 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_69_313, binders, k, identterms) -> begin
(
# 345 "FStar.Parser.Dep.fst"
let _69_319 = (collect_binders binders)
in (
# 346 "FStar.Parser.Dep.fst"
let _69_321 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _69_328 -> (match (_69_328) with
| (_69_324, t, _69_327) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_69_330, binders, k, identterms) -> begin
(
# 349 "FStar.Parser.Dep.fst"
let _69_336 = (collect_binders binders)
in (
# 350 "FStar.Parser.Dep.fst"
let _69_338 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _69_347 -> (match (_69_347) with
| (_69_341, t, _69_344, _69_346) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _69_7 -> (match (_69_7) with
| FStar_Parser_AST.DefineEffect (_69_350, binders, t, decls, actions) -> begin
(
# 355 "FStar.Parser.Dep.fst"
let _69_357 = (collect_binders binders)
in (
# 356 "FStar.Parser.Dep.fst"
let _69_359 = (collect_term t)
in (
# 357 "FStar.Parser.Dep.fst"
let _69_361 = (collect_decls decls)
in (collect_decls actions))))
end
| FStar_Parser_AST.RedefineEffect (_69_364, binders, t) -> begin
(
# 360 "FStar.Parser.Dep.fst"
let _69_369 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _69_8 -> (match (_69_8) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _69_405 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun _69_9 -> (match (_69_9) with
| FStar_Const.Const_int (_69_409, Some (signedness, width)) -> begin
(
# 379 "FStar.Parser.Dep.fst"
let u = (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)
in (
# 380 "FStar.Parser.Dep.fst"
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
in (let _162_164 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep _162_164))))
end
| _69_425 -> begin
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
# 391 "FStar.Parser.Dep.fst"
let _69_434 = if (s = "@") then begin
(let _162_167 = (let _162_166 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (_162_166))
in (collect_term' _162_167))
end else begin
()
end
in (FStar_List.iter collect_term ts))
end
| FStar_Parser_AST.Tvar (_69_437) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(record_lid false lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
(
# 400 "FStar.Parser.Dep.fst"
let _69_446 = if (((FStar_List.length termimps) = 1) && (FStar_Options.universes ())) then begin
(record_lid true lid)
end else begin
()
end
in (FStar_List.iter (fun _69_451 -> (match (_69_451) with
| (t, _69_450) -> begin
(collect_term t)
end)) termimps))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 404 "FStar.Parser.Dep.fst"
let _69_456 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _69_461) -> begin
(
# 407 "FStar.Parser.Dep.fst"
let _69_464 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_69_467, patterms, t) -> begin
(
# 410 "FStar.Parser.Dep.fst"
let _69_477 = (FStar_List.iter (fun _69_474 -> (match (_69_474) with
| (pat, t) -> begin
(
# 410 "FStar.Parser.Dep.fst"
let _69_475 = (collect_pattern pat)
in (collect_term t))
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
(
# 413 "FStar.Parser.Dep.fst"
let _69_483 = (record_open true lid)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 416 "FStar.Parser.Dep.fst"
let _69_489 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 419 "FStar.Parser.Dep.fst"
let _69_496 = (collect_term t1)
in (
# 420 "FStar.Parser.Dep.fst"
let _69_498 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 424 "FStar.Parser.Dep.fst"
let _69_506 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 427 "FStar.Parser.Dep.fst"
let _69_512 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(
# 430 "FStar.Parser.Dep.fst"
let _69_518 = (FStar_Util.iter_opt t collect_term)
in (FStar_List.iter (fun _69_523 -> (match (_69_523) with
| (_69_521, t) -> begin
(collect_term t)
end)) idterms))
end
| FStar_Parser_AST.Project (t, _69_526) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 436 "FStar.Parser.Dep.fst"
let _69_535 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 440 "FStar.Parser.Dep.fst"
let _69_544 = (collect_binders binders)
in (
# 441 "FStar.Parser.Dep.fst"
let _69_546 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 444 "FStar.Parser.Dep.fst"
let _69_552 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_69_555, t) -> begin
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
# 468 "FStar.Parser.Dep.fst"
let _69_594 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _69_617 -> (match (_69_617) with
| (_69_615, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 481 "FStar.Parser.Dep.fst"
let _69_622 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _69_628 -> (match (_69_628) with
| (pat, t1, t2) -> begin
(
# 489 "FStar.Parser.Dep.fst"
let _69_629 = (collect_pattern pat)
in (
# 490 "FStar.Parser.Dep.fst"
let _69_631 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 494 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file filename)
in (
# 495 "FStar.Parser.Dep.fst"
let _69_634 = (collect_file ast)
in (FStar_ST.read deps)))))))))))))

# 497 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 499 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 499 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 499 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 499 "FStar.Parser.Dep.fst"
let print_graph = (fun graph -> (
# 502 "FStar.Parser.Dep.fst"
let _69_637 = (FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph")
in (
# 503 "FStar.Parser.Dep.fst"
let _69_639 = (FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph")
in (
# 504 "FStar.Parser.Dep.fst"
let _69_641 = (FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims")
in (let _162_192 = (let _162_191 = (let _162_190 = (let _162_189 = (let _162_188 = (let _162_187 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _162_187))
in (FStar_List.collect (fun k -> (
# 508 "FStar.Parser.Dep.fst"
let deps = (let _162_183 = (let _162_182 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _162_182))
in (Prims.fst _162_183))
in (
# 509 "FStar.Parser.Dep.fst"
let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) _162_188))
in (FStar_String.concat "\n" _162_189))
in (Prims.strcat _162_190 "\n}\n"))
in (Prims.strcat "digraph {\n" _162_191))
in (FStar_Util.write_file "dep.graph" _162_192))))))

# 516 "FStar.Parser.Dep.fst"
let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (
# 519 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 523 "FStar.Parser.Dep.fst"
let verify_flags = (let _162_199 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (let _162_198 = (FStar_ST.alloc false)
in ((f), (_162_198)))) _162_199))
in (
# 528 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 539 "FStar.Parser.Dep.fst"
let collect_one = (collect_one verify_flags verify_mode)
in (
# 542 "FStar.Parser.Dep.fst"
let rec discover_one = (fun is_user_provided_filename key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 545 "FStar.Parser.Dep.fst"
let _69_660 = (let _162_207 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _162_207))
in (match (_69_660) with
| (intf, impl) -> begin
(
# 546 "FStar.Parser.Dep.fst"
let intf_deps = (match (intf) with
| None -> begin
[]
end
| Some (intf) -> begin
(collect_one is_user_provided_filename m intf)
end)
in (
# 551 "FStar.Parser.Dep.fst"
let impl_deps = (match (impl) with
| None -> begin
[]
end
| Some (impl) -> begin
(collect_one is_user_provided_filename m impl)
end)
in (
# 556 "FStar.Parser.Dep.fst"
let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in (
# 557 "FStar.Parser.Dep.fst"
let _69_670 = (FStar_Util.smap_add graph key ((deps), (White)))
in (FStar_List.iter (discover_one false) deps)))))
end))
end else begin
()
end)
in (
# 560 "FStar.Parser.Dep.fst"
let _69_672 = (let _162_208 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter (discover_one true) _162_208))
in (
# 563 "FStar.Parser.Dep.fst"
let immediate_graph = (FStar_Util.smap_copy graph)
in (
# 565 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 568 "FStar.Parser.Dep.fst"
let rec discover = (fun cycle key -> (
# 569 "FStar.Parser.Dep.fst"
let _69_681 = (let _162_213 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _162_213))
in (match (_69_681) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 572 "FStar.Parser.Dep.fst"
let _69_683 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 573 "FStar.Parser.Dep.fst"
let _69_685 = (FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle))
in (
# 574 "FStar.Parser.Dep.fst"
let _69_687 = (print_graph immediate_graph)
in (
# 575 "FStar.Parser.Dep.fst"
let _69_689 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 583 "FStar.Parser.Dep.fst"
let _69_693 = (FStar_Util.smap_add graph key ((direct_deps), (Gray)))
in (
# 584 "FStar.Parser.Dep.fst"
let all_deps = (let _162_217 = (let _162_216 = (FStar_List.map (fun dep -> (let _162_215 = (discover ((key)::cycle) dep)
in (dep)::_162_215)) direct_deps)
in (FStar_List.flatten _162_216))
in (FStar_List.unique _162_217))
in (
# 588 "FStar.Parser.Dep.fst"
let _69_697 = (FStar_Util.smap_add graph key ((all_deps), (Black)))
in (
# 590 "FStar.Parser.Dep.fst"
let _69_699 = (let _162_219 = (let _162_218 = (FStar_ST.read topologically_sorted)
in (key)::_162_218)
in (FStar_ST.op_Colon_Equals topologically_sorted _162_219))
in all_deps))))
end)
end)))
in (
# 594 "FStar.Parser.Dep.fst"
let discover = (discover [])
in (
# 596 "FStar.Parser.Dep.fst"
let must_find = (must_find m)
in (
# 597 "FStar.Parser.Dep.fst"
let must_find_r = (fun f -> (let _162_224 = (must_find f)
in (FStar_List.rev _162_224)))
in (
# 598 "FStar.Parser.Dep.fst"
let by_target = (let _162_229 = (FStar_Util.smap_keys graph)
in (FStar_List.collect (fun k -> (
# 599 "FStar.Parser.Dep.fst"
let as_list = (must_find k)
in (
# 600 "FStar.Parser.Dep.fst"
let is_interleaved = ((FStar_List.length as_list) = 2)
in (FStar_List.map (fun f -> (
# 602 "FStar.Parser.Dep.fst"
let should_append_fsti = ((is_implementation f) && is_interleaved)
in (
# 603 "FStar.Parser.Dep.fst"
let suffix = if should_append_fsti then begin
((Prims.strcat f "i"))::[]
end else begin
[]
end
in (
# 604 "FStar.Parser.Dep.fst"
let k = (lowercase_module_name f)
in (
# 605 "FStar.Parser.Dep.fst"
let deps = (let _162_227 = (discover k)
in (FStar_List.rev _162_227))
in (
# 606 "FStar.Parser.Dep.fst"
let deps_as_filenames = (let _162_228 = (FStar_List.collect must_find deps)
in (FStar_List.append _162_228 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) _162_229))
in (
# 611 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _162_230 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r _162_230))
in (
# 613 "FStar.Parser.Dep.fst"
let _69_719 = (FStar_List.iter (fun _69_718 -> (match (_69_718) with
| (m, r) -> begin
if ((not ((FStar_ST.read r))) && (not ((FStar_Options.interactive ())))) then begin
(let _162_233 = (let _162_232 = (FStar_Util.format2 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph\n" m m)
in FStar_Absyn_Syntax.Err (_162_232))
in (Prims.raise _162_233))
end else begin
()
end
end)) verify_flags)
in ((by_target), (topologically_sorted), (immediate_graph))))))))))))))))))

# 627 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _69_724 -> (match (_69_724) with
| (f, deps) -> begin
(
# 629 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 631 "FStar.Parser.Dep.fst"
let print = (fun _69_731 -> (match (_69_731) with
| (make_deps, _69_729, graph) -> begin
(match ((FStar_Options.dep ())) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (_69_737) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end)
end))





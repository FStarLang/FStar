
open Prims
# 36 "FStar.Parser.Dep.fst"
type map =
Prims.string FStar_Util.smap

# 38 "FStar.Parser.Dep.fst"
let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (
# 39 "FStar.Parser.Dep.fst"
let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (
# 40 "FStar.Parser.Dep.fst"
let matches = (FStar_List.map (fun ext -> (
# 41 "FStar.Parser.Dep.fst"
let lext = (FStar_String.length ext)
in (
# 42 "FStar.Parser.Dep.fst"
let l = (FStar_String.length f)
in if ((l > lext) && ((FStar_String.substring f (l - lext) lext) = ext)) then begin
(let _136_4 = (FStar_String.substring f 0 (l - lext))
in Some (_136_4))
end else begin
None
end))) suffixes)
in (match ((FStar_List.filter FStar_Util.is_some matches)) with
| Some (m)::_57_17 -> begin
Some (m)
end
| _57_22 -> begin
None
end))))

# 55 "FStar.Parser.Dep.fst"
let is_interface : Prims.string  ->  Prims.bool = (fun f -> ((FStar_String.get f ((FStar_String.length f) - 1)) = 'i'))

# 58 "FStar.Parser.Dep.fst"
let print_map : map  ->  Prims.unit = (fun m -> (let _136_13 = (let _136_12 = (FStar_Util.smap_keys m)
in (FStar_List.unique _136_12))
in (FStar_List.iter (fun k -> (let _136_11 = (let _136_10 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _136_10))
in (FStar_Util.print2 "%s: %s\n" k _136_11))) _136_13)))

# 64 "FStar.Parser.Dep.fst"
let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (match ((let _136_16 = (FStar_Util.basename f)
in (check_and_strip_suffix _136_16))) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(let _136_18 = (let _136_17 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Absyn_Syntax.Err (_136_17))
in (Prims.raise _136_18))
end))

# 74 "FStar.Parser.Dep.fst"
let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (
# 75 "FStar.Parser.Dep.fst"
let include_directories = (FStar_Options.get_include_path ())
in (
# 76 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (
# 77 "FStar.Parser.Dep.fst"
let include_directories = (FStar_List.unique include_directories)
in (
# 78 "FStar.Parser.Dep.fst"
let cwd = (let _136_21 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path _136_21))
in (
# 79 "FStar.Parser.Dep.fst"
let map = (FStar_Util.smap_create 41)
in (
# 80 "FStar.Parser.Dep.fst"
let _57_52 = (FStar_List.iter (fun d -> if (FStar_Util.file_exists d) then begin
(
# 82 "FStar.Parser.Dep.fst"
let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (
# 84 "FStar.Parser.Dep.fst"
let f = (FStar_Util.basename f)
in (match ((check_and_strip_suffix f)) with
| Some (longname) -> begin
(
# 87 "FStar.Parser.Dep.fst"
let key = (FStar_String.lowercase longname)
in (
# 88 "FStar.Parser.Dep.fst"
let full_path = if (d = cwd) then begin
f
end else begin
(FStar_Util.join_paths d f)
end
in (match ((FStar_Util.smap_try_find map key)) with
| Some (existing_file) -> begin
(
# 91 "FStar.Parser.Dep.fst"
let _57_46 = if ((FStar_String.lowercase existing_file) = (FStar_String.lowercase f)) then begin
(let _136_25 = (let _136_24 = (FStar_Util.format1 "I\'m case insensitive, and I found the same file twice (%s)\n" f)
in FStar_Absyn_Syntax.Err (_136_24))
in (Prims.raise _136_25))
end else begin
()
end
in (
# 93 "FStar.Parser.Dep.fst"
let _57_48 = if ((is_interface existing_file) = (is_interface f)) then begin
(let _136_27 = (let _136_26 = (FStar_Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)\n" f)
in FStar_Absyn_Syntax.Err (_136_26))
in (Prims.raise _136_27))
end else begin
()
end
in if (not ((is_interface existing_file))) then begin
(FStar_Util.smap_add map key full_path)
end else begin
()
end))
end
| None -> begin
(FStar_Util.smap_add map key full_path)
end)))
end
| None -> begin
()
end))) files))
end else begin
()
end) include_directories)
in (
# 106 "FStar.Parser.Dep.fst"
let _57_55 = (FStar_List.iter (fun f -> (let _136_29 = (lowercase_module_name f)
in (FStar_Util.smap_add map _136_29 f))) filenames)
in map))))))))

# 115 "FStar.Parser.Dep.fst"
let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (
# 116 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc false)
in (
# 117 "FStar.Parser.Dep.fst"
let prefix = (Prims.strcat prefix ".")
in (
# 118 "FStar.Parser.Dep.fst"
let _57_67 = (let _136_39 = (let _136_38 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique _136_38))
in (FStar_List.iter (fun k -> if (FStar_Util.starts_with k prefix) then begin
(
# 120 "FStar.Parser.Dep.fst"
let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (
# 123 "FStar.Parser.Dep.fst"
let filename = (let _136_37 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must _136_37))
in (
# 124 "FStar.Parser.Dep.fst"
let _57_65 = (FStar_Util.smap_add working_map suffix filename)
in (FStar_ST.op_Colon_Equals found true))))
end else begin
()
end) _136_39))
in (FStar_ST.read found)))))

# 130 "FStar.Parser.Dep.fst"
let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (
# 131 "FStar.Parser.Dep.fst"
let suffix = if last then begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end else begin
[]
end
in (
# 132 "FStar.Parser.Dep.fst"
let names = (let _136_45 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append _136_45 suffix))
in (FStar_String.concat "." names))))

# 137 "FStar.Parser.Dep.fst"
let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (let _136_50 = (string_of_lid l last)
in (FStar_String.lowercase _136_50)))

# 141 "FStar.Parser.Dep.fst"
let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (
# 142 "FStar.Parser.Dep.fst"
let k' = (lowercase_join_longident lid true)
in if ((let _136_57 = (let _136_56 = (let _136_55 = (FStar_Util.basename filename)
in (check_and_strip_suffix _136_55))
in (FStar_Util.must _136_56))
in (FStar_String.lowercase _136_57)) <> k') then begin
(let _136_59 = (let _136_58 = (string_of_lid lid true)
in (_136_58)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" _136_59))
end else begin
()
end))

# 148 "FStar.Parser.Dep.fst"
exception Exit

# 148 "FStar.Parser.Dep.fst"
let is_Exit = (fun _discr_ -> (match (_discr_) with
| Exit (_) -> begin
true
end
| _ -> begin
false
end))

# 152 "FStar.Parser.Dep.fst"
let collect_one : Prims.string FStar_Util.smap  ->  Prims.string  ->  Prims.string Prims.list = (fun original_map filename -> (
# 153 "FStar.Parser.Dep.fst"
let deps = (FStar_ST.alloc [])
in (
# 154 "FStar.Parser.Dep.fst"
let add_dep = (fun d -> if (not ((let _136_68 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) _136_68)))) then begin
(let _136_70 = (let _136_69 = (FStar_ST.read deps)
in (d)::_136_69)
in (FStar_ST.op_Colon_Equals deps _136_70))
end else begin
()
end)
in (
# 158 "FStar.Parser.Dep.fst"
let working_map = (FStar_Util.smap_copy original_map)
in (
# 160 "FStar.Parser.Dep.fst"
let record_open = (fun lid -> (
# 161 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid true)
in (match ((FStar_Util.smap_try_find original_map key)) with
| Some (filename) -> begin
(let _136_73 = (lowercase_module_name filename)
in (add_dep _136_73))
end
| None -> begin
(
# 166 "FStar.Parser.Dep.fst"
let r = (enter_namespace original_map working_map key)
in if (not (r)) then begin
(let _136_75 = (let _136_74 = (string_of_lid lid true)
in (_136_74)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" _136_75))
end else begin
()
end)
end)))
in (
# 175 "FStar.Parser.Dep.fst"
let auto_open = (
# 176 "FStar.Parser.Dep.fst"
let index_of = (fun s l -> (
# 177 "FStar.Parser.Dep.fst"
let found = (FStar_ST.alloc (- (1)))
in (FStar_All.try_with (fun _57_98 -> (match (()) with
| () -> begin
(
# 179 "FStar.Parser.Dep.fst"
let _57_107 = (FStar_List.iteri (fun i x -> if (s = x) then begin
(
# 181 "FStar.Parser.Dep.fst"
let _57_105 = (FStar_ST.op_Colon_Equals found i)
in (Prims.raise Exit))
end else begin
()
end) l)
in (- (1)))
end)) (fun _57_97 -> (match (_57_97) with
| Exit -> begin
(FStar_ST.read found)
end)))))
in (
# 190 "FStar.Parser.Dep.fst"
let ordered = ("fstar")::("prims")::("fstar.functionalextensionality")::("fstar.set")::("fstar.heap")::("fstar.st")::("fstar.all")::[]
in (
# 192 "FStar.Parser.Dep.fst"
let desired_opens = (FStar_Absyn_Const.fstar_ns_lid)::(FStar_Absyn_Const.prims_lid)::(FStar_Absyn_Const.st_lid)::(FStar_Absyn_Const.all_lid)::[]
in (
# 193 "FStar.Parser.Dep.fst"
let me = (let _136_86 = (let _136_85 = (let _136_84 = (FStar_Util.basename filename)
in (check_and_strip_suffix _136_84))
in (FStar_Util.must _136_85))
in (FStar_String.lowercase _136_86))
in (
# 194 "FStar.Parser.Dep.fst"
let index_or_length = (fun s l -> (
# 195 "FStar.Parser.Dep.fst"
let i = (index_of s l)
in if (i < 0) then begin
(FStar_List.length l)
end else begin
i
end))
in (
# 198 "FStar.Parser.Dep.fst"
let my_index = (index_or_length me ordered)
in (FStar_List.filter (fun lid -> ((let _136_92 = (lowercase_join_longident lid true)
in (index_or_length _136_92 ordered)) < my_index)) desired_opens)))))))
in (
# 201 "FStar.Parser.Dep.fst"
let _57_119 = (FStar_List.iter record_open auto_open)
in (
# 203 "FStar.Parser.Dep.fst"
let rec collect_fragment = (fun _57_1 -> (match (_57_1) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun _57_2 -> (match (_57_2) with
| modul::[] -> begin
(collect_module modul)
end
| modules -> begin
(
# 213 "FStar.Parser.Dep.fst"
let _57_146 = (FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]))
in (FStar_List.iter collect_module modules))
end))
and collect_module = (fun _57_3 -> (match (_57_3) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
(
# 219 "FStar.Parser.Dep.fst"
let _57_157 = (check_module_declaration_against_filename lid filename)
in (collect_decls decls))
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> (collect_decl x.FStar_Parser_AST.d)) decls))
and collect_decl = (fun _57_4 -> (match (_57_4) with
| FStar_Parser_AST.Open (lid) -> begin
(record_open lid)
end
| FStar_Parser_AST.ToplevelLet (_57_165, _57_167, patterms) -> begin
(FStar_List.iter (fun _57_174 -> (match (_57_174) with
| (_57_172, t) -> begin
(collect_term t)
end)) patterms)
end
| FStar_Parser_AST.KindAbbrev (_57_176, binders, t) -> begin
(
# 231 "FStar.Parser.Dep.fst"
let _57_181 = (collect_term t)
in (collect_binders binders))
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, _, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = t})) | (FStar_Parser_AST.Val (_, _, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.Tycon (_57_204, ts) -> begin
(FStar_List.iter collect_tycon ts)
end
| FStar_Parser_AST.Exception (_57_209, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (_57_214, ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Pragma (_57_219) -> begin
()
end))
and collect_tycon = (fun _57_5 -> (match (_57_5) with
| FStar_Parser_AST.TyconAbstract (_57_223, binders, k) -> begin
(
# 249 "FStar.Parser.Dep.fst"
let _57_228 = (collect_binders binders)
in (FStar_Util.iter_opt k collect_term))
end
| FStar_Parser_AST.TyconAbbrev (_57_231, binders, k, t) -> begin
(
# 252 "FStar.Parser.Dep.fst"
let _57_237 = (collect_binders binders)
in (
# 253 "FStar.Parser.Dep.fst"
let _57_239 = (FStar_Util.iter_opt k collect_term)
in (collect_term t)))
end
| FStar_Parser_AST.TyconRecord (_57_242, binders, k, identterms) -> begin
(
# 256 "FStar.Parser.Dep.fst"
let _57_248 = (collect_binders binders)
in (
# 257 "FStar.Parser.Dep.fst"
let _57_250 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _57_255 -> (match (_57_255) with
| (_57_253, t) -> begin
(collect_term t)
end)) identterms)))
end
| FStar_Parser_AST.TyconVariant (_57_257, binders, k, identterms) -> begin
(
# 260 "FStar.Parser.Dep.fst"
let _57_263 = (collect_binders binders)
in (
# 261 "FStar.Parser.Dep.fst"
let _57_265 = (FStar_Util.iter_opt k collect_term)
in (FStar_List.iter (fun _57_272 -> (match (_57_272) with
| (_57_268, t, _57_271) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms)))
end))
and collect_effect_decl = (fun _57_6 -> (match (_57_6) with
| FStar_Parser_AST.DefineEffect (_57_275, binders, t, decls) -> begin
(
# 266 "FStar.Parser.Dep.fst"
let _57_281 = (collect_binders binders)
in (
# 267 "FStar.Parser.Dep.fst"
let _57_283 = (collect_term t)
in (collect_decls decls)))
end
| FStar_Parser_AST.RedefineEffect (_57_286, binders, t) -> begin
(
# 270 "FStar.Parser.Dep.fst"
let _57_291 = (collect_binders binders)
in (collect_term t))
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun _57_7 -> (match (_57_7) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| _57_319 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_term' = (fun _57_8 -> (match (_57_8) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (_57_324) -> begin
()
end
| FStar_Parser_AST.Op (_57_327, ts) -> begin
(FStar_List.iter collect_term ts)
end
| FStar_Parser_AST.Tvar (_57_332) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(
# 298 "FStar.Parser.Dep.fst"
let key = (lowercase_join_longident lid false)
in (match ((FStar_Util.smap_try_find working_map key)) with
| Some (filename) -> begin
(let _136_124 = (lowercase_module_name filename)
in (add_dep _136_124))
end
| None -> begin
if (((FStar_List.length lid.FStar_Ident.ns) > 0) && ((FStar_ST.read FStar_Options.debug) <> [])) then begin
(let _136_126 = (let _136_125 = (string_of_lid lid false)
in (_136_125)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" _136_126))
end else begin
()
end
end))
end
| FStar_Parser_AST.Construct (_57_342, termimps) -> begin
(FStar_List.iter (fun _57_349 -> (match (_57_349) with
| (t, _57_348) -> begin
(collect_term t)
end)) termimps)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 310 "FStar.Parser.Dep.fst"
let _57_354 = (collect_patterns pats)
in (collect_term t))
end
| FStar_Parser_AST.App (t1, t2, _57_359) -> begin
(
# 313 "FStar.Parser.Dep.fst"
let _57_362 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Let (_57_365, patterms, t) -> begin
(
# 316 "FStar.Parser.Dep.fst"
let _57_374 = (FStar_List.iter (fun _57_373 -> (match (_57_373) with
| (_57_371, t) -> begin
(collect_term t)
end)) patterms)
in (collect_term t))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(
# 319 "FStar.Parser.Dep.fst"
let _57_380 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 322 "FStar.Parser.Dep.fst"
let _57_387 = (collect_term t1)
in (
# 323 "FStar.Parser.Dep.fst"
let _57_389 = (collect_term t2)
in (collect_term t3)))
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
(
# 327 "FStar.Parser.Dep.fst"
let _57_397 = (collect_term t)
in (collect_branches bs))
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
(
# 330 "FStar.Parser.Dep.fst"
let _57_403 = (collect_term t1)
in (collect_term t2))
end
| FStar_Parser_AST.Record (t, idterms) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.Project (t, _57_411) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
(
# 338 "FStar.Parser.Dep.fst"
let _57_420 = (collect_binders binders)
in (collect_term t))
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
(
# 342 "FStar.Parser.Dep.fst"
let _57_429 = (collect_binders binders)
in (
# 343 "FStar.Parser.Dep.fst"
let _57_431 = (FStar_List.iter (FStar_List.iter collect_term) ts)
in (collect_term t)))
end
| FStar_Parser_AST.Refine (binder, t) -> begin
(
# 346 "FStar.Parser.Dep.fst"
let _57_437 = (collect_binder binder)
in (collect_term t))
end
| FStar_Parser_AST.NamedTyp (_57_440, t) -> begin
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
and collect_pattern' = (fun _57_9 -> (match (_57_9) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatConst (_57_466) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
(
# 369 "FStar.Parser.Dep.fst"
let _57_472 = (collect_pattern p)
in (collect_patterns ps))
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun _57_495 -> (match (_57_495) with
| (_57_493, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 382 "FStar.Parser.Dep.fst"
let _57_500 = (collect_pattern p)
in (collect_term t))
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun _57_506 -> (match (_57_506) with
| (pat, t1, t2) -> begin
(
# 390 "FStar.Parser.Dep.fst"
let _57_507 = (collect_pattern pat)
in (
# 391 "FStar.Parser.Dep.fst"
let _57_509 = (FStar_Util.iter_opt t1 collect_term)
in (collect_term t2)))
end))
in (
# 395 "FStar.Parser.Dep.fst"
let ast = (FStar_Parser_Driver.parse_file_raw filename)
in (
# 396 "FStar.Parser.Dep.fst"
let _57_512 = (collect_file ast)
in (FStar_ST.read deps)))))))))))

# 399 "FStar.Parser.Dep.fst"
type color =
| White
| Gray
| Black

# 399 "FStar.Parser.Dep.fst"
let is_White = (fun _discr_ -> (match (_discr_) with
| White (_) -> begin
true
end
| _ -> begin
false
end))

# 399 "FStar.Parser.Dep.fst"
let is_Gray = (fun _discr_ -> (match (_discr_) with
| Gray (_) -> begin
true
end
| _ -> begin
false
end))

# 399 "FStar.Parser.Dep.fst"
let is_Black = (fun _discr_ -> (match (_discr_) with
| Black (_) -> begin
true
end
| _ -> begin
false
end))

# 402 "FStar.Parser.Dep.fst"
let collect : Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list) = (fun filenames -> (
# 405 "FStar.Parser.Dep.fst"
let graph = (FStar_Util.smap_create 41)
in (
# 410 "FStar.Parser.Dep.fst"
let m = (build_map filenames)
in (
# 413 "FStar.Parser.Dep.fst"
let rec discover_one = (fun key -> if ((FStar_Util.smap_try_find graph key) = None) then begin
(
# 415 "FStar.Parser.Dep.fst"
let filename = (let _136_142 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must _136_142))
in (
# 416 "FStar.Parser.Dep.fst"
let deps = (collect_one m filename)
in (
# 417 "FStar.Parser.Dep.fst"
let _57_521 = (FStar_Util.smap_add graph key (deps, White))
in (FStar_List.iter discover_one deps))))
end else begin
()
end)
in (
# 420 "FStar.Parser.Dep.fst"
let _57_523 = (let _136_143 = (FStar_List.map lowercase_module_name filenames)
in (FStar_List.iter discover_one _136_143))
in (
# 423 "FStar.Parser.Dep.fst"
let print_graph = (fun _57_526 -> (match (()) with
| () -> begin
(let _136_152 = (let _136_151 = (FStar_Util.smap_keys graph)
in (FStar_List.unique _136_151))
in (FStar_List.iter (fun k -> (let _136_150 = (let _136_149 = (let _136_148 = (let _136_147 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must _136_147))
in (Prims.fst _136_148))
in (FStar_String.concat " " _136_149))
in (FStar_Util.print2 "%s: %s\n" k _136_150))) _136_152))
end))
in (
# 429 "FStar.Parser.Dep.fst"
let topologically_sorted = (FStar_ST.alloc [])
in (
# 432 "FStar.Parser.Dep.fst"
let rec discover = (fun key -> (
# 433 "FStar.Parser.Dep.fst"
let _57_533 = (let _136_155 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must _136_155))
in (match (_57_533) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
(
# 436 "FStar.Parser.Dep.fst"
let _57_535 = (FStar_Util.print1 "Warning: recursive dependency on module %s\n" key)
in (
# 437 "FStar.Parser.Dep.fst"
let _57_537 = (FStar_Util.print_string "Here\'s the (non-transitive) dependency graph:\n")
in (
# 438 "FStar.Parser.Dep.fst"
let _57_539 = (print_graph ())
in (
# 439 "FStar.Parser.Dep.fst"
let _57_541 = (FStar_Util.print_string "\n")
in (FStar_All.exit 1)))))
end
| Black -> begin
direct_deps
end
| White -> begin
(
# 447 "FStar.Parser.Dep.fst"
let _57_545 = (FStar_Util.smap_add graph key (direct_deps, Gray))
in (
# 448 "FStar.Parser.Dep.fst"
let all_deps = (let _136_159 = (let _136_158 = (FStar_List.map (fun dep -> (let _136_157 = (discover dep)
in (dep)::_136_157)) direct_deps)
in (FStar_List.flatten _136_158))
in (FStar_List.unique _136_159))
in (
# 452 "FStar.Parser.Dep.fst"
let _57_549 = (FStar_Util.smap_add graph key (all_deps, Black))
in (
# 454 "FStar.Parser.Dep.fst"
let _57_551 = (let _136_161 = (let _136_160 = (FStar_ST.read topologically_sorted)
in (key)::_136_160)
in (FStar_ST.op_Colon_Equals topologically_sorted _136_161))
in all_deps))))
end)
end)))
in (
# 459 "FStar.Parser.Dep.fst"
let must_find = (fun k -> (let _136_164 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must _136_164)))
in (
# 462 "FStar.Parser.Dep.fst"
let by_target = (let _136_169 = (FStar_Util.smap_keys graph)
in (FStar_List.map (fun k -> (
# 463 "FStar.Parser.Dep.fst"
let deps = (let _136_166 = (discover k)
in (FStar_List.rev _136_166))
in (let _136_168 = (must_find k)
in (let _136_167 = (FStar_List.map must_find deps)
in (_136_168, _136_167))))) _136_169))
in (
# 466 "FStar.Parser.Dep.fst"
let topologically_sorted = (let _136_170 = (FStar_ST.read topologically_sorted)
in (FStar_List.map must_find _136_170))
in (by_target, topologically_sorted))))))))))))

# 473 "FStar.Parser.Dep.fst"
let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun _57_562 -> (match (_57_562) with
| (f, deps) -> begin
(
# 475 "FStar.Parser.Dep.fst"
let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))

# 479 "FStar.Parser.Dep.fst"
let print_nubuild : Prims.string Prims.list  ->  Prims.unit = (fun l -> (FStar_List.iter FStar_Util.print_endline (FStar_List.rev l)))

# 482 "FStar.Parser.Dep.fst"
let print : ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list)  ->  Prims.unit = (fun deps -> (match ((FStar_ST.read FStar_Options.dep)) with
| Some ("nubuild") -> begin
(print_nubuild (Prims.snd deps))
end
| Some ("make") -> begin
(print_make (Prims.fst deps))
end
| Some (_57_572) -> begin
(Prims.raise (FStar_Absyn_Syntax.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))






open Prims
type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut


let uu___is_VerifyAll : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyAll -> begin
true
end
| uu____4 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____8 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____12 -> begin
false
end))


type map =
(Prims.string Prims.option * Prims.string Prims.option) FStar_Util.smap

type color =
| White
| Gray
| Black


let uu___is_White : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| White -> begin
true
end
| uu____21 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____25 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____29 -> begin
false
end))


let check_and_strip_suffix : Prims.string  ->  Prims.string Prims.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let matches = (FStar_List.map (fun ext -> (

let lext = (FStar_String.length ext)
in (

let l = (FStar_String.length f)
in (

let uu____46 = ((l > lext) && (

let uu____52 = (FStar_String.substring f (l - lext) lext)
in (uu____52 = ext)))
in (match (uu____46) with
| true -> begin
(

let uu____61 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in Some (uu____61))
end
| uu____67 -> begin
None
end))))) suffixes)
in (

let uu____68 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____68) with
| (Some (m))::uu____74 -> begin
Some (m)
end
| uu____78 -> begin
None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____84 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (uu____84 = 'i')))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____91 = (is_interface f)
in (not (uu____91))))


let list_of_option = (fun uu___129_100 -> (match (uu___129_100) with
| Some (x) -> begin
(x)::[]
end
| None -> begin
[]
end))


let list_of_pair = (fun uu____114 -> (match (uu____114) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____128 = (

let uu____130 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____130))
in (match (uu____128) with
| Some (longname) -> begin
(FStar_String.lowercase longname)
end
| None -> begin
(

let uu____132 = (

let uu____133 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Errors.Err (uu____133))
in (Prims.raise uu____132))
end)))


let try_convert_file_name_to_windows : Prims.string  ->  Prims.string = (fun s -> try
(match (()) with
| () -> begin
(

let uu____138 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (uu____138) with
| (uu____142, t_out, uu____144) -> begin
(match ((not (((FStar_Util.trim_string t_out) = "/usr/bin/cygpath")))) with
| true -> begin
s
end
| uu____145 -> begin
(

let uu____146 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (uu____146) with
| (uu____150, t_out, uu____152) -> begin
(FStar_Util.trim_string t_out)
end))
end)
end))
end)
with
| uu____154 -> begin
s
end)


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories = (FStar_List.map try_convert_file_name_to_windows include_directories)
in (

let include_directories = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories = (FStar_List.unique include_directories)
in (

let cwd = (

let uu____169 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____169))
in (

let map = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____187 = (FStar_Util.smap_try_find map key)
in (match (uu____187) with
| Some (intf, impl) -> begin
(

let uu____207 = (is_interface full_path)
in (match (uu____207) with
| true -> begin
(FStar_Util.smap_add map key ((Some (full_path)), (impl)))
end
| uu____214 -> begin
(FStar_Util.smap_add map key ((intf), (Some (full_path))))
end))
end
| None -> begin
(

let uu____225 = (is_interface full_path)
in (match (uu____225) with
| true -> begin
(FStar_Util.smap_add map key ((Some (full_path)), (None)))
end
| uu____232 -> begin
(FStar_Util.smap_add map key ((None), (Some (full_path))))
end))
end)))
in ((FStar_List.iter (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (

let f = (FStar_Util.basename f)
in (

let uu____245 = (check_and_strip_suffix f)
in (match (uu____245) with
| Some (longname) -> begin
(

let full_path = (match ((d = cwd)) with
| true -> begin
f
end
| uu____249 -> begin
(FStar_Util.join_paths d f)
end)
in (

let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| None -> begin
()
end)))) files))
end
| uu____251 -> begin
(

let uu____252 = (

let uu____253 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (uu____253))
in (Prims.raise uu____252))
end)) include_directories);
(FStar_List.iter (fun f -> (

let uu____256 = (lowercase_module_name f)
in (add_entry uu____256 f))) filenames);
map;
)))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix = (Prims.strcat prefix ".")
in ((

let uu____271 = (

let uu____273 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____273))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix) ((FStar_String.length k) - (FStar_String.length prefix)))
in (

let filename = (

let uu____293 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____293))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.write found true);
)))
end
| uu____314 -> begin
()
end)) uu____271));
(FStar_ST.read found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let suffix = (match (last) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____326 -> begin
[]
end)
in (

let names = (

let uu____329 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____329 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last -> (

let uu____338 = (string_of_lid l last)
in (FStar_String.lowercase uu____338)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____346 = (

let uu____347 = (

let uu____348 = (

let uu____349 = (

let uu____351 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____351))
in (FStar_Util.must uu____349))
in (FStar_String.lowercase uu____348))
in (uu____347 <> k'))
in (match (uu____346) with
| true -> begin
(

let uu____352 = (

let uu____354 = (string_of_lid lid true)
in (uu____354)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" uu____352))
end
| uu____355 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____359 -> begin
false
end))


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> (

let uu____394 = (

let uu____395 = (

let uu____396 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) uu____396))
in (not (uu____395)))
in (match (uu____394) with
| true -> begin
(

let uu____402 = (

let uu____404 = (FStar_ST.read deps)
in (d)::uu____404)
in (FStar_ST.write deps uu____402))
end
| uu____412 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____431 = (FStar_Util.smap_try_find working_map key)
in (match (uu____431) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____451 = (lowercase_module_name f)
in (add_dep uu____451))) (list_of_pair pair))
end
| None -> begin
(

let r = (enter_namespace original_map working_map key)
in (match ((not (r))) with
| true -> begin
(match (let_open) with
| true -> begin
(Prims.raise (FStar_Errors.Err ("let-open only supported for modules, not namespaces")))
end
| uu____457 -> begin
(

let uu____458 = (

let uu____460 = (string_of_lid lid true)
in (uu____460)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" uu____458))
end)
end
| uu____461 -> begin
()
end))
end))))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____471 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____471) with
| Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| None -> begin
(

let uu____498 = (

let uu____499 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (uu____499))
in (Prims.raise uu____498))
end)))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (

let uu____508 = (FStar_Util.smap_try_find working_map key)
in (match (uu____508) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____528 = (lowercase_module_name f)
in (add_dep uu____528))) (list_of_pair pair))
end
| None -> begin
(

let uu____533 = (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ()))
in (match (uu____533) with
| true -> begin
(

let uu____537 = (

let uu____539 = (string_of_lid lid false)
in (uu____539)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" uu____537))
end
| uu____540 -> begin
()
end))
end)))
in (

let uu____542 = (lowercase_join_longident lid false)
in (try_key uu____542))))
in (

let auto_open = (

let uu____545 = (

let uu____546 = (FStar_Util.basename filename)
in (uu____546 = "prims.fst"))
in (match (uu____545) with
| true -> begin
[]
end
| uu____548 -> begin
(FStar_Syntax_Const.fstar_ns_lid)::(FStar_Syntax_Const.prims_lid)::[]
end))
in ((FStar_List.iter (record_open false) auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun uu___130_621 -> (match (uu___130_621) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun uu___131_634 -> (match (uu___131_634) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
((FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]));
(FStar_List.iter collect_module modules);
)
end))
and collect_module = (fun uu___132_640 -> (match (uu___132_640) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
((check_module_declaration_against_filename lid filename);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____650 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____650))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____651 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____651))
end
| uu____652 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____656 -> (match (uu____656) with
| (m, r) -> begin
(

let uu____664 = (

let uu____665 = (

let uu____666 = (string_of_lid lid true)
in (FStar_String.lowercase uu____666))
in ((FStar_String.lowercase m) = uu____665))
in (match (uu____664) with
| true -> begin
(FStar_ST.write r true)
end
| uu____669 -> begin
()
end))
end)) verify_flags)
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
)) decls))
and collect_decl = (fun uu___133_674 -> (match (uu___133_674) with
| (FStar_Parser_AST.Include (lid)) | (FStar_Parser_AST.Open (lid)) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
((

let uu____679 = (lowercase_join_longident lid true)
in (add_dep uu____679));
(record_module_alias ident lid);
)
end
| FStar_Parser_AST.TopLevelLet (uu____680, patterms) -> begin
(FStar_List.iter (fun uu____690 -> (match (uu____690) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)})) | (FStar_Parser_AST.Val (_, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____703; FStar_Parser_AST.mdest = uu____704; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____708, ts) -> begin
(

let ts = (FStar_List.map (fun uu____723 -> (match (uu____723) with
| (x, doc) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts))
end
| FStar_Parser_AST.Exception (uu____731, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| (FStar_Parser_AST.NewEffectForFree (ed)) | (FStar_Parser_AST.NewEffect (ed)) -> begin
(collect_effect_decl ed)
end
| (FStar_Parser_AST.Fsdoc (_)) | (FStar_Parser_AST.Pragma (_)) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____743 = (

let uu____744 = (FStar_ST.read num_of_toplevelmods)
in (uu____744 > (Prims.parse_int "1")))
in (match (uu____743) with
| true -> begin
(

let uu____747 = (

let uu____748 = (

let uu____749 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____749))
in FStar_Errors.Err (uu____748))
in (Prims.raise uu____747))
end
| uu____750 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___134_751 -> (match (uu___134_751) with
| FStar_Parser_AST.TyconAbstract (uu____752, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____760, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____770, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____794 -> (match (uu____794) with
| (uu____799, t, uu____801) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____804, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____834 -> (match (uu____834) with
| (uu____841, t, uu____843, uu____844) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___135_849 -> (match (uu___135_849) with
| FStar_Parser_AST.DefineEffect (uu____850, binders, t, decls, actions) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
(collect_decls actions);
)
end
| FStar_Parser_AST.RedefineEffect (uu____864, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___136_872 -> (match (uu___136_872) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| uu____885 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___137_887 -> (match (uu___137_887) with
| FStar_Const.Const_int (uu____888, Some (signedness, width)) -> begin
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
in (

let uu____898 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep uu____898))))
end
| uu____899 -> begin
()
end))
and collect_term' = (fun uu___138_900 -> (match (uu___138_900) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((match ((s = "@")) with
| true -> begin
(

let uu____907 = (

let uu____908 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____908))
in (collect_term' uu____907))
end
| uu____909 -> begin
()
end);
(FStar_List.iter collect_term ts);
)
end
| (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.Uvar (_)) -> begin
()
end
| (FStar_Parser_AST.Var (lid)) | (FStar_Parser_AST.Projector (lid, _)) | (FStar_Parser_AST.Discrim (lid)) | (FStar_Parser_AST.Name (lid)) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((match (((FStar_List.length termimps) = (Prims.parse_int "1"))) with
| true -> begin
(record_lid lid)
end
| uu____927 -> begin
()
end);
(FStar_List.iter (fun uu____930 -> (match (uu____930) with
| (t, uu____934) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____942) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____944, patterms, t) -> begin
((FStar_List.iter (fun uu____956 -> (match (uu____956) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms);
(collect_term t);
)
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
((record_open true lid);
(collect_term t);
)
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
((collect_term t1);
(collect_term t2);
(collect_term t3);
)
end
| (FStar_Parser_AST.Match (t, bs)) | (FStar_Parser_AST.TryWith (t, bs)) -> begin
((collect_term t);
(collect_branches bs);
)
end
| FStar_Parser_AST.Ascribed (t1, t2) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Record (t, idterms) -> begin
((FStar_Util.iter_opt t collect_term);
(FStar_List.iter (fun uu____1012 -> (match (uu____1012) with
| (uu____1015, t) -> begin
(collect_term t)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____1018) -> begin
(collect_term t)
end
| (FStar_Parser_AST.Product (binders, t)) | (FStar_Parser_AST.Sum (binders, t)) -> begin
((collect_binders binders);
(collect_term t);
)
end
| (FStar_Parser_AST.QForall (binders, ts, t)) | (FStar_Parser_AST.QExists (binders, ts, t)) -> begin
((collect_binders binders);
(FStar_List.iter (FStar_List.iter collect_term) ts);
(collect_term t);
)
end
| FStar_Parser_AST.Refine (binder, t) -> begin
((collect_binder binder);
(collect_term t);
)
end
| FStar_Parser_AST.NamedTyp (uu____1047, t) -> begin
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
and collect_pattern' = (fun uu___139_1063 -> (match (uu___139_1063) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatOp (_)) | (FStar_Parser_AST.PatConst (_)) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| (FStar_Parser_AST.PatVar (_)) | (FStar_Parser_AST.PatName (_)) | (FStar_Parser_AST.PatTvar (_)) -> begin
()
end
| (FStar_Parser_AST.PatList (ps)) | (FStar_Parser_AST.PatOr (ps)) | (FStar_Parser_AST.PatTuple (ps, _)) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____1086 -> (match (uu____1086) with
| (uu____1089, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
((collect_pattern p);
(collect_term t);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____1104 -> (match (uu____1104) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____1116 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____1116) with
| (ast, uu____1124) -> begin
((collect_file ast);
(FStar_ST.read deps);
)
end))));
)))))))))


let print_graph = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1153 = (

let uu____1154 = (

let uu____1155 = (

let uu____1156 = (

let uu____1158 = (

let uu____1160 = (FStar_Util.smap_keys graph)
in (FStar_List.unique uu____1160))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1168 = (

let uu____1172 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must uu____1172))
in (Prims.fst uu____1168))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep))) deps)))) uu____1158))
in (FStar_String.concat "\n" uu____1156))
in (Prims.strcat uu____1155 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1154))
in (FStar_Util.write_file "dep.graph" uu____1153));
))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (

let uu____1234 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (

let uu____1240 = (FStar_Util.mk_ref false)
in ((f), (uu____1240)))) uu____1234))
in (

let m = (build_map filenames)
in (

let collect_one = (collect_one verify_flags verify_mode)
in (

let partial_discovery = (

let uu____1256 = ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
in (not (uu____1256)))
in (

let rec discover_one = (fun is_user_provided_filename interface_only key -> (

let uu____1267 = (

let uu____1268 = (FStar_Util.smap_try_find graph key)
in (uu____1268 = None))
in (match (uu____1267) with
| true -> begin
(

let uu____1283 = (

let uu____1288 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must uu____1288))
in (match (uu____1283) with
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
| (Some (impl), Some (uu____1318)) when interface_only -> begin
[]
end
| (Some (impl), uu____1322) -> begin
(collect_one is_user_provided_filename m impl)
end
| (None, uu____1326) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in ((FStar_Util.smap_add graph key ((deps), (White)));
(FStar_List.iter (discover_one false partial_discovery) deps);
))))
end))
end
| uu____1337 -> begin
()
end)))
in (

let discover_command_line_argument = (fun f -> (

let m = (lowercase_module_name f)
in (

let uu____1343 = (is_interface f)
in (match (uu____1343) with
| true -> begin
(discover_one true true m)
end
| uu____1344 -> begin
(discover_one true false m)
end))))
in ((FStar_List.iter discover_command_line_argument filenames);
(

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let uu____1369 = (

let uu____1373 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must uu____1373))
in (match (uu____1369) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((FStar_Util.print1 "Warning: recursive dependency on module %s\n" key);
(FStar_Util.print1 "The cycle is: %s \n" (FStar_String.concat " -> " cycle));
(print_graph immediate_graph);
(FStar_Util.print_string "\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Black -> begin
direct_deps
end
| White -> begin
((FStar_Util.smap_add graph key ((direct_deps), (Gray)));
(

let all_deps = (

let uu____1402 = (

let uu____1404 = (FStar_List.map (fun dep -> (

let uu____1409 = (discover ((key)::cycle) dep)
in (dep)::uu____1409)) direct_deps)
in (FStar_List.flatten uu____1404))
in (FStar_List.unique uu____1402))
in ((FStar_Util.smap_add graph key ((all_deps), (Black)));
(

let uu____1417 = (

let uu____1419 = (FStar_ST.read topologically_sorted)
in (key)::uu____1419)
in (FStar_ST.write topologically_sorted uu____1417));
all_deps;
));
)
end)
end)))
in (

let discover = (discover [])
in (

let must_find = (fun k -> (

let uu____1436 = (

let uu____1441 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1441))
in (match (uu____1436) with
| (Some (intf), Some (impl)) when ((not (partial_discovery)) && (

let uu____1460 = (FStar_List.existsML (fun f -> (

let uu____1462 = (lowercase_module_name f)
in (uu____1462 = k))) filenames)
in (not (uu____1460)))) -> begin
(intf)::(impl)::[]
end
| (Some (intf), Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && (

let uu____1468 = (lowercase_module_name f)
in (uu____1468 = k)))) filenames) -> begin
(intf)::(impl)::[]
end
| (Some (intf), uu____1470) -> begin
(intf)::[]
end
| (None, Some (impl)) -> begin
(impl)::[]
end
| (None, None) -> begin
[]
end)))
in (

let must_find_r = (fun f -> (

let uu____1484 = (must_find f)
in (FStar_List.rev uu____1484)))
in (

let by_target = (

let uu____1491 = (FStar_Util.smap_keys graph)
in (FStar_List.collect (fun k -> (

let as_list = (must_find k)
in (

let is_interleaved = ((FStar_List.length as_list) = (Prims.parse_int "2"))
in (FStar_List.map (fun f -> (

let should_append_fsti = ((is_implementation f) && is_interleaved)
in (

let suffix = (match (should_append_fsti) with
| true -> begin
((Prims.strcat f "i"))::[]
end
| uu____1513 -> begin
[]
end)
in (

let k = (lowercase_module_name f)
in (

let deps = (

let uu____1517 = (discover k)
in (FStar_List.rev uu____1517))
in (

let deps_as_filenames = (

let uu____1521 = (FStar_List.collect must_find deps)
in (FStar_List.append uu____1521 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) uu____1491))
in (

let topologically_sorted = (

let uu____1526 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r uu____1526))
in ((FStar_List.iter (fun uu____1535 -> (match (uu____1535) with
| (m, r) -> begin
(

let uu____1543 = ((

let uu____1544 = (FStar_ST.read r)
in (not (uu____1544))) && (

let uu____1547 = (FStar_Options.interactive ())
in (not (uu____1547))))
in (match (uu____1543) with
| true -> begin
(

let maybe_fst = (

let k = (FStar_String.length m)
in (

let uu____1551 = ((k > (Prims.parse_int "4")) && (

let uu____1555 = (FStar_String.substring m (k - (Prims.parse_int "4")) (Prims.parse_int "4"))
in (uu____1555 = ".fst")))
in (match (uu____1551) with
| true -> begin
(

let uu____1559 = (FStar_String.substring m (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" uu____1559))
end
| uu____1563 -> begin
""
end)))
in (

let uu____1564 = (

let uu____1565 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m m maybe_fst)
in FStar_Errors.Err (uu____1565))
in (Prims.raise uu____1564)))
end
| uu____1566 -> begin
()
end))
end)) verify_flags);
((by_target), (topologically_sorted), (immediate_graph));
)))))))));
)))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun uu____1590 -> (match (uu____1590) with
| (f, deps) -> begin
(

let deps = (FStar_List.map (fun s -> (FStar_Util.replace_string s " " "\\ ")) deps)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps)))
end)) deps))


let print = (fun uu____1620 -> (match (uu____1620) with
| (make_deps, uu____1633, graph) -> begin
(

let uu____1651 = (FStar_Options.dep ())
in (match (uu____1651) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (uu____1653) -> begin
(Prims.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))
end))





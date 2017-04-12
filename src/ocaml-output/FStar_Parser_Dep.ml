
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


let list_of_option = (fun uu___113_100 -> (match (uu___113_100) with
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


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____146 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____146))
in (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____164 = (FStar_Util.smap_try_find map1 key)
in (match (uu____164) with
| Some (intf, impl) -> begin
(

let uu____184 = (is_interface full_path)
in (match (uu____184) with
| true -> begin
(FStar_Util.smap_add map1 key ((Some (full_path)), (impl)))
end
| uu____191 -> begin
(FStar_Util.smap_add map1 key ((intf), (Some (full_path))))
end))
end
| None -> begin
(

let uu____202 = (is_interface full_path)
in (match (uu____202) with
| true -> begin
(FStar_Util.smap_add map1 key ((Some (full_path)), (None)))
end
| uu____209 -> begin
(FStar_Util.smap_add map1 key ((None), (Some (full_path))))
end))
end)))
in ((FStar_List.iter (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____222 = (check_and_strip_suffix f1)
in (match (uu____222) with
| Some (longname) -> begin
(

let full_path = (match ((d = cwd)) with
| true -> begin
f1
end
| uu____226 -> begin
(FStar_Util.join_paths d f1)
end)
in (

let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| None -> begin
()
end)))) files))
end
| uu____228 -> begin
(

let uu____229 = (

let uu____230 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (uu____230))
in (Prims.raise uu____229))
end)) include_directories2);
(FStar_List.iter (fun f -> (

let uu____233 = (lowercase_module_name f)
in (add_entry uu____233 f))) filenames);
map1;
))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____248 = (

let uu____250 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____250))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____270 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____270))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.write found true);
)))
end
| uu____291 -> begin
()
end)) uu____248));
(FStar_ST.read found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____303 -> begin
[]
end)
in (

let names = (

let uu____306 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____306 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____315 = (string_of_lid l last1)
in (FStar_String.lowercase uu____315)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____323 = (

let uu____324 = (

let uu____325 = (

let uu____326 = (

let uu____328 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____328))
in (FStar_Util.must uu____326))
in (FStar_String.lowercase uu____325))
in (uu____324 <> k'))
in (match (uu____323) with
| true -> begin
(

let uu____329 = (

let uu____331 = (string_of_lid lid true)
in (uu____331)::(filename)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" uu____329))
end
| uu____332 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____336 -> begin
false
end))


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> (

let uu____371 = (

let uu____372 = (

let uu____373 = (FStar_ST.read deps)
in (FStar_List.existsb (fun d' -> (d' = d)) uu____373))
in (not (uu____372)))
in (match (uu____371) with
| true -> begin
(

let uu____379 = (

let uu____381 = (FStar_ST.read deps)
in (d)::uu____381)
in (FStar_ST.write deps uu____379))
end
| uu____389 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____408 = (FStar_Util.smap_try_find working_map key)
in (match (uu____408) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____428 = (lowercase_module_name f)
in (add_dep uu____428))) (list_of_pair pair))
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
| uu____434 -> begin
(

let uu____435 = (

let uu____437 = (string_of_lid lid true)
in (uu____437)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: no modules in namespace %s and no file with that name either\n" uu____435))
end)
end
| uu____438 -> begin
()
end))
end))))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____448 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____448) with
| Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| None -> begin
(

let uu____475 = (

let uu____476 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (uu____476))
in (Prims.raise uu____475))
end)))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (

let uu____485 = (FStar_Util.smap_try_find working_map key)
in (match (uu____485) with
| Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____505 = (lowercase_module_name f)
in (add_dep uu____505))) (list_of_pair pair))
end
| None -> begin
(

let uu____510 = (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ()))
in (match (uu____510) with
| true -> begin
(

let uu____514 = (

let uu____516 = (string_of_lid lid false)
in (uu____516)::[])
in (FStar_Util.fprint FStar_Util.stderr "Warning: unbound module reference %s\n" uu____514))
end
| uu____517 -> begin
()
end))
end)))
in (

let uu____519 = (lowercase_join_longident lid false)
in (try_key uu____519))))
in (

let auto_open = (

let uu____522 = (

let uu____523 = (FStar_Util.basename filename)
in (

let uu____524 = (FStar_Options.prims_basename ())
in (uu____523 = uu____524)))
in (match (uu____522) with
| true -> begin
[]
end
| uu____526 -> begin
(FStar_Syntax_Const.fstar_ns_lid)::(FStar_Syntax_Const.prims_lid)::[]
end))
in ((FStar_List.iter (record_open false) auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun uu___114_599 -> (match (uu___114_599) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun uu___115_612 -> (match (uu___115_612) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
((FStar_Util.fprint FStar_Util.stderr "Warning: file %s does not respect the one module per file convention\n" ((filename)::[]));
(FStar_List.iter collect_module modules);
)
end))
and collect_module = (fun uu___116_618 -> (match (uu___116_618) with
| (FStar_Parser_AST.Module (lid, decls)) | (FStar_Parser_AST.Interface (lid, decls, _)) -> begin
((check_module_declaration_against_filename lid filename);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____628 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____628))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____629 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____629))
end
| uu____630 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____634 -> (match (uu____634) with
| (m, r) -> begin
(

let uu____642 = (

let uu____643 = (

let uu____644 = (string_of_lid lid true)
in (FStar_String.lowercase uu____644))
in ((FStar_String.lowercase m) = uu____643))
in (match (uu____642) with
| true -> begin
(FStar_ST.write r true)
end
| uu____647 -> begin
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
and collect_decl = (fun uu___117_652 -> (match (uu___117_652) with
| (FStar_Parser_AST.Include (lid)) | (FStar_Parser_AST.Open (lid)) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
((

let uu____657 = (lowercase_join_longident lid true)
in (add_dep uu____657));
(record_module_alias ident lid);
)
end
| FStar_Parser_AST.TopLevelLet (uu____658, patterms) -> begin
(FStar_List.iter (fun uu____668 -> (match (uu____668) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| (FStar_Parser_AST.Main (t)) | (FStar_Parser_AST.Assume (_, t)) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)})) | (FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = _; FStar_Parser_AST.mdest = _; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)})) | (FStar_Parser_AST.Val (_, t)) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____681; FStar_Parser_AST.mdest = uu____682; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____686, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____701 -> (match (uu____701) with
| (x, doc1) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____709, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| (FStar_Parser_AST.Fsdoc (_)) | (FStar_Parser_AST.Pragma (_)) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____721 = (

let uu____722 = (FStar_ST.read num_of_toplevelmods)
in (uu____722 > (Prims.parse_int "1")))
in (match (uu____721) with
| true -> begin
(

let uu____725 = (

let uu____726 = (

let uu____727 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____727))
in FStar_Errors.Err (uu____726))
in (Prims.raise uu____725))
end
| uu____728 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___118_729 -> (match (uu___118_729) with
| FStar_Parser_AST.TyconAbstract (uu____730, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____738, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____748, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____772 -> (match (uu____772) with
| (uu____777, t, uu____779) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____782, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____812 -> (match (uu____812) with
| (uu____819, t, uu____821, uu____822) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___119_827 -> (match (uu___119_827) with
| FStar_Parser_AST.DefineEffect (uu____828, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____838, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___120_846 -> (match (uu___120_846) with
| ({FStar_Parser_AST.b = FStar_Parser_AST.Annotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (_, t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) | ({FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = _; FStar_Parser_AST.blevel = _; FStar_Parser_AST.aqual = _}) -> begin
(collect_term t)
end
| uu____859 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___121_861 -> (match (uu___121_861) with
| FStar_Const.Const_int (uu____862, Some (signedness, width)) -> begin
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

let uu____872 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep uu____872))))
end
| uu____873 -> begin
()
end))
and collect_term' = (fun uu___122_874 -> (match (uu___122_874) with
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

let uu____881 = (

let uu____882 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____882))
in (collect_term' uu____881))
end
| uu____883 -> begin
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
| uu____901 -> begin
()
end);
(FStar_List.iter (fun uu____904 -> (match (uu____904) with
| (t, uu____908) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____916) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____918, patterms, t) -> begin
((FStar_List.iter (fun uu____930 -> (match (uu____930) with
| (pat, t1) -> begin
((collect_pattern pat);
(collect_term t1);
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
| FStar_Parser_AST.Ascribed (t1, t2, None) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Ascribed (t1, t2, Some (tac)) -> begin
((collect_term t1);
(collect_term t2);
(collect_term tac);
)
end
| FStar_Parser_AST.Record (t, idterms) -> begin
((FStar_Util.iter_opt t collect_term);
(FStar_List.iter (fun uu____993 -> (match (uu____993) with
| (uu____996, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____999) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____1028, t) -> begin
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
and collect_pattern' = (fun uu___123_1044 -> (match (uu___123_1044) with
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
(FStar_List.iter (fun uu____1067 -> (match (uu____1067) with
| (uu____1070, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
((collect_pattern p);
(collect_term t);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____1085 -> (match (uu____1085) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____1097 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____1097) with
| (ast, uu____1105) -> begin
((collect_file ast);
(FStar_ST.read deps);
)
end))));
)))))))))


let print_graph = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1134 = (

let uu____1135 = (

let uu____1136 = (

let uu____1137 = (

let uu____1139 = (

let uu____1141 = (FStar_Util.smap_keys graph)
in (FStar_List.unique uu____1141))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1149 = (

let uu____1153 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must uu____1153))
in (Prims.fst uu____1149))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep1 -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep1))) deps)))) uu____1139))
in (FStar_String.concat "\n" uu____1137))
in (Prims.strcat uu____1136 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1135))
in (FStar_Util.write_file "dep.graph" uu____1134));
))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (

let uu____1215 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (

let uu____1221 = (FStar_Util.mk_ref false)
in ((f), (uu____1221)))) uu____1215))
in (

let m = (build_map filenames)
in (

let collect_one1 = (collect_one verify_flags verify_mode)
in (

let partial_discovery = (

let uu____1237 = ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
in (not (uu____1237)))
in (

let rec discover_one = (fun is_user_provided_filename interface_only key -> (

let uu____1248 = (

let uu____1249 = (FStar_Util.smap_try_find graph key)
in (uu____1249 = None))
in (match (uu____1248) with
| true -> begin
(

let uu____1264 = (

let uu____1269 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must uu____1269))
in (match (uu____1264) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| Some (intf1) -> begin
(collect_one1 is_user_provided_filename m intf1)
end
| None -> begin
[]
end)
in (

let impl_deps = (match (((impl), (intf))) with
| (Some (impl1), Some (uu____1299)) when interface_only -> begin
[]
end
| (Some (impl1), uu____1303) -> begin
(collect_one1 is_user_provided_filename m impl1)
end
| (None, uu____1307) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in ((FStar_Util.smap_add graph key ((deps), (White)));
(FStar_List.iter (discover_one false partial_discovery) deps);
))))
end))
end
| uu____1318 -> begin
()
end)))
in (

let discover_command_line_argument = (fun f -> (

let mn = (lowercase_module_name f)
in (

let interface_only = (

let uu____1325 = (

let uu____1330 = (FStar_Util.smap_try_find m mn)
in (FStar_Util.must uu____1330))
in (match (uu____1325) with
| (Some (uu____1344), None) -> begin
true
end
| uu____1347 -> begin
false
end))
in (discover_one true interface_only mn))))
in ((FStar_List.iter discover_command_line_argument filenames);
(

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let uu____1376 = (

let uu____1380 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must uu____1380))
in (match (uu____1376) with
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

let uu____1409 = (

let uu____1411 = (FStar_List.map (fun dep1 -> (

let uu____1416 = (discover ((key)::cycle) dep1)
in (dep1)::uu____1416)) direct_deps)
in (FStar_List.flatten uu____1411))
in (FStar_List.unique uu____1409))
in ((FStar_Util.smap_add graph key ((all_deps), (Black)));
(

let uu____1424 = (

let uu____1426 = (FStar_ST.read topologically_sorted)
in (key)::uu____1426)
in (FStar_ST.write topologically_sorted uu____1424));
all_deps;
));
)
end)
end)))
in (

let discover1 = (discover [])
in (

let must_find = (fun k -> (

let uu____1443 = (

let uu____1448 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1448))
in (match (uu____1443) with
| (Some (intf), Some (impl)) when ((not (partial_discovery)) && (

let uu____1467 = (FStar_List.existsML (fun f -> (

let uu____1469 = (lowercase_module_name f)
in (uu____1469 = k))) filenames)
in (not (uu____1467)))) -> begin
(intf)::(impl)::[]
end
| (Some (intf), Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && (

let uu____1475 = (lowercase_module_name f)
in (uu____1475 = k)))) filenames) -> begin
(intf)::(impl)::[]
end
| (Some (intf), uu____1477) -> begin
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

let uu____1491 = (must_find f)
in (FStar_List.rev uu____1491)))
in (

let by_target = (

let uu____1498 = (

let uu____1500 = (FStar_Util.smap_keys graph)
in (FStar_List.sortWith (fun x y -> (FStar_String.compare x y)) uu____1500))
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
| uu____1524 -> begin
[]
end)
in (

let k1 = (lowercase_module_name f)
in (

let deps = (

let uu____1528 = (discover1 k1)
in (FStar_List.rev uu____1528))
in (

let deps_as_filenames = (

let uu____1532 = (FStar_List.collect must_find deps)
in (FStar_List.append uu____1532 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) uu____1498))
in (

let topologically_sorted1 = (

let uu____1537 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r uu____1537))
in ((FStar_List.iter (fun uu____1546 -> (match (uu____1546) with
| (m1, r) -> begin
(

let uu____1554 = ((

let uu____1555 = (FStar_ST.read r)
in (not (uu____1555))) && (

let uu____1558 = (FStar_Options.interactive ())
in (not (uu____1558))))
in (match (uu____1554) with
| true -> begin
(

let maybe_fst = (

let k = (FStar_String.length m1)
in (

let uu____1562 = ((k > (Prims.parse_int "4")) && (

let uu____1566 = (FStar_String.substring m1 (k - (Prims.parse_int "4")) (Prims.parse_int "4"))
in (uu____1566 = ".fst")))
in (match (uu____1562) with
| true -> begin
(

let uu____1570 = (FStar_String.substring m1 (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" uu____1570))
end
| uu____1574 -> begin
""
end)))
in (

let uu____1575 = (

let uu____1576 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m1 m1 maybe_fst)
in FStar_Errors.Err (uu____1576))
in (Prims.raise uu____1575)))
end
| uu____1577 -> begin
()
end))
end)) verify_flags);
((by_target), (topologically_sorted1), (immediate_graph));
)))))))));
)))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun uu____1601 -> (match (uu____1601) with
| (f, deps1) -> begin
(

let deps2 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s ' ' "\\ ")) deps1)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2)))
end)) deps))


let print = (fun uu____1631 -> (match (uu____1631) with
| (make_deps, uu____1644, graph) -> begin
(

let uu____1662 = (FStar_Options.dep ())
in (match (uu____1662) with
| Some ("make") -> begin
(print_make make_deps)
end
| Some ("graph") -> begin
(print_graph graph)
end
| Some (uu____1664) -> begin
(Prims.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| None -> begin
()
end))
end))





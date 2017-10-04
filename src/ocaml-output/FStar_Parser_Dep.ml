
open Prims
open FStar_Pervasives
type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut


let uu___is_VerifyAll : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyAll -> begin
true
end
| uu____5 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____15 -> begin
false
end))


type map =
(Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap

type color =
| White
| Gray
| Black


let uu___is_White : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| White -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____35 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____40 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____45 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____50 -> begin
false
end))


let check_and_strip_suffix : Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun f -> (

let suffixes = (".fsti")::(".fst")::(".fsi")::(".fs")::[]
in (

let matches = (FStar_List.map (fun ext -> (

let lext = (FStar_String.length ext)
in (

let l = (FStar_String.length f)
in (

let uu____77 = ((l > lext) && (

let uu____89 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____89 ext)))
in (match (uu____77) with
| true -> begin
(

let uu____106 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____106))
end
| uu____117 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____118 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____118) with
| (FStar_Pervasives_Native.Some (m))::uu____128 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____135 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____144 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____144 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____149 = (is_interface f)
in (not (uu____149))))


let list_of_option : 'Auu____154 . 'Auu____154 FStar_Pervasives_Native.option  ->  'Auu____154 Prims.list = (fun uu___82_162 -> (match (uu___82_162) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____170 . ('Auu____170 FStar_Pervasives_Native.option * 'Auu____170 FStar_Pervasives_Native.option)  ->  'Auu____170 Prims.list = (fun uu____184 -> (match (uu____184) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____207 = (

let uu____210 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____210))
in (match (uu____207) with
| FStar_Pervasives_Native.Some (longname) -> begin
(FStar_String.lowercase longname)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____212 = (

let uu____213 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Errors.Err (uu____213))
in (FStar_Exn.raise uu____212))
end)))


let build_inclusion_candidates_list : Prims.unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____223 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____240 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____240))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____266 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____266 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____285 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____286 -> begin
(

let uu____287 = (

let uu____288 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (uu____288))
in (FStar_Exn.raise uu____287))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____329 = (FStar_Util.smap_try_find map1 key)
in (match (uu____329) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____366 = (is_interface full_path)
in (match (uu____366) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____379 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____400 = (is_interface full_path)
in (match (uu____400) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____413 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____427 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____441 -> (match (uu____441) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____427));
(FStar_List.iter (fun f -> (

let uu____452 = (lowercase_module_name f)
in (add_entry uu____452 f))) filenames);
map1;
))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____470 = (

let uu____473 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____473))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____499 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____499))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____595 -> begin
()
end)) uu____470));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____669 -> begin
[]
end)
in (

let names = (

let uu____673 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____673 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____686 = (string_of_lid l last1)
in (FStar_String.lowercase uu____686)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____691 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____691)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____703 = (

let uu____704 = (

let uu____705 = (

let uu____706 = (

let uu____709 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____709))
in (FStar_Util.must uu____706))
in (FStar_String.lowercase uu____705))
in (Prims.op_disEquality uu____704 k'))
in (match (uu____703) with
| true -> begin
(

let uu____710 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" uu____710 filename))
end
| uu____711 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____716 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun filename -> (

let filename1 = (FStar_Util.basename filename)
in (

let corelibs = (

let uu____731 = (FStar_Options.prims_basename ())
in (

let uu____732 = (

let uu____735 = (FStar_Options.pervasives_basename ())
in (

let uu____736 = (

let uu____739 = (FStar_Options.pervasives_native_basename ())
in (uu____739)::[])
in (uu____735)::uu____736))
in (uu____731)::uu____732))
in (match ((FStar_List.mem filename1 corelibs)) with
| true -> begin
[]
end
| uu____750 -> begin
(((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
end))))


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> (

let uu____818 = (

let uu____819 = (

let uu____820 = (FStar_ST.op_Bang deps)
in (FStar_List.existsML (fun d' -> (Prims.op_Equality d' d)) uu____820))
in (not (uu____819)))
in (match (uu____818) with
| true -> begin
(

let uu____889 = (

let uu____892 = (FStar_ST.op_Bang deps)
in (d)::uu____892)
in (FStar_ST.op_Colon_Equals deps uu____889))
end
| uu____1023 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open_module = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____1051 = (FStar_Util.smap_try_find working_map key)
in (match (uu____1051) with
| FStar_Pervasives_Native.Some (pair) -> begin
((FStar_List.iter (fun f -> (

let uu____1091 = (lowercase_module_name f)
in (add_dep uu____1091))) (list_of_pair pair));
true;
)
end
| FStar_Pervasives_Native.None -> begin
(

let r = (enter_namespace original_map working_map key)
in ((match ((not (r))) with
| true -> begin
(match (let_open) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Err ("let-open only supported for modules, not namespaces")))
end
| uu____1102 -> begin
(

let uu____1103 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: in %s: no modules in namespace %s and no file with that name either\n" filename uu____1103))
end)
end
| uu____1104 -> begin
()
end);
false;
))
end))))
in (

let record_open_namespace = (fun error_msg lid -> (

let key = (lowercase_join_longident lid true)
in (

let r = (enter_namespace original_map working_map key)
in (match ((not (r))) with
| true -> begin
(match (error_msg) with
| FStar_Pervasives_Native.Some (e) -> begin
(FStar_Exn.raise (FStar_Errors.Err (e)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1119 = (string_of_lid lid true)
in (FStar_Util.print1_warning "Warning: no modules in namespace %s and no file with that name either\n" uu____1119))
end)
end
| uu____1120 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____1128 = (record_open_module let_open lid)
in (match (uu____1128) with
| true -> begin
()
end
| uu____1129 -> begin
(

let msg = (match (let_open) with
| true -> begin
FStar_Pervasives_Native.Some ("let-open only supported for modules, not namespaces")
end
| uu____1135 -> begin
FStar_Pervasives_Native.None
end)
in (record_open_namespace msg lid))
end)))
in (

let record_open_module_or_namespace = (fun uu____1143 -> (match (uu____1143) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace FStar_Pervasives_Native.None lid)
end
| Open_module -> begin
(

let uu____1150 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____1160 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____1160) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1212 = (

let uu____1213 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (uu____1213))
in (FStar_Exn.raise uu____1212))
end)))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (

let uu____1222 = (FStar_Util.smap_try_find working_map key)
in (match (uu____1222) with
| FStar_Pervasives_Native.Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____1261 = (lowercase_module_name f)
in (add_dep uu____1261))) (list_of_pair pair))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1270 = (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ()))
in (match (uu____1270) with
| true -> begin
(

let uu____1271 = (

let uu____1272 = (string_of_lid lid false)
in (FStar_Util.format1 "Unbound module reference %s" uu____1272))
in (FStar_Errors.warn (FStar_Ident.range_of_lid lid) uu____1271))
end
| uu____1273 -> begin
()
end))
end)))
in (

let uu____1275 = (lowercase_join_longident lid false)
in (try_key uu____1275))))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_module = (fun uu___83_1360 -> (match (uu___83_1360) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1369 = (

let uu____1370 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____1370))
in ())
end
| uu____1371 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____1373 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____1373))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____1374 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____1374))
end
| uu____1375 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____1478 -> (match (uu____1478) with
| (m, r) -> begin
(

let uu____1767 = (

let uu____1768 = (

let uu____1769 = (string_of_lid lid true)
in (FStar_String.lowercase uu____1769))
in (Prims.op_Equality (FStar_String.lowercase m) uu____1768))
in (match (uu____1767) with
| true -> begin
(FStar_ST.op_Colon_Equals r true)
end
| uu____1912 -> begin
()
end))
end)) verify_flags)
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____1915) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____1922 = (

let uu____1923 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____1923))
in ())
end
| uu____1924 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____1926 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____1926))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____1927 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____1927))
end
| uu____1928 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____2031 -> (match (uu____2031) with
| (m, r) -> begin
(

let uu____2320 = (

let uu____2321 = (

let uu____2322 = (string_of_lid lid true)
in (FStar_String.lowercase uu____2322))
in (Prims.op_Equality (FStar_String.lowercase m) uu____2321))
in (match (uu____2320) with
| true -> begin
(FStar_ST.op_Colon_Equals r true)
end
| uu____2465 -> begin
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
and collect_decl = (fun uu___84_2473 -> (match (uu___84_2473) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
((

let uu____2479 = (lowercase_join_longident lid true)
in (add_dep uu____2479));
(record_module_alias ident lid);
)
end
| FStar_Parser_AST.TopLevelLet (uu____2480, patterms) -> begin
(FStar_List.iter (fun uu____2502 -> (match (uu____2502) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____2511, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2513; FStar_Parser_AST.mdest = uu____2514; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2516; FStar_Parser_AST.mdest = uu____2517; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____2519, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2521; FStar_Parser_AST.mdest = uu____2522; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____2526, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____2556 -> (match (uu____2556) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____2569, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____2576) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____2577) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____2601 = (

let uu____2602 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____2602 > (Prims.parse_int "1")))
in (match (uu____2601) with
| true -> begin
(

let uu____2663 = (

let uu____2664 = (

let uu____2665 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____2665))
in FStar_Errors.Err (uu____2664))
in (FStar_Exn.raise uu____2663))
end
| uu____2666 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___85_2667 -> (match (uu___85_2667) with
| FStar_Parser_AST.TyconAbstract (uu____2668, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____2680, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____2694, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____2740 -> (match (uu____2740) with
| (uu____2749, t, uu____2751) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____2756, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____2815 -> (match (uu____2815) with
| (uu____2828, t, uu____2830, uu____2831) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___86_2840 -> (match (uu___86_2840) with
| FStar_Parser_AST.DefineEffect (uu____2841, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____2855, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___87_2866 -> (match (uu___87_2866) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2867, t); FStar_Parser_AST.brange = uu____2869; FStar_Parser_AST.blevel = uu____2870; FStar_Parser_AST.aqual = uu____2871} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2872, t); FStar_Parser_AST.brange = uu____2874; FStar_Parser_AST.blevel = uu____2875; FStar_Parser_AST.aqual = uu____2876} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____2878; FStar_Parser_AST.blevel = uu____2879; FStar_Parser_AST.aqual = uu____2880} -> begin
(collect_term t)
end
| uu____2881 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___88_2883 -> (match (uu___88_2883) with
| FStar_Const.Const_int (uu____2884, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____2899 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep uu____2899))))
end
| FStar_Const.Const_char (uu____2900) -> begin
(add_dep "fstar.char")
end
| FStar_Const.Const_float (uu____2901) -> begin
(add_dep "fstar.float")
end
| uu____2902 -> begin
()
end))
and collect_term' = (fun uu___89_2903 -> (match (uu___89_2903) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((match ((Prims.op_Equality (FStar_Ident.text_of_id s) "@")) with
| true -> begin
(

let uu____2912 = (

let uu____2913 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____2913))
in (collect_term' uu____2912))
end
| uu____2914 -> begin
()
end);
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____2915) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____2916) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____2919) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Name (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((match ((Prims.op_Equality (FStar_List.length termimps) (Prims.parse_int "1"))) with
| true -> begin
(record_lid lid)
end
| uu____2941 -> begin
()
end);
(FStar_List.iter (fun uu____2949 -> (match (uu____2949) with
| (t, uu____2955) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____2965) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____2967, patterms, t) -> begin
((FStar_List.iter (fun uu____2991 -> (match (uu____2991) with
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
| FStar_Parser_AST.Bind (uu____3002, t1, t2) -> begin
((collect_term t1);
(collect_term t2);
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
| FStar_Parser_AST.Match (t, bs) -> begin
((collect_term t);
(collect_branches bs);
)
end
| FStar_Parser_AST.TryWith (t, bs) -> begin
((collect_term t);
(collect_branches bs);
)
end
| FStar_Parser_AST.Ascribed (t1, t2, FStar_Pervasives_Native.None) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Ascribed (t1, t2, FStar_Pervasives_Native.Some (tac)) -> begin
((collect_term t1);
(collect_term t2);
(collect_term tac);
)
end
| FStar_Parser_AST.Record (t, idterms) -> begin
((FStar_Util.iter_opt t collect_term);
(FStar_List.iter (fun uu____3098 -> (match (uu____3098) with
| (uu____3103, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____3106) -> begin
(collect_term t)
end
| FStar_Parser_AST.Product (binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end
| FStar_Parser_AST.QForall (binders, ts, t) -> begin
((collect_binders binders);
(FStar_List.iter (FStar_List.iter collect_term) ts);
(collect_term t);
)
end
| FStar_Parser_AST.QExists (binders, ts, t) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____3162, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assign (uu____3165, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____3168) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____3174) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____3180, uu____3181) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___90_3189 -> (match (uu___90_3189) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____3190) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____3191) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____3199) -> begin
()
end
| FStar_Parser_AST.PatName (uu____3206) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____3207) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____3221) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____3240 -> (match (uu____3240) with
| (uu____3245, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
((collect_pattern p);
(collect_term t);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____3269 -> (match (uu____3269) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____3287 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____3287) with
| (ast, uu____3301) -> begin
((collect_module ast);
(FStar_ST.op_Bang deps);
)
end))));
))))))))))))


let print_graph : 'Auu____3383 . (Prims.string Prims.list * 'Auu____3383) FStar_Util.smap  ->  Prims.unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____3407 = (

let uu____3408 = (

let uu____3409 = (

let uu____3410 = (

let uu____3413 = (

let uu____3416 = (FStar_Util.smap_keys graph)
in (FStar_List.unique uu____3416))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____3432 = (

let uu____3439 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must uu____3439))
in (FStar_Pervasives_Native.fst uu____3432))
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (FStar_List.map (fun dep1 -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep1))) deps)))) uu____3413))
in (FStar_String.concat "\n" uu____3410))
in (Prims.strcat uu____3409 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____3408))
in (FStar_Util.write_file "dep.graph" uu____3407));
))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (

let uu____3528 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (

let uu____3540 = (FStar_Util.mk_ref false)
in ((f), (uu____3540)))) uu____3528))
in (

let partial_discovery = (

let uu____3560 = ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
in (not (uu____3560)))
in (

let m = (build_map filenames)
in (

let file_names_of_key = (fun k -> (

let uu____3566 = (

let uu____3575 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____3575))
in (match (uu____3566) with
| (intf, impl) -> begin
(match (((intf), (impl))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
(failwith "Impossible")
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (i)) -> begin
i
end
| (FStar_Pervasives_Native.Some (i), FStar_Pervasives_Native.None) -> begin
i
end
| (FStar_Pervasives_Native.Some (i), uu____3631) when partial_discovery -> begin
i
end
| (FStar_Pervasives_Native.Some (i), FStar_Pervasives_Native.Some (j)) -> begin
(Prims.strcat i (Prims.strcat " && " j))
end)
end)))
in (

let collect_one1 = (collect_one verify_flags verify_mode)
in (

let rec discover_one = (fun is_user_provided_filename interface_only key -> (

let uu____3663 = (

let uu____3664 = (FStar_Util.smap_try_find graph key)
in (Prims.op_Equality uu____3664 FStar_Pervasives_Native.None))
in (match (uu____3663) with
| true -> begin
(

let uu____3693 = (

let uu____3702 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must uu____3702))
in (match (uu____3693) with
| (intf, impl) -> begin
(

let intf_deps = (match (intf) with
| FStar_Pervasives_Native.Some (intf1) -> begin
(collect_one1 is_user_provided_filename m intf1)
end
| FStar_Pervasives_Native.None -> begin
[]
end)
in (

let impl_deps = (match (((impl), (intf))) with
| (FStar_Pervasives_Native.Some (impl1), FStar_Pervasives_Native.Some (uu____3755)) when interface_only -> begin
[]
end
| (FStar_Pervasives_Native.Some (impl1), uu____3761) -> begin
(collect_one1 is_user_provided_filename m impl1)
end
| (FStar_Pervasives_Native.None, uu____3768) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in ((FStar_Util.smap_add graph key ((deps), (White)));
(FStar_List.iter (discover_one false partial_discovery) deps);
))))
end))
end
| uu____3787 -> begin
()
end)))
in (

let discover_command_line_argument = (fun f -> (

let m1 = (lowercase_module_name f)
in (

let interface_only = ((is_interface f) && (

let uu____3795 = (FStar_List.existsML (fun f1 -> ((

let uu____3800 = (lowercase_module_name f1)
in (Prims.op_Equality uu____3800 m1)) && (is_implementation f1))) filenames)
in (not (uu____3795))))
in (discover_one true interface_only m1))))
in ((FStar_List.iter discover_command_line_argument filenames);
(

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let uu____3837 = (

let uu____3844 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must uu____3844))
in (match (uu____3837) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((FStar_Util.print1_warning "Warning: recursive dependency on module %s\n" key);
(

let cycle1 = (FStar_All.pipe_right cycle (FStar_List.map file_names_of_key))
in ((FStar_Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (FStar_String.concat "\n`used by` " cycle1));
(print_graph immediate_graph);
(FStar_Util.print_string "\n");
(FStar_All.exit (Prims.parse_int "1"));
));
)
end
| Black -> begin
direct_deps
end
| White -> begin
((FStar_Util.smap_add graph key ((direct_deps), (Gray)));
(

let all_deps = (

let uu____3900 = (

let uu____3903 = (FStar_List.map (fun dep1 -> (

let uu____3913 = (discover ((key)::cycle) dep1)
in (dep1)::uu____3913)) direct_deps)
in (FStar_List.flatten uu____3903))
in (FStar_List.unique uu____3900))
in ((FStar_Util.smap_add graph key ((all_deps), (Black)));
(

let uu____3926 = (

let uu____3929 = (FStar_ST.op_Bang topologically_sorted)
in (key)::uu____3929)
in (FStar_ST.op_Colon_Equals topologically_sorted uu____3926));
all_deps;
));
)
end)
end)))
in (

let discover1 = (discover [])
in (

let must_find = (fun k -> (

let uu____4071 = (

let uu____4080 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____4080))
in (match (uu____4071) with
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when ((not (partial_discovery)) && (

let uu____4116 = (FStar_List.existsML (fun f -> (

let uu____4120 = (lowercase_module_name f)
in (Prims.op_Equality uu____4120 k))) filenames)
in (not (uu____4116)))) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && (

let uu____4130 = (lowercase_module_name f)
in (Prims.op_Equality uu____4130 k)))) filenames) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), uu____4132) -> begin
(intf)::[]
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (impl)) -> begin
(impl)::[]
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
[]
end)))
in (

let must_find_r = (fun f -> (

let uu____4154 = (must_find f)
in (FStar_List.rev uu____4154)))
in (

let by_target = (

let uu____4166 = (

let uu____4169 = (FStar_Util.smap_keys graph)
in (FStar_List.sortWith (fun x y -> (FStar_String.compare x y)) uu____4169))
in (FStar_List.collect (fun k -> (

let as_list = (must_find k)
in (

let is_interleaved = (Prims.op_Equality (FStar_List.length as_list) (Prims.parse_int "2"))
in (FStar_List.map (fun f -> (

let should_append_fsti = ((is_implementation f) && is_interleaved)
in (

let k1 = (lowercase_module_name f)
in (

let suffix = (

let uu____4214 = (

let uu____4223 = (FStar_Util.smap_try_find m k1)
in (FStar_Util.must uu____4223))
in (match (uu____4214) with
| (FStar_Pervasives_Native.Some (intf), uu____4253) when should_append_fsti -> begin
(intf)::[]
end
| uu____4260 -> begin
[]
end))
in (

let deps = (

let uu____4272 = (discover1 k1)
in (FStar_List.rev uu____4272))
in (

let deps_as_filenames = (

let uu____4278 = (FStar_List.collect must_find deps)
in (FStar_List.append uu____4278 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) uu____4166))
in (

let topologically_sorted1 = (

let uu____4286 = (FStar_ST.op_Bang topologically_sorted)
in (FStar_List.collect must_find_r uu____4286))
in ((FStar_List.iter (fun uu____4458 -> (match (uu____4458) with
| (m1, r) -> begin
(

let uu____4747 = ((

let uu____4750 = (FStar_ST.op_Bang r)
in (not (uu____4750))) && (

let uu____4894 = (FStar_Options.interactive ())
in (not (uu____4894))))
in (match (uu____4747) with
| true -> begin
(

let maybe_fst = (

let k = (FStar_String.length m1)
in (

let uu____4897 = ((k > (Prims.parse_int "4")) && (

let uu____4905 = (FStar_String.substring m1 (k - (Prims.parse_int "4")) (Prims.parse_int "4"))
in (Prims.op_Equality uu____4905 ".fst")))
in (match (uu____4897) with
| true -> begin
(

let uu____4912 = (FStar_String.substring m1 (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" uu____4912))
end
| uu____4919 -> begin
""
end)))
in (

let uu____4920 = (

let uu____4921 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m1 m1 maybe_fst)
in FStar_Errors.Err (uu____4921))
in (FStar_Exn.raise uu____4920)))
end
| uu____4922 -> begin
()
end))
end)) verify_flags);
((by_target), (topologically_sorted1), (immediate_graph));
)))))))));
))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun uu____4971 -> (match (uu____4971) with
| (f, deps1) -> begin
(

let deps2 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) deps1)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2)))
end)) deps))


let print : 'a 'b . ((Prims.string * Prims.string Prims.list) Prims.list * 'a * (Prims.string Prims.list * 'b) FStar_Util.smap)  ->  Prims.unit = (fun uu____5022 -> (match (uu____5022) with
| (make_deps, uu____5046, graph) -> begin
(

let uu____5080 = (FStar_Options.dep ())
in (match (uu____5080) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make make_deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph graph)
end
| FStar_Pervasives_Native.Some (uu____5083) -> begin
(FStar_Exn.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end))
end))





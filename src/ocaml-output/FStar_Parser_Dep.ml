
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
| uu____25 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____30 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____35 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____45 -> begin
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

let uu____70 = ((l > lext) && (

let uu____82 = (FStar_String.substring f (l - lext) lext)
in (uu____82 = ext)))
in (match (uu____70) with
| true -> begin
(

let uu____98 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____98))
end
| uu____109 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____110 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____110) with
| (FStar_Pervasives_Native.Some (m))::uu____116 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____120 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____127 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (uu____127 = 'i')))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____138 = (is_interface f)
in (not (uu____138))))


let list_of_option = (fun uu___83_149 -> (match (uu___83_149) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair = (fun uu____165 -> (match (uu____165) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____180 = (

let uu____182 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____182))
in (match (uu____180) with
| FStar_Pervasives_Native.Some (longname) -> begin
(FStar_String.lowercase longname)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____184 = (

let uu____185 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Errors.Err (uu____185))
in (FStar_Pervasives.raise uu____184))
end)))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____199 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____199))
in (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____217 = (FStar_Util.smap_try_find map1 key)
in (match (uu____217) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____237 = (is_interface full_path)
in (match (uu____237) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____244 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____255 = (is_interface full_path)
in (match (uu____255) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____262 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((FStar_List.iter (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.iter (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____283 = (check_and_strip_suffix f1)
in (match (uu____283) with
| FStar_Pervasives_Native.Some (longname) -> begin
(

let full_path = (match ((d = cwd)) with
| true -> begin
f1
end
| uu____287 -> begin
(FStar_Util.join_paths d f1)
end)
in (

let key = (FStar_String.lowercase longname)
in (add_entry key full_path)))
end
| FStar_Pervasives_Native.None -> begin
()
end)))) files))
end
| uu____289 -> begin
(

let uu____290 = (

let uu____291 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (uu____291))
in (FStar_Pervasives.raise uu____290))
end)) include_directories2);
(FStar_List.iter (fun f -> (

let uu____296 = (lowercase_module_name f)
in (add_entry uu____296 f))) filenames);
map1;
))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____314 = (

let uu____316 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____316))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____347 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____347))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.write found true);
)))
end
| uu____368 -> begin
()
end)) uu____314));
(FStar_ST.read found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____382 -> begin
[]
end)
in (

let names = (

let uu____385 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____385 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____397 = (string_of_lid l last1)
in (FStar_String.lowercase uu____397)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____402 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____402)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____413 = (

let uu____414 = (

let uu____415 = (

let uu____416 = (

let uu____418 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____418))
in (FStar_Util.must uu____416))
in (FStar_String.lowercase uu____415))
in (uu____414 <> k'))
in (match (uu____413) with
| true -> begin
(

let uu____419 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" uu____419 filename))
end
| uu____420 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____425 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun filename -> (

let filename1 = (FStar_Util.basename filename)
in (

let corelibs = (

let uu____436 = (FStar_Options.prims_basename ())
in (

let uu____437 = (

let uu____439 = (FStar_Options.pervasives_basename ())
in (

let uu____440 = (

let uu____442 = (FStar_Options.pervasives_native_basename ())
in (uu____442)::[])
in (uu____439)::uu____440))
in (uu____436)::uu____437))
in (match ((FStar_List.mem filename1 corelibs)) with
| true -> begin
[]
end
| uu____448 -> begin
(((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
end))))


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> (

let uu____496 = (

let uu____497 = (

let uu____498 = (FStar_ST.read deps)
in (FStar_List.existsML (fun d' -> (d' = d)) uu____498))
in (not (uu____497)))
in (match (uu____496) with
| true -> begin
(

let uu____505 = (

let uu____507 = (FStar_ST.read deps)
in (d)::uu____507)
in (FStar_ST.write deps uu____505))
end
| uu____515 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open_module = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____534 = (FStar_Util.smap_try_find working_map key)
in (match (uu____534) with
| FStar_Pervasives_Native.Some (pair) -> begin
((FStar_List.iter (fun f -> (

let uu____557 = (lowercase_module_name f)
in (add_dep uu____557))) (list_of_pair pair));
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
(FStar_Pervasives.raise (FStar_Errors.Err ("let-open only supported for modules, not namespaces")))
end
| uu____564 -> begin
(

let uu____565 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: in %s: no modules in namespace %s and no file with that name either\n" filename uu____565))
end)
end
| uu____566 -> begin
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
(FStar_Pervasives.raise (FStar_Errors.Err (e)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____579 = (string_of_lid lid true)
in (FStar_Util.print1_warning "Warning: no modules in namespace %s and no file with that name either\n" uu____579))
end)
end
| uu____580 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____588 = (record_open_module let_open lid)
in (match (uu____588) with
| true -> begin
()
end
| uu____589 -> begin
(

let msg = (match (let_open) with
| true -> begin
FStar_Pervasives_Native.Some ("let-open only supported for modules, not namespaces")
end
| uu____593 -> begin
FStar_Pervasives_Native.None
end)
in (record_open_namespace msg lid))
end)))
in (

let record_open_module_or_namespace = (fun uu____599 -> (match (uu____599) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace FStar_Pervasives_Native.None lid)
end
| Open_module -> begin
(

let uu____604 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____614 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____614) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____641 = (

let uu____642 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (uu____642))
in (FStar_Pervasives.raise uu____641))
end)))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (

let uu____651 = (FStar_Util.smap_try_find working_map key)
in (match (uu____651) with
| FStar_Pervasives_Native.Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____673 = (lowercase_module_name f)
in (add_dep uu____673))) (list_of_pair pair))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____678 = (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ()))
in (match (uu____678) with
| true -> begin
(

let uu____685 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid lid))
in (

let uu____686 = (string_of_lid lid false)
in (FStar_Util.print2_warning "%s (Warning): unbound module reference %s\n" uu____685 uu____686)))
end
| uu____687 -> begin
()
end))
end)))
in (

let uu____689 = (lowercase_join_longident lid false)
in (try_key uu____689))))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_file = (fun uu___84_761 -> (match (uu___84_761) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
((FStar_Util.print1_warning "Warning: file %s does not respect the one module per file convention\n" filename);
(FStar_List.iter collect_module modules);
)
end))
and collect_module = (fun uu___85_767 -> (match (uu___85_767) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____780 = (

let uu____781 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____781))
in ())
end
| uu____782 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____784 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____784))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____785 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____785))
end
| uu____786 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____794 -> (match (uu____794) with
| (m, r) -> begin
(

let uu____802 = (

let uu____803 = (

let uu____804 = (string_of_lid lid true)
in (FStar_String.lowercase uu____804))
in ((FStar_String.lowercase m) = uu____803))
in (match (uu____802) with
| true -> begin
(FStar_ST.write r true)
end
| uu____807 -> begin
()
end))
end)) verify_flags)
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____810) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____821 = (

let uu____822 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____822))
in ())
end
| uu____823 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____825 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____825))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____826 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____826))
end
| uu____827 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____835 -> (match (uu____835) with
| (m, r) -> begin
(

let uu____843 = (

let uu____844 = (

let uu____845 = (string_of_lid lid true)
in (FStar_String.lowercase uu____845))
in ((FStar_String.lowercase m) = uu____844))
in (match (uu____843) with
| true -> begin
(FStar_ST.write r true)
end
| uu____848 -> begin
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
and collect_decl = (fun uu___86_855 -> (match (uu___86_855) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
((

let uu____861 = (lowercase_join_longident lid true)
in (add_dep uu____861));
(record_module_alias ident lid);
)
end
| FStar_Parser_AST.TopLevelLet (uu____862, patterms) -> begin
(FStar_List.iter (fun uu____876 -> (match (uu____876) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____883, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____885; FStar_Parser_AST.mdest = uu____886; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____888; FStar_Parser_AST.mdest = uu____889; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____891, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____893; FStar_Parser_AST.mdest = uu____894; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____898, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____916 -> (match (uu____916) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____924, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____929) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____930) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____936 = (

let uu____937 = (FStar_ST.read num_of_toplevelmods)
in (uu____937 > (Prims.parse_int "1")))
in (match (uu____936) with
| true -> begin
(

let uu____940 = (

let uu____941 = (

let uu____942 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____942))
in FStar_Errors.Err (uu____941))
in (FStar_Pervasives.raise uu____940))
end
| uu____943 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___87_944 -> (match (uu___87_944) with
| FStar_Parser_AST.TyconAbstract (uu____945, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____953, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____963, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____991 -> (match (uu____991) with
| (uu____996, t, uu____998) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____1001, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____1036 -> (match (uu____1036) with
| (uu____1043, t, uu____1045, uu____1046) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___88_1051 -> (match (uu___88_1051) with
| FStar_Parser_AST.DefineEffect (uu____1052, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____1062, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___89_1070 -> (match (uu___89_1070) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____1071, t); FStar_Parser_AST.brange = uu____1073; FStar_Parser_AST.blevel = uu____1074; FStar_Parser_AST.aqual = uu____1075} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____1076, t); FStar_Parser_AST.brange = uu____1078; FStar_Parser_AST.blevel = uu____1079; FStar_Parser_AST.aqual = uu____1080} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____1082; FStar_Parser_AST.blevel = uu____1083; FStar_Parser_AST.aqual = uu____1084} -> begin
(collect_term t)
end
| uu____1085 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___90_1087 -> (match (uu___90_1087) with
| FStar_Const.Const_int (uu____1088, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____1098 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep uu____1098))))
end
| uu____1099 -> begin
()
end))
and collect_term' = (fun uu___91_1100 -> (match (uu___91_1100) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((match (((FStar_Ident.text_of_id s) = "@")) with
| true -> begin
(

let uu____1107 = (

let uu____1108 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____1108))
in (collect_term' uu____1107))
end
| uu____1109 -> begin
()
end);
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____1110) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____1111) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____1114) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Name (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((match (((FStar_List.length termimps) = (Prims.parse_int "1"))) with
| true -> begin
(record_lid lid)
end
| uu____1132 -> begin
()
end);
(FStar_List.iter (fun uu____1138 -> (match (uu____1138) with
| (t, uu____1142) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____1150) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____1152, patterms, t) -> begin
((FStar_List.iter (fun uu____1168 -> (match (uu____1168) with
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
| FStar_Parser_AST.Bind (uu____1177, t1, t2) -> begin
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
(FStar_List.iter (fun uu____1241 -> (match (uu____1241) with
| (uu____1244, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____1247) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____1285, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assign (uu____1288, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____1291) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____1295) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____1299, uu____1300) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___92_1306 -> (match (uu___92_1306) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____1307) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____1308) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____1314) -> begin
()
end
| FStar_Parser_AST.PatName (uu____1318) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____1319) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____1328) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____1340 -> (match (uu____1340) with
| (uu____1343, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
((collect_pattern p);
(collect_term t);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____1358 -> (match (uu____1358) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____1370 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____1370) with
| (ast, uu____1378) -> begin
((collect_file ast);
(FStar_ST.read deps);
)
end))));
))))))))))))


let print_graph = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1409 = (

let uu____1410 = (

let uu____1411 = (

let uu____1412 = (

let uu____1414 = (

let uu____1416 = (FStar_Util.smap_keys graph)
in (FStar_List.unique uu____1416))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1427 = (

let uu____1431 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must uu____1431))
in (FStar_Pervasives_Native.fst uu____1427))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep1 -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep1))) deps)))) uu____1414))
in (FStar_String.concat "\n" uu____1412))
in (Prims.strcat uu____1411 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1410))
in (FStar_Util.write_file "dep.graph" uu____1409));
))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (

let uu____1484 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (

let uu____1492 = (FStar_Util.mk_ref false)
in ((f), (uu____1492)))) uu____1484))
in (

let partial_discovery = (

let uu____1499 = ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
in (not (uu____1499)))
in (

let m = (build_map filenames)
in (

let file_names_of_key = (fun k -> (

let uu____1505 = (

let uu____1510 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1510))
in (match (uu____1505) with
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
| (FStar_Pervasives_Native.Some (i), uu____1541) when partial_discovery -> begin
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

let uu____1567 = (

let uu____1568 = (FStar_Util.smap_try_find graph key)
in (uu____1568 = FStar_Pervasives_Native.None))
in (match (uu____1567) with
| true -> begin
(

let uu____1583 = (

let uu____1588 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must uu____1588))
in (match (uu____1583) with
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
| (FStar_Pervasives_Native.Some (impl1), FStar_Pervasives_Native.Some (uu____1618)) when interface_only -> begin
[]
end
| (FStar_Pervasives_Native.Some (impl1), uu____1622) -> begin
(collect_one1 is_user_provided_filename m impl1)
end
| (FStar_Pervasives_Native.None, uu____1626) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in ((FStar_Util.smap_add graph key ((deps), (White)));
(FStar_List.iter (discover_one false partial_discovery) deps);
))))
end))
end
| uu____1637 -> begin
()
end)))
in (

let discover_command_line_argument = (fun f -> (

let m1 = (lowercase_module_name f)
in (

let interface_only = ((is_interface f) && (

let uu____1645 = (FStar_List.existsML (fun f1 -> ((

let uu____1650 = (lowercase_module_name f1)
in (uu____1650 = m1)) && (is_implementation f1))) filenames)
in (not (uu____1645))))
in (discover_one true interface_only m1))))
in ((FStar_List.iter discover_command_line_argument filenames);
(

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let uu____1675 = (

let uu____1679 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must uu____1679))
in (match (uu____1675) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((FStar_Util.print1 "Warning: recursive dependency on module %s\n" key);
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

let uu____1712 = (

let uu____1714 = (FStar_List.map (fun dep1 -> (

let uu____1721 = (discover ((key)::cycle) dep1)
in (dep1)::uu____1721)) direct_deps)
in (FStar_List.flatten uu____1714))
in (FStar_List.unique uu____1712))
in ((FStar_Util.smap_add graph key ((all_deps), (Black)));
(

let uu____1729 = (

let uu____1731 = (FStar_ST.read topologically_sorted)
in (key)::uu____1731)
in (FStar_ST.write topologically_sorted uu____1729));
all_deps;
));
)
end)
end)))
in (

let discover1 = (discover [])
in (

let must_find = (fun k -> (

let uu____1748 = (

let uu____1753 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1753))
in (match (uu____1748) with
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when ((not (partial_discovery)) && (

let uu____1773 = (FStar_List.existsML (fun f -> (

let uu____1777 = (lowercase_module_name f)
in (uu____1777 = k))) filenames)
in (not (uu____1773)))) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && (

let uu____1785 = (lowercase_module_name f)
in (uu____1785 = k)))) filenames) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), uu____1787) -> begin
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

let uu____1801 = (must_find f)
in (FStar_List.rev uu____1801)))
in (

let by_target = (

let uu____1808 = (

let uu____1810 = (FStar_Util.smap_keys graph)
in (FStar_List.sortWith (fun x y -> (FStar_String.compare x y)) uu____1810))
in (FStar_List.collect (fun k -> (

let as_list = (must_find k)
in (

let is_interleaved = ((FStar_List.length as_list) = (Prims.parse_int "2"))
in (FStar_List.map (fun f -> (

let should_append_fsti = ((is_implementation f) && is_interleaved)
in (

let k1 = (lowercase_module_name f)
in (

let suffix = (

let uu____1847 = (

let uu____1852 = (FStar_Util.smap_try_find m k1)
in (FStar_Util.must uu____1852))
in (match (uu____1847) with
| (FStar_Pervasives_Native.Some (intf), uu____1868) when should_append_fsti -> begin
(intf)::[]
end
| uu____1872 -> begin
[]
end))
in (

let deps = (

let uu____1879 = (discover1 k1)
in (FStar_List.rev uu____1879))
in (

let deps_as_filenames = (

let uu____1883 = (FStar_List.collect must_find deps)
in (FStar_List.append uu____1883 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) uu____1808))
in (

let topologically_sorted1 = (

let uu____1888 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r uu____1888))
in ((FStar_List.iter (fun uu____1903 -> (match (uu____1903) with
| (m1, r) -> begin
(

let uu____1911 = ((

let uu____1914 = (FStar_ST.read r)
in (not (uu____1914))) && (

let uu____1918 = (FStar_Options.interactive ())
in (not (uu____1918))))
in (match (uu____1911) with
| true -> begin
(

let maybe_fst = (

let k = (FStar_String.length m1)
in (

let uu____1923 = ((k > (Prims.parse_int "4")) && (

let uu____1931 = (FStar_String.substring m1 (k - (Prims.parse_int "4")) (Prims.parse_int "4"))
in (uu____1931 = ".fst")))
in (match (uu____1923) with
| true -> begin
(

let uu____1938 = (FStar_String.substring m1 (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" uu____1938))
end
| uu____1945 -> begin
""
end)))
in (

let uu____1946 = (

let uu____1947 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m1 m1 maybe_fst)
in FStar_Errors.Err (uu____1947))
in (FStar_Pervasives.raise uu____1946)))
end
| uu____1948 -> begin
()
end))
end)) verify_flags);
((by_target), (topologically_sorted1), (immediate_graph));
)))))))));
))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun uu____1977 -> (match (uu____1977) with
| (f, deps1) -> begin
(

let deps2 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s ' ' "\\ ")) deps1)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2)))
end)) deps))


let print = (fun uu____2011 -> (match (uu____2011) with
| (make_deps, uu____2024, graph) -> begin
(

let uu____2042 = (FStar_Options.dep ())
in (match (uu____2042) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make make_deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph graph)
end
| FStar_Pervasives_Native.Some (uu____2044) -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end))
end))





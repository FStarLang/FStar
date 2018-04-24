
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
| uu____6 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____12 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____18 -> begin
false
end))


type files_for_module_name =
(Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap

type color =
| White
| Gray
| Black


let uu___is_White : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| White -> begin
true
end
| uu____34 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____40 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____46 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____52 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____58 -> begin
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

let uu____86 = ((l > lext) && (

let uu____98 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____98 ext)))
in (match (uu____86) with
| true -> begin
(

let uu____115 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____115))
end
| uu____126 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____127 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____127) with
| (FStar_Pervasives_Native.Some (m))::uu____137 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____144 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____154 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____154 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____163 = (is_interface f)
in (not (uu____163))))


let list_of_option : 'Auu____168 . 'Auu____168 FStar_Pervasives_Native.option  ->  'Auu____168 Prims.list = (fun uu___58_177 -> (match (uu___58_177) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____185 . ('Auu____185 FStar_Pervasives_Native.option * 'Auu____185 FStar_Pervasives_Native.option)  ->  'Auu____185 Prims.list = (fun uu____200 -> (match (uu____200) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let module_name_of_file : Prims.string  ->  Prims.string = (fun f -> (

let uu____224 = (

let uu____227 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____227))
in (match (uu____224) with
| FStar_Pervasives_Native.Some (longname) -> begin
longname
end
| FStar_Pervasives_Native.None -> begin
(

let uu____229 = (

let uu____234 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in ((FStar_Errors.Fatal_NotValidFStarFile), (uu____234)))
in (FStar_Errors.raise_err uu____229))
end)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____240 = (module_name_of_file f)
in (FStar_String.lowercase uu____240)))


let namespace_of_module : Prims.string  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun f -> (

let lid = (

let uu____249 = (FStar_Ident.path_of_text f)
in (FStar_Ident.lid_of_path uu____249 FStar_Range.dummyRange))
in (match (lid.FStar_Ident.ns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____252 -> begin
(

let uu____255 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_Pervasives_Native.Some (uu____255))
end)))


type file_name =
Prims.string


type module_name =
Prims.string

type dependence =
| UseInterface of module_name
| PreferInterface of module_name
| UseImplementation of module_name


let uu___is_UseInterface : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UseInterface (_0) -> begin
true
end
| uu____277 -> begin
false
end))


let __proj__UseInterface__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseInterface (_0) -> begin
_0
end))


let uu___is_PreferInterface : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| PreferInterface (_0) -> begin
true
end
| uu____291 -> begin
false
end))


let __proj__PreferInterface__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| PreferInterface (_0) -> begin
_0
end))


let uu___is_UseImplementation : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
true
end
| uu____305 -> begin
false
end))


let __proj__UseImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
_0
end))


type dependences =
dependence Prims.list


let empty_dependences : 'Auu____317 . unit  ->  'Auu____317 Prims.list = (fun uu____320 -> [])

type dependence_graph =
| Deps of (dependences * color) FStar_Util.smap


let uu___is_Deps : dependence_graph  ->  Prims.bool = (fun projectee -> true)


let __proj__Deps__item___0 : dependence_graph  ->  (dependences * color) FStar_Util.smap = (fun projectee -> (match (projectee) with
| Deps (_0) -> begin
_0
end))

type deps =
| Mk of (dependence_graph * files_for_module_name * file_name Prims.list)


let uu___is_Mk : deps  ->  Prims.bool = (fun projectee -> true)


let __proj__Mk__item___0 : deps  ->  (dependence_graph * files_for_module_name * file_name Prims.list) = (fun projectee -> (match (projectee) with
| Mk (_0) -> begin
_0
end))


let deps_try_find : dependence_graph  ->  Prims.string  ->  (dependences * color) FStar_Pervasives_Native.option = (fun uu____423 k -> (match (uu____423) with
| Deps (m) -> begin
(FStar_Util.smap_try_find m k)
end))


let deps_add_dep : dependence_graph  ->  Prims.string  ->  (dependences * color)  ->  unit = (fun uu____458 k v1 -> (match (uu____458) with
| Deps (m) -> begin
(FStar_Util.smap_add m k v1)
end))


let deps_keys : dependence_graph  ->  Prims.string Prims.list = (fun uu____482 -> (match (uu____482) with
| Deps (m) -> begin
(FStar_Util.smap_keys m)
end))


let deps_empty : unit  ->  dependence_graph = (fun uu____500 -> (

let uu____501 = (FStar_Util.smap_create (Prims.parse_int "41"))
in Deps (uu____501)))


let empty_deps : deps = (

let uu____512 = (

let uu____521 = (deps_empty ())
in (

let uu____522 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((uu____521), (uu____522), ([]))))
in Mk (uu____512))


let module_name_of_dep : dependence  ->  module_name = (fun uu___59_557 -> (match (uu___59_557) with
| UseInterface (m) -> begin
m
end
| PreferInterface (m) -> begin
m
end
| UseImplementation (m) -> begin
m
end))


let resolve_module_name : files_for_module_name  ->  module_name  ->  module_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____575 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____575) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____597) -> begin
(

let uu____612 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____612))
end
| FStar_Pervasives_Native.Some (uu____613, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____629 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____629))
end
| uu____630 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____655 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____655) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____677) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____692 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____717 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____717) with
| FStar_Pervasives_Native.Some (uu____738, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____754 -> begin
FStar_Pervasives_Native.None
end)))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____775 = (interface_of file_system_map key)
in (FStar_Option.isSome uu____775)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____788 = (implementation_of file_system_map key)
in (FStar_Option.isSome uu____788)))


let cache_file_name : Prims.string  ->  Prims.string = (fun fn -> (

let uu____796 = (

let uu____797 = (FStar_Options.lax ())
in (match (uu____797) with
| true -> begin
(Prims.strcat fn ".checked.lax")
end
| uu____798 -> begin
(Prims.strcat fn ".checked")
end))
in (FStar_Options.prepend_cache_dir uu____796)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____834 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____834)))))))
in (

let maybe_add_suffix = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____841 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____843 = (interface_of file_system_map key)
in (match (uu____843) with
| FStar_Pervasives_Native.None -> begin
(

let uu____847 = (

let uu____852 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____852)))
in (FStar_Errors.raise_err uu____847))
end
| FStar_Pervasives_Native.Some (f) -> begin
(match (use_checked_file) with
| true -> begin
(FStar_Options.prepend_cache_dir (Prims.strcat f ".source"))
end
| uu____854 -> begin
f
end)
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____856 = ((cmd_line_has_impl key) && (

let uu____858 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____858)))
in (match (uu____856) with
| true -> begin
(

let uu____861 = (FStar_Options.expose_interfaces ())
in (match (uu____861) with
| true -> begin
(

let uu____862 = (

let uu____863 = (implementation_of file_system_map key)
in (FStar_Option.get uu____863))
in (maybe_add_suffix uu____862))
end
| uu____866 -> begin
(

let uu____867 = (

let uu____872 = (

let uu____873 = (

let uu____874 = (implementation_of file_system_map key)
in (FStar_Option.get uu____874))
in (

let uu____877 = (

let uu____878 = (interface_of file_system_map key)
in (FStar_Option.get uu____878))
in (FStar_Util.format2 "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" uu____873 uu____877)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____872)))
in (FStar_Errors.raise_err uu____867))
end))
end
| uu____881 -> begin
(

let uu____882 = (

let uu____883 = (interface_of file_system_map key)
in (FStar_Option.get uu____883))
in (maybe_add_suffix uu____882))
end))
end
| PreferInterface (key) -> begin
(

let uu____887 = (implementation_of file_system_map key)
in (match (uu____887) with
| FStar_Pervasives_Native.None -> begin
(

let uu____891 = (

let uu____896 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____896)))
in (FStar_Errors.raise_err uu____891))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end
| UseImplementation (key) -> begin
(

let uu____899 = (implementation_of file_system_map key)
in (match (uu____899) with
| FStar_Pervasives_Native.None -> begin
(

let uu____903 = (

let uu____908 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____908)))
in (FStar_Errors.raise_err uu____903))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____952 = (deps_try_find deps fn)
in (match (uu____952) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some (deps1, uu____966) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let add_dependence : dependence_graph  ->  file_name  ->  file_name  ->  unit = (fun deps from to_ -> (

let add_dep = (fun uu____1007 to_1 -> (match (uu____1007) with
| (d, color) -> begin
(

let uu____1027 = (is_interface to_1)
in (match (uu____1027) with
| true -> begin
(

let uu____1034 = (

let uu____1037 = (

let uu____1038 = (lowercase_module_name to_1)
in PreferInterface (uu____1038))
in (uu____1037)::d)
in ((uu____1034), (color)))
end
| uu____1041 -> begin
(

let uu____1042 = (

let uu____1045 = (

let uu____1046 = (lowercase_module_name to_1)
in UseImplementation (uu____1046))
in (uu____1045)::d)
in ((uu____1042), (color)))
end))
end))
in (

let uu____1049 = (deps_try_find deps from)
in (match (uu____1049) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1060 = (add_dep (((empty_dependences ())), (White)) to_)
in (deps_add_dep deps from uu____1060))
end
| FStar_Pervasives_Native.Some (key_deps) -> begin
(

let uu____1076 = (add_dep key_deps to_)
in (deps_add_dep deps from uu____1076))
end))))


let print_graph : dependence_graph  ->  unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1089 = (

let uu____1090 = (

let uu____1091 = (

let uu____1092 = (

let uu____1095 = (

let uu____1098 = (deps_keys graph)
in (FStar_List.unique uu____1098))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1107 = (

let uu____1112 = (deps_try_find graph k)
in (FStar_Util.must uu____1112))
in (FStar_Pervasives_Native.fst uu____1107))
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (FStar_Util.format2 " %s -> %s" (r k) (r (module_name_of_dep dep1))))
in (FStar_List.map print7 deps))))) uu____1095))
in (FStar_String.concat "\n" uu____1092))
in (Prims.strcat uu____1091 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1090))
in (FStar_Util.write_file "dep.graph" uu____1089));
))


let build_inclusion_candidates_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1147 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____1164 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____1164))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____1190 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____1190 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____1209 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____1210 -> begin
(

let uu____1211 = (

let uu____1216 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____1216)))
in (FStar_Errors.raise_err uu____1211))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____1262 = (FStar_Util.smap_try_find map1 key)
in (match (uu____1262) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____1299 = (is_interface full_path)
in (match (uu____1299) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____1312 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1333 = (is_interface full_path)
in (match (uu____1333) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____1346 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____1360 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____1374 -> (match (uu____1374) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____1360));
(FStar_List.iter (fun f -> (

let uu____1385 = (lowercase_module_name f)
in (add_entry uu____1385 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____1406 = (

let uu____1409 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____1409))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____1435 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____1435))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____1570 -> begin
()
end)) uu____1406));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____1685 -> begin
[]
end)
in (

let names = (

let uu____1689 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____1689 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____1704 = (string_of_lid l last1)
in (FStar_String.lowercase uu____1704)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____1710 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____1710)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____1724 = (

let uu____1725 = (

let uu____1726 = (

let uu____1727 = (

let uu____1730 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____1730))
in (FStar_Util.must uu____1727))
in (FStar_String.lowercase uu____1726))
in (Prims.op_disEquality uu____1725 k'))
in (match (uu____1724) with
| true -> begin
(

let uu____1731 = (FStar_Ident.range_of_lid lid)
in (

let uu____1732 = (

let uu____1737 = (

let uu____1738 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____1738 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____1737)))
in (FStar_Errors.log_issue uu____1731 uu____1732)))
end
| uu____1739 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1745 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____1761 = (FStar_Options.prims_basename ())
in (

let uu____1762 = (

let uu____1765 = (FStar_Options.pervasives_basename ())
in (

let uu____1766 = (

let uu____1769 = (FStar_Options.pervasives_native_basename ())
in (uu____1769)::[])
in (uu____1765)::uu____1766))
in (uu____1761)::uu____1762))
in (match ((FStar_List.mem filename corelibs)) with
| true -> begin
[]
end
| uu____1780 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____1804 = (

let uu____1807 = (lowercase_module_name full_filename)
in (namespace_of_module uu____1807))
in (match (uu____1804) with
| FStar_Pervasives_Native.None -> begin
implicit_deps
end
| FStar_Pervasives_Native.Some (ns) -> begin
(FStar_List.append implicit_deps ((((ns), (Open_namespace)))::[]))
end)))
end))))


let collect_one : files_for_module_name  ->  Prims.string  ->  (dependence Prims.list * dependence Prims.list) = (fun original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let mo_roots = (FStar_Util.mk_ref [])
in (

let add_dep = (fun deps1 d -> (

let uu____2093 = (

let uu____2094 = (

let uu____2095 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (fun d' -> (Prims.op_Equality d' d)) uu____2095))
in (not (uu____2094)))
in (match (uu____2093) with
| true -> begin
(

let uu____2199 = (

let uu____2202 = (FStar_ST.op_Bang deps1)
in (d)::uu____2202)
in (FStar_ST.op_Colon_Equals deps1 uu____2199))
end
| uu____2403 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let add_dependence_edge = (fun original_or_working_map lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____2435 = (resolve_module_name original_or_working_map key)
in (match (uu____2435) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (PreferInterface (module_name)));
(

let uu____2546 = (((has_interface original_or_working_map module_name) && (has_implementation original_or_working_map module_name)) && (

let uu____2548 = (FStar_Options.dep ())
in (Prims.op_Equality uu____2548 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____2546) with
| true -> begin
(add_dep mo_roots (UseImplementation (module_name)))
end
| uu____2658 -> begin
()
end));
true;
)
end
| uu____2659 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____2673 = ((let_open && (add_dependence_edge working_map lid)) || ((not (let_open)) && (add_dependence_edge original_map lid)))
in (match (uu____2673) with
| true -> begin
true
end
| uu____2674 -> begin
((match (let_open) with
| true -> begin
(

let uu____2676 = (FStar_Ident.range_of_lid lid)
in (

let uu____2677 = (

let uu____2682 = (

let uu____2683 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____2683))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2682)))
in (FStar_Errors.log_issue uu____2676 uu____2677)))
end
| uu____2684 -> begin
()
end);
false;
)
end)))
in (

let record_open_namespace = (fun lid -> (

let key = (lowercase_join_longident lid true)
in (

let r = (enter_namespace original_map working_map key)
in (match ((not (r))) with
| true -> begin
(

let uu____2693 = (FStar_Ident.range_of_lid lid)
in (

let uu____2694 = (

let uu____2699 = (

let uu____2700 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____2700))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2699)))
in (FStar_Errors.log_issue uu____2693 uu____2694)))
end
| uu____2701 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____2713 = (record_open_module let_open lid)
in (match (uu____2713) with
| true -> begin
()
end
| uu____2714 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____2715 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____2725 -> (match (uu____2725) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____2732 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (

let uu____2745 = (FStar_Ident.text_of_id ident)
in (FStar_String.lowercase uu____2745))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____2747 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____2747) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____2801 = (FStar_Ident.range_of_lid lid)
in (

let uu____2802 = (

let uu____2807 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2807)))
in (FStar_Errors.log_issue uu____2801 uu____2802)));
false;
)
end)))))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____2814 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____2818 = (add_dependence_edge working_map module_name)
in (match (uu____2818) with
| true -> begin
()
end
| uu____2819 -> begin
(

let uu____2820 = (FStar_Options.debug_any ())
in (match (uu____2820) with
| true -> begin
(

let uu____2821 = (FStar_Ident.range_of_lid lid)
in (

let uu____2822 = (

let uu____2827 = (

let uu____2828 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____2828))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____2827)))
in (FStar_Errors.log_issue uu____2821 uu____2822)))
end
| uu____2829 -> begin
()
end))
end)))
end))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_module = (fun uu___60_2944 -> (match (uu___60_2944) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2953 = (

let uu____2954 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2954))
in ())
end
| uu____2955 -> begin
()
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____2958) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2965 = (

let uu____2966 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2966))
in ())
end
| uu____2967 -> begin
()
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
)) decls))
and collect_decl = (fun uu___61_2975 -> (match (uu___61_2975) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let uu____2980 = (record_module_alias ident lid)
in (match (uu____2980) with
| true -> begin
(

let uu____2981 = (

let uu____2982 = (lowercase_join_longident lid true)
in PreferInterface (uu____2982))
in (add_dep deps uu____2981))
end
| uu____3088 -> begin
()
end))
end
| FStar_Parser_AST.TopLevelLet (uu____3089, patterms) -> begin
(FStar_List.iter (fun uu____3111 -> (match (uu____3111) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (uu____3120, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____3126, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3128; FStar_Parser_AST.mdest = uu____3129; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3131; FStar_Parser_AST.mdest = uu____3132; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____3134, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3136; FStar_Parser_AST.mdest = uu____3137; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____3141, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____3171 -> (match (uu____3171) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____3184, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____3191) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____3192) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____3300 = (

let uu____3301 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____3301 > (Prims.parse_int "1")))
in (match (uu____3300) with
| true -> begin
(

let uu____3401 = (

let uu____3406 = (

let uu____3407 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____3407))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____3406)))
in (

let uu____3408 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____3401 uu____3408)))
end
| uu____3409 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___62_3410 -> (match (uu___62_3410) with
| FStar_Parser_AST.TyconAbstract (uu____3411, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____3423, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____3437, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3483 -> (match (uu____3483) with
| (uu____3492, t, uu____3494) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____3499, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3558 -> (match (uu____3558) with
| (uu____3571, t, uu____3573, uu____3574) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___63_3583 -> (match (uu___63_3583) with
| FStar_Parser_AST.DefineEffect (uu____3584, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____3598, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___64_3609 -> (match (uu___64_3609) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3610, t); FStar_Parser_AST.brange = uu____3612; FStar_Parser_AST.blevel = uu____3613; FStar_Parser_AST.aqual = uu____3614} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3615, t); FStar_Parser_AST.brange = uu____3617; FStar_Parser_AST.blevel = uu____3618; FStar_Parser_AST.aqual = uu____3619} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____3621; FStar_Parser_AST.blevel = uu____3622; FStar_Parser_AST.aqual = uu____3623} -> begin
(collect_term t)
end
| uu____3624 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___65_3626 -> (match (uu___65_3626) with
| FStar_Const.Const_int (uu____3627, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____3642 = (

let uu____3643 = (FStar_Util.format2 "fstar.%sint%s" u w)
in PreferInterface (uu____3643))
in (add_dep deps uu____3642))))
end
| FStar_Const.Const_char (uu____3749) -> begin
(add_dep deps (PreferInterface ("fstar.char")))
end
| FStar_Const.Const_float (uu____3855) -> begin
(add_dep deps (PreferInterface ("fstar.float")))
end
| uu____3961 -> begin
()
end))
and collect_term' = (fun uu___66_3962 -> (match (uu___66_3962) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((

let uu____3971 = (

let uu____3972 = (FStar_Ident.text_of_id s)
in (Prims.op_Equality uu____3972 "@"))
in (match (uu____3971) with
| true -> begin
(

let uu____3973 = (

let uu____3974 = (

let uu____3975 = (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
in (FStar_Ident.lid_of_path uu____3975 FStar_Range.dummyRange))
in FStar_Parser_AST.Name (uu____3974))
in (collect_term' uu____3973))
end
| uu____3976 -> begin
()
end));
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____3977) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____3978) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____3981) -> begin
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
| uu____4003 -> begin
()
end);
(FStar_List.iter (fun uu____4011 -> (match (uu____4011) with
| (t, uu____4017) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____4027) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____4029, patterms, t) -> begin
((FStar_List.iter (fun uu____4079 -> (match (uu____4079) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____4108 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
in ());
(collect_pattern pat);
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
| FStar_Parser_AST.Bind (uu____4117, t1, t2) -> begin
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
(FStar_List.iter (fun uu____4213 -> (match (uu____4213) with
| (uu____4218, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____4221) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____4277, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____4281) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____4287) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____4293, uu____4294) -> begin
(collect_term t)
end
| FStar_Parser_AST.VQuote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (uu____4296) -> begin
()
end
| FStar_Parser_AST.Antiquote (uu____4301) -> begin
()
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___67_4313 -> (match (uu___67_4313) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____4314) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____4315) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____4323) -> begin
()
end
| FStar_Parser_AST.PatName (uu____4330) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____4331) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____4345) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____4364 -> (match (uu____4364) with
| (uu____4369, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, (t, FStar_Pervasives_Native.None)) -> begin
((collect_pattern p);
(collect_term t);
)
end
| FStar_Parser_AST.PatAscribed (p, (t, FStar_Pervasives_Native.Some (tac))) -> begin
((collect_pattern p);
(collect_term t);
(collect_term tac);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____4414 -> (match (uu____4414) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____4432 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____4432) with
| (ast, uu____4452) -> begin
(

let mname = (lowercase_module_name filename)
in ((

let uu____4467 = (((is_interface filename) && (has_implementation original_map mname)) && (

let uu____4469 = (FStar_Options.dep ())
in (Prims.op_Equality uu____4469 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____4467) with
| true -> begin
(add_dep mo_roots (UseImplementation (mname)))
end
| uu____4579 -> begin
()
end));
(collect_module ast);
(

let uu____4581 = (FStar_ST.op_Bang deps)
in (

let uu____4687 = (FStar_ST.op_Bang mo_roots)
in ((uu____4581), (uu____4687))));
))
end))));
))))))))))))))


let collect_one_cache : (dependence Prims.list * dependence Prims.list) FStar_Util.smap FStar_ST.ref = (

let uu____4844 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (FStar_Util.mk_ref uu____4844))


let set_collect_one_cache : (dependence Prims.list * dependence Prims.list) FStar_Util.smap  ->  unit = (fun cache -> (FStar_ST.op_Colon_Equals collect_one_cache cache))


let collect : Prims.string Prims.list  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____4979 = (FStar_Options.find_file fn)
in (match (uu____4979) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4982 = (

let uu____4987 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____4987)))
in (FStar_Errors.raise_err uu____4982))
end
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end)))))
in (

let dep_graph = (deps_empty ())
in (

let file_system_map = (build_map all_cmd_line_files1)
in (

let rec discover_one = (fun file_name -> (

let uu____4997 = (

let uu____4998 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____4998 FStar_Pervasives_Native.None))
in (match (uu____4997) with
| true -> begin
(

let uu____5015 = (

let uu____5024 = (

let uu____5035 = (FStar_ST.op_Bang collect_one_cache)
in (FStar_Util.smap_try_find uu____5035 file_name))
in (match (uu____5024) with
| FStar_Pervasives_Native.Some (cached) -> begin
cached
end
| FStar_Pervasives_Native.None -> begin
(collect_one file_system_map file_name)
end))
in (match (uu____5015) with
| (deps, mo_roots) -> begin
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____5150 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____5150) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____5153 -> begin
deps
end)))
in ((

let uu____5155 = (

let uu____5160 = (FStar_List.unique deps1)
in ((uu____5160), (White)))
in (deps_add_dep dep_graph file_name uu____5155));
(

let uu____5165 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____5165));
))
end))
end
| uu____5168 -> begin
()
end)))
in ((FStar_List.iter discover_one all_cmd_line_files1);
(

let topological_dependences_of = (fun all_command_line_files -> (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec aux = (fun cycle filename -> (

let uu____5204 = (

let uu____5209 = (deps_try_find dep_graph filename)
in (FStar_Util.must uu____5209))
in (match (uu____5204) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((

let uu____5223 = (

let uu____5228 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Warning_RecursiveDependency), (uu____5228)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____5223));
(FStar_Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (FStar_String.concat "\n`used by` " cycle));
(print_graph dep_graph);
(FStar_Util.print_string "\n");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| Black -> begin
()
end
| White -> begin
((deps_add_dep dep_graph filename ((direct_deps), (Gray)));
(

let uu____5234 = (dependences_of file_system_map dep_graph all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____5234));
(deps_add_dep dep_graph filename ((direct_deps), (Black)));
(

let uu____5240 = (

let uu____5243 = (FStar_ST.op_Bang topologically_sorted)
in (filename)::uu____5243)
in (FStar_ST.op_Colon_Equals topologically_sorted uu____5240));
)
end)
end)))
in ((FStar_List.iter (aux []) all_command_line_files);
(FStar_ST.op_Bang topologically_sorted);
))))
in ((FStar_All.pipe_right all_cmd_line_files1 (FStar_List.iter (fun f -> (

let m = (lowercase_module_name f)
in (FStar_Options.add_verify_module m)))));
(

let uu____5563 = (topological_dependences_of all_cmd_line_files1)
in ((uu____5563), (Mk (((dep_graph), (file_system_map), (all_cmd_line_files1))))));
));
))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun uu____5580 f -> (match (uu____5580) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(dependences_of file_system_map deps all_cmd_line_files f)
end))


let hash_dependences : deps  ->  Prims.string  ->  (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option = (fun uu____5609 fn -> (match (uu____5609) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let fn1 = (

let uu____5627 = (FStar_Options.find_file fn)
in (match (uu____5627) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____5631 -> begin
fn
end))
in (

let cache_file = (cache_file_name fn1)
in (

let digest_of_file1 = (fun fn2 -> ((

let uu____5642 = (FStar_Options.debug_any ())
in (match (uu____5642) with
| true -> begin
(FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2)
end
| uu____5643 -> begin
()
end));
(FStar_Util.digest_of_file fn2);
))
in (

let module_name = (lowercase_module_name fn1)
in (

let source_hash = (digest_of_file1 fn1)
in (

let interface_hash = (

let uu____5653 = ((is_implementation fn1) && (has_interface file_system_map module_name))
in (match (uu____5653) with
| true -> begin
(

let uu____5660 = (

let uu____5665 = (

let uu____5666 = (

let uu____5667 = (interface_of file_system_map module_name)
in (FStar_Option.get uu____5667))
in (digest_of_file1 uu____5666))
in (("interface"), (uu____5665)))
in (uu____5660)::[])
end
| uu____5678 -> begin
[]
end))
in (

let binary_deps = (

let uu____5686 = (dependences_of file_system_map deps all_cmd_line_files fn1)
in (FStar_All.pipe_right uu____5686 (FStar_List.filter (fun fn2 -> (

let uu____5696 = ((is_interface fn2) && (

let uu____5698 = (lowercase_module_name fn2)
in (Prims.op_Equality uu____5698 module_name)))
in (not (uu____5696)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____5708 = (lowercase_module_name fn11)
in (

let uu____5709 = (lowercase_module_name fn2)
in (FStar_String.compare uu____5708 uu____5709)))) binary_deps)
in (

let rec hash_deps = (fun out uu___68_5736 -> (match (uu___68_5736) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps1 -> begin
(

let cache_fn = (cache_file_name fn2)
in (match ((FStar_Util.file_exists cache_fn)) with
| true -> begin
(

let uu____5780 = (

let uu____5787 = (

let uu____5792 = (lowercase_module_name fn2)
in (

let uu____5793 = (digest_of_file1 cache_fn)
in ((uu____5792), (uu____5793))))
in (uu____5787)::out)
in (hash_deps uu____5780 deps1))
end
| uu____5798 -> begin
((

let uu____5800 = (FStar_Options.debug_any ())
in (match (uu____5800) with
| true -> begin
(FStar_Util.print2 "%s: missed digest of file %s\n" cache_file cache_fn)
end
| uu____5801 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end))
end))
in (hash_deps [] binary_deps1))))))))))
end))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____5829 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____5848 -> (match (uu____5848) with
| (m, d) -> begin
(

let uu____5855 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____5855))
end))))
in (FStar_All.pipe_right uu____5829 (FStar_String.concat "\n"))))


let print_make : deps  ->  unit = (fun uu____5862 -> (match (uu____5862) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let keys = (deps_keys deps)
in (FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____5882 = (

let uu____5887 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____5887 FStar_Option.get))
in (match (uu____5882) with
| (f_deps, uu____5909) -> begin
(

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) f_deps)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1))))
end))))))
end))


let print_full : deps  ->  unit = (fun uu____5923 -> (match (uu____5923) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let sort_output_files = (fun orig_output_file_map -> (

let order = (FStar_Util.mk_ref [])
in (

let remaining_output_files = (FStar_Util.smap_copy orig_output_file_map)
in (

let visited_other_modules = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let should_visit = (fun lc_module_name -> ((

let uu____5964 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____5964)) || (

let uu____5968 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____5968))))
in (

let mark_visiting = (fun lc_module_name -> (

let ml_file_opt = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in ((FStar_Util.smap_remove remaining_output_files lc_module_name);
(FStar_Util.smap_add visited_other_modules lc_module_name true);
ml_file_opt;
)))
in (

let emit_output_file_opt = (fun ml_file_opt -> (match (ml_file_opt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (ml_file) -> begin
(

let uu____5995 = (

let uu____5998 = (FStar_ST.op_Bang order)
in (ml_file)::uu____5998)
in (FStar_ST.op_Colon_Equals order uu____5995))
end))
in (

let rec aux = (fun uu___69_6214 -> (match (uu___69_6214) with
| [] -> begin
()
end
| (lc_module_name)::modules_to_extract -> begin
(

let visit_file = (fun file_opt -> (match (file_opt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (file_name) -> begin
(

let uu____6232 = (deps_try_find deps file_name)
in (match (uu____6232) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6243 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____6243))
end
| FStar_Pervasives_Native.Some (immediate_deps, uu____6245) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____6256 = (should_visit lc_module_name)
in (match (uu____6256) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____6261 = (implementation_of file_system_map lc_module_name)
in (visit_file uu____6261));
(

let uu____6265 = (interface_of file_system_map lc_module_name)
in (visit_file uu____6265));
(emit_output_file_opt ml_file_opt);
))
end
| uu____6268 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____6273 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____6273));
))))))))))
in (

let keys = (deps_keys deps)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____6394 = (

let uu____6395 = (

let uu____6398 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____6398))
in (FStar_Option.get uu____6395))
in (FStar_Util.replace_chars uu____6394 46 (*.*) "_"))
in (FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____6413 = (output_file ".ml" f)
in (norm_path uu____6413)))
in (

let output_krml_file = (fun f -> (

let uu____6420 = (output_file ".krml" f)
in (norm_path uu____6420)))
in (

let output_cmx_file = (fun f -> (

let uu____6427 = (output_file ".cmx" f)
in (norm_path uu____6427)))
in (

let cache_file = (fun f -> (

let uu____6434 = (cache_file_name f)
in (norm_path uu____6434)))
in (

let transitive_krml = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____6477 = (

let uu____6482 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____6482 FStar_Option.get))
in (match (uu____6477) with
| (f_deps, uu____6504) -> begin
(

let norm_f = (norm_path f)
in (

let files = (FStar_List.map (file_of_dep_aux true file_system_map all_cmd_line_files) f_deps)
in (

let files1 = (FStar_List.map norm_path files)
in (

let files2 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files1)
in (

let files3 = (FStar_String.concat "\\\n\t" files2)
in ((

let uu____6520 = (is_interface f)
in (match (uu____6520) with
| true -> begin
(

let uu____6521 = (

let uu____6522 = (FStar_Options.prepend_cache_dir norm_f)
in (norm_path uu____6522))
in (FStar_Util.print3 "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" uu____6521 norm_f files3))
end
| uu____6523 -> begin
()
end));
(

let uu____6525 = (cache_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____6525 norm_f files3));
(

let already_there = (

let uu____6529 = (

let uu____6540 = (

let uu____6541 = (output_file ".krml" f)
in (norm_path uu____6541))
in (FStar_Util.smap_try_find transitive_krml uu____6540))
in (match (uu____6529) with
| FStar_Pervasives_Native.Some (uu____6552, already_there, uu____6554) -> begin
already_there
end
| FStar_Pervasives_Native.None -> begin
[]
end))
in ((

let uu____6576 = (

let uu____6577 = (output_file ".krml" f)
in (norm_path uu____6577))
in (

let uu____6578 = (

let uu____6587 = (

let uu____6588 = (output_file ".exe" f)
in (norm_path uu____6588))
in (

let uu____6589 = (

let uu____6592 = (

let uu____6595 = (

let uu____6598 = (deps_of (Mk (((deps), (file_system_map), (all_cmd_line_files)))) f)
in (FStar_List.map (fun x -> (

let uu____6606 = (output_file ".krml" x)
in (norm_path uu____6606))) uu____6598))
in (FStar_List.append already_there uu____6595))
in (FStar_List.unique uu____6592))
in ((uu____6587), (uu____6589), (false))))
in (FStar_Util.smap_add transitive_krml uu____6576 uu____6578)));
(

let uu____6617 = (is_implementation f)
in (match (uu____6617) with
| true -> begin
((

let uu____6619 = (output_ml_file f)
in (

let uu____6620 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____6619 uu____6620)));
(

let cmx_files = (

let fst_files = (FStar_All.pipe_right f_deps (FStar_List.map (file_of_dep_aux false file_system_map all_cmd_line_files)))
in (

let extracted_fst_files = (FStar_All.pipe_right fst_files (FStar_List.filter (fun df -> ((

let uu____6642 = (lowercase_module_name df)
in (

let uu____6643 = (lowercase_module_name f)
in (Prims.op_disEquality uu____6642 uu____6643))) && (

let uu____6645 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____6645))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file))))
in ((

let uu____6651 = (

let uu____6652 = (lowercase_module_name f)
in (FStar_Options.should_extract uu____6652))
in (match (uu____6651) with
| true -> begin
(

let uu____6653 = (output_cmx_file f)
in (

let uu____6654 = (output_ml_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____6653 uu____6654 (FStar_String.concat "\\\n\t" cmx_files))))
end
| uu____6655 -> begin
()
end));
(

let uu____6656 = (output_krml_file f)
in (

let uu____6657 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____6656 uu____6657)));
));
)
end
| uu____6658 -> begin
(

let uu____6659 = ((

let uu____6662 = (

let uu____6663 = (lowercase_module_name f)
in (has_implementation file_system_map uu____6663))
in (not (uu____6662))) && (is_interface f))
in (match (uu____6659) with
| true -> begin
(

let uu____6664 = (output_krml_file f)
in (

let uu____6665 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____6664 uu____6665)))
end
| uu____6666 -> begin
()
end))
end));
));
))))))
end)))));
(

let all_fst_files = (

let uu____6670 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____6670 (FStar_Util.sort_with FStar_String.compare)))
in (

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____6696 = (FStar_Options.should_extract mname)
in (match (uu____6696) with
| true -> begin
(

let uu____6697 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____6697))
end
| uu____6698 -> begin
()
end))))));
(sort_output_files ml_file_map);
))
in (

let all_krml_files = (

let krml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right keys (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____6713 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____6713))))));
(sort_output_files krml_file_map);
))
in (

let rec make_transitive = (fun f -> (

let uu____6726 = (

let uu____6735 = (FStar_Util.smap_try_find transitive_krml f)
in (FStar_Util.must uu____6735))
in (match (uu____6726) with
| (exe, deps1, seen) -> begin
(match (seen) with
| true -> begin
((exe), (deps1))
end
| uu____6783 -> begin
((FStar_Util.smap_add transitive_krml f ((exe), (deps1), (true)));
(

let deps2 = (

let uu____6798 = (

let uu____6801 = (FStar_List.map (fun dep1 -> (

let uu____6813 = (make_transitive dep1)
in (match (uu____6813) with
| (uu____6822, deps2) -> begin
(dep1)::deps2
end))) deps1)
in (FStar_List.flatten uu____6801))
in (FStar_List.unique uu____6798))
in ((FStar_Util.smap_add transitive_krml f ((exe), (deps2), (true)));
((exe), (deps2));
));
)
end)
end)))
in ((

let uu____6842 = (FStar_Util.smap_keys transitive_krml)
in (FStar_List.iter (fun f -> (

let uu____6861 = (make_transitive f)
in (match (uu____6861) with
| (exe, deps1) -> begin
(

let deps2 = (

let uu____6875 = (FStar_List.unique ((f)::deps1))
in (FStar_String.concat " " uu____6875))
in (

let wasm = (

let uu____6879 = (FStar_Util.substring exe (Prims.parse_int "0") ((FStar_String.length exe) - (Prims.parse_int "4")))
in (Prims.strcat uu____6879 ".wasm"))
in ((FStar_Util.print2 "%s: %s\n\n" exe deps2);
(FStar_Util.print2 "%s: %s\n\n" wasm deps2);
)))
end))) uu____6842));
(

let uu____6882 = (

let uu____6883 = (FStar_All.pipe_right all_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____6883 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____6882));
(

let uu____6893 = (

let uu____6894 = (FStar_All.pipe_right all_ml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____6894 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____6893));
(

let uu____6903 = (

let uu____6904 = (FStar_All.pipe_right all_krml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____6904 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____6903));
)))));
))))))))))
end))


let print : deps  ->  unit = (fun deps -> (

let uu____6918 = (FStar_Options.dep ())
in (match (uu____6918) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(print_full deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(

let uu____6921 = deps
in (match (uu____6921) with
| Mk (deps1, uu____6923, uu____6924) -> begin
(print_graph deps1)
end))
end
| FStar_Pervasives_Native.Some (uu____6929) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))





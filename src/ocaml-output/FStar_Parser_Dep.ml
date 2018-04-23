
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


let list_of_option : 'Auu____168 . 'Auu____168 FStar_Pervasives_Native.option  ->  'Auu____168 Prims.list = (fun uu___55_177 -> (match (uu___55_177) with
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


let module_name_of_dep : dependence  ->  module_name = (fun uu___56_537 -> (match (uu___56_537) with
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

let uu____555 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____555) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____577) -> begin
(

let uu____592 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____592))
end
| FStar_Pervasives_Native.Some (uu____593, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____609 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____609))
end
| uu____610 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____635 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____635) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____657) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____672 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____697 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____697) with
| FStar_Pervasives_Native.Some (uu____718, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____734 -> begin
FStar_Pervasives_Native.None
end)))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____755 = (interface_of file_system_map key)
in (FStar_Option.isSome uu____755)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____768 = (implementation_of file_system_map key)
in (FStar_Option.isSome uu____768)))


let cache_file_name : Prims.string  ->  Prims.string = (fun fn -> (

let uu____776 = (

let uu____777 = (FStar_Options.lax ())
in (match (uu____777) with
| true -> begin
(Prims.strcat fn ".checked.lax")
end
| uu____778 -> begin
(Prims.strcat fn ".checked")
end))
in (FStar_Options.prepend_cache_dir uu____776)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____814 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____814)))))))
in (

let maybe_add_suffix = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____821 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____823 = (interface_of file_system_map key)
in (match (uu____823) with
| FStar_Pervasives_Native.None -> begin
(

let uu____827 = (

let uu____832 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____832)))
in (FStar_Errors.raise_err uu____827))
end
| FStar_Pervasives_Native.Some (f) -> begin
(match (use_checked_file) with
| true -> begin
(FStar_Options.prepend_cache_dir (Prims.strcat f ".source"))
end
| uu____834 -> begin
f
end)
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____836 = ((cmd_line_has_impl key) && (

let uu____838 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____838)))
in (match (uu____836) with
| true -> begin
(

let uu____841 = (FStar_Options.expose_interfaces ())
in (match (uu____841) with
| true -> begin
(

let uu____842 = (

let uu____843 = (implementation_of file_system_map key)
in (FStar_Option.get uu____843))
in (maybe_add_suffix uu____842))
end
| uu____846 -> begin
(

let uu____847 = (

let uu____852 = (

let uu____853 = (

let uu____854 = (implementation_of file_system_map key)
in (FStar_Option.get uu____854))
in (

let uu____857 = (

let uu____858 = (interface_of file_system_map key)
in (FStar_Option.get uu____858))
in (FStar_Util.format2 "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" uu____853 uu____857)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____852)))
in (FStar_Errors.raise_err uu____847))
end))
end
| uu____861 -> begin
(

let uu____862 = (

let uu____863 = (interface_of file_system_map key)
in (FStar_Option.get uu____863))
in (maybe_add_suffix uu____862))
end))
end
| PreferInterface (key) -> begin
(

let uu____867 = (implementation_of file_system_map key)
in (match (uu____867) with
| FStar_Pervasives_Native.None -> begin
(

let uu____871 = (

let uu____876 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____876)))
in (FStar_Errors.raise_err uu____871))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end
| UseImplementation (key) -> begin
(

let uu____879 = (implementation_of file_system_map key)
in (match (uu____879) with
| FStar_Pervasives_Native.None -> begin
(

let uu____883 = (

let uu____888 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____888)))
in (FStar_Errors.raise_err uu____883))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____932 = (deps_try_find deps fn)
in (match (uu____932) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some (deps1, uu____946) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let add_dependence : dependence_graph  ->  file_name  ->  file_name  ->  unit = (fun deps from to_ -> (

let add_dep = (fun uu____987 to_1 -> (match (uu____987) with
| (d, color) -> begin
(

let uu____1007 = (is_interface to_1)
in (match (uu____1007) with
| true -> begin
(

let uu____1014 = (

let uu____1017 = (

let uu____1018 = (lowercase_module_name to_1)
in PreferInterface (uu____1018))
in (uu____1017)::d)
in ((uu____1014), (color)))
end
| uu____1021 -> begin
(

let uu____1022 = (

let uu____1025 = (

let uu____1026 = (lowercase_module_name to_1)
in UseImplementation (uu____1026))
in (uu____1025)::d)
in ((uu____1022), (color)))
end))
end))
in (

let uu____1029 = (deps_try_find deps from)
in (match (uu____1029) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1040 = (add_dep (((empty_dependences ())), (White)) to_)
in (deps_add_dep deps from uu____1040))
end
| FStar_Pervasives_Native.Some (key_deps) -> begin
(

let uu____1056 = (add_dep key_deps to_)
in (deps_add_dep deps from uu____1056))
end))))


let print_graph : dependence_graph  ->  unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1069 = (

let uu____1070 = (

let uu____1071 = (

let uu____1072 = (

let uu____1075 = (

let uu____1078 = (deps_keys graph)
in (FStar_List.unique uu____1078))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1087 = (

let uu____1092 = (deps_try_find graph k)
in (FStar_Util.must uu____1092))
in (FStar_Pervasives_Native.fst uu____1087))
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (FStar_Util.format2 " %s -> %s" (r k) (r (module_name_of_dep dep1))))
in (FStar_List.map print7 deps))))) uu____1075))
in (FStar_String.concat "\n" uu____1072))
in (Prims.strcat uu____1071 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1070))
in (FStar_Util.write_file "dep.graph" uu____1069));
))


let build_inclusion_candidates_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1127 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____1144 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____1144))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____1170 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____1170 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____1189 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____1190 -> begin
(

let uu____1191 = (

let uu____1196 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____1196)))
in (FStar_Errors.raise_err uu____1191))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____1242 = (FStar_Util.smap_try_find map1 key)
in (match (uu____1242) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____1279 = (is_interface full_path)
in (match (uu____1279) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____1292 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1313 = (is_interface full_path)
in (match (uu____1313) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____1326 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____1340 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____1354 -> (match (uu____1354) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____1340));
(FStar_List.iter (fun f -> (

let uu____1365 = (lowercase_module_name f)
in (add_entry uu____1365 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____1386 = (

let uu____1389 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____1389))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____1415 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____1415))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____1496 -> begin
()
end)) uu____1386));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____1557 -> begin
[]
end)
in (

let names = (

let uu____1561 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____1561 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____1576 = (string_of_lid l last1)
in (FStar_String.lowercase uu____1576)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____1582 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____1582)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____1596 = (

let uu____1597 = (

let uu____1598 = (

let uu____1599 = (

let uu____1602 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____1602))
in (FStar_Util.must uu____1599))
in (FStar_String.lowercase uu____1598))
in (Prims.op_disEquality uu____1597 k'))
in (match (uu____1596) with
| true -> begin
(

let uu____1603 = (FStar_Ident.range_of_lid lid)
in (

let uu____1604 = (

let uu____1609 = (

let uu____1610 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____1610 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____1609)))
in (FStar_Errors.log_issue uu____1603 uu____1604)))
end
| uu____1611 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1617 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____1633 = (FStar_Options.prims_basename ())
in (

let uu____1634 = (

let uu____1637 = (FStar_Options.pervasives_basename ())
in (

let uu____1638 = (

let uu____1641 = (FStar_Options.pervasives_native_basename ())
in (uu____1641)::[])
in (uu____1637)::uu____1638))
in (uu____1633)::uu____1634))
in (match ((FStar_List.mem filename corelibs)) with
| true -> begin
[]
end
| uu____1652 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____1676 = (

let uu____1679 = (lowercase_module_name full_filename)
in (namespace_of_module uu____1679))
in (match (uu____1676) with
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

let uu____1905 = (

let uu____1906 = (

let uu____1907 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (fun d' -> (Prims.op_Equality d' d)) uu____1907))
in (not (uu____1906)))
in (match (uu____1905) with
| true -> begin
(

let uu____1981 = (

let uu____1984 = (FStar_ST.op_Bang deps1)
in (d)::uu____1984)
in (FStar_ST.op_Colon_Equals deps1 uu____1981))
end
| uu____2125 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let add_dependence_edge = (fun original_or_working_map lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____2157 = (resolve_module_name original_or_working_map key)
in (match (uu____2157) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (PreferInterface (module_name)));
(

let uu____2196 = (((has_interface original_or_working_map module_name) && (has_implementation original_or_working_map module_name)) && (

let uu____2198 = (FStar_Options.dep ())
in (Prims.op_Equality uu____2198 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____2196) with
| true -> begin
(add_dep mo_roots (UseImplementation (module_name)))
end
| uu____2236 -> begin
()
end));
true;
)
end
| uu____2237 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____2251 = ((let_open && (add_dependence_edge working_map lid)) || ((not (let_open)) && (add_dependence_edge original_map lid)))
in (match (uu____2251) with
| true -> begin
true
end
| uu____2252 -> begin
((match (let_open) with
| true -> begin
(

let uu____2254 = (FStar_Ident.range_of_lid lid)
in (

let uu____2255 = (

let uu____2260 = (

let uu____2261 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____2261))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2260)))
in (FStar_Errors.log_issue uu____2254 uu____2255)))
end
| uu____2262 -> begin
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

let uu____2271 = (FStar_Ident.range_of_lid lid)
in (

let uu____2272 = (

let uu____2277 = (

let uu____2278 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____2278))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2277)))
in (FStar_Errors.log_issue uu____2271 uu____2272)))
end
| uu____2279 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____2291 = (record_open_module let_open lid)
in (match (uu____2291) with
| true -> begin
()
end
| uu____2292 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____2293 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____2303 -> (match (uu____2303) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____2310 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (

let uu____2323 = (FStar_Ident.text_of_id ident)
in (FStar_String.lowercase uu____2323))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____2325 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____2325) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____2379 = (FStar_Ident.range_of_lid lid)
in (

let uu____2380 = (

let uu____2385 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2385)))
in (FStar_Errors.log_issue uu____2379 uu____2380)));
false;
)
end)))))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____2392 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____2396 = (add_dependence_edge working_map module_name)
in (match (uu____2396) with
| true -> begin
()
end
| uu____2397 -> begin
(

let uu____2398 = (FStar_Options.debug_any ())
in (match (uu____2398) with
| true -> begin
(

let uu____2399 = (FStar_Ident.range_of_lid lid)
in (

let uu____2400 = (

let uu____2405 = (

let uu____2406 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____2406))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____2405)))
in (FStar_Errors.log_issue uu____2399 uu____2400)))
end
| uu____2407 -> begin
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

let rec collect_module = (fun uu___57_2522 -> (match (uu___57_2522) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2531 = (

let uu____2532 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2532))
in ())
end
| uu____2533 -> begin
()
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____2536) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2543 = (

let uu____2544 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2544))
in ())
end
| uu____2545 -> begin
()
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
)) decls))
and collect_decl = (fun uu___58_2553 -> (match (uu___58_2553) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let uu____2558 = (record_module_alias ident lid)
in (match (uu____2558) with
| true -> begin
(

let uu____2559 = (

let uu____2560 = (lowercase_join_longident lid true)
in PreferInterface (uu____2560))
in (add_dep deps uu____2559))
end
| uu____2594 -> begin
()
end))
end
| FStar_Parser_AST.TopLevelLet (uu____2595, patterms) -> begin
(FStar_List.iter (fun uu____2617 -> (match (uu____2617) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (uu____2626, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____2632, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2634; FStar_Parser_AST.mdest = uu____2635; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2637; FStar_Parser_AST.mdest = uu____2638; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____2640, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2642; FStar_Parser_AST.mdest = uu____2643; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____2647, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____2677 -> (match (uu____2677) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____2690, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____2697) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____2698) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____2734 = (

let uu____2735 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____2735 > (Prims.parse_int "1")))
in (match (uu____2734) with
| true -> begin
(

let uu____2781 = (

let uu____2786 = (

let uu____2787 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____2787))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____2786)))
in (

let uu____2788 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____2781 uu____2788)))
end
| uu____2789 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___59_2790 -> (match (uu___59_2790) with
| FStar_Parser_AST.TyconAbstract (uu____2791, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____2803, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____2817, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____2863 -> (match (uu____2863) with
| (uu____2872, t, uu____2874) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____2879, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____2938 -> (match (uu____2938) with
| (uu____2951, t, uu____2953, uu____2954) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___60_2963 -> (match (uu___60_2963) with
| FStar_Parser_AST.DefineEffect (uu____2964, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____2978, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___61_2989 -> (match (uu___61_2989) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____2990, t); FStar_Parser_AST.brange = uu____2992; FStar_Parser_AST.blevel = uu____2993; FStar_Parser_AST.aqual = uu____2994} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____2995, t); FStar_Parser_AST.brange = uu____2997; FStar_Parser_AST.blevel = uu____2998; FStar_Parser_AST.aqual = uu____2999} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____3001; FStar_Parser_AST.blevel = uu____3002; FStar_Parser_AST.aqual = uu____3003} -> begin
(collect_term t)
end
| uu____3004 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___62_3006 -> (match (uu___62_3006) with
| FStar_Const.Const_int (uu____3007, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____3022 = (

let uu____3023 = (FStar_Util.format2 "fstar.%sint%s" u w)
in PreferInterface (uu____3023))
in (add_dep deps uu____3022))))
end
| FStar_Const.Const_char (uu____3057) -> begin
(add_dep deps (PreferInterface ("fstar.char")))
end
| FStar_Const.Const_float (uu____3091) -> begin
(add_dep deps (PreferInterface ("fstar.float")))
end
| uu____3125 -> begin
()
end))
and collect_term' = (fun uu___63_3126 -> (match (uu___63_3126) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((

let uu____3135 = (

let uu____3136 = (FStar_Ident.text_of_id s)
in (Prims.op_Equality uu____3136 "@"))
in (match (uu____3135) with
| true -> begin
(

let uu____3137 = (

let uu____3138 = (

let uu____3139 = (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
in (FStar_Ident.lid_of_path uu____3139 FStar_Range.dummyRange))
in FStar_Parser_AST.Name (uu____3138))
in (collect_term' uu____3137))
end
| uu____3140 -> begin
()
end));
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____3141) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____3142) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____3145) -> begin
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
| uu____3167 -> begin
()
end);
(FStar_List.iter (fun uu____3175 -> (match (uu____3175) with
| (t, uu____3181) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____3191) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____3193, patterms, t) -> begin
((FStar_List.iter (fun uu____3243 -> (match (uu____3243) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____3272 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
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
| FStar_Parser_AST.Bind (uu____3281, t1, t2) -> begin
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
(FStar_List.iter (fun uu____3377 -> (match (uu____3377) with
| (uu____3382, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____3385) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____3441, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____3445) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____3451) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____3457, uu____3458) -> begin
(collect_term t)
end
| FStar_Parser_AST.VQuote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (uu____3460) -> begin
()
end
| FStar_Parser_AST.Antiquote (uu____3465) -> begin
()
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___64_3477 -> (match (uu___64_3477) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____3478) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____3479) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____3487) -> begin
()
end
| FStar_Parser_AST.PatName (uu____3494) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____3495) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____3509) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____3528 -> (match (uu____3528) with
| (uu____3533, p) -> begin
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
and collect_branch = (fun uu____3578 -> (match (uu____3578) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____3596 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____3596) with
| (ast, uu____3616) -> begin
(

let mname = (lowercase_module_name filename)
in ((

let uu____3631 = (((is_interface filename) && (has_implementation original_map mname)) && (

let uu____3633 = (FStar_Options.dep ())
in (Prims.op_Equality uu____3633 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____3631) with
| true -> begin
(add_dep mo_roots (UseImplementation (mname)))
end
| uu____3671 -> begin
()
end));
(collect_module ast);
(

let uu____3673 = (FStar_ST.op_Bang deps)
in (

let uu____3725 = (FStar_ST.op_Bang mo_roots)
in ((uu____3673), (uu____3725))));
))
end))));
))))))))))))))


let collect : Prims.string Prims.list  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____3813 = (FStar_Options.find_file fn)
in (match (uu____3813) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3816 = (

let uu____3821 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____3821)))
in (FStar_Errors.raise_err uu____3816))
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

let uu____3831 = (

let uu____3832 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____3832 FStar_Pervasives_Native.None))
in (match (uu____3831) with
| true -> begin
(

let uu____3849 = (collect_one file_system_map file_name)
in (match (uu____3849) with
| (deps, mo_roots) -> begin
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____3872 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____3872) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____3875 -> begin
deps
end)))
in ((

let uu____3877 = (

let uu____3882 = (FStar_List.unique deps1)
in ((uu____3882), (White)))
in (deps_add_dep dep_graph file_name uu____3877));
(

let uu____3883 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____3883));
))
end))
end
| uu____3886 -> begin
()
end)))
in ((FStar_List.iter discover_one all_cmd_line_files1);
(

let topological_dependences_of = (fun all_command_line_files -> (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec aux = (fun cycle filename -> (

let uu____3922 = (

let uu____3927 = (deps_try_find dep_graph filename)
in (FStar_Util.must uu____3927))
in (match (uu____3922) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((

let uu____3941 = (

let uu____3946 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Warning_RecursiveDependency), (uu____3946)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____3941));
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

let uu____3952 = (dependences_of file_system_map dep_graph all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____3952));
(deps_add_dep dep_graph filename ((direct_deps), (Black)));
(

let uu____3958 = (

let uu____3961 = (FStar_ST.op_Bang topologically_sorted)
in (filename)::uu____3961)
in (FStar_ST.op_Colon_Equals topologically_sorted uu____3958));
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

let uu____4119 = (topological_dependences_of all_cmd_line_files1)
in ((uu____4119), (Mk (((dep_graph), (file_system_map), (all_cmd_line_files1))))));
));
))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun uu____4136 f -> (match (uu____4136) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(dependences_of file_system_map deps all_cmd_line_files f)
end))


let hash_dependences : deps  ->  Prims.string  ->  (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option = (fun uu____4165 fn -> (match (uu____4165) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let fn1 = (

let uu____4183 = (FStar_Options.find_file fn)
in (match (uu____4183) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____4187 -> begin
fn
end))
in (

let cache_file = (cache_file_name fn1)
in (

let digest_of_file1 = (fun fn2 -> ((

let uu____4198 = (FStar_Options.debug_any ())
in (match (uu____4198) with
| true -> begin
(FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2)
end
| uu____4199 -> begin
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

let uu____4209 = ((is_implementation fn1) && (has_interface file_system_map module_name))
in (match (uu____4209) with
| true -> begin
(

let uu____4216 = (

let uu____4221 = (

let uu____4222 = (

let uu____4223 = (interface_of file_system_map module_name)
in (FStar_Option.get uu____4223))
in (digest_of_file1 uu____4222))
in (("interface"), (uu____4221)))
in (uu____4216)::[])
end
| uu____4234 -> begin
[]
end))
in (

let binary_deps = (

let uu____4242 = (dependences_of file_system_map deps all_cmd_line_files fn1)
in (FStar_All.pipe_right uu____4242 (FStar_List.filter (fun fn2 -> (

let uu____4252 = ((is_interface fn2) && (

let uu____4254 = (lowercase_module_name fn2)
in (Prims.op_Equality uu____4254 module_name)))
in (not (uu____4252)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____4264 = (lowercase_module_name fn11)
in (

let uu____4265 = (lowercase_module_name fn2)
in (FStar_String.compare uu____4264 uu____4265)))) binary_deps)
in (

let rec hash_deps = (fun out uu___65_4292 -> (match (uu___65_4292) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps1 -> begin
(

let cache_fn = (cache_file_name fn2)
in (match ((FStar_Util.file_exists cache_fn)) with
| true -> begin
(

let uu____4336 = (

let uu____4343 = (

let uu____4348 = (lowercase_module_name fn2)
in (

let uu____4349 = (digest_of_file1 cache_fn)
in ((uu____4348), (uu____4349))))
in (uu____4343)::out)
in (hash_deps uu____4336 deps1))
end
| uu____4354 -> begin
((

let uu____4356 = (FStar_Options.debug_any ())
in (match (uu____4356) with
| true -> begin
(FStar_Util.print2 "%s: missed digest of file %s\n" cache_file cache_fn)
end
| uu____4357 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end))
end))
in (hash_deps [] binary_deps1))))))))))
end))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____4385 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____4404 -> (match (uu____4404) with
| (m, d) -> begin
(

let uu____4411 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____4411))
end))))
in (FStar_All.pipe_right uu____4385 (FStar_String.concat "\n"))))


let print_make : deps  ->  unit = (fun uu____4418 -> (match (uu____4418) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let keys = (deps_keys deps)
in (FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____4438 = (

let uu____4445 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____4445 FStar_Option.get))
in (match (uu____4438) with
| (f_deps, uu____4469) -> begin
(

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) f_deps)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1))))
end))))))
end))


let print_full : deps  ->  unit = (fun uu____4487 -> (match (uu____4487) with
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

let uu____4528 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____4528)) || (

let uu____4532 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____4532))))
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

let uu____4559 = (

let uu____4562 = (FStar_ST.op_Bang order)
in (ml_file)::uu____4562)
in (FStar_ST.op_Colon_Equals order uu____4559))
end))
in (

let rec aux = (fun uu___66_4670 -> (match (uu___66_4670) with
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

let uu____4688 = (deps_try_find deps file_name)
in (match (uu____4688) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4699 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____4699))
end
| FStar_Pervasives_Native.Some (immediate_deps, uu____4701) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____4712 = (should_visit lc_module_name)
in (match (uu____4712) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____4717 = (implementation_of file_system_map lc_module_name)
in (visit_file uu____4717));
(

let uu____4721 = (interface_of file_system_map lc_module_name)
in (visit_file uu____4721));
(emit_output_file_opt ml_file_opt);
))
end
| uu____4724 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____4729 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____4729));
))))))))))
in (

let keys = (deps_keys deps)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____4796 = (

let uu____4797 = (

let uu____4800 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____4800))
in (FStar_Option.get uu____4797))
in (FStar_Util.replace_chars uu____4796 46 (*.*) "_"))
in (FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____4815 = (output_file ".ml" f)
in (norm_path uu____4815)))
in (

let output_krml_file = (fun f -> (

let uu____4822 = (output_file ".krml" f)
in (norm_path uu____4822)))
in (

let output_cmx_file = (fun f -> (

let uu____4829 = (output_file ".cmx" f)
in (norm_path uu____4829)))
in (

let cache_file = (fun f -> (

let uu____4836 = (cache_file_name f)
in (norm_path uu____4836)))
in (

let transitive_krml = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____4879 = (

let uu____4884 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____4884 FStar_Option.get))
in (match (uu____4879) with
| (f_deps, uu____4906) -> begin
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

let uu____4922 = (is_interface f)
in (match (uu____4922) with
| true -> begin
(

let uu____4923 = (

let uu____4924 = (FStar_Options.prepend_cache_dir norm_f)
in (norm_path uu____4924))
in (FStar_Util.print3 "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" uu____4923 norm_f files3))
end
| uu____4925 -> begin
()
end));
(

let uu____4927 = (cache_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____4927 norm_f files3));
(

let already_there = (

let uu____4931 = (

let uu____4942 = (

let uu____4943 = (output_file ".krml" f)
in (norm_path uu____4943))
in (FStar_Util.smap_try_find transitive_krml uu____4942))
in (match (uu____4931) with
| FStar_Pervasives_Native.Some (uu____4954, already_there, uu____4956) -> begin
already_there
end
| FStar_Pervasives_Native.None -> begin
[]
end))
in ((

let uu____4978 = (

let uu____4979 = (output_file ".krml" f)
in (norm_path uu____4979))
in (

let uu____4980 = (

let uu____4989 = (

let uu____4990 = (output_file ".exe" f)
in (norm_path uu____4990))
in (

let uu____4991 = (

let uu____4994 = (

let uu____4997 = (

let uu____5000 = (deps_of (Mk (((deps), (file_system_map), (all_cmd_line_files)))) f)
in (FStar_List.map (fun x -> (

let uu____5008 = (output_file ".krml" x)
in (norm_path uu____5008))) uu____5000))
in (FStar_List.append already_there uu____4997))
in (FStar_List.unique uu____4994))
in ((uu____4989), (uu____4991), (false))))
in (FStar_Util.smap_add transitive_krml uu____4978 uu____4980)));
(

let uu____5019 = (is_implementation f)
in (match (uu____5019) with
| true -> begin
((

let uu____5021 = (output_ml_file f)
in (

let uu____5022 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5021 uu____5022)));
(

let cmx_files = (

let fst_files = (FStar_All.pipe_right f_deps (FStar_List.map (file_of_dep_aux false file_system_map all_cmd_line_files)))
in (

let extracted_fst_files = (FStar_All.pipe_right fst_files (FStar_List.filter (fun df -> ((

let uu____5046 = (lowercase_module_name df)
in (

let uu____5047 = (lowercase_module_name f)
in (Prims.op_disEquality uu____5046 uu____5047))) && (

let uu____5049 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____5049))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file))))
in ((

let uu____5055 = (

let uu____5056 = (lowercase_module_name f)
in (FStar_Options.should_extract uu____5056))
in (match (uu____5055) with
| true -> begin
(

let uu____5057 = (output_cmx_file f)
in (

let uu____5058 = (output_ml_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5057 uu____5058 (FStar_String.concat "\\\n\t" cmx_files))))
end
| uu____5059 -> begin
()
end));
(

let uu____5060 = (output_krml_file f)
in (

let uu____5061 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5060 uu____5061)));
));
)
end
| uu____5062 -> begin
(

let uu____5063 = ((

let uu____5066 = (

let uu____5067 = (lowercase_module_name f)
in (has_implementation file_system_map uu____5067))
in (not (uu____5066))) && (is_interface f))
in (match (uu____5063) with
| true -> begin
(

let uu____5068 = (output_krml_file f)
in (

let uu____5069 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5068 uu____5069)))
end
| uu____5070 -> begin
()
end))
end));
));
))))))
end)))));
(

let all_fst_files = (

let uu____5074 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____5074 (FStar_Util.sort_with FStar_String.compare)))
in (

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____5100 = (FStar_Options.should_extract mname)
in (match (uu____5100) with
| true -> begin
(

let uu____5101 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____5101))
end
| uu____5102 -> begin
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

let uu____5117 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____5117))))));
(sort_output_files krml_file_map);
))
in (

let rec make_transitive = (fun f -> (

let uu____5130 = (

let uu____5139 = (FStar_Util.smap_try_find transitive_krml f)
in (FStar_Util.must uu____5139))
in (match (uu____5130) with
| (exe, deps1, seen) -> begin
(match (seen) with
| true -> begin
((exe), (deps1))
end
| uu____5187 -> begin
((FStar_Util.smap_add transitive_krml f ((exe), (deps1), (true)));
(

let deps2 = (

let uu____5202 = (

let uu____5205 = (FStar_List.map (fun dep1 -> (

let uu____5217 = (make_transitive dep1)
in (match (uu____5217) with
| (uu____5226, deps2) -> begin
(dep1)::deps2
end))) deps1)
in (FStar_List.flatten uu____5205))
in (FStar_List.unique uu____5202))
in ((FStar_Util.smap_add transitive_krml f ((exe), (deps2), (true)));
((exe), (deps2));
));
)
end)
end)))
in ((

let uu____5246 = (FStar_Util.smap_keys transitive_krml)
in (FStar_List.iter (fun f -> (

let uu____5265 = (make_transitive f)
in (match (uu____5265) with
| (exe, deps1) -> begin
(

let deps2 = (

let uu____5279 = (FStar_List.unique ((f)::deps1))
in (FStar_String.concat " " uu____5279))
in (

let wasm = (

let uu____5283 = (FStar_Util.substring exe (Prims.parse_int "0") ((FStar_String.length exe) - (Prims.parse_int "4")))
in (Prims.strcat uu____5283 ".wasm"))
in ((FStar_Util.print2 "%s: %s\n\n" exe deps2);
(FStar_Util.print2 "%s: %s\n\n" wasm deps2);
)))
end))) uu____5246));
(

let uu____5286 = (

let uu____5287 = (FStar_All.pipe_right all_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5287 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5286));
(

let uu____5297 = (

let uu____5298 = (FStar_All.pipe_right all_ml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5298 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5297));
(

let uu____5307 = (

let uu____5308 = (FStar_All.pipe_right all_krml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5308 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5307));
)))));
))))))))))
end))


let print : deps  ->  unit = (fun deps -> (

let uu____5322 = (FStar_Options.dep ())
in (match (uu____5322) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(print_full deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(

let uu____5325 = deps
in (match (uu____5325) with
| Mk (deps1, uu____5327, uu____5328) -> begin
(print_graph deps1)
end))
end
| FStar_Pervasives_Native.Some (uu____5333) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))





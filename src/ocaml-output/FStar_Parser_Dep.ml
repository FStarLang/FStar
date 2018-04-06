
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
| uu____26 -> begin
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
| uu____34 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____38 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____42 -> begin
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

let uu____68 = ((l > lext) && (

let uu____80 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____80 ext)))
in (match (uu____68) with
| true -> begin
(

let uu____97 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____97))
end
| uu____108 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____109 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____109) with
| (FStar_Pervasives_Native.Some (m))::uu____119 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____126 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____134 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____134 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____141 = (is_interface f)
in (not (uu____141))))


let list_of_option : 'Auu____144 . 'Auu____144 FStar_Pervasives_Native.option  ->  'Auu____144 Prims.list = (fun uu___56_152 -> (match (uu___56_152) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____158 . ('Auu____158 FStar_Pervasives_Native.option * 'Auu____158 FStar_Pervasives_Native.option)  ->  'Auu____158 Prims.list = (fun uu____172 -> (match (uu____172) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let module_name_of_file : Prims.string  ->  Prims.string = (fun f -> (

let uu____194 = (

let uu____197 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____197))
in (match (uu____194) with
| FStar_Pervasives_Native.Some (longname) -> begin
longname
end
| FStar_Pervasives_Native.None -> begin
(

let uu____199 = (

let uu____204 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in ((FStar_Errors.Fatal_NotValidFStarFile), (uu____204)))
in (FStar_Errors.raise_err uu____199))
end)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____208 = (module_name_of_file f)
in (FStar_String.lowercase uu____208)))


let namespace_of_module : Prims.string  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun f -> (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text f) FStar_Range.dummyRange)
in (match (lid.FStar_Ident.ns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____217 -> begin
(

let uu____220 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_Pervasives_Native.Some (uu____220))
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
| uu____237 -> begin
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
| uu____249 -> begin
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
| uu____261 -> begin
false
end))


let __proj__UseImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
_0
end))


type dependences =
dependence Prims.list


let empty_dependences : 'Auu____272 . Prims.unit  ->  'Auu____272 Prims.list = (fun uu____275 -> [])

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


let deps_try_find : dependence_graph  ->  Prims.string  ->  (dependences * color) FStar_Pervasives_Native.option = (fun uu____364 k -> (match (uu____364) with
| Deps (m) -> begin
(FStar_Util.smap_try_find m k)
end))


let deps_add_dep : dependence_graph  ->  Prims.string  ->  (dependences * color)  ->  Prims.unit = (fun uu____393 k v1 -> (match (uu____393) with
| Deps (m) -> begin
(FStar_Util.smap_add m k v1)
end))


let deps_keys : dependence_graph  ->  Prims.string Prims.list = (fun uu____415 -> (match (uu____415) with
| Deps (m) -> begin
(FStar_Util.smap_keys m)
end))


let deps_empty : Prims.unit  ->  dependence_graph = (fun uu____431 -> (

let uu____432 = (FStar_Util.smap_create (Prims.parse_int "41"))
in Deps (uu____432)))


let empty_deps : deps = (

let uu____443 = (

let uu____452 = (deps_empty ())
in (

let uu____453 = (FStar_Util.smap_create (Prims.parse_int "0"))
in ((uu____452), (uu____453), ([]))))
in Mk (uu____443))


let module_name_of_dep : dependence  ->  module_name = (fun uu___57_486 -> (match (uu___57_486) with
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

let uu____500 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____500) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____522) -> begin
(

let uu____537 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____537))
end
| FStar_Pervasives_Native.Some (uu____538, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____554 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____554))
end
| uu____555 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____576 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____576) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____598) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____613 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____634 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____634) with
| FStar_Pervasives_Native.Some (uu____655, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____671 -> begin
FStar_Pervasives_Native.None
end)))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____688 = (interface_of file_system_map key)
in (FStar_Option.isSome uu____688)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____697 = (implementation_of file_system_map key)
in (FStar_Option.isSome uu____697)))


let cache_file_name : Prims.string  ->  Prims.string = (fun fn -> (

let uu____703 = (

let uu____704 = (FStar_Options.lax ())
in (match (uu____704) with
| true -> begin
(Prims.strcat fn ".checked.lax")
end
| uu____705 -> begin
(Prims.strcat fn ".checked")
end))
in (FStar_Options.prepend_cache_dir uu____703)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____731 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____731)))))))
in (

let maybe_add_suffix = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____736 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____738 = (interface_of file_system_map key)
in (match (uu____738) with
| FStar_Pervasives_Native.None -> begin
(

let uu____750 = (

let uu____755 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____755)))
in (FStar_Errors.raise_err uu____750))
end
| FStar_Pervasives_Native.Some (f) -> begin
(match (use_checked_file) with
| true -> begin
(FStar_Options.prepend_cache_dir (Prims.strcat f ".source"))
end
| uu____757 -> begin
f
end)
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____759 = ((cmd_line_has_impl key) && (

let uu____761 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____761)))
in (match (uu____759) with
| true -> begin
(

let uu____764 = (FStar_Options.expose_interfaces ())
in (match (uu____764) with
| true -> begin
(

let uu____765 = (

let uu____766 = (implementation_of file_system_map key)
in (FStar_Option.get uu____766))
in (maybe_add_suffix uu____765))
end
| uu____769 -> begin
(

let uu____770 = (

let uu____775 = (

let uu____776 = (

let uu____777 = (implementation_of file_system_map key)
in (FStar_Option.get uu____777))
in (

let uu____780 = (

let uu____781 = (interface_of file_system_map key)
in (FStar_Option.get uu____781))
in (FStar_Util.format2 "Invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" uu____776 uu____780)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____775)))
in (FStar_Errors.raise_err uu____770))
end))
end
| uu____784 -> begin
(

let uu____785 = (

let uu____786 = (interface_of file_system_map key)
in (FStar_Option.get uu____786))
in (maybe_add_suffix uu____785))
end))
end
| PreferInterface (key) -> begin
(

let uu____790 = (implementation_of file_system_map key)
in (match (uu____790) with
| FStar_Pervasives_Native.None -> begin
(

let uu____802 = (

let uu____807 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____807)))
in (FStar_Errors.raise_err uu____802))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end
| UseImplementation (key) -> begin
(

let uu____810 = (implementation_of file_system_map key)
in (match (uu____810) with
| FStar_Pervasives_Native.None -> begin
(

let uu____822 = (

let uu____827 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____827)))
in (FStar_Errors.raise_err uu____822))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_add_suffix f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____857 = (deps_try_find deps fn)
in (match (uu____857) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some (deps1, uu____871) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let add_dependence : dependence_graph  ->  file_name  ->  file_name  ->  Prims.unit = (fun deps from to_ -> (

let add_dep = (fun uu____902 to_1 -> (match (uu____902) with
| (d, color) -> begin
(

let uu____922 = (is_interface to_1)
in (match (uu____922) with
| true -> begin
(

let uu____929 = (

let uu____932 = (

let uu____933 = (lowercase_module_name to_1)
in PreferInterface (uu____933))
in (uu____932)::d)
in ((uu____929), (color)))
end
| uu____936 -> begin
(

let uu____937 = (

let uu____940 = (

let uu____941 = (lowercase_module_name to_1)
in UseImplementation (uu____941))
in (uu____940)::d)
in ((uu____937), (color)))
end))
end))
in (

let uu____944 = (deps_try_find deps from)
in (match (uu____944) with
| FStar_Pervasives_Native.None -> begin
(

let uu____955 = (add_dep (((empty_dependences ())), (White)) to_)
in (deps_add_dep deps from uu____955))
end
| FStar_Pervasives_Native.Some (key_deps) -> begin
(

let uu____971 = (add_dep key_deps to_)
in (deps_add_dep deps from uu____971))
end))))


let print_graph : dependence_graph  ->  Prims.unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____982 = (

let uu____983 = (

let uu____984 = (

let uu____985 = (

let uu____988 = (

let uu____991 = (deps_keys graph)
in (FStar_List.unique uu____991))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1000 = (

let uu____1005 = (deps_try_find graph k)
in (FStar_Util.must uu____1005))
in (FStar_Pervasives_Native.fst uu____1000))
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (FStar_Util.format2 " %s -> %s" (r k) (r (module_name_of_dep dep1))))
in (FStar_List.map print7 deps))))) uu____988))
in (FStar_String.concat "\n" uu____985))
in (Prims.strcat uu____984 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____983))
in (FStar_Util.write_file "dep.graph" uu____982));
))


let build_inclusion_candidates_list : Prims.unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1034 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____1051 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____1051))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.file_exists d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____1077 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____1077 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____1096 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____1097 -> begin
(

let uu____1098 = (

let uu____1103 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____1103)))
in (FStar_Errors.raise_err uu____1098))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____1143 = (FStar_Util.smap_try_find map1 key)
in (match (uu____1143) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____1180 = (is_interface full_path)
in (match (uu____1180) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____1193 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1214 = (is_interface full_path)
in (match (uu____1214) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____1227 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____1241 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____1255 -> (match (uu____1255) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____1241));
(FStar_List.iter (fun f -> (

let uu____1266 = (lowercase_module_name f)
in (add_entry uu____1266 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____1281 = (

let uu____1284 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____1284))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____1310 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____1310))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____1441 -> begin
()
end)) uu____1281));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____1548 -> begin
[]
end)
in (

let names = (

let uu____1552 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____1552 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____1563 = (string_of_lid l last1)
in (FStar_String.lowercase uu____1563)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____1567 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____1567)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____1577 = (

let uu____1578 = (

let uu____1579 = (

let uu____1580 = (

let uu____1583 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____1583))
in (FStar_Util.must uu____1580))
in (FStar_String.lowercase uu____1579))
in (Prims.op_disEquality uu____1578 k'))
in (match (uu____1577) with
| true -> begin
(

let uu____1584 = (

let uu____1589 = (

let uu____1590 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____1590 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____1589)))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____1584))
end
| uu____1591 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____1595 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____1609 = (FStar_Options.prims_basename ())
in (

let uu____1610 = (

let uu____1613 = (FStar_Options.pervasives_basename ())
in (

let uu____1614 = (

let uu____1617 = (FStar_Options.pervasives_native_basename ())
in (uu____1617)::[])
in (uu____1613)::uu____1614))
in (uu____1609)::uu____1610))
in (match ((FStar_List.mem filename corelibs)) with
| true -> begin
[]
end
| uu____1628 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____1652 = (

let uu____1655 = (lowercase_module_name full_filename)
in (namespace_of_module uu____1655))
in (match (uu____1652) with
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

let uu____1892 = (

let uu____1893 = (

let uu____1894 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (fun d' -> (Prims.op_Equality d' d)) uu____1894))
in (not (uu____1893)))
in (match (uu____1892) with
| true -> begin
(

let uu____1994 = (

let uu____1997 = (FStar_ST.op_Bang deps1)
in (d)::uu____1997)
in (FStar_ST.op_Colon_Equals deps1 uu____1994))
end
| uu____2190 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let add_dependence_edge = (fun original_or_working_map lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____2218 = (resolve_module_name original_or_working_map key)
in (match (uu____2218) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (PreferInterface (module_name)));
(

let uu____2329 = (((has_interface original_or_working_map module_name) && (has_implementation original_or_working_map module_name)) && (

let uu____2331 = (FStar_Options.dep ())
in (Prims.op_Equality uu____2331 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____2329) with
| true -> begin
(add_dep mo_roots (UseImplementation (module_name)))
end
| uu____2441 -> begin
()
end));
true;
)
end
| uu____2442 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____2452 = ((let_open && (add_dependence_edge working_map lid)) || ((not (let_open)) && (add_dependence_edge original_map lid)))
in (match (uu____2452) with
| true -> begin
true
end
| uu____2453 -> begin
((match (let_open) with
| true -> begin
(

let uu____2455 = (

let uu____2460 = (

let uu____2461 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____2461))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2460)))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2455))
end
| uu____2462 -> begin
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

let uu____2469 = (

let uu____2474 = (

let uu____2475 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____2475))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2474)))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2469))
end
| uu____2476 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____2484 = (record_open_module let_open lid)
in (match (uu____2484) with
| true -> begin
()
end
| uu____2485 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____2486 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____2494 -> (match (uu____2494) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____2501 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____2511 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____2511) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____2565 = (

let uu____2570 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____2570)))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2565));
false;
)
end)))))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____2575 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (

let uu____2579 = (add_dependence_edge working_map module_name)
in (match (uu____2579) with
| true -> begin
()
end
| uu____2580 -> begin
(

let uu____2581 = (FStar_Options.debug_any ())
in (match (uu____2581) with
| true -> begin
(

let uu____2582 = (

let uu____2587 = (

let uu____2588 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____2588))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____2587)))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid lid) uu____2582))
end
| uu____2589 -> begin
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

let rec collect_module = (fun uu___58_2674 -> (match (uu___58_2674) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2683 = (

let uu____2684 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2684))
in ())
end
| uu____2685 -> begin
()
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____2688) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____2695 = (

let uu____2696 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____2696))
in ())
end
| uu____2697 -> begin
()
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
)) decls))
and collect_decl = (fun uu___59_2705 -> (match (uu___59_2705) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let uu____2710 = (record_module_alias ident lid)
in (match (uu____2710) with
| true -> begin
(

let uu____2711 = (

let uu____2712 = (lowercase_join_longident lid true)
in PreferInterface (uu____2712))
in (add_dep deps uu____2711))
end
| uu____2818 -> begin
()
end))
end
| FStar_Parser_AST.TopLevelLet (uu____2819, patterms) -> begin
(FStar_List.iter (fun uu____2841 -> (match (uu____2841) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____2851, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2853; FStar_Parser_AST.mdest = uu____2854; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2856; FStar_Parser_AST.mdest = uu____2857; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____2859, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____2861; FStar_Parser_AST.mdest = uu____2862; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____2866, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____2896 -> (match (uu____2896) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____2909, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____2916) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____2917) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____3025 = (

let uu____3026 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____3026 > (Prims.parse_int "1")))
in (match (uu____3025) with
| true -> begin
(

let uu____3122 = (

let uu____3127 = (

let uu____3128 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____3128))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____3127)))
in (FStar_Errors.raise_error uu____3122 (FStar_Ident.range_of_lid lid)))
end
| uu____3129 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___60_3130 -> (match (uu___60_3130) with
| FStar_Parser_AST.TyconAbstract (uu____3131, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____3143, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____3157, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3203 -> (match (uu____3203) with
| (uu____3212, t, uu____3214) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____3219, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3278 -> (match (uu____3278) with
| (uu____3291, t, uu____3293, uu____3294) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___61_3303 -> (match (uu___61_3303) with
| FStar_Parser_AST.DefineEffect (uu____3304, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____3318, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___62_3329 -> (match (uu___62_3329) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____3330, t); FStar_Parser_AST.brange = uu____3332; FStar_Parser_AST.blevel = uu____3333; FStar_Parser_AST.aqual = uu____3334} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____3335, t); FStar_Parser_AST.brange = uu____3337; FStar_Parser_AST.blevel = uu____3338; FStar_Parser_AST.aqual = uu____3339} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____3341; FStar_Parser_AST.blevel = uu____3342; FStar_Parser_AST.aqual = uu____3343} -> begin
(collect_term t)
end
| uu____3344 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___63_3346 -> (match (uu___63_3346) with
| FStar_Const.Const_int (uu____3347, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____3362 = (

let uu____3363 = (FStar_Util.format2 "fstar.%sint%s" u w)
in PreferInterface (uu____3363))
in (add_dep deps uu____3362))))
end
| FStar_Const.Const_char (uu____3469) -> begin
(add_dep deps (PreferInterface ("fstar.char")))
end
| FStar_Const.Const_float (uu____3575) -> begin
(add_dep deps (PreferInterface ("fstar.float")))
end
| uu____3681 -> begin
()
end))
and collect_term' = (fun uu___64_3682 -> (match (uu___64_3682) with
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

let uu____3691 = (

let uu____3692 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____3692))
in (collect_term' uu____3691))
end
| uu____3693 -> begin
()
end);
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____3694) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____3695) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____3698) -> begin
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
| uu____3720 -> begin
()
end);
(FStar_List.iter (fun uu____3728 -> (match (uu____3728) with
| (t, uu____3734) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____3744) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____3746, patterms, t) -> begin
((FStar_List.iter (fun uu____3796 -> (match (uu____3796) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____3825 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
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
| FStar_Parser_AST.Bind (uu____3836, t1, t2) -> begin
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
(FStar_List.iter (fun uu____3932 -> (match (uu____3932) with
| (uu____3937, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____3940) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____3996, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____4000) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____4006) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____4012, uu____4013) -> begin
(collect_term t)
end
| FStar_Parser_AST.VQuote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (uu____4015) -> begin
()
end
| FStar_Parser_AST.Antiquote (uu____4020) -> begin
()
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___65_4032 -> (match (uu___65_4032) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____4033) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____4034) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____4042) -> begin
()
end
| FStar_Parser_AST.PatName (uu____4049) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____4050) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____4064) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____4083 -> (match (uu____4083) with
| (uu____4088, p) -> begin
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
and collect_branch = (fun uu____4133 -> (match (uu____4133) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____4151 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____4151) with
| (ast, uu____4171) -> begin
(

let mname = (lowercase_module_name filename)
in ((

let uu____4186 = (((is_interface filename) && (has_implementation original_map mname)) && (

let uu____4188 = (FStar_Options.dep ())
in (Prims.op_Equality uu____4188 (FStar_Pervasives_Native.Some ("full")))))
in (match (uu____4186) with
| true -> begin
(add_dep mo_roots (UseImplementation (mname)))
end
| uu____4298 -> begin
()
end));
(collect_module ast);
(

let uu____4300 = (FStar_ST.op_Bang deps)
in (

let uu____4402 = (FStar_ST.op_Bang mo_roots)
in ((uu____4300), (uu____4402))));
))
end))));
))))))))))))))


let collect : Prims.string Prims.list  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____4538 = (FStar_Options.find_file fn)
in (match (uu____4538) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4541 = (

let uu____4546 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____4546)))
in (FStar_Errors.raise_err uu____4541))
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

let uu____4554 = (

let uu____4555 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____4555 FStar_Pervasives_Native.None))
in (match (uu____4554) with
| true -> begin
(

let uu____4572 = (collect_one file_system_map file_name)
in (match (uu____4572) with
| (deps, mo_roots) -> begin
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____4595 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____4595) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____4598 -> begin
deps
end)))
in ((

let uu____4600 = (

let uu____4605 = (FStar_List.unique deps1)
in ((uu____4605), (White)))
in (deps_add_dep dep_graph file_name uu____4600));
(

let uu____4610 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____4610));
))
end))
end
| uu____4613 -> begin
()
end)))
in ((FStar_List.iter discover_one all_cmd_line_files1);
(

let topological_dependences_of = (fun all_command_line_files -> (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec aux = (fun cycle filename -> (

let uu____4643 = (

let uu____4648 = (deps_try_find dep_graph filename)
in (FStar_Util.must uu____4648))
in (match (uu____4643) with
| (direct_deps, color) -> begin
(match (color) with
| Gray -> begin
((

let uu____4662 = (

let uu____4667 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Warning_RecursiveDependency), (uu____4667)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____4662));
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

let uu____4673 = (dependences_of file_system_map dep_graph all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____4673));
(deps_add_dep dep_graph filename ((direct_deps), (Black)));
(

let uu____4679 = (

let uu____4682 = (FStar_ST.op_Bang topologically_sorted)
in (filename)::uu____4682)
in (FStar_ST.op_Colon_Equals topologically_sorted uu____4679));
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

let uu____4990 = (topological_dependences_of all_cmd_line_files1)
in ((uu____4990), (Mk (((dep_graph), (file_system_map), (all_cmd_line_files1))))));
));
))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun uu____5003 f -> (match (uu____5003) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(dependences_of file_system_map deps all_cmd_line_files f)
end))


let hash_dependences : deps  ->  Prims.string  ->  (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option = (fun uu____5028 fn -> (match (uu____5028) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let fn1 = (

let uu____5046 = (FStar_Options.find_file fn)
in (match (uu____5046) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____5050 -> begin
fn
end))
in (

let cache_file = (cache_file_name fn1)
in (

let digest_of_file1 = (fun fn2 -> ((

let uu____5059 = (FStar_Options.debug_any ())
in (match (uu____5059) with
| true -> begin
(FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2)
end
| uu____5060 -> begin
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

let uu____5070 = ((is_implementation fn1) && (has_interface file_system_map module_name))
in (match (uu____5070) with
| true -> begin
(

let uu____5077 = (

let uu____5082 = (

let uu____5083 = (

let uu____5084 = (interface_of file_system_map module_name)
in (FStar_Option.get uu____5084))
in (digest_of_file1 uu____5083))
in (("interface"), (uu____5082)))
in (uu____5077)::[])
end
| uu____5095 -> begin
[]
end))
in (

let binary_deps = (

let uu____5103 = (dependences_of file_system_map deps all_cmd_line_files fn1)
in (FStar_All.pipe_right uu____5103 (FStar_List.filter (fun fn2 -> (

let uu____5113 = ((is_interface fn2) && (

let uu____5115 = (lowercase_module_name fn2)
in (Prims.op_Equality uu____5115 module_name)))
in (not (uu____5113)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____5125 = (lowercase_module_name fn11)
in (

let uu____5126 = (lowercase_module_name fn2)
in (FStar_String.compare uu____5125 uu____5126)))) binary_deps)
in (

let rec hash_deps = (fun out uu___66_5149 -> (match (uu___66_5149) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps1 -> begin
(

let cache_fn = (cache_file_name fn2)
in (match ((FStar_Util.file_exists cache_fn)) with
| true -> begin
(

let uu____5193 = (

let uu____5200 = (

let uu____5205 = (lowercase_module_name fn2)
in (

let uu____5206 = (digest_of_file1 cache_fn)
in ((uu____5205), (uu____5206))))
in (uu____5200)::out)
in (hash_deps uu____5193 deps1))
end
| uu____5211 -> begin
((

let uu____5213 = (FStar_Options.debug_any ())
in (match (uu____5213) with
| true -> begin
(FStar_Util.print2 "%s: missed digest of file %s\n" cache_file cache_fn)
end
| uu____5214 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end))
end))
in (hash_deps [] binary_deps1))))))))))
end))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____5240 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____5259 -> (match (uu____5259) with
| (m, d) -> begin
(

let uu____5266 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____5266))
end))))
in (FStar_All.pipe_right uu____5240 (FStar_String.concat "\n"))))


let print_make : deps  ->  Prims.unit = (fun uu____5271 -> (match (uu____5271) with
| Mk (deps, file_system_map, all_cmd_line_files) -> begin
(

let keys = (deps_keys deps)
in (FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____5291 = (

let uu____5296 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____5296 FStar_Option.get))
in (match (uu____5291) with
| (f_deps, uu____5318) -> begin
(

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) f_deps)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1))))
end))))))
end))


let print_full : deps  ->  Prims.unit = (fun uu____5330 -> (match (uu____5330) with
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

let uu____5367 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____5367)) || (

let uu____5371 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____5371))))
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

let uu____5394 = (

let uu____5397 = (FStar_ST.op_Bang order)
in (ml_file)::uu____5397)
in (FStar_ST.op_Colon_Equals order uu____5394))
end))
in (

let rec aux = (fun uu___67_5603 -> (match (uu___67_5603) with
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

let uu____5619 = (deps_try_find deps file_name)
in (match (uu____5619) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5630 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____5630))
end
| FStar_Pervasives_Native.Some (immediate_deps, uu____5632) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____5643 = (should_visit lc_module_name)
in (match (uu____5643) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____5648 = (implementation_of file_system_map lc_module_name)
in (visit_file uu____5648));
(

let uu____5652 = (interface_of file_system_map lc_module_name)
in (visit_file uu____5652));
(emit_output_file_opt ml_file_opt);
))
end
| uu____5655 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____5660 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____5660));
))))))))))
in (

let keys = (deps_keys deps)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____5773 = (

let uu____5774 = (

let uu____5777 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____5777))
in (FStar_Option.get uu____5774))
in (FStar_Util.replace_chars uu____5773 46 (*.*) "_"))
in (FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____5788 = (output_file ".ml" f)
in (norm_path uu____5788)))
in (

let output_krml_file = (fun f -> (

let uu____5793 = (output_file ".krml" f)
in (norm_path uu____5793)))
in (

let output_cmx_file = (fun f -> (

let uu____5798 = (output_file ".cmx" f)
in (norm_path uu____5798)))
in (

let cache_file = (fun f -> (

let uu____5803 = (cache_file_name f)
in (norm_path uu____5803)))
in ((FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let uu____5825 = (

let uu____5830 = (deps_try_find deps f)
in (FStar_All.pipe_right uu____5830 FStar_Option.get))
in (match (uu____5825) with
| (f_deps, uu____5852) -> begin
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

let uu____5868 = (is_interface f)
in (match (uu____5868) with
| true -> begin
(

let uu____5869 = (

let uu____5870 = (FStar_Options.prepend_cache_dir norm_f)
in (norm_path uu____5870))
in (FStar_Util.print3 "%s.source: %s \\\n\t%s\n\ttouch $@\n\n" uu____5869 norm_f files3))
end
| uu____5871 -> begin
()
end));
(

let uu____5873 = (cache_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5873 norm_f files3));
(

let uu____5874 = (is_implementation f)
in (match (uu____5874) with
| true -> begin
((

let uu____5876 = (output_ml_file f)
in (

let uu____5877 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5876 uu____5877)));
(

let cmx_files = (

let fst_files = (FStar_All.pipe_right f_deps (FStar_List.map (file_of_dep_aux false file_system_map all_cmd_line_files)))
in (

let extracted_fst_files = (FStar_All.pipe_right fst_files (FStar_List.filter (fun df -> ((

let uu____5899 = (lowercase_module_name df)
in (

let uu____5900 = (lowercase_module_name f)
in (Prims.op_disEquality uu____5899 uu____5900))) && (

let uu____5902 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____5902))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file))))
in ((

let uu____5908 = (

let uu____5909 = (lowercase_module_name f)
in (FStar_Options.should_extract uu____5909))
in (match (uu____5908) with
| true -> begin
(

let uu____5910 = (output_cmx_file f)
in (

let uu____5911 = (output_ml_file f)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____5910 uu____5911 (FStar_String.concat "\\\n\t" cmx_files))))
end
| uu____5912 -> begin
()
end));
(

let uu____5913 = (output_krml_file f)
in (

let uu____5914 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5913 uu____5914)));
));
)
end
| uu____5915 -> begin
(

let uu____5916 = ((

let uu____5919 = (

let uu____5920 = (lowercase_module_name f)
in (has_implementation file_system_map uu____5920))
in (not (uu____5919))) && (is_interface f))
in (match (uu____5916) with
| true -> begin
(

let uu____5921 = (output_krml_file f)
in (

let uu____5922 = (cache_file f)
in (FStar_Util.print2 "%s: %s\n\n" uu____5921 uu____5922)))
end
| uu____5923 -> begin
()
end))
end));
))))))
end)))));
(

let all_fst_files = (

let uu____5927 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____5927 (FStar_Util.sort_with FStar_String.compare)))
in (

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____5953 = (FStar_Options.should_extract mname)
in (match (uu____5953) with
| true -> begin
(

let uu____5954 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____5954))
end
| uu____5955 -> begin
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

let uu____5970 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____5970))))));
(sort_output_files krml_file_map);
))
in ((

let uu____5972 = (

let uu____5973 = (FStar_All.pipe_right all_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5973 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____5972));
(

let uu____5983 = (

let uu____5984 = (FStar_All.pipe_right all_ml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5984 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____5983));
(

let uu____5993 = (

let uu____5994 = (FStar_All.pipe_right all_krml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____5994 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____5993));
))));
)))))))))
end))


let print : deps  ->  Prims.unit = (fun deps -> (

let uu____6006 = (FStar_Options.dep ())
in (match (uu____6006) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(print_full deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(

let uu____6009 = deps
in (match (uu____6009) with
| Mk (deps1, uu____6011, uu____6012) -> begin
(print_graph deps1)
end))
end
| FStar_Pervasives_Native.Some (uu____6017) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))





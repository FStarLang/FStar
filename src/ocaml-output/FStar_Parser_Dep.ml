
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
| uu____9 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____31 -> begin
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
| uu____54 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____65 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____76 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____87 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____98 -> begin
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

let uu____146 = ((l > lext) && (

let uu____159 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____159 ext)))
in (match (uu____146) with
| true -> begin
(

let uu____180 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____180))
end
| uu____194 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____197 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____197) with
| (FStar_Pervasives_Native.Some (m))::uu____211 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____223 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____240 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____240 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____254 = (is_interface f)
in (not (uu____254))))


let list_of_option : 'Auu____261 . 'Auu____261 FStar_Pervasives_Native.option  ->  'Auu____261 Prims.list = (fun uu___118_270 -> (match (uu___118_270) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____279 . ('Auu____279 FStar_Pervasives_Native.option * 'Auu____279 FStar_Pervasives_Native.option)  ->  'Auu____279 Prims.list = (fun uu____294 -> (match (uu____294) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let module_name_of_file : Prims.string  ->  Prims.string = (fun f -> (

let uu____322 = (

let uu____326 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____326))
in (match (uu____322) with
| FStar_Pervasives_Native.Some (longname) -> begin
longname
end
| FStar_Pervasives_Native.None -> begin
(

let uu____333 = (

let uu____339 = (FStar_Util.format1 "not a valid FStar file: %s" f)
in ((FStar_Errors.Fatal_NotValidFStarFile), (uu____339)))
in (FStar_Errors.raise_err uu____333))
end)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____353 = (module_name_of_file f)
in (FStar_String.lowercase uu____353)))


let namespace_of_module : Prims.string  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun f -> (

let lid = (

let uu____366 = (FStar_Ident.path_of_text f)
in (FStar_Ident.lid_of_path uu____366 FStar_Range.dummyRange))
in (match (lid.FStar_Ident.ns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____369 -> begin
(

let uu____372 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_Pervasives_Native.Some (uu____372))
end)))


type file_name =
Prims.string


type module_name =
Prims.string

type dependence =
| UseInterface of module_name
| PreferInterface of module_name
| UseImplementation of module_name
| FriendImplementation of module_name


let uu___is_UseInterface : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UseInterface (_0) -> begin
true
end
| uu____414 -> begin
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
| uu____438 -> begin
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
| uu____462 -> begin
false
end))


let __proj__UseImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| UseImplementation (_0) -> begin
_0
end))


let uu___is_FriendImplementation : dependence  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FriendImplementation (_0) -> begin
true
end
| uu____486 -> begin
false
end))


let __proj__FriendImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| FriendImplementation (_0) -> begin
_0
end))


let dep_to_string : dependence  ->  Prims.string = (fun uu___119_505 -> (match (uu___119_505) with
| UseInterface (f) -> begin
(Prims.strcat "UseInterface " f)
end
| PreferInterface (f) -> begin
(Prims.strcat "PreferInterface " f)
end
| UseImplementation (f) -> begin
(Prims.strcat "UseImplementation " f)
end
| FriendImplementation (f) -> begin
(Prims.strcat "FriendImplementation " f)
end))


type dependences =
dependence Prims.list


let empty_dependences : 'Auu____524 . unit  ->  'Auu____524 Prims.list = (fun uu____527 -> [])

type dep_node =
{edges : dependences; color : color}


let __proj__Mkdep_node__item__edges : dep_node  ->  dependences = (fun projectee -> (match (projectee) with
| {edges = edges; color = color} -> begin
edges
end))


let __proj__Mkdep_node__item__color : dep_node  ->  color = (fun projectee -> (match (projectee) with
| {edges = edges; color = color} -> begin
color
end))

type dependence_graph =
| Deps of dep_node FStar_Util.smap


let uu___is_Deps : dependence_graph  ->  Prims.bool = (fun projectee -> true)


let __proj__Deps__item___0 : dependence_graph  ->  dep_node FStar_Util.smap = (fun projectee -> (match (projectee) with
| Deps (_0) -> begin
_0
end))

type deps =
{dep_graph : dependence_graph; file_system_map : files_for_module_name; cmd_line_files : file_name Prims.list; all_files : file_name Prims.list; interfaces_with_inlining : module_name Prims.list}


let __proj__Mkdeps__item__dep_graph : deps  ->  dependence_graph = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
dep_graph
end))


let __proj__Mkdeps__item__file_system_map : deps  ->  files_for_module_name = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
file_system_map
end))


let __proj__Mkdeps__item__cmd_line_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
cmd_line_files
end))


let __proj__Mkdeps__item__all_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
all_files
end))


let __proj__Mkdeps__item__interfaces_with_inlining : deps  ->  module_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining} -> begin
interfaces_with_inlining
end))


let deps_try_find : dependence_graph  ->  Prims.string  ->  dep_node FStar_Pervasives_Native.option = (fun uu____746 k -> (match (uu____746) with
| Deps (m) -> begin
(FStar_Util.smap_try_find m k)
end))


let deps_add_dep : dependence_graph  ->  Prims.string  ->  dep_node  ->  unit = (fun uu____768 k v1 -> (match (uu____768) with
| Deps (m) -> begin
(FStar_Util.smap_add m k v1)
end))


let deps_keys : dependence_graph  ->  Prims.string Prims.list = (fun uu____783 -> (match (uu____783) with
| Deps (m) -> begin
(FStar_Util.smap_keys m)
end))


let deps_empty : unit  ->  dependence_graph = (fun uu____795 -> (

let uu____796 = (FStar_Util.smap_create (Prims.parse_int "41"))
in Deps (uu____796)))


let mk_deps : dependence_graph  ->  files_for_module_name  ->  file_name Prims.list  ->  file_name Prims.list  ->  module_name Prims.list  ->  deps = (fun dg fs c a i -> {dep_graph = dg; file_system_map = fs; cmd_line_files = c; all_files = a; interfaces_with_inlining = i})


let empty_deps : deps = (

let uu____845 = (deps_empty ())
in (

let uu____846 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (mk_deps uu____845 uu____846 [] [] [])))


let module_name_of_dep : dependence  ->  module_name = (fun uu___120_867 -> (match (uu___120_867) with
| UseInterface (m) -> begin
m
end
| PreferInterface (m) -> begin
m
end
| UseImplementation (m) -> begin
m
end
| FriendImplementation (m) -> begin
m
end))


let resolve_module_name : files_for_module_name  ->  module_name  ->  module_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____896 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____896) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____923) -> begin
(

let uu____945 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____945))
end
| FStar_Pervasives_Native.Some (uu____948, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____971 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____971))
end
| uu____974 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____1007 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1007) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____1034) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____1057 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____1090 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1090) with
| FStar_Pervasives_Native.Some (uu____1116, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____1140 -> begin
FStar_Pervasives_Native.None
end)))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1169 = (interface_of file_system_map key)
in (FStar_Option.isSome uu____1169)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1189 = (implementation_of file_system_map key)
in (FStar_Option.isSome uu____1189)))


let cache_file_name_internal : Prims.string  ->  (Prims.string * Prims.bool) = (fun fn -> (

let cache_fn = (

let uu____1216 = (

let uu____1218 = (FStar_Options.lax ())
in (match (uu____1218) with
| true -> begin
".checked.lax"
end
| uu____1223 -> begin
".checked"
end))
in (Prims.strcat fn uu____1216))
in (

let uu____1226 = (

let uu____1230 = (FStar_All.pipe_right cache_fn FStar_Util.basename)
in (FStar_Options.find_file uu____1230))
in (match (uu____1226) with
| FStar_Pervasives_Native.Some (path) -> begin
((path), (true))
end
| FStar_Pervasives_Native.None -> begin
(

let mname = (FStar_All.pipe_right fn module_name_of_file)
in (

let uu____1251 = (FStar_All.pipe_right mname FStar_Options.should_be_already_cached)
in (match (uu____1251) with
| true -> begin
(

let uu____1262 = (

let uu____1268 = (FStar_Util.format1 "Expected %s to be already checked but could not find it" mname)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1268)))
in (FStar_Errors.raise_err uu____1262))
end
| uu____1278 -> begin
(

let uu____1280 = (FStar_Options.prepend_cache_dir cache_fn)
in ((uu____1280), (false)))
end)))
end))))


let cache_file_name : Prims.string  ->  Prims.string = (fun fn -> (

let uu____1294 = (FStar_All.pipe_right fn cache_file_name_internal)
in (FStar_All.pipe_right uu____1294 FStar_Pervasives_Native.fst)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____1366 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____1366)))))))
in (

let maybe_use_cache_of = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____1380 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____1385 = (interface_of file_system_map key)
in (match (uu____1385) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1392 = (

let uu____1398 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____1398)))
in (FStar_Errors.raise_err uu____1392))
end
| FStar_Pervasives_Native.Some (f) -> begin
f
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____1408 = ((cmd_line_has_impl key) && (

let uu____1411 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____1411)))
in (match (uu____1408) with
| true -> begin
(

let uu____1418 = (FStar_Options.expose_interfaces ())
in (match (uu____1418) with
| true -> begin
(

let uu____1422 = (

let uu____1424 = (implementation_of file_system_map key)
in (FStar_Option.get uu____1424))
in (maybe_use_cache_of uu____1422))
end
| uu____1429 -> begin
(

let uu____1431 = (

let uu____1437 = (

let uu____1439 = (

let uu____1441 = (implementation_of file_system_map key)
in (FStar_Option.get uu____1441))
in (

let uu____1446 = (

let uu____1448 = (interface_of file_system_map key)
in (FStar_Option.get uu____1448))
in (FStar_Util.format3 "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" key uu____1439 uu____1446)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____1437)))
in (FStar_Errors.raise_err uu____1431))
end))
end
| uu____1456 -> begin
(

let uu____1458 = (

let uu____1460 = (interface_of file_system_map key)
in (FStar_Option.get uu____1460))
in (maybe_use_cache_of uu____1458))
end))
end
| PreferInterface (key) -> begin
(

let uu____1467 = (implementation_of file_system_map key)
in (match (uu____1467) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1473 = (

let uu____1479 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1479)))
in (FStar_Errors.raise_err uu____1473))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| UseImplementation (key) -> begin
(

let uu____1489 = (implementation_of file_system_map key)
in (match (uu____1489) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1495 = (

let uu____1501 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1501)))
in (FStar_Errors.raise_err uu____1495))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| FriendImplementation (key) -> begin
(

let uu____1511 = (implementation_of file_system_map key)
in (match (uu____1511) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1517 = (

let uu____1523 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____1523)))
in (FStar_Errors.raise_err uu____1517))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____1584 = (deps_try_find deps fn)
in (match (uu____1584) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some ({edges = deps1; color = uu____1592}) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let print_graph : dependence_graph  ->  unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1606 = (

let uu____1608 = (

let uu____1610 = (

let uu____1612 = (

let uu____1616 = (

let uu____1620 = (deps_keys graph)
in (FStar_List.unique uu____1620))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1634 = (

let uu____1635 = (deps_try_find graph k)
in (FStar_Util.must uu____1635))
in uu____1634.edges)
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (

let uu____1656 = (

let uu____1658 = (lowercase_module_name k)
in (r uu____1658))
in (FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____1656 (r (module_name_of_dep dep1)))))
in (FStar_List.map print7 deps))))) uu____1616))
in (FStar_String.concat "\n" uu____1612))
in (Prims.strcat uu____1610 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1608))
in (FStar_Util.write_file "dep.graph" uu____1606));
))


let build_inclusion_candidates_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____1679 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____1705 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____1705))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.is_directory d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____1745 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____1745 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____1776 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____1780 -> begin
(

let uu____1782 = (

let uu____1788 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____1788)))
in (FStar_Errors.raise_err uu____1782))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____1851 = (FStar_Util.smap_try_find map1 key)
in (match (uu____1851) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____1898 = (is_interface full_path)
in (match (uu____1898) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____1918 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1947 = (is_interface full_path)
in (match (uu____1947) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____1968 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____1989 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____2007 -> (match (uu____2007) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____1989));
(FStar_List.iter (fun f -> (

let uu____2026 = (lowercase_module_name f)
in (add_entry uu____2026 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____2058 = (

let uu____2062 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____2062))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____2098 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____2098))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____2186 -> begin
()
end)) uu____2058));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____2255 -> begin
[]
end)
in (

let names = (

let uu____2262 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____2262 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____2285 = (string_of_lid l last1)
in (FStar_String.lowercase uu____2285)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____2294 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____2294)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____2316 = (

let uu____2318 = (

let uu____2320 = (

let uu____2322 = (

let uu____2326 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____2326))
in (FStar_Util.must uu____2322))
in (FStar_String.lowercase uu____2320))
in (Prims.op_disEquality uu____2318 k'))
in (match (uu____2316) with
| true -> begin
(

let uu____2331 = (FStar_Ident.range_of_lid lid)
in (

let uu____2332 = (

let uu____2338 = (

let uu____2340 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____2340 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____2338)))
in (FStar_Errors.log_issue uu____2331 uu____2332)))
end
| uu____2345 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____2356 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____2378 = (FStar_Options.prims_basename ())
in (

let uu____2380 = (

let uu____2384 = (FStar_Options.pervasives_basename ())
in (

let uu____2386 = (

let uu____2390 = (FStar_Options.pervasives_native_basename ())
in (uu____2390)::[])
in (uu____2384)::uu____2386))
in (uu____2378)::uu____2380))
in (

let uu____2396 = ((FStar_List.mem filename corelibs) || (

let uu____2400 = (module_name_of_file filename)
in (FStar_Util.starts_with uu____2400 "FStar.Pervasives")))
in (match (uu____2396) with
| true -> begin
[]
end
| uu____2414 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____2439 = (

let uu____2442 = (lowercase_module_name full_filename)
in (namespace_of_module uu____2442))
in (match (uu____2439) with
| FStar_Pervasives_Native.None -> begin
implicit_deps
end
| FStar_Pervasives_Native.Some (ns) -> begin
(FStar_List.append implicit_deps ((((ns), (Open_namespace)))::[]))
end)))
end)))))


let dep_subsumed_by : dependence  ->  dependence  ->  Prims.bool = (fun d d' -> (match (((d), (d'))) with
| (PreferInterface (l'), FriendImplementation (l)) -> begin
(Prims.op_Equality l l')
end
| uu____2481 -> begin
(Prims.op_Equality d d')
end))


let collect_one : files_for_module_name  ->  Prims.string  ->  (dependence Prims.list * dependence Prims.list * Prims.bool) = (fun original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let mo_roots = (FStar_Util.mk_ref [])
in (

let has_inline_for_extraction = (FStar_Util.mk_ref false)
in (

let set_interface_inlining = (fun uu____2546 -> (

let uu____2547 = (is_interface filename)
in (match (uu____2547) with
| true -> begin
(FStar_ST.op_Colon_Equals has_inline_for_extraction true)
end
| uu____2594 -> begin
()
end)))
in (

let add_dep = (fun deps1 d -> (

let uu____2754 = (

let uu____2756 = (

let uu____2758 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (dep_subsumed_by d) uu____2758))
in (not (uu____2756)))
in (match (uu____2754) with
| true -> begin
(

let uu____2827 = (

let uu____2830 = (FStar_ST.op_Bang deps1)
in (d)::uu____2830)
in (FStar_ST.op_Colon_Equals deps1 uu____2827))
end
| uu____2963 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let dep_edge = (fun module_name -> PreferInterface (module_name))
in (

let add_dependence_edge = (fun original_or_working_map lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____3011 = (resolve_module_name original_or_working_map key)
in (match (uu____3011) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (dep_edge module_name));
(

let uu____3054 = ((has_interface original_or_working_map module_name) && (has_implementation original_or_working_map module_name))
in (match (uu____3054) with
| true -> begin
(add_dep mo_roots (UseImplementation (module_name)))
end
| uu____3090 -> begin
()
end));
true;
)
end
| uu____3093 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____3112 = ((let_open && (add_dependence_edge working_map lid)) || ((not (let_open)) && (add_dependence_edge original_map lid)))
in (match (uu____3112) with
| true -> begin
true
end
| uu____3117 -> begin
((match (let_open) with
| true -> begin
(

let uu____3121 = (FStar_Ident.range_of_lid lid)
in (

let uu____3122 = (

let uu____3128 = (

let uu____3130 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____3130))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3128)))
in (FStar_Errors.log_issue uu____3121 uu____3122)))
end
| uu____3135 -> begin
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

let uu____3150 = (FStar_Ident.range_of_lid lid)
in (

let uu____3151 = (

let uu____3157 = (

let uu____3159 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____3159))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3157)))
in (FStar_Errors.log_issue uu____3150 uu____3151)))
end
| uu____3164 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____3179 = (record_open_module let_open lid)
in (match (uu____3179) with
| true -> begin
()
end
| uu____3182 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____3185 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____3196 -> (match (uu____3196) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____3203 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (

let uu____3220 = (FStar_Ident.text_of_id ident)
in (FStar_String.lowercase uu____3220))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____3225 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____3225) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____3293 = (FStar_Ident.range_of_lid lid)
in (

let uu____3294 = (

let uu____3300 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3300)))
in (FStar_Errors.log_issue uu____3293 uu____3294)));
false;
)
end)))))
in (

let add_dep_on_module = (fun module_name -> (

let uu____3311 = (add_dependence_edge working_map module_name)
in (match (uu____3311) with
| true -> begin
()
end
| uu____3314 -> begin
(

let uu____3316 = (FStar_Options.debug_any ())
in (match (uu____3316) with
| true -> begin
(

let uu____3319 = (FStar_Ident.range_of_lid module_name)
in (

let uu____3320 = (

let uu____3326 = (

let uu____3328 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____3328))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____3326)))
in (FStar_Errors.log_issue uu____3319 uu____3320)))
end
| uu____3332 -> begin
()
end))
end)))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3340 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (add_dep_on_module module_name))
end))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_module = (fun uu___121_3468 -> (match (uu___121_3468) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3479 = (

let uu____3481 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____3481))
in ())
end
| uu____3483 -> begin
()
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____3487) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3498 = (

let uu____3500 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____3500))
in ())
end
| uu____3502 -> begin
()
end);
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
(match ((FStar_List.contains FStar_Parser_AST.Inline_for_extraction x.FStar_Parser_AST.quals)) with
| true -> begin
(set_interface_inlining ())
end
| uu____3514 -> begin
()
end);
)) decls))
and collect_decl = (fun d -> (match (d) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Friend (lid) -> begin
(

let uu____3522 = (

let uu____3523 = (lowercase_join_longident lid true)
in FriendImplementation (uu____3523))
in (add_dep deps uu____3522))
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(

let uu____3561 = (record_module_alias ident lid)
in (match (uu____3561) with
| true -> begin
(

let uu____3564 = (

let uu____3565 = (lowercase_join_longident lid true)
in (dep_edge uu____3565))
in (add_dep deps uu____3564))
end
| uu____3601 -> begin
()
end))
end
| FStar_Parser_AST.TopLevelLet (uu____3603, patterms) -> begin
(FStar_List.iter (fun uu____3625 -> (match (uu____3625) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (uu____3634, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____3640, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3642; FStar_Parser_AST.mdest = uu____3643; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3645; FStar_Parser_AST.mdest = uu____3646; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____3648, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____3650; FStar_Parser_AST.mdest = uu____3651; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____3655, tc, ts) -> begin
((match (tc) with
| true -> begin
(record_lid FStar_Parser_Const.mk_class_lid)
end
| uu____3680 -> begin
()
end);
(

let ts1 = (FStar_List.map (fun uu____3694 -> (match (uu____3694) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1));
)
end
| FStar_Parser_AST.Exception (uu____3707, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____3714) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____3715) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____3751 = (

let uu____3753 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____3753 > (Prims.parse_int "1")))
in (match (uu____3751) with
| true -> begin
(

let uu____3800 = (

let uu____3806 = (

let uu____3808 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____3808))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____3806)))
in (

let uu____3813 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____3800 uu____3813)))
end
| uu____3814 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___122_3816 -> (match (uu___122_3816) with
| FStar_Parser_AST.TyconAbstract (uu____3817, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____3829, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____3843, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3889 -> (match (uu____3889) with
| (uu____3898, t, uu____3900) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____3905, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____3967 -> (match (uu____3967) with
| (uu____3981, t, uu____3983, uu____3984) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___123_3995 -> (match (uu___123_3995) with
| FStar_Parser_AST.DefineEffect (uu____3996, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____4010, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun b -> ((collect_aqual b.FStar_Parser_AST.aqual);
(match (b) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____4023, t); FStar_Parser_AST.brange = uu____4025; FStar_Parser_AST.blevel = uu____4026; FStar_Parser_AST.aqual = uu____4027} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____4030, t); FStar_Parser_AST.brange = uu____4032; FStar_Parser_AST.blevel = uu____4033; FStar_Parser_AST.aqual = uu____4034} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____4038; FStar_Parser_AST.blevel = uu____4039; FStar_Parser_AST.aqual = uu____4040} -> begin
(collect_term t)
end
| uu____4043 -> begin
()
end);
))
and collect_aqual = (fun uu___124_4044 -> (match (uu___124_4044) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (t)) -> begin
(collect_term t)
end
| uu____4048 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___125_4052 -> (match (uu___125_4052) with
| FStar_Const.Const_int (uu____4053, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____4080 = (

let uu____4081 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (dep_edge uu____4081))
in (add_dep deps uu____4080))))
end
| FStar_Const.Const_char (uu____4117) -> begin
(add_dep deps (dep_edge "fstar.char"))
end
| FStar_Const.Const_float (uu____4153) -> begin
(add_dep deps (dep_edge "fstar.float"))
end
| uu____4188 -> begin
()
end))
and collect_term' = (fun uu___129_4189 -> (match (uu___129_4189) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4191}, (lhs)::(rhs)::[]) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4207}, (t1)::(t2)::[]) -> begin
(

let uu____4213 = (flatten1 t1)
in (FStar_List.append uu____4213 ((t2)::[])))
end
| uu____4216 -> begin
(t)::[]
end))
in (

let terms = (flatten1 lhs)
in (

let n1 = ((FStar_List.length terms) + (Prims.parse_int "1"))
in ((

let uu____4224 = (FStar_Parser_Const.mk_n_tuple_lid n1 "tuple" FStar_Range.dummyRange)
in (record_lid uu____4224));
(FStar_List.iter collect_term ((lhs)::(rhs)::[]));
))))
end
| FStar_Parser_AST.Op (s, ts) -> begin
((

let uu____4233 = (

let uu____4235 = (FStar_Ident.text_of_id s)
in (Prims.op_Equality uu____4235 "@"))
in (match (uu____4233) with
| true -> begin
(

let uu____4240 = (

let uu____4241 = (

let uu____4242 = (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
in (FStar_Ident.lid_of_path uu____4242 FStar_Range.dummyRange))
in FStar_Parser_AST.Name (uu____4241))
in (collect_term' uu____4240))
end
| uu____4244 -> begin
()
end));
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____4246) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____4247) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____4250) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Name (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((record_lid lid);
(FStar_List.iter (fun uu____4275 -> (match (uu____4275) with
| (t, uu____4281) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____4291) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____4293, patterms, t) -> begin
((FStar_List.iter (fun uu____4343 -> (match (uu____4343) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____4372 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
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
| FStar_Parser_AST.Bind (uu____4382, t1, t2) -> begin
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
(FStar_List.iter (fun uu____4478 -> (match (uu____4478) with
| (uu____4483, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____4486) -> begin
(collect_term t)
end
| FStar_Parser_AST.Product (binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
((FStar_List.iter (fun uu___126_4515 -> (match (uu___126_4515) with
| FStar_Util.Inl (b) -> begin
(collect_binder b)
end
| FStar_Util.Inr (t1) -> begin
(collect_term t1)
end)) binders);
(

let n1 = ((FStar_List.length binders) + (Prims.parse_int "1"))
in (

let dependent = (FStar_Util.for_some (fun uu___127_4537 -> (match (uu___127_4537) with
| FStar_Util.Inl (uu____4543) -> begin
true
end
| uu____4545 -> begin
false
end)) binders)
in ((match (dependent) with
| true -> begin
(match ((n1 > (Prims.parse_int "2"))) with
| true -> begin
(

let uu____4555 = (FStar_Parser_Const.mod_prefix_dtuple n1 "dtuple")
in (record_lid uu____4555))
end
| uu____4557 -> begin
()
end)
end
| uu____4559 -> begin
(

let uu____4561 = (FStar_Parser_Const.mk_n_tuple_lid n1 "tuple" FStar_Range.dummyRange)
in (record_lid uu____4561))
end);
(collect_term t);
)));
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
| FStar_Parser_AST.NamedTyp (uu____4604, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____4608) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____4616) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____4624, uu____4625) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (t, uu____4631) -> begin
(collect_term t)
end
| FStar_Parser_AST.Antiquote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.VQuote (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end
| FStar_Parser_AST.CalcProof (rel, init1, steps) -> begin
((

let uu____4645 = (FStar_Ident.lid_of_str "FStar.Calc")
in (add_dep_on_module uu____4645));
(collect_term rel);
(collect_term init1);
(FStar_List.iter (fun uu___128_4655 -> (match (uu___128_4655) with
| FStar_Parser_AST.CalcStep (rel1, just, next) -> begin
((collect_term rel1);
(collect_term just);
(collect_term next);
)
end)) steps);
)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___130_4665 -> (match (uu___130_4665) with
| FStar_Parser_AST.PatVar (uu____4666, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatTvar (uu____4672, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatWild (aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatOp (uu____4681) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____4682) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatName (uu____4690) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(

let n1 = (FStar_List.length ps)
in ((

let uu____4696 = (FStar_Parser_Const.mk_n_tuple_lid n1 "tuple" FStar_Range.dummyRange)
in (record_lid uu____4696));
(collect_patterns ps);
))
end
| FStar_Parser_AST.PatOr (ps) -> begin
(

let n1 = (FStar_List.length ps)
in ((

let uu____4709 = (FStar_Parser_Const.mk_n_tuple_lid n1 "tuple" FStar_Range.dummyRange)
in (record_lid uu____4709));
(collect_patterns ps);
))
end
| FStar_Parser_AST.PatTuple (ps, uu____4718) -> begin
(

let n1 = (FStar_List.length ps)
in ((

let uu____4727 = (FStar_Parser_Const.mk_n_tuple_lid n1 "tuple" FStar_Range.dummyRange)
in (record_lid uu____4727));
(collect_patterns ps);
))
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____4749 -> (match (uu____4749) with
| (uu____4754, p) -> begin
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
and collect_branch = (fun uu____4799 -> (match (uu____4799) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____4817 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____4817) with
| (ast, uu____4841) -> begin
(

let mname = (lowercase_module_name filename)
in ((

let uu____4859 = ((is_interface filename) && (has_implementation original_map mname))
in (match (uu____4859) with
| true -> begin
(add_dep mo_roots (UseImplementation (mname)))
end
| uu____4895 -> begin
()
end));
(collect_module ast);
(

let uu____4898 = (FStar_ST.op_Bang deps)
in (

let uu____4946 = (FStar_ST.op_Bang mo_roots)
in (

let uu____4994 = (FStar_ST.op_Bang has_inline_for_extraction)
in ((uu____4898), (uu____4946), (uu____4994)))));
))
end))));
))))))))))))))))))


let collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap FStar_ST.ref = (

let uu____5071 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (FStar_Util.mk_ref uu____5071))


let set_collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap  ->  unit = (fun cache -> (FStar_ST.op_Colon_Equals collect_one_cache cache))


let dep_graph_copy : dependence_graph  ->  dependence_graph = (fun dep_graph -> (

let uu____5193 = dep_graph
in (match (uu____5193) with
| Deps (g) -> begin
(

let uu____5197 = (FStar_Util.smap_copy g)
in Deps (uu____5197))
end)))


let topological_dependences_of : files_for_module_name  ->  dependence_graph  ->  Prims.string Prims.list  ->  file_name Prims.list  ->  Prims.bool  ->  (file_name Prims.list * Prims.bool) = (fun file_system_map dep_graph interfaces_needing_inlining root_files for_extraction -> (

let rec all_friend_deps_1 = (fun dep_graph1 cycle uu____5342 filename -> (match (uu____5342) with
| (all_friends, all_files) -> begin
(

let dep_node = (

let uu____5383 = (deps_try_find dep_graph1 filename)
in (FStar_Util.must uu____5383))
in (match (dep_node.color) with
| Gray -> begin
(failwith "Impossible: cycle detected after cycle detection has passed")
end
| Black -> begin
((all_friends), (all_files))
end
| White -> begin
((

let uu____5414 = (FStar_Options.debug_any ())
in (match (uu____5414) with
| true -> begin
(

let uu____5417 = (

let uu____5419 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_String.concat ", " uu____5419))
in (FStar_Util.print2 "Visiting %s: direct deps are %s\n" filename uu____5417))
end
| uu____5426 -> begin
()
end));
(deps_add_dep dep_graph1 filename (

let uu___134_5430 = dep_node
in {edges = uu___134_5430.edges; color = Gray}));
(

let uu____5431 = (

let uu____5442 = (dependences_of file_system_map dep_graph1 root_files filename)
in (all_friend_deps dep_graph1 cycle ((all_friends), (all_files)) uu____5442))
in (match (uu____5431) with
| (all_friends1, all_files1) -> begin
((deps_add_dep dep_graph1 filename (

let uu___135_5478 = dep_node
in {edges = uu___135_5478.edges; color = Black}));
(

let uu____5480 = (FStar_Options.debug_any ())
in (match (uu____5480) with
| true -> begin
(FStar_Util.print1 "Adding %s\n" filename)
end
| uu____5484 -> begin
()
end));
(

let uu____5486 = (

let uu____5490 = (FStar_List.collect (fun uu___131_5497 -> (match (uu___131_5497) with
| FriendImplementation (m) -> begin
(m)::[]
end
| d -> begin
[]
end)) dep_node.edges)
in (FStar_List.append uu____5490 all_friends1))
in ((uu____5486), ((filename)::all_files1)));
)
end));
)
end))
end))
and all_friend_deps = (fun dep_graph1 cycle all_friends filenames -> (FStar_List.fold_left (fun all_friends1 k -> (all_friend_deps_1 dep_graph1 ((k)::cycle) all_friends1 k)) all_friends filenames))
in ((

let uu____5563 = (FStar_Options.debug_any ())
in (match (uu____5563) with
| true -> begin
(FStar_Util.print_string "==============Phase1==================\n")
end
| uu____5567 -> begin
()
end));
(

let widened = (FStar_Util.mk_ref false)
in (

let widen_deps = (fun friends deps -> (

let uu____5592 = deps
in (match (uu____5592) with
| Deps (dg) -> begin
(

let uu____5596 = (deps_empty ())
in (match (uu____5596) with
| Deps (dg') -> begin
(

let widen_one = (fun deps1 -> (FStar_All.pipe_right deps1 (FStar_List.map (fun d -> (match (d) with
| PreferInterface (m) when ((FStar_List.contains m friends) && (has_implementation file_system_map m)) -> begin
((FStar_ST.op_Colon_Equals widened true);
FriendImplementation (m);
)
end
| uu____5668 -> begin
d
end)))))
in ((FStar_Util.smap_fold dg (fun filename dep_node uu____5676 -> (

let uu____5678 = (

let uu___136_5679 = dep_node
in (

let uu____5680 = (widen_one dep_node.edges)
in {edges = uu____5680; color = White}))
in (FStar_Util.smap_add dg' filename uu____5678))) ());
Deps (dg');
))
end))
end)))
in (

let dep_graph1 = (

let uu____5682 = ((FStar_Options.cmi ()) && for_extraction)
in (match (uu____5682) with
| true -> begin
(widen_deps interfaces_needing_inlining dep_graph)
end
| uu____5685 -> begin
dep_graph
end))
in (

let uu____5687 = (all_friend_deps dep_graph1 [] (([]), ([])) root_files)
in (match (uu____5687) with
| (friends, all_files_0) -> begin
((

let uu____5730 = (FStar_Options.debug_any ())
in (match (uu____5730) with
| true -> begin
(

let uu____5733 = (

let uu____5735 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) friends)
in (FStar_String.concat ", " uu____5735))
in (FStar_Util.print3 "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n" (FStar_String.concat ", " all_files_0) uu____5733 (FStar_String.concat ", " interfaces_needing_inlining)))
end
| uu____5751 -> begin
()
end));
(

let dep_graph2 = (widen_deps friends dep_graph1)
in (

let uu____5754 = ((

let uu____5766 = (FStar_Options.debug_any ())
in (match (uu____5766) with
| true -> begin
(FStar_Util.print_string "==============Phase2==================\n")
end
| uu____5770 -> begin
()
end));
(all_friend_deps dep_graph2 [] (([]), ([])) root_files);
)
in (match (uu____5754) with
| (uu____5789, all_files) -> begin
((

let uu____5804 = (FStar_Options.debug_any ())
in (match (uu____5804) with
| true -> begin
(FStar_Util.print1 "Phase2 complete: all_files = %s\n" (FStar_String.concat ", " all_files))
end
| uu____5809 -> begin
()
end));
(

let uu____5811 = (FStar_ST.op_Bang widened)
in ((all_files), (uu____5811)));
)
end)));
)
end)))));
)))


let collect : Prims.string Prims.list  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____5903 = (FStar_Options.find_file fn)
in (match (uu____5903) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5909 = (

let uu____5915 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____5915)))
in (FStar_Errors.raise_err uu____5909))
end
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end)))))
in (

let dep_graph = (deps_empty ())
in (

let file_system_map = (build_map all_cmd_line_files1)
in (

let interfaces_needing_inlining = (FStar_Util.mk_ref [])
in (

let add_interface_for_inlining = (fun l -> (

let l1 = (lowercase_module_name l)
in (

let uu____5945 = (

let uu____5949 = (FStar_ST.op_Bang interfaces_needing_inlining)
in (l1)::uu____5949)
in (FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____5945))))
in (

let rec discover_one = (fun file_name -> (

let uu____6056 = (

let uu____6058 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____6058 FStar_Pervasives_Native.None))
in (match (uu____6056) with
| true -> begin
(

let uu____6064 = (

let uu____6076 = (

let uu____6090 = (FStar_ST.op_Bang collect_one_cache)
in (FStar_Util.smap_try_find uu____6090 file_name))
in (match (uu____6076) with
| FStar_Pervasives_Native.Some (cached) -> begin
cached
end
| FStar_Pervasives_Native.None -> begin
(collect_one file_system_map file_name)
end))
in (match (uu____6064) with
| (deps, mo_roots, needs_interface_inlining) -> begin
((match (needs_interface_inlining) with
| true -> begin
(add_interface_for_inlining file_name)
end
| uu____6220 -> begin
()
end);
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____6227 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____6227) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____6232 -> begin
deps
end)))
in (

let dep_node = (

let uu____6235 = (FStar_List.unique deps1)
in {edges = uu____6235; color = White})
in ((deps_add_dep dep_graph file_name dep_node);
(

let uu____6237 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____6237));
)));
)
end))
end
| uu____6243 -> begin
()
end)))
in ((FStar_List.iter discover_one all_cmd_line_files1);
(

let cycle_detected = (fun dep_graph1 cycle filename -> ((FStar_Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (FStar_String.concat "\n`used by` " cycle));
(print_graph dep_graph1);
(FStar_Util.print_string "\n");
(

let uu____6277 = (

let uu____6283 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Fatal_CyclicDependence), (uu____6283)))
in (FStar_Errors.raise_err uu____6277));
))
in (

let full_cycle_detection = (fun all_command_line_files -> (

let dep_graph1 = (dep_graph_copy dep_graph)
in (

let rec aux = (fun cycle filename -> (

let node = (

let uu____6320 = (deps_try_find dep_graph1 filename)
in (match (uu____6320) with
| FStar_Pervasives_Native.Some (node) -> begin
node
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6324 = (FStar_Util.format1 "Failed to find dependences of %s" filename)
in (failwith uu____6324))
end))
in (

let direct_deps = (FStar_All.pipe_right node.edges (FStar_List.collect (fun x -> (match (x) with
| UseInterface (f) -> begin
(

let uu____6338 = (implementation_of file_system_map f)
in (match (uu____6338) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6349 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| PreferInterface (f) -> begin
(

let uu____6355 = (implementation_of file_system_map f)
in (match (uu____6355) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6366 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| uu____6370 -> begin
(x)::[]
end))))
in (match (node.color) with
| Gray -> begin
(cycle_detected dep_graph1 cycle filename)
end
| Black -> begin
()
end
| White -> begin
((deps_add_dep dep_graph1 filename (

let uu___137_6373 = node
in {edges = direct_deps; color = Gray}));
(

let uu____6375 = (dependences_of file_system_map dep_graph1 all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____6375));
(deps_add_dep dep_graph1 filename (

let uu___138_6385 = node
in {edges = direct_deps; color = Black}));
)
end))))
in (FStar_List.iter (aux []) all_command_line_files))))
in ((full_cycle_detection all_cmd_line_files1);
(FStar_All.pipe_right all_cmd_line_files1 (FStar_List.iter (fun f -> (

let m = (lowercase_module_name f)
in (FStar_Options.add_verify_module m)))));
(

let inlining_ifaces = (FStar_ST.op_Bang interfaces_needing_inlining)
in (

let uu____6451 = (

let uu____6460 = (

let uu____6462 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____6462 FStar_Pervasives_Native.None))
in (topological_dependences_of file_system_map dep_graph inlining_ifaces all_cmd_line_files1 uu____6460))
in (match (uu____6451) with
| (all_files, uu____6475) -> begin
((

let uu____6485 = (FStar_Options.debug_any ())
in (match (uu____6485) with
| true -> begin
(FStar_Util.print1 "Interfaces needing inlining: %s\n" (FStar_String.concat ", " inlining_ifaces))
end
| uu____6490 -> begin
()
end));
((all_files), ((mk_deps dep_graph file_system_map all_cmd_line_files1 all_files inlining_ifaces)));
)
end)));
)));
))))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun deps f -> (dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f))


let hash_dependences : deps  ->  Prims.string  ->  Prims.string  ->  (Prims.string * Prims.string) Prims.list FStar_Pervasives_Native.option = (fun deps fn cache_file -> (

let file_system_map = deps.file_system_map
in (

let all_cmd_line_files = deps.cmd_line_files
in (

let deps1 = deps.dep_graph
in (

let fn1 = (

let uu____6552 = (FStar_Options.find_file fn)
in (match (uu____6552) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____6560 -> begin
fn
end))
in (

let digest_of_file1 = (fun fn2 -> ((

let uu____6574 = (FStar_Options.debug_any ())
in (match (uu____6574) with
| true -> begin
(FStar_Util.print2 "%s: contains digest of %s\n" cache_file fn2)
end
| uu____6578 -> begin
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

let uu____6593 = ((is_implementation fn1) && (has_interface file_system_map module_name))
in (match (uu____6593) with
| true -> begin
(

let uu____6604 = (

let uu____6611 = (

let uu____6613 = (

let uu____6615 = (interface_of file_system_map module_name)
in (FStar_Option.get uu____6615))
in (digest_of_file1 uu____6613))
in (("interface"), (uu____6611)))
in (uu____6604)::[])
end
| uu____6635 -> begin
[]
end))
in (

let binary_deps = (

let uu____6647 = (dependences_of file_system_map deps1 all_cmd_line_files fn1)
in (FStar_All.pipe_right uu____6647 (FStar_List.filter (fun fn2 -> (

let uu____6662 = ((is_interface fn2) && (

let uu____6665 = (lowercase_module_name fn2)
in (Prims.op_Equality uu____6665 module_name)))
in (not (uu____6662)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____6681 = (lowercase_module_name fn11)
in (

let uu____6683 = (lowercase_module_name fn2)
in (FStar_String.compare uu____6681 uu____6683)))) binary_deps)
in (

let rec hash_deps = (fun out uu___132_6716 -> (match (uu___132_6716) with
| [] -> begin
FStar_Pervasives_Native.Some ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps2 -> begin
(

let cache_fn = (cache_file_name fn2)
in (

let digest = (match ((FStar_Util.file_exists cache_fn)) with
| true -> begin
(

let uu____6779 = (digest_of_file1 fn2)
in FStar_Pervasives_Native.Some (uu____6779))
end
| uu____6782 -> begin
FStar_Pervasives_Native.None
end)
in (match (digest) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6797 = (FStar_Options.debug_any ())
in (match (uu____6797) with
| true -> begin
(

let uu____6800 = (FStar_Util.basename cache_fn)
in (FStar_Util.print2 "%s: missed digest of file %s\n" cache_file uu____6800))
end
| uu____6803 -> begin
()
end));
FStar_Pervasives_Native.None;
)
end
| FStar_Pervasives_Native.Some (dig) -> begin
(

let uu____6816 = (

let uu____6825 = (

let uu____6832 = (lowercase_module_name fn2)
in ((uu____6832), (dig)))
in (uu____6825)::out)
in (hash_deps uu____6816 deps2))
end)))
end))
in (hash_deps [] binary_deps1)))))))))))))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____6872 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____6898 -> (match (uu____6898) with
| (m, d) -> begin
(

let uu____6912 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____6912))
end))))
in (FStar_All.pipe_right uu____6872 (FStar_String.concat "\n"))))


let print_make : deps  ->  unit = (fun deps -> (

let file_system_map = deps.file_system_map
in (

let all_cmd_line_files = deps.cmd_line_files
in (

let deps1 = deps.dep_graph
in (

let keys = (deps_keys deps1)
in (FStar_All.pipe_right keys (FStar_List.iter (fun f -> (

let dep_node = (

let uu____6947 = (deps_try_find deps1 f)
in (FStar_All.pipe_right uu____6947 FStar_Option.get))
in (

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) dep_node.edges)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))))))))))))


let print_raw : deps  ->  unit = (fun deps -> (

let uu____6976 = deps.dep_graph
in (match (uu____6976) with
| Deps (deps1) -> begin
(

let uu____6980 = (

let uu____6982 = (FStar_Util.smap_fold deps1 (fun k dep_node out -> (

let uu____7000 = (

let uu____7002 = (

let uu____7004 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_All.pipe_right uu____7004 (FStar_String.concat ";\n\t")))
in (FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7002))
in (uu____7000)::out)) [])
in (FStar_All.pipe_right uu____6982 (FStar_String.concat ";;\n")))
in (FStar_All.pipe_right uu____6980 FStar_Util.print_endline))
end)))


let print_full : deps  ->  unit = (fun deps -> (

let sort_output_files = (fun orig_output_file_map -> (

let order = (FStar_Util.mk_ref [])
in (

let remaining_output_files = (FStar_Util.smap_copy orig_output_file_map)
in (

let visited_other_modules = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let should_visit = (fun lc_module_name -> ((

let uu____7076 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____7076)) || (

let uu____7083 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____7083))))
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

let uu____7126 = (

let uu____7130 = (FStar_ST.op_Bang order)
in (ml_file)::uu____7130)
in (FStar_ST.op_Colon_Equals order uu____7126))
end))
in (

let rec aux = (fun uu___133_7237 -> (match (uu___133_7237) with
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

let uu____7265 = (deps_try_find deps.dep_graph file_name)
in (match (uu____7265) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7268 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____7268))
end
| FStar_Pervasives_Native.Some ({edges = immediate_deps; color = uu____7272}) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____7281 = (should_visit lc_module_name)
in (match (uu____7281) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____7289 = (implementation_of deps.file_system_map lc_module_name)
in (visit_file uu____7289));
(

let uu____7294 = (interface_of deps.file_system_map lc_module_name)
in (visit_file uu____7294));
(emit_output_file_opt ml_file_opt);
))
end
| uu____7298 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____7306 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____7306));
))))))))))
in (

let keys = (deps_keys deps.dep_graph)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____7380 = (

let uu____7382 = (

let uu____7386 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____7386))
in (FStar_Option.get uu____7382))
in (FStar_Util.replace_chars uu____7380 46 (*.*) "_"))
in (FStar_Options.prepend_output_dir (Prims.strcat ml_base_name ext))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____7411 = (output_file ".ml" f)
in (norm_path uu____7411)))
in (

let output_krml_file = (fun f -> (

let uu____7423 = (output_file ".krml" f)
in (norm_path uu____7423)))
in (

let output_cmx_file = (fun f -> (

let uu____7435 = (output_file ".cmx" f)
in (norm_path uu____7435)))
in (

let cache_file = (fun f -> (

let uu____7452 = (FStar_All.pipe_right f cache_file_name_internal)
in (FStar_All.pipe_right uu____7452 (fun uu____7481 -> (match (uu____7481) with
| (f1, b) -> begin
(((norm_path f1)), (b))
end)))))
in (

let transitive_krml = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let set_of_unchecked_files = (

let uu____7532 = (

let uu____7543 = (FStar_Util.new_set FStar_Util.compare)
in (FStar_List.fold_left (fun set_of_unchecked_files file_name -> (

let dep_node = (

let uu____7582 = (deps_try_find deps.dep_graph file_name)
in (FStar_All.pipe_right uu____7582 FStar_Option.get))
in (

let iface_deps = (

let uu____7592 = (is_interface file_name)
in (match (uu____7592) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7601 -> begin
(

let uu____7603 = (

let uu____7607 = (lowercase_module_name file_name)
in (interface_of deps.file_system_map uu____7607))
in (match (uu____7603) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (iface) -> begin
(

let uu____7619 = (

let uu____7622 = (

let uu____7623 = (deps_try_find deps.dep_graph iface)
in (FStar_Option.get uu____7623))
in uu____7622.edges)
in FStar_Pervasives_Native.Some (uu____7619))
end))
end))
in (

let iface_deps1 = (FStar_Util.map_opt iface_deps (FStar_List.filter (fun iface_dep -> (

let uu____7640 = (FStar_Util.for_some (dep_subsumed_by iface_dep) dep_node.edges)
in (not (uu____7640))))))
in (

let norm_f = (norm_path file_name)
in (

let files = (FStar_List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) dep_node.edges)
in (

let files1 = (match (iface_deps1) with
| FStar_Pervasives_Native.None -> begin
files
end
| FStar_Pervasives_Native.Some (iface_deps2) -> begin
(

let iface_files = (FStar_List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) iface_deps2)
in (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) (FStar_List.append files iface_files)))
end)
in (

let files2 = (FStar_List.map norm_path files1)
in (

let files3 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files2)
in (

let files4 = (FStar_String.concat "\\\n\t" files3)
in (

let uu____7699 = (cache_file file_name)
in (match (uu____7699) with
| (cache_file_name1, b) -> begin
(

let set_of_unchecked_files1 = (match (b) with
| true -> begin
set_of_unchecked_files
end
| uu____7723 -> begin
(FStar_Util.set_add file_name set_of_unchecked_files)
end)
in ((FStar_Util.print3 "%s: %s \\\n\t%s\n\n" cache_file_name1 norm_f files4);
(

let already_there = (

let uu____7732 = (

let uu____7746 = (

let uu____7748 = (output_file ".krml" file_name)
in (norm_path uu____7748))
in (FStar_Util.smap_try_find transitive_krml uu____7746))
in (match (uu____7732) with
| FStar_Pervasives_Native.Some (uu____7765, already_there, uu____7767) -> begin
already_there
end
| FStar_Pervasives_Native.None -> begin
[]
end))
in ((

let uu____7802 = (

let uu____7804 = (output_file ".krml" file_name)
in (norm_path uu____7804))
in (

let uu____7807 = (

let uu____7819 = (

let uu____7821 = (output_file ".exe" file_name)
in (norm_path uu____7821))
in (

let uu____7824 = (

let uu____7828 = (

let uu____7832 = (

let uu____7836 = (deps_of deps file_name)
in (FStar_List.map (fun x -> (

let uu____7846 = (output_file ".krml" x)
in (norm_path uu____7846))) uu____7836))
in (FStar_List.append already_there uu____7832))
in (FStar_List.unique uu____7828))
in ((uu____7819), (uu____7824), (false))))
in (FStar_Util.smap_add transitive_krml uu____7802 uu____7807)));
(

let uu____7868 = (

let uu____7877 = (FStar_Options.cmi ())
in (match (uu____7877) with
| true -> begin
(topological_dependences_of deps.file_system_map deps.dep_graph deps.interfaces_with_inlining ((file_name)::[]) true)
end
| uu____7891 -> begin
(

let maybe_widen_deps = (fun f_deps -> (FStar_List.map (fun dep1 -> (file_of_dep_aux false deps.file_system_map deps.cmd_line_files dep1)) f_deps))
in (

let fst_files = (maybe_widen_deps dep_node.edges)
in (

let fst_files_from_iface = (match (iface_deps1) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (iface_deps2) -> begin
(maybe_widen_deps iface_deps2)
end)
in (

let uu____7925 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) (FStar_List.append fst_files fst_files_from_iface))
in ((uu____7925), (false))))))
end))
in (match (uu____7868) with
| (all_fst_files_dep, widened) -> begin
(

let all_checked_fst_dep_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.map (fun f -> (

let uu____7972 = (FStar_All.pipe_right f cache_file)
in (FStar_All.pipe_right uu____7972 FStar_Pervasives_Native.fst)))))
in ((

let uu____7996 = (is_implementation file_name)
in (match (uu____7996) with
| true -> begin
((

let uu____8000 = ((FStar_Options.cmi ()) && widened)
in (match (uu____8000) with
| true -> begin
((

let uu____8004 = (output_ml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____8004 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)));
(

let uu____8008 = (output_krml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____8008 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)));
)
end
| uu____8012 -> begin
((

let uu____8015 = (output_ml_file file_name)
in (FStar_Util.print2 "%s: %s \n\n" uu____8015 cache_file_name1));
(

let uu____8018 = (output_krml_file file_name)
in (FStar_Util.print2 "%s: %s\n\n" uu____8018 cache_file_name1));
)
end));
(

let cmx_files = (

let extracted_fst_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.filter (fun df -> ((

let uu____8043 = (lowercase_module_name df)
in (

let uu____8045 = (lowercase_module_name file_name)
in (Prims.op_disEquality uu____8043 uu____8045))) && (

let uu____8049 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____8049))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file)))
in (

let uu____8059 = (

let uu____8061 = (lowercase_module_name file_name)
in (FStar_Options.should_extract uu____8061))
in (match (uu____8059) with
| true -> begin
(

let uu____8064 = (output_cmx_file file_name)
in (

let uu____8066 = (output_ml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____8064 uu____8066 (FStar_String.concat "\\\n\t" cmx_files))))
end
| uu____8070 -> begin
()
end)));
)
end
| uu____8072 -> begin
(

let uu____8074 = ((

let uu____8078 = (

let uu____8080 = (lowercase_module_name file_name)
in (has_implementation deps.file_system_map uu____8080))
in (not (uu____8078))) && (is_interface file_name))
in (match (uu____8074) with
| true -> begin
(

let uu____8083 = ((FStar_Options.cmi ()) && widened)
in (match (uu____8083) with
| true -> begin
(

let uu____8086 = (output_krml_file file_name)
in (FStar_Util.print3 "%s: %s \\\n\t%s\n\n" uu____8086 cache_file_name1 (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)))
end
| uu____8090 -> begin
(

let uu____8092 = (output_krml_file file_name)
in (FStar_Util.print2 "%s: %s \n\n" uu____8092 cache_file_name1))
end))
end
| uu____8095 -> begin
()
end))
end));
set_of_unchecked_files1;
))
end));
));
))
end)))))))))))) uu____7543))
in (FStar_All.pipe_right keys uu____7532))
in (

let uu____8103 = (

let uu____8114 = (

let uu____8118 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____8118 (FStar_Util.sort_with FStar_String.compare)))
in (FStar_All.pipe_right uu____8114 (fun l -> (

let uu____8155 = (FStar_All.pipe_right l (FStar_List.filter (fun f -> (FStar_Util.set_mem f set_of_unchecked_files))))
in ((l), (uu____8155))))))
in (match (uu____8103) with
| (all_fst_files, all_unchecked_fst_files) -> begin
(

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____8213 = (FStar_Options.should_extract mname)
in (match (uu____8213) with
| true -> begin
(

let uu____8216 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____8216))
end
| uu____8219 -> begin
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

let uu____8243 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____8243))))));
(sort_output_files krml_file_map);
))
in (

let rec make_transitive = (fun f -> (

let uu____8262 = (

let uu____8274 = (FStar_Util.smap_try_find transitive_krml f)
in (FStar_Util.must uu____8274))
in (match (uu____8262) with
| (exe, deps1, seen) -> begin
(match (seen) with
| true -> begin
((exe), (deps1))
end
| uu____8344 -> begin
((FStar_Util.smap_add transitive_krml f ((exe), (deps1), (true)));
(

let deps2 = (

let uu____8368 = (

let uu____8372 = (FStar_List.map (fun dep1 -> (

let uu____8388 = (make_transitive dep1)
in (match (uu____8388) with
| (uu____8400, deps2) -> begin
(dep1)::deps2
end))) deps1)
in (FStar_List.flatten uu____8372))
in (FStar_List.unique uu____8368))
in ((FStar_Util.smap_add transitive_krml f ((exe), (deps2), (true)));
((exe), (deps2));
));
)
end)
end)))
in ((

let uu____8436 = (FStar_Util.smap_keys transitive_krml)
in (FStar_List.iter (fun f -> (

let uu____8461 = (make_transitive f)
in (match (uu____8461) with
| (exe, deps1) -> begin
(

let deps2 = (

let uu____8482 = (FStar_List.unique ((f)::deps1))
in (FStar_String.concat " " uu____8482))
in (

let wasm = (

let uu____8491 = (FStar_Util.substring exe (Prims.parse_int "0") ((FStar_String.length exe) - (Prims.parse_int "4")))
in (Prims.strcat uu____8491 ".wasm"))
in ((FStar_Util.print2 "%s: %s\n\n" exe deps2);
(FStar_Util.print2 "%s: %s\n\n" wasm deps2);
)))
end))) uu____8436));
(

let uu____8500 = (

let uu____8502 = (FStar_All.pipe_right all_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8502 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n" uu____8500));
(

let uu____8521 = (

let uu____8523 = (FStar_All.pipe_right all_unchecked_fst_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8523 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_UNCHECKED_FST_FILES=\\\n\t%s\n\n" uu____8521));
(

let uu____8542 = (

let uu____8544 = (FStar_All.pipe_right all_ml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8544 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n" uu____8542));
(

let uu____8562 = (

let uu____8564 = (FStar_All.pipe_right all_krml_files (FStar_List.map norm_path))
in (FStar_All.pipe_right uu____8564 (FStar_String.concat " \\\n\t")))
in (FStar_Util.print1 "ALL_KRML_FILES=\\\n\t%s\n" uu____8562));
))))
end)))))))))))))


let print : deps  ->  unit = (fun deps -> (

let uu____8588 = (FStar_Options.dep ())
in (match (uu____8588) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(print_full deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph deps.dep_graph)
end
| FStar_Pervasives_Native.Some ("raw") -> begin
(print_raw deps)
end
| FStar_Pervasives_Native.Some (uu____8600) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))


let print_fsmap : (Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap  ->  Prims.string = (fun fsmap -> (FStar_Util.smap_fold fsmap (fun k uu____8655 s -> (match (uu____8655) with
| (v0, v1) -> begin
(

let uu____8684 = (

let uu____8686 = (FStar_Util.format3 "%s -> (%s, %s)" k (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1))
in (Prims.strcat "; " uu____8686))
in (Prims.strcat s uu____8684))
end)) ""))


let module_has_interface : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let uu____8707 = (

let uu____8709 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8709))
in (has_interface deps.file_system_map uu____8707)))


let deps_has_implementation : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let m = (

let uu____8725 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8725))
in (FStar_All.pipe_right deps.all_files (FStar_Util.for_some (fun f -> ((is_implementation f) && (

let uu____8736 = (

let uu____8738 = (module_name_of_file f)
in (FStar_String.lowercase uu____8738))
in (Prims.op_Equality uu____8736 m))))))))





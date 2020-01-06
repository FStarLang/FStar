
open Prims
open FStar_Pervasives

let profile : 'Auu____16 . (unit  ->  'Auu____16)  ->  Prims.string  ->  'Auu____16 = (fun f c -> (FStar_Profiling.profile f FStar_Pervasives_Native.None c))

type verify_mode =
| VerifyAll
| VerifyUserList
| VerifyFigureItOut


let uu___is_VerifyAll : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyAll -> begin
true
end
| uu____44 -> begin
false
end))


let uu___is_VerifyUserList : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyUserList -> begin
true
end
| uu____55 -> begin
false
end))


let uu___is_VerifyFigureItOut : verify_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| VerifyFigureItOut -> begin
true
end
| uu____66 -> begin
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
| uu____89 -> begin
false
end))


let uu___is_Gray : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gray -> begin
true
end
| uu____100 -> begin
false
end))


let uu___is_Black : color  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Black -> begin
true
end
| uu____111 -> begin
false
end))

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____122 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____133 -> begin
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

let uu____181 = ((l > lext) && (

let uu____184 = (FStar_String.substring f (l - lext) lext)
in (Prims.op_Equality uu____184 ext)))
in (match (uu____181) with
| true -> begin
(

let uu____191 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____191))
end
| uu____195 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____198 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____198) with
| (FStar_Pervasives_Native.Some (m))::uu____212 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____224 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____241 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (Prims.op_Equality uu____241 105 (*i*))))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____255 = (is_interface f)
in (not (uu____255))))


let list_of_option : 'Auu____262 . 'Auu____262 FStar_Pervasives_Native.option  ->  'Auu____262 Prims.list = (fun uu___0_271 -> (match (uu___0_271) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair : 'Auu____280 . ('Auu____280 FStar_Pervasives_Native.option * 'Auu____280 FStar_Pervasives_Native.option)  ->  'Auu____280 Prims.list = (fun uu____295 -> (match (uu____295) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let module_name_of_file : Prims.string  ->  Prims.string = (fun f -> (

let uu____323 = (

let uu____327 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____327))
in (match (uu____323) with
| FStar_Pervasives_Native.Some (longname) -> begin
longname
end
| FStar_Pervasives_Native.None -> begin
(

let uu____334 = (

let uu____340 = (FStar_Util.format1 "not a valid FStar file: %s" f)
in ((FStar_Errors.Fatal_NotValidFStarFile), (uu____340)))
in (FStar_Errors.raise_err uu____334))
end)))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____354 = (module_name_of_file f)
in (FStar_String.lowercase uu____354)))


let namespace_of_module : Prims.string  ->  FStar_Ident.lident FStar_Pervasives_Native.option = (fun f -> (

let lid = (

let uu____367 = (FStar_Ident.path_of_text f)
in (FStar_Ident.lid_of_path uu____367 FStar_Range.dummyRange))
in (match (lid.FStar_Ident.ns) with
| [] -> begin
FStar_Pervasives_Native.None
end
| uu____370 -> begin
(

let uu____373 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_Pervasives_Native.Some (uu____373))
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
| uu____413 -> begin
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
| uu____436 -> begin
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
| uu____459 -> begin
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
| uu____482 -> begin
false
end))


let __proj__FriendImplementation__item___0 : dependence  ->  module_name = (fun projectee -> (match (projectee) with
| FriendImplementation (_0) -> begin
_0
end))


let dep_to_string : dependence  ->  Prims.string = (fun uu___1_500 -> (match (uu___1_500) with
| UseInterface (f) -> begin
(FStar_String.op_Hat "UseInterface " f)
end
| PreferInterface (f) -> begin
(FStar_String.op_Hat "PreferInterface " f)
end
| UseImplementation (f) -> begin
(FStar_String.op_Hat "UseImplementation " f)
end
| FriendImplementation (f) -> begin
(FStar_String.op_Hat "FriendImplementation " f)
end))


type dependences =
dependence Prims.list


let empty_dependences : 'Auu____519 . unit  ->  'Auu____519 Prims.list = (fun uu____522 -> [])

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

type parsing_data_elt =
| P_begin_module of FStar_Ident.lident
| P_open of (Prims.bool * FStar_Ident.lident)
| P_open_module_or_namespace of (open_kind * FStar_Ident.lid)
| P_dep of (Prims.bool * FStar_Ident.lident)
| P_alias of (FStar_Ident.ident * FStar_Ident.lident)
| P_lid of FStar_Ident.lident
| P_inline_for_extraction


let uu___is_P_begin_module : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_begin_module (_0) -> begin
true
end
| uu____635 -> begin
false
end))


let __proj__P_begin_module__item___0 : parsing_data_elt  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| P_begin_module (_0) -> begin
_0
end))


let uu___is_P_open : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_open (_0) -> begin
true
end
| uu____659 -> begin
false
end))


let __proj__P_open__item___0 : parsing_data_elt  ->  (Prims.bool * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| P_open (_0) -> begin
_0
end))


let uu___is_P_open_module_or_namespace : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_open_module_or_namespace (_0) -> begin
true
end
| uu____697 -> begin
false
end))


let __proj__P_open_module_or_namespace__item___0 : parsing_data_elt  ->  (open_kind * FStar_Ident.lid) = (fun projectee -> (match (projectee) with
| P_open_module_or_namespace (_0) -> begin
_0
end))


let uu___is_P_dep : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_dep (_0) -> begin
true
end
| uu____733 -> begin
false
end))


let __proj__P_dep__item___0 : parsing_data_elt  ->  (Prims.bool * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| P_dep (_0) -> begin
_0
end))


let uu___is_P_alias : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_alias (_0) -> begin
true
end
| uu____771 -> begin
false
end))


let __proj__P_alias__item___0 : parsing_data_elt  ->  (FStar_Ident.ident * FStar_Ident.lident) = (fun projectee -> (match (projectee) with
| P_alias (_0) -> begin
_0
end))


let uu___is_P_lid : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_lid (_0) -> begin
true
end
| uu____802 -> begin
false
end))


let __proj__P_lid__item___0 : parsing_data_elt  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| P_lid (_0) -> begin
_0
end))


let uu___is_P_inline_for_extraction : parsing_data_elt  ->  Prims.bool = (fun projectee -> (match (projectee) with
| P_inline_for_extraction -> begin
true
end
| uu____820 -> begin
false
end))

type parsing_data =
| Mk_pd of parsing_data_elt Prims.list


let uu___is_Mk_pd : parsing_data  ->  Prims.bool = (fun projectee -> true)


let __proj__Mk_pd__item___0 : parsing_data  ->  parsing_data_elt Prims.list = (fun projectee -> (match (projectee) with
| Mk_pd (_0) -> begin
_0
end))


let str_of_parsing_data_elt : parsing_data_elt  ->  Prims.string = (fun elt -> (

let str_of_open_kind = (fun uu___2_863 -> (match (uu___2_863) with
| Open_module -> begin
"P_open_module"
end
| Open_namespace -> begin
"P_open_namespace"
end))
in (match (elt) with
| P_begin_module (lid) -> begin
(

let uu____869 = (

let uu____871 = (FStar_Ident.text_of_lid lid)
in (FStar_String.op_Hat uu____871 ")"))
in (FStar_String.op_Hat "P_begin_module (" uu____869))
end
| P_open (b, lid) -> begin
(

let uu____879 = (

let uu____881 = (FStar_Util.string_of_bool b)
in (

let uu____883 = (

let uu____885 = (

let uu____887 = (FStar_Ident.text_of_lid lid)
in (FStar_String.op_Hat uu____887 ")"))
in (FStar_String.op_Hat ", " uu____885))
in (FStar_String.op_Hat uu____881 uu____883)))
in (FStar_String.op_Hat "P_open (" uu____879))
end
| P_open_module_or_namespace (k, lid) -> begin
(

let uu____894 = (

let uu____896 = (

let uu____898 = (

let uu____900 = (FStar_Ident.text_of_lid lid)
in (FStar_String.op_Hat uu____900 ")"))
in (FStar_String.op_Hat ", " uu____898))
in (FStar_String.op_Hat (str_of_open_kind k) uu____896))
in (FStar_String.op_Hat "P_open_module_or_namespace (" uu____894))
end
| P_dep (b, lid) -> begin
(

let uu____909 = (

let uu____911 = (FStar_Ident.text_of_lid lid)
in (

let uu____913 = (

let uu____915 = (

let uu____917 = (FStar_Util.string_of_bool b)
in (FStar_String.op_Hat uu____917 ")"))
in (FStar_String.op_Hat ", " uu____915))
in (FStar_String.op_Hat uu____911 uu____913)))
in (FStar_String.op_Hat "P_dep (" uu____909))
end
| P_alias (id1, lid) -> begin
(

let uu____924 = (

let uu____926 = (FStar_Ident.text_of_id id1)
in (

let uu____928 = (

let uu____930 = (

let uu____932 = (FStar_Ident.text_of_lid lid)
in (FStar_String.op_Hat uu____932 ")"))
in (FStar_String.op_Hat ", " uu____930))
in (FStar_String.op_Hat uu____926 uu____928)))
in (FStar_String.op_Hat "P_alias (" uu____924))
end
| P_lid (lid) -> begin
(

let uu____938 = (

let uu____940 = (FStar_Ident.text_of_lid lid)
in (FStar_String.op_Hat uu____940 ")"))
in (FStar_String.op_Hat "P_lid (" uu____938))
end
| P_inline_for_extraction -> begin
"P_inline_for_extraction"
end)))


let str_of_parsing_data : parsing_data  ->  Prims.string = (fun uu___3_951 -> (match (uu___3_951) with
| Mk_pd (l) -> begin
(FStar_All.pipe_right l (FStar_List.fold_left (fun s elt -> (

let uu____966 = (

let uu____968 = (FStar_All.pipe_right elt str_of_parsing_data_elt)
in (FStar_String.op_Hat "; " uu____968))
in (FStar_String.op_Hat s uu____966))) ""))
end))


let parsing_data_elt_eq : parsing_data_elt  ->  parsing_data_elt  ->  Prims.bool = (fun e1 e2 -> (match (((e1), (e2))) with
| (P_begin_module (l1), P_begin_module (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (P_open (b1, l1), P_open (b2, l2)) -> begin
((Prims.op_Equality b1 b2) && (FStar_Ident.lid_equals l1 l2))
end
| (P_open_module_or_namespace (k1, l1), P_open_module_or_namespace (k2, l2)) -> begin
((Prims.op_Equality k1 k2) && (FStar_Ident.lid_equals l1 l2))
end
| (P_dep (b1, l1), P_dep (b2, l2)) -> begin
((Prims.op_Equality b1 b2) && (FStar_Ident.lid_equals l1 l2))
end
| (P_alias (i1, l1), P_alias (i2, l2)) -> begin
((

let uu____1018 = (FStar_Ident.text_of_id i1)
in (

let uu____1020 = (FStar_Ident.text_of_id i2)
in (Prims.op_Equality uu____1018 uu____1020))) && (FStar_Ident.lid_equals l1 l2))
end
| (P_lid (l1), P_lid (l2)) -> begin
(FStar_Ident.lid_equals l1 l2)
end
| (P_inline_for_extraction, P_inline_for_extraction) -> begin
true
end
| (uu____1026, uu____1027) -> begin
false
end))


let empty_parsing_data : parsing_data = Mk_pd ([])

type deps =
{dep_graph : dependence_graph; file_system_map : files_for_module_name; cmd_line_files : file_name Prims.list; all_files : file_name Prims.list; interfaces_with_inlining : module_name Prims.list; parse_results : parsing_data FStar_Util.smap}


let __proj__Mkdeps__item__dep_graph : deps  ->  dependence_graph = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
dep_graph
end))


let __proj__Mkdeps__item__file_system_map : deps  ->  files_for_module_name = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
file_system_map
end))


let __proj__Mkdeps__item__cmd_line_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
cmd_line_files
end))


let __proj__Mkdeps__item__all_files : deps  ->  file_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
all_files
end))


let __proj__Mkdeps__item__interfaces_with_inlining : deps  ->  module_name Prims.list = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
interfaces_with_inlining
end))


let __proj__Mkdeps__item__parse_results : deps  ->  parsing_data FStar_Util.smap = (fun projectee -> (match (projectee) with
| {dep_graph = dep_graph; file_system_map = file_system_map; cmd_line_files = cmd_line_files; all_files = all_files; interfaces_with_inlining = interfaces_with_inlining; parse_results = parse_results} -> begin
parse_results
end))


let deps_try_find : dependence_graph  ->  Prims.string  ->  dep_node FStar_Pervasives_Native.option = (fun uu____1243 k -> (match (uu____1243) with
| Deps (m) -> begin
(FStar_Util.smap_try_find m k)
end))


let deps_add_dep : dependence_graph  ->  Prims.string  ->  dep_node  ->  unit = (fun uu____1265 k v1 -> (match (uu____1265) with
| Deps (m) -> begin
(FStar_Util.smap_add m k v1)
end))


let deps_keys : dependence_graph  ->  Prims.string Prims.list = (fun uu____1280 -> (match (uu____1280) with
| Deps (m) -> begin
(FStar_Util.smap_keys m)
end))


let deps_empty : unit  ->  dependence_graph = (fun uu____1292 -> (

let uu____1293 = (FStar_Util.smap_create (Prims.parse_int "41"))
in Deps (uu____1293)))


let mk_deps : dependence_graph  ->  files_for_module_name  ->  file_name Prims.list  ->  file_name Prims.list  ->  module_name Prims.list  ->  parsing_data FStar_Util.smap  ->  deps = (fun dg fs c a i pr -> {dep_graph = dg; file_system_map = fs; cmd_line_files = c; all_files = a; interfaces_with_inlining = i; parse_results = pr})


let empty_deps : deps = (

let uu____1351 = (deps_empty ())
in (

let uu____1352 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (

let uu____1364 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (mk_deps uu____1351 uu____1352 [] [] [] uu____1364))))


let module_name_of_dep : dependence  ->  module_name = (fun uu___4_1377 -> (match (uu___4_1377) with
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

let uu____1406 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1406) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (fn), uu____1433) -> begin
(

let uu____1455 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____1455))
end
| FStar_Pervasives_Native.Some (uu____1458, FStar_Pervasives_Native.Some (fn)) -> begin
(

let uu____1481 = (lowercase_module_name fn)
in FStar_Pervasives_Native.Some (uu____1481))
end
| uu____1484 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of_internal : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____1517 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1517) with
| FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some (iface), uu____1544) -> begin
FStar_Pervasives_Native.Some (iface)
end
| uu____1567 -> begin
FStar_Pervasives_Native.None
end)))


let implementation_of_internal : files_for_module_name  ->  module_name  ->  file_name FStar_Pervasives_Native.option = (fun file_system_map key -> (

let uu____1600 = (FStar_Util.smap_try_find file_system_map key)
in (match (uu____1600) with
| FStar_Pervasives_Native.Some (uu____1626, FStar_Pervasives_Native.Some (impl)) -> begin
FStar_Pervasives_Native.Some (impl)
end
| uu____1650 -> begin
FStar_Pervasives_Native.None
end)))


let interface_of : deps  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun deps key -> (interface_of_internal deps.file_system_map key))


let implementation_of : deps  ->  Prims.string  ->  Prims.string FStar_Pervasives_Native.option = (fun deps key -> (implementation_of_internal deps.file_system_map key))


let has_interface : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1711 = (interface_of_internal file_system_map key)
in (FStar_Option.isSome uu____1711)))


let has_implementation : files_for_module_name  ->  module_name  ->  Prims.bool = (fun file_system_map key -> (

let uu____1731 = (implementation_of_internal file_system_map key)
in (FStar_Option.isSome uu____1731)))


let cache_file_name : Prims.string  ->  Prims.string = (

let checked_file_and_exists_flag = (fun fn -> (

let lax1 = (FStar_Options.lax ())
in (

let cache_fn = (match (lax1) with
| true -> begin
(FStar_String.op_Hat fn ".checked.lax")
end
| uu____1759 -> begin
(FStar_String.op_Hat fn ".checked")
end)
in (

let mname = (FStar_All.pipe_right fn module_name_of_file)
in (

let uu____1766 = (

let uu____1770 = (FStar_All.pipe_right cache_fn FStar_Util.basename)
in (FStar_Options.find_file uu____1770))
in (match (uu____1766) with
| FStar_Pervasives_Native.Some (path) -> begin
(

let expected_cache_file = (FStar_Options.prepend_cache_dir cache_fn)
in ((

let uu____1781 = (((

let uu____1785 = (FStar_Options.dep ())
in (FStar_Option.isSome uu____1785)) && (

let uu____1791 = (FStar_Options.should_be_already_cached mname)
in (not (uu____1791)))) && ((not ((FStar_Util.file_exists expected_cache_file))) || (

let uu____1794 = (FStar_Util.paths_to_same_file path expected_cache_file)
in (not (uu____1794)))))
in (match (uu____1781) with
| true -> begin
(

let uu____1797 = (

let uu____1803 = (

let uu____1805 = (FStar_Options.prepend_cache_dir cache_fn)
in (FStar_Util.format3 "Did not expected %s to be already checked, but found it in an unexpected location %s instead of %s" mname path uu____1805))
in ((FStar_Errors.Warning_UnexpectedCheckedFile), (uu____1803)))
in (FStar_Errors.log_issue FStar_Range.dummyRange uu____1797))
end
| uu____1809 -> begin
()
end));
path;
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1812 = (FStar_All.pipe_right mname FStar_Options.should_be_already_cached)
in (match (uu____1812) with
| true -> begin
(

let uu____1818 = (

let uu____1824 = (FStar_Util.format1 "Expected %s to be already checked but could not find it" mname)
in ((FStar_Errors.Error_AlreadyCachedAssertionFailure), (uu____1824)))
in (FStar_Errors.raise_err uu____1818))
end
| uu____1829 -> begin
(FStar_Options.prepend_cache_dir cache_fn)
end))
end))))))
in (

let memo = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let memo1 = (fun f x -> (

let uu____1860 = (FStar_Util.smap_try_find memo x)
in (match (uu____1860) with
| FStar_Pervasives_Native.Some (res) -> begin
res
end
| FStar_Pervasives_Native.None -> begin
(

let res = (f x)
in ((FStar_Util.smap_add memo x res);
res;
))
end)))
in (memo1 checked_file_and_exists_flag))))


let parsing_data_of : deps  ->  Prims.string  ->  parsing_data = (fun deps fn -> (

let uu____1887 = (FStar_Util.smap_try_find deps.parse_results fn)
in (FStar_All.pipe_right uu____1887 FStar_Util.must)))


let file_of_dep_aux : Prims.bool  ->  files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (fun use_checked_file file_system_map all_cmd_line_files d -> (

let cmd_line_has_impl = (fun key -> (FStar_All.pipe_right all_cmd_line_files (FStar_Util.for_some (fun fn -> ((is_implementation fn) && (

let uu____1941 = (lowercase_module_name fn)
in (Prims.op_Equality key uu____1941)))))))
in (

let maybe_use_cache_of = (fun f -> (match (use_checked_file) with
| true -> begin
(cache_file_name f)
end
| uu____1955 -> begin
f
end))
in (match (d) with
| UseInterface (key) -> begin
(

let uu____1960 = (interface_of_internal file_system_map key)
in (match (uu____1960) with
| FStar_Pervasives_Native.None -> begin
(

let uu____1967 = (

let uu____1973 = (FStar_Util.format1 "Expected an interface for module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingInterface), (uu____1973)))
in (FStar_Errors.raise_err uu____1967))
end
| FStar_Pervasives_Native.Some (f) -> begin
f
end))
end
| PreferInterface (key) when (has_interface file_system_map key) -> begin
(

let uu____1983 = ((cmd_line_has_impl key) && (

let uu____1986 = (FStar_Options.dep ())
in (FStar_Option.isNone uu____1986)))
in (match (uu____1983) with
| true -> begin
(

let uu____1993 = (FStar_Options.expose_interfaces ())
in (match (uu____1993) with
| true -> begin
(

let uu____1997 = (

let uu____1999 = (implementation_of_internal file_system_map key)
in (FStar_Option.get uu____1999))
in (maybe_use_cache_of uu____1997))
end
| uu____2004 -> begin
(

let uu____2006 = (

let uu____2012 = (

let uu____2014 = (

let uu____2016 = (implementation_of_internal file_system_map key)
in (FStar_Option.get uu____2016))
in (

let uu____2021 = (

let uu____2023 = (interface_of_internal file_system_map key)
in (FStar_Option.get uu____2023))
in (FStar_Util.format3 "You may have a cyclic dependence on module %s: use --dep full to confirm. Alternatively, invoking fstar with %s on the command line breaks the abstraction imposed by its interface %s; if you really want this behavior add the option \'--expose_interfaces\'" key uu____2014 uu____2021)))
in ((FStar_Errors.Fatal_MissingExposeInterfacesOption), (uu____2012)))
in (FStar_Errors.raise_err uu____2006))
end))
end
| uu____2031 -> begin
(

let uu____2033 = (

let uu____2035 = (interface_of_internal file_system_map key)
in (FStar_Option.get uu____2035))
in (maybe_use_cache_of uu____2033))
end))
end
| PreferInterface (key) -> begin
(

let uu____2042 = (implementation_of_internal file_system_map key)
in (match (uu____2042) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2048 = (

let uu____2054 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2054)))
in (FStar_Errors.raise_err uu____2048))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| UseImplementation (key) -> begin
(

let uu____2064 = (implementation_of_internal file_system_map key)
in (match (uu____2064) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2070 = (

let uu____2076 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2076)))
in (FStar_Errors.raise_err uu____2070))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end
| FriendImplementation (key) -> begin
(

let uu____2086 = (implementation_of_internal file_system_map key)
in (match (uu____2086) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2092 = (

let uu____2098 = (FStar_Util.format1 "Expected an implementation of module %s, but couldn\'t find one" key)
in ((FStar_Errors.Fatal_MissingImplementation), (uu____2098)))
in (FStar_Errors.raise_err uu____2092))
end
| FStar_Pervasives_Native.Some (f) -> begin
(maybe_use_cache_of f)
end))
end))))


let file_of_dep : files_for_module_name  ->  file_name Prims.list  ->  dependence  ->  file_name = (file_of_dep_aux false)


let dependences_of : files_for_module_name  ->  dependence_graph  ->  file_name Prims.list  ->  file_name  ->  file_name Prims.list = (fun file_system_map deps all_cmd_line_files fn -> (

let uu____2159 = (deps_try_find deps fn)
in (match (uu____2159) with
| FStar_Pervasives_Native.None -> begin
(empty_dependences ())
end
| FStar_Pervasives_Native.Some ({edges = deps1; color = uu____2167}) -> begin
(FStar_List.map (file_of_dep file_system_map all_cmd_line_files) deps1)
end)))


let print_graph : dependence_graph  ->  unit = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____2181 = (

let uu____2183 = (

let uu____2185 = (

let uu____2187 = (

let uu____2191 = (

let uu____2195 = (deps_keys graph)
in (FStar_List.unique uu____2195))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____2209 = (

let uu____2210 = (deps_try_find graph k)
in (FStar_Util.must uu____2210))
in uu____2209.edges)
in (

let r = (fun s -> (FStar_Util.replace_char s 46 (*.*) 95 (*_*)))
in (

let print7 = (fun dep1 -> (

let uu____2231 = (

let uu____2233 = (lowercase_module_name k)
in (r uu____2233))
in (FStar_Util.format2 "  \"%s\" -> \"%s\"" uu____2231 (r (module_name_of_dep dep1)))))
in (FStar_List.map print7 deps))))) uu____2191))
in (FStar_String.concat "\n" uu____2187))
in (FStar_String.op_Hat uu____2185 "\n}\n"))
in (FStar_String.op_Hat "digraph {\n" uu____2183))
in (FStar_Util.write_file "dep.graph" uu____2181));
))


let build_inclusion_candidates_list : unit  ->  (Prims.string * Prims.string) Prims.list = (fun uu____2254 -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____2280 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____2280))
in (FStar_List.concatMap (fun d -> (match ((FStar_Util.is_directory d)) with
| true -> begin
(

let files = (FStar_Util.readdir d)
in (FStar_List.filter_map (fun f -> (

let f1 = (FStar_Util.basename f)
in (

let uu____2320 = (check_and_strip_suffix f1)
in (FStar_All.pipe_right uu____2320 (FStar_Util.map_option (fun longname -> (

let full_path = (match ((Prims.op_Equality d cwd)) with
| true -> begin
f1
end
| uu____2351 -> begin
(FStar_Util.join_paths d f1)
end)
in ((longname), (full_path))))))))) files))
end
| uu____2355 -> begin
(

let uu____2357 = (

let uu____2363 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in ((FStar_Errors.Fatal_NotValidIncludeDirectory), (uu____2363)))
in (FStar_Errors.raise_err uu____2357))
end)) include_directories2))))))


let build_map : Prims.string Prims.list  ->  files_for_module_name = (fun filenames -> (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____2426 = (FStar_Util.smap_try_find map1 key)
in (match (uu____2426) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____2473 = (is_interface full_path)
in (match (uu____2473) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____2493 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2522 = (is_interface full_path)
in (match (uu____2522) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____2543 -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.Some (full_path))))
end))
end)))
in ((

let uu____2564 = (build_inclusion_candidates_list ())
in (FStar_List.iter (fun uu____2582 -> (match (uu____2582) with
| (longname, full_path) -> begin
(add_entry (FStar_String.lowercase longname) full_path)
end)) uu____2564));
(FStar_List.iter (fun f -> (

let uu____2601 = (lowercase_module_name f)
in (add_entry uu____2601 f))) filenames);
map1;
))))


let enter_namespace : files_for_module_name  ->  files_for_module_name  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (FStar_String.op_Hat prefix1 ".")
in ((FStar_Util.smap_iter original_map (fun k uu____2649 -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____2675 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____2675))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.op_Colon_Equals found true);
)))
end
| uu____2741 -> begin
()
end)));
(FStar_ST.op_Bang found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____2788 -> begin
[]
end)
in (

let names = (

let uu____2795 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____2795 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____2818 = (string_of_lid l last1)
in (FStar_String.lowercase uu____2818)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____2827 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____2827)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____2849 = (

let uu____2851 = (

let uu____2853 = (

let uu____2855 = (

let uu____2859 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____2859))
in (FStar_Util.must uu____2855))
in (FStar_String.lowercase uu____2853))
in (Prims.op_disEquality uu____2851 k'))
in (match (uu____2849) with
| true -> begin
(

let uu____2864 = (FStar_Ident.range_of_lid lid)
in (

let uu____2865 = (

let uu____2871 = (

let uu____2873 = (string_of_lid lid true)
in (FStar_Util.format2 "The module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect and the module will not be verified.\n" uu____2873 filename))
in ((FStar_Errors.Error_ModuleFileNameMismatch), (uu____2871)))
in (FStar_Errors.log_issue uu____2864 uu____2865)))
end
| uu____2878 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____2889 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun full_filename -> (

let filename = (FStar_Util.basename full_filename)
in (

let corelibs = (

let uu____2911 = (FStar_Options.prims_basename ())
in (

let uu____2913 = (

let uu____2917 = (FStar_Options.pervasives_basename ())
in (

let uu____2919 = (

let uu____2923 = (FStar_Options.pervasives_native_basename ())
in (uu____2923)::[])
in (uu____2917)::uu____2919))
in (uu____2911)::uu____2913))
in (match ((FStar_List.mem filename corelibs)) with
| true -> begin
[]
end
| uu____2941 -> begin
(

let implicit_deps = (((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
in (

let uu____2966 = (

let uu____2969 = (lowercase_module_name full_filename)
in (namespace_of_module uu____2969))
in (match (uu____2966) with
| FStar_Pervasives_Native.None -> begin
implicit_deps
end
| FStar_Pervasives_Native.Some (ns) -> begin
(FStar_List.append implicit_deps ((((ns), (Open_namespace)))::[]))
end)))
end))))


let dep_subsumed_by : dependence  ->  dependence  ->  Prims.bool = (fun d d' -> (match (((d), (d'))) with
| (PreferInterface (l'), FriendImplementation (l)) -> begin
(Prims.op_Equality l l')
end
| uu____3008 -> begin
(Prims.op_Equality d d')
end))


let collect_one : files_for_module_name  ->  Prims.string  ->  (Prims.string  ->  parsing_data FStar_Pervasives_Native.option)  ->  (parsing_data * dependence Prims.list * Prims.bool * dependence Prims.list) = (fun original_map filename get_parsing_data_from_cache -> (

let from_parsing_data = (fun pd original_map1 filename1 -> (

let deps = (FStar_Util.mk_ref [])
in (

let has_inline_for_extraction = (FStar_Util.mk_ref false)
in (

let mo_roots = (

let mname = (lowercase_module_name filename1)
in (

let uu____3126 = ((is_interface filename1) && (has_implementation original_map1 mname))
in (match (uu____3126) with
| true -> begin
(UseImplementation (mname))::[]
end
| uu____3131 -> begin
[]
end)))
in (

let auto_open = (

let uu____3136 = (hard_coded_dependencies filename1)
in (FStar_All.pipe_right uu____3136 (FStar_List.map (fun uu____3158 -> (match (uu____3158) with
| (lid, k) -> begin
P_open_module_or_namespace (((k), (lid)))
end)))))
in (

let working_map = (FStar_Util.smap_copy original_map1)
in (

let set_interface_inlining = (fun uu____3193 -> (

let uu____3194 = (is_interface filename1)
in (match (uu____3194) with
| true -> begin
(FStar_ST.op_Colon_Equals has_inline_for_extraction true)
end
| uu____3219 -> begin
()
end)))
in (

let add_dep = (fun deps1 d -> (

let uu____3316 = (

let uu____3318 = (

let uu____3320 = (FStar_ST.op_Bang deps1)
in (FStar_List.existsML (dep_subsumed_by d) uu____3320))
in (not (uu____3318)))
in (match (uu____3316) with
| true -> begin
(

let uu____3347 = (

let uu____3350 = (FStar_ST.op_Bang deps1)
in (d)::uu____3350)
in (FStar_ST.op_Colon_Equals deps1 uu____3347))
end
| uu____3399 -> begin
()
end)))
in (

let dep_edge = (fun module_name is_friend -> (match (is_friend) with
| true -> begin
FriendImplementation (module_name)
end
| uu____3417 -> begin
PreferInterface (module_name)
end))
in (

let add_dependence_edge = (fun original_or_working_map lid is_friend -> (

let key = (lowercase_join_longident lid true)
in (

let uu____3441 = (resolve_module_name original_or_working_map key)
in (match (uu____3441) with
| FStar_Pervasives_Native.Some (module_name) -> begin
((add_dep deps (dep_edge module_name is_friend));
true;
)
end
| uu____3451 -> begin
false
end))))
in (

let record_open_module = (fun let_open lid -> (

let uu____3470 = ((let_open && (add_dependence_edge working_map lid false)) || ((not (let_open)) && (add_dependence_edge original_map1 lid false)))
in (match (uu____3470) with
| true -> begin
true
end
| uu____3477 -> begin
((match (let_open) with
| true -> begin
(

let uu____3481 = (FStar_Ident.range_of_lid lid)
in (

let uu____3482 = (

let uu____3488 = (

let uu____3490 = (string_of_lid lid true)
in (FStar_Util.format1 "Module not found: %s" uu____3490))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3488)))
in (FStar_Errors.log_issue uu____3481 uu____3482)))
end
| uu____3495 -> begin
()
end);
false;
)
end)))
in (

let record_open_namespace = (fun lid -> (

let key = (lowercase_join_longident lid true)
in (

let r = (enter_namespace original_map1 working_map key)
in (match ((not (r))) with
| true -> begin
(

let uu____3510 = (FStar_Ident.range_of_lid lid)
in (

let uu____3511 = (

let uu____3517 = (

let uu____3519 = (string_of_lid lid true)
in (FStar_Util.format1 "No modules in namespace %s and no file with that name either" uu____3519))
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3517)))
in (FStar_Errors.log_issue uu____3510 uu____3511)))
end
| uu____3524 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____3539 = (record_open_module let_open lid)
in (match (uu____3539) with
| true -> begin
()
end
| uu____3542 -> begin
(match ((not (let_open))) with
| true -> begin
(record_open_namespace lid)
end
| uu____3545 -> begin
()
end)
end)))
in (

let record_open_module_or_namespace = (fun uu____3556 -> (match (uu____3556) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace lid)
end
| Open_module -> begin
(

let uu____3563 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (

let uu____3580 = (FStar_Ident.text_of_id ident)
in (FStar_String.lowercase uu____3580))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____3585 = (FStar_Util.smap_try_find original_map1 alias)
in (match (uu____3585) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
((FStar_Util.smap_add working_map key deps_of_aliased_module);
(

let uu____3642 = (

let uu____3643 = (lowercase_join_longident lid true)
in (dep_edge uu____3643 false))
in (add_dep deps uu____3642));
true;
)
end
| FStar_Pervasives_Native.None -> begin
((

let uu____3659 = (FStar_Ident.range_of_lid lid)
in (

let uu____3660 = (

let uu____3666 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in ((FStar_Errors.Warning_ModuleOrFileNotFoundWarning), (uu____3666)))
in (FStar_Errors.log_issue uu____3659 uu____3660)));
false;
)
end)))))
in (

let add_dep_on_module = (fun module_name is_friend -> (

let uu____3684 = (add_dependence_edge working_map module_name is_friend)
in (match (uu____3684) with
| true -> begin
()
end
| uu____3687 -> begin
(

let uu____3689 = (FStar_Options.debug_any ())
in (match (uu____3689) with
| true -> begin
(

let uu____3692 = (FStar_Ident.range_of_lid module_name)
in (

let uu____3693 = (

let uu____3699 = (

let uu____3701 = (FStar_Ident.string_of_lid module_name)
in (FStar_Util.format1 "Unbound module reference %s" uu____3701))
in ((FStar_Errors.Warning_UnboundModuleReference), (uu____3699)))
in (FStar_Errors.log_issue uu____3692 uu____3693)))
end
| uu____3705 -> begin
()
end))
end)))
in (

let record_lid = (fun lid -> (match (lid.FStar_Ident.ns) with
| [] -> begin
()
end
| uu____3713 -> begin
(

let module_name = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in (add_dep_on_module module_name false))
end))
in (

let begin_module = (fun lid -> (match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____3726 = (

let uu____3728 = (namespace_of_lid lid)
in (enter_namespace original_map1 working_map uu____3728))
in ())
end
| uu____3730 -> begin
()
end))
in ((match (pd) with
| Mk_pd (l) -> begin
(FStar_All.pipe_right (FStar_List.append auto_open l) (FStar_List.iter (fun elt -> (match (elt) with
| P_begin_module (lid) -> begin
(begin_module lid)
end
| P_open (b, lid) -> begin
(record_open b lid)
end
| P_open_module_or_namespace (k, lid) -> begin
(record_open_module_or_namespace ((lid), (k)))
end
| P_dep (b, lid) -> begin
(add_dep_on_module lid b)
end
| P_alias (id1, lid) -> begin
(

let uu____3754 = (record_module_alias id1 lid)
in ())
end
| P_lid (lid) -> begin
(record_lid lid)
end
| P_inline_for_extraction -> begin
(set_interface_inlining ())
end))))
end);
(

let uu____3757 = (FStar_ST.op_Bang deps)
in (

let uu____3783 = (FStar_ST.op_Bang has_inline_for_extraction)
in ((uu____3757), (uu____3783), (mo_roots))));
)))))))))))))))))))
in (

let data_from_cache = (FStar_All.pipe_right filename get_parsing_data_from_cache)
in (

let uu____3817 = (FStar_All.pipe_right data_from_cache FStar_Util.is_some)
in (match (uu____3817) with
| true -> begin
((

let uu____3837 = (FStar_Options.debug_any ())
in (match (uu____3837) with
| true -> begin
(FStar_Util.print1 "Reading the parsing data for %s from its checked file\n" filename)
end
| uu____3841 -> begin
()
end));
(

let uu____3843 = (

let uu____3855 = (FStar_All.pipe_right data_from_cache FStar_Util.must)
in (from_parsing_data uu____3855 original_map filename))
in (match (uu____3843) with
| (deps, has_inline_for_extraction, mo_roots) -> begin
(

let uu____3884 = (FStar_All.pipe_right data_from_cache FStar_Util.must)
in ((uu____3884), (deps), (has_inline_for_extraction), (mo_roots)))
end));
)
end
| uu____3892 -> begin
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let pd = (FStar_Util.mk_ref [])
in (

let add_to_parsing_data = (fun elt -> (

let uu____3913 = (

let uu____3915 = (

let uu____3917 = (FStar_ST.op_Bang pd)
in (FStar_List.existsML (fun e -> (parsing_data_elt_eq e elt)) uu____3917))
in (not (uu____3915)))
in (match (uu____3913) with
| true -> begin
(

let uu____3946 = (

let uu____3949 = (FStar_ST.op_Bang pd)
in (elt)::uu____3949)
in (FStar_ST.op_Colon_Equals pd uu____3946))
end
| uu____3998 -> begin
()
end)))
in (

let rec collect_module = (fun uu___5_4106 -> (match (uu___5_4106) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(add_to_parsing_data (P_begin_module (lid)));
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____4117) -> begin
((check_module_declaration_against_filename lid filename);
(add_to_parsing_data (P_begin_module (lid)));
(collect_decls decls);
)
end))
and collect_decls = (fun decls -> (FStar_List.iter (fun x -> ((collect_decl x.FStar_Parser_AST.d);
(FStar_List.iter collect_term x.FStar_Parser_AST.attrs);
(match (x.FStar_Parser_AST.d) with
| FStar_Parser_AST.Val (uu____4136) when (FStar_List.contains FStar_Parser_AST.Inline_for_extraction x.FStar_Parser_AST.quals) -> begin
(add_to_parsing_data P_inline_for_extraction)
end
| uu____4141 -> begin
()
end);
)) decls))
and collect_decl = (fun d -> (match (d) with
| FStar_Parser_AST.Include (lid) -> begin
(add_to_parsing_data (P_open (((false), (lid)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(add_to_parsing_data (P_open (((false), (lid)))))
end
| FStar_Parser_AST.Friend (lid) -> begin
(

let uu____4150 = (

let uu____4151 = (

let uu____4157 = (

let uu____4158 = (lowercase_join_longident lid true)
in (FStar_All.pipe_right uu____4158 FStar_Ident.lid_of_str))
in ((true), (uu____4157)))
in P_dep (uu____4151))
in (add_to_parsing_data uu____4150))
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
(add_to_parsing_data (P_alias (((ident), (lid)))))
end
| FStar_Parser_AST.TopLevelLet (uu____4166, patterms) -> begin
(FStar_List.iter (fun uu____4188 -> (match (uu____4188) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Splice (uu____4197, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____4203, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____4205; FStar_Parser_AST.mdest = uu____4206; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____4208; FStar_Parser_AST.mdest = uu____4209; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____4211, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____4213; FStar_Parser_AST.mdest = uu____4214; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____4218, tc, ts) -> begin
((match (tc) with
| true -> begin
(add_to_parsing_data (P_lid (FStar_Parser_Const.mk_class_lid)))
end
| uu____4243 -> begin
()
end);
(

let ts1 = (FStar_List.map (fun uu____4257 -> (match (uu____4257) with
| (x, docnik) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1));
)
end
| FStar_Parser_AST.Exception (uu____4270, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.LayeredEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____4278) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____4279) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____4282 = (

let uu____4284 = (FStar_ST.op_Bang num_of_toplevelmods)
in (uu____4284 > (Prims.parse_int "1")))
in (match (uu____4282) with
| true -> begin
(

let uu____4309 = (

let uu____4315 = (

let uu____4317 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____4317))
in ((FStar_Errors.Fatal_OneModulePerFile), (uu____4315)))
in (

let uu____4322 = (FStar_Ident.range_of_lid lid)
in (FStar_Errors.raise_error uu____4309 uu____4322)))
end
| uu____4323 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___6_4325 -> (match (uu___6_4325) with
| FStar_Parser_AST.TyconAbstract (uu____4326, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____4338, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____4352, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____4398 -> (match (uu____4398) with
| (uu____4407, t, uu____4409) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____4414, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____4476 -> (match (uu____4476) with
| (uu____4490, t, uu____4492, uu____4493) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___7_4504 -> (match (uu___7_4504) with
| FStar_Parser_AST.DefineEffect (uu____4505, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____4519, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun b -> ((collect_aqual b.FStar_Parser_AST.aqual);
(match (b) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____4532, t); FStar_Parser_AST.brange = uu____4534; FStar_Parser_AST.blevel = uu____4535; FStar_Parser_AST.aqual = uu____4536} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____4539, t); FStar_Parser_AST.brange = uu____4541; FStar_Parser_AST.blevel = uu____4542; FStar_Parser_AST.aqual = uu____4543} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____4547; FStar_Parser_AST.blevel = uu____4548; FStar_Parser_AST.aqual = uu____4549} -> begin
(collect_term t)
end
| uu____4552 -> begin
()
end);
))
and collect_aqual = (fun uu___8_4553 -> (match (uu___8_4553) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (t)) -> begin
(collect_term t)
end
| uu____4557 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___9_4561 -> (match (uu___9_4561) with
| FStar_Const.Const_int (uu____4562, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____4589 = (

let uu____4590 = (

let uu____4596 = (

let uu____4597 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (FStar_All.pipe_right uu____4597 FStar_Ident.lid_of_str))
in ((false), (uu____4596)))
in P_dep (uu____4590))
in (add_to_parsing_data uu____4589))))
end
| FStar_Const.Const_char (uu____4603) -> begin
(

let uu____4605 = (

let uu____4606 = (

let uu____4612 = (FStar_All.pipe_right "fstar.char" FStar_Ident.lid_of_str)
in ((false), (uu____4612)))
in P_dep (uu____4606))
in (add_to_parsing_data uu____4605))
end
| FStar_Const.Const_float (uu____4617) -> begin
(

let uu____4618 = (

let uu____4619 = (

let uu____4625 = (FStar_All.pipe_right "fstar.float" FStar_Ident.lid_of_str)
in ((false), (uu____4625)))
in P_dep (uu____4619))
in (add_to_parsing_data uu____4618))
end
| uu____4630 -> begin
()
end))
and collect_term' = (fun uu___12_4631 -> (match (uu___12_4631) with
| FStar_Parser_AST.Wild -> begin
()
end
| FStar_Parser_AST.Const (c) -> begin
(collect_constant c)
end
| FStar_Parser_AST.Op (s, ts) -> begin
((

let uu____4640 = (

let uu____4642 = (FStar_Ident.text_of_id s)
in (Prims.op_Equality uu____4642 "@"))
in (match (uu____4640) with
| true -> begin
(

let uu____4647 = (

let uu____4648 = (

let uu____4649 = (FStar_Ident.path_of_text "FStar.List.Tot.Base.append")
in (FStar_Ident.lid_of_path uu____4649 FStar_Range.dummyRange))
in FStar_Parser_AST.Name (uu____4648))
in (collect_term' uu____4647))
end
| uu____4651 -> begin
()
end));
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____4653) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____4654) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(add_to_parsing_data (P_lid (lid)))
end
| FStar_Parser_AST.Projector (lid, uu____4657) -> begin
(add_to_parsing_data (P_lid (lid)))
end
| FStar_Parser_AST.Discrim (lid) -> begin
(add_to_parsing_data (P_lid (lid)))
end
| FStar_Parser_AST.Name (lid) -> begin
(add_to_parsing_data (P_lid (lid)))
end
| FStar_Parser_AST.Construct (lid, termimps) -> begin
((add_to_parsing_data (P_lid (lid)));
(FStar_List.iter (fun uu____4682 -> (match (uu____4682) with
| (t, uu____4688) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____4698) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____4700, patterms, t) -> begin
((FStar_List.iter (fun uu____4750 -> (match (uu____4750) with
| (attrs_opt, (pat, t1)) -> begin
((

let uu____4779 = (FStar_Util.map_opt attrs_opt (FStar_List.iter collect_term))
in ());
(collect_pattern pat);
(collect_term t1);
)
end)) patterms);
(collect_term t);
)
end
| FStar_Parser_AST.LetOpen (lid, t) -> begin
((add_to_parsing_data (P_open (((true), (lid)))));
(collect_term t);
)
end
| FStar_Parser_AST.Bind (uu____4790, t1, t2) -> begin
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
(FStar_List.iter (fun uu____4886 -> (match (uu____4886) with
| (uu____4891, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____4894) -> begin
(collect_term t)
end
| FStar_Parser_AST.Product (binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
((FStar_List.iter (fun uu___10_4923 -> (match (uu___10_4923) with
| FStar_Util.Inl (b) -> begin
(collect_binder b)
end
| FStar_Util.Inr (t1) -> begin
(collect_term t1)
end)) binders);
(collect_term t);
)
end
| FStar_Parser_AST.QForall (binders, (uu____4931, ts), t) -> begin
((collect_binders binders);
(FStar_List.iter (FStar_List.iter collect_term) ts);
(collect_term t);
)
end
| FStar_Parser_AST.QExists (binders, (uu____4965, ts), t) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____5001, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____5005) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____5013) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____5021, uu____5022) -> begin
(collect_term t)
end
| FStar_Parser_AST.Quote (t, uu____5028) -> begin
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

let uu____5042 = (

let uu____5043 = (

let uu____5049 = (FStar_Ident.lid_of_str "FStar.Calc")
in ((false), (uu____5049)))
in P_dep (uu____5043))
in (add_to_parsing_data uu____5042));
(collect_term rel);
(collect_term init1);
(FStar_List.iter (fun uu___11_5061 -> (match (uu___11_5061) with
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
and collect_pattern' = (fun uu___13_5071 -> (match (uu___13_5071) with
| FStar_Parser_AST.PatVar (uu____5072, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatTvar (uu____5078, aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatWild (aqual) -> begin
(collect_aqual aqual)
end
| FStar_Parser_AST.PatOp (uu____5087) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____5088) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatName (uu____5096) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____5104) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____5125 -> (match (uu____5125) with
| (uu____5130, p) -> begin
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
and collect_branch = (fun uu____5175 -> (match (uu____5175) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____5193 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____5193) with
| (ast, uu____5219) -> begin
((collect_module ast);
(

let pd1 = (

let uu____5236 = (

let uu____5239 = (FStar_ST.op_Bang pd)
in (FStar_List.rev uu____5239))
in Mk_pd (uu____5236))
in (

let uu____5265 = (from_parsing_data pd1 original_map filename)
in (match (uu____5265) with
| (deps, has_inline_for_extraction, mo_roots) -> begin
((pd1), (deps), (has_inline_for_extraction), (mo_roots))
end)));
)
end))))))
end)))))


let collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap FStar_ST.ref = (

let uu____5324 = (FStar_Util.smap_create (Prims.parse_int "0"))
in (FStar_Util.mk_ref uu____5324))


let set_collect_one_cache : (dependence Prims.list * dependence Prims.list * Prims.bool) FStar_Util.smap  ->  unit = (fun cache -> (FStar_ST.op_Colon_Equals collect_one_cache cache))


let dep_graph_copy : dependence_graph  ->  dependence_graph = (fun dep_graph -> (

let uu____5446 = dep_graph
in (match (uu____5446) with
| Deps (g) -> begin
(

let uu____5450 = (FStar_Util.smap_copy g)
in Deps (uu____5450))
end)))


let widen_deps : module_name Prims.list  ->  dependence_graph  ->  files_for_module_name  ->  Prims.bool  ->  (Prims.bool * dependence_graph) = (fun friends dep_graph file_system_map widened -> (

let widened1 = (FStar_Util.mk_ref widened)
in (

let uu____5492 = dep_graph
in (match (uu____5492) with
| Deps (dg) -> begin
(

let uu____5501 = (deps_empty ())
in (match (uu____5501) with
| Deps (dg') -> begin
(

let widen_one = (fun deps -> (FStar_All.pipe_right deps (FStar_List.map (fun d -> (match (d) with
| PreferInterface (m) when ((FStar_List.contains m friends) && (has_implementation file_system_map m)) -> begin
((FStar_ST.op_Colon_Equals widened1 true);
FriendImplementation (m);
)
end
| uu____5556 -> begin
d
end)))))
in ((FStar_Util.smap_fold dg (fun filename dep_node uu____5564 -> (

let uu____5566 = (

let uu___986_5567 = dep_node
in (

let uu____5568 = (widen_one dep_node.edges)
in {edges = uu____5568; color = White}))
in (FStar_Util.smap_add dg' filename uu____5566))) ());
(

let uu____5569 = (FStar_ST.op_Bang widened1)
in ((uu____5569), (Deps (dg'))));
))
end))
end))))


let topological_dependences_of' : files_for_module_name  ->  dependence_graph  ->  Prims.string Prims.list  ->  file_name Prims.list  ->  Prims.bool  ->  (file_name Prims.list * Prims.bool) = (fun file_system_map dep_graph interfaces_needing_inlining root_files widened -> (

let rec all_friend_deps_1 = (fun dep_graph1 cycle uu____5735 filename -> (match (uu____5735) with
| (all_friends, all_files) -> begin
(

let dep_node = (

let uu____5776 = (deps_try_find dep_graph1 filename)
in (FStar_Util.must uu____5776))
in (match (dep_node.color) with
| Gray -> begin
(failwith "Impossible: cycle detected after cycle detection has passed")
end
| Black -> begin
((all_friends), (all_files))
end
| White -> begin
((

let uu____5807 = (FStar_Options.debug_any ())
in (match (uu____5807) with
| true -> begin
(

let uu____5810 = (

let uu____5812 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_String.concat ", " uu____5812))
in (FStar_Util.print2 "Visiting %s: direct deps are %s\n" filename uu____5810))
end
| uu____5819 -> begin
()
end));
(deps_add_dep dep_graph1 filename (

let uu___1008_5823 = dep_node
in {edges = uu___1008_5823.edges; color = Gray}));
(

let uu____5824 = (

let uu____5835 = (dependences_of file_system_map dep_graph1 root_files filename)
in (all_friend_deps dep_graph1 cycle ((all_friends), (all_files)) uu____5835))
in (match (uu____5824) with
| (all_friends1, all_files1) -> begin
((deps_add_dep dep_graph1 filename (

let uu___1014_5871 = dep_node
in {edges = uu___1014_5871.edges; color = Black}));
(

let uu____5873 = (FStar_Options.debug_any ())
in (match (uu____5873) with
| true -> begin
(FStar_Util.print1 "Adding %s\n" filename)
end
| uu____5877 -> begin
()
end));
(

let uu____5879 = (

let uu____5883 = (FStar_List.collect (fun uu___14_5890 -> (match (uu___14_5890) with
| FriendImplementation (m) -> begin
(m)::[]
end
| d -> begin
[]
end)) dep_node.edges)
in (FStar_List.append uu____5883 all_friends1))
in ((uu____5879), ((filename)::all_files1)));
)
end));
)
end))
end))
and all_friend_deps = (fun dep_graph1 cycle all_friends filenames -> (FStar_List.fold_left (fun all_friends1 k -> (all_friend_deps_1 dep_graph1 ((k)::cycle) all_friends1 k)) all_friends filenames))
in (

let uu____5955 = (all_friend_deps dep_graph [] (([]), ([])) root_files)
in (match (uu____5955) with
| (friends, all_files_0) -> begin
((

let uu____5998 = (FStar_Options.debug_any ())
in (match (uu____5998) with
| true -> begin
(

let uu____6001 = (

let uu____6003 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) friends)
in (FStar_String.concat ", " uu____6003))
in (FStar_Util.print3 "Phase1 complete:\n\tall_files = %s\n\tall_friends=%s\n\tinterfaces_with_inlining=%s\n" (FStar_String.concat ", " all_files_0) uu____6001 (FStar_String.concat ", " interfaces_needing_inlining)))
end
| uu____6019 -> begin
()
end));
(

let uu____6021 = (widen_deps friends dep_graph file_system_map widened)
in (match (uu____6021) with
| (widened1, dep_graph1) -> begin
(

let uu____6039 = ((

let uu____6051 = (FStar_Options.debug_any ())
in (match (uu____6051) with
| true -> begin
(FStar_Util.print_string "==============Phase2==================\n")
end
| uu____6055 -> begin
()
end));
(all_friend_deps dep_graph1 [] (([]), ([])) root_files);
)
in (match (uu____6039) with
| (uu____6074, all_files) -> begin
((

let uu____6089 = (FStar_Options.debug_any ())
in (match (uu____6089) with
| true -> begin
(FStar_Util.print1 "Phase2 complete: all_files = %s\n" (FStar_String.concat ", " all_files))
end
| uu____6094 -> begin
()
end));
((all_files), (widened1));
)
end))
end));
)
end))))


let phase1 : files_for_module_name  ->  dependence_graph  ->  module_name Prims.list  ->  Prims.bool  ->  (Prims.bool * dependence_graph) = (fun file_system_map dep_graph interfaces_needing_inlining for_extraction -> ((

let uu____6135 = (FStar_Options.debug_any ())
in (match (uu____6135) with
| true -> begin
(FStar_Util.print_string "==============Phase1==================\n")
end
| uu____6139 -> begin
()
end));
(

let widened = false
in (

let uu____6144 = ((FStar_Options.cmi ()) && for_extraction)
in (match (uu____6144) with
| true -> begin
(widen_deps interfaces_needing_inlining dep_graph file_system_map widened)
end
| uu____6152 -> begin
((widened), (dep_graph))
end)));
))


let topological_dependences_of : files_for_module_name  ->  dependence_graph  ->  Prims.string Prims.list  ->  file_name Prims.list  ->  Prims.bool  ->  (file_name Prims.list * Prims.bool) = (fun file_system_map dep_graph interfaces_needing_inlining root_files for_extraction -> (

let uu____6211 = (phase1 file_system_map dep_graph interfaces_needing_inlining for_extraction)
in (match (uu____6211) with
| (widened, dep_graph1) -> begin
(topological_dependences_of' file_system_map dep_graph1 interfaces_needing_inlining root_files widened)
end)))


let collect : Prims.string Prims.list  ->  (Prims.string  ->  parsing_data FStar_Pervasives_Native.option)  ->  (Prims.string Prims.list * deps) = (fun all_cmd_line_files get_parsing_data_from_cache -> (

let all_cmd_line_files1 = (FStar_All.pipe_right all_cmd_line_files (FStar_List.map (fun fn -> (

let uu____6288 = (FStar_Options.find_file fn)
in (match (uu____6288) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6294 = (

let uu____6300 = (FStar_Util.format1 "File %s could not be found\n" fn)
in ((FStar_Errors.Fatal_ModuleOrFileNotFound), (uu____6300)))
in (FStar_Errors.raise_err uu____6294))
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

let uu____6330 = (

let uu____6334 = (FStar_ST.op_Bang interfaces_needing_inlining)
in (l1)::uu____6334)
in (FStar_ST.op_Colon_Equals interfaces_needing_inlining uu____6330))))
in (

let parse_results = (FStar_Util.smap_create (Prims.parse_int "40"))
in (

let rec discover_one = (fun file_name -> (

let uu____6401 = (

let uu____6403 = (deps_try_find dep_graph file_name)
in (Prims.op_Equality uu____6403 FStar_Pervasives_Native.None))
in (match (uu____6401) with
| true -> begin
(

let uu____6409 = (

let uu____6425 = (

let uu____6439 = (FStar_ST.op_Bang collect_one_cache)
in (FStar_Util.smap_try_find uu____6439 file_name))
in (match (uu____6425) with
| FStar_Pervasives_Native.Some (cached) -> begin
((Mk_pd ([])), (cached))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6569 = (collect_one file_system_map file_name get_parsing_data_from_cache)
in (match (uu____6569) with
| (parsing_data, deps, needs_interface_inlining, additional_roots) -> begin
((parsing_data), (((deps), (additional_roots), (needs_interface_inlining))))
end))
end))
in (match (uu____6409) with
| (parsing_data, (deps, mo_roots, needs_interface_inlining)) -> begin
((match (needs_interface_inlining) with
| true -> begin
(add_interface_for_inlining file_name)
end
| uu____6655 -> begin
()
end);
(FStar_Util.smap_add parse_results file_name parsing_data);
(

let deps1 = (

let module_name = (lowercase_module_name file_name)
in (

let uu____6663 = ((is_implementation file_name) && (has_interface file_system_map module_name))
in (match (uu____6663) with
| true -> begin
(FStar_List.append deps ((UseInterface (module_name))::[]))
end
| uu____6668 -> begin
deps
end)))
in (

let dep_node = (

let uu____6671 = (FStar_List.unique deps1)
in {edges = uu____6671; color = White})
in ((deps_add_dep dep_graph file_name dep_node);
(

let uu____6673 = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files1) (FStar_List.append deps1 mo_roots))
in (FStar_List.iter discover_one uu____6673));
)));
)
end))
end
| uu____6679 -> begin
()
end)))
in ((profile (fun uu____6683 -> (FStar_List.iter discover_one all_cmd_line_files1)) "FStar.Parser.Dep.discover");
(

let cycle_detected = (fun dep_graph1 cycle filename -> ((FStar_Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (FStar_String.concat "\n`used by` " cycle));
(print_graph dep_graph1);
(FStar_Util.print_string "\n");
(

let uu____6716 = (

let uu____6722 = (FStar_Util.format1 "Recursive dependency on module %s\n" filename)
in ((FStar_Errors.Fatal_CyclicDependence), (uu____6722)))
in (FStar_Errors.raise_err uu____6716));
))
in (

let full_cycle_detection = (fun all_command_line_files file_system_map1 -> (

let dep_graph1 = (dep_graph_copy dep_graph)
in (

let mo_files = (FStar_Util.mk_ref [])
in (

let rec aux = (fun cycle filename -> (

let node = (

let uu____6774 = (deps_try_find dep_graph1 filename)
in (match (uu____6774) with
| FStar_Pervasives_Native.Some (node) -> begin
node
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6778 = (FStar_Util.format1 "Failed to find dependences of %s" filename)
in (failwith uu____6778))
end))
in (

let direct_deps = (FStar_All.pipe_right node.edges (FStar_List.collect (fun x -> (match (x) with
| UseInterface (f) -> begin
(

let uu____6792 = (implementation_of_internal file_system_map1 f)
in (match (uu____6792) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6803 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| PreferInterface (f) -> begin
(

let uu____6809 = (implementation_of_internal file_system_map1 f)
in (match (uu____6809) with
| FStar_Pervasives_Native.None -> begin
(x)::[]
end
| FStar_Pervasives_Native.Some (fn) when (Prims.op_Equality fn filename) -> begin
(x)::[]
end
| uu____6820 -> begin
(x)::(UseImplementation (f))::[]
end))
end
| uu____6824 -> begin
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

let uu___1135_6827 = node
in {edges = direct_deps; color = Gray}));
(

let uu____6829 = (dependences_of file_system_map1 dep_graph1 all_command_line_files filename)
in (FStar_List.iter (fun k -> (aux ((k)::cycle) k)) uu____6829));
(deps_add_dep dep_graph1 filename (

let uu___1140_6840 = node
in {edges = direct_deps; color = Black}));
(

let uu____6841 = (is_interface filename)
in (match (uu____6841) with
| true -> begin
(

let uu____6844 = (

let uu____6848 = (lowercase_module_name filename)
in (implementation_of_internal file_system_map1 uu____6848))
in (FStar_Util.iter_opt uu____6844 (fun impl -> (match ((not ((FStar_List.contains impl all_command_line_files)))) with
| true -> begin
(

let uu____6857 = (

let uu____6861 = (FStar_ST.op_Bang mo_files)
in (impl)::uu____6861)
in (FStar_ST.op_Colon_Equals mo_files uu____6857))
end
| uu____6916 -> begin
()
end))))
end
| uu____6918 -> begin
()
end));
)
end))))
in ((FStar_List.iter (aux []) all_command_line_files);
(

let uu____6923 = (FStar_ST.op_Bang mo_files)
in (FStar_List.iter (aux []) uu____6923));
)))))
in ((full_cycle_detection all_cmd_line_files1 file_system_map);
(FStar_All.pipe_right all_cmd_line_files1 (FStar_List.iter (fun f -> (

let m = (lowercase_module_name f)
in (FStar_Options.add_verify_module m)))));
(

let inlining_ifaces = (FStar_ST.op_Bang interfaces_needing_inlining)
in (

let uu____6995 = (profile (fun uu____7014 -> (

let uu____7015 = (

let uu____7017 = (FStar_Options.codegen ())
in (Prims.op_disEquality uu____7017 FStar_Pervasives_Native.None))
in (topological_dependences_of file_system_map dep_graph inlining_ifaces all_cmd_line_files1 uu____7015))) "FStar.Parser.Dep.topological_dependences_of")
in (match (uu____6995) with
| (all_files, uu____7031) -> begin
((

let uu____7041 = (FStar_Options.debug_any ())
in (match (uu____7041) with
| true -> begin
(FStar_Util.print1 "Interfaces needing inlining: %s\n" (FStar_String.concat ", " inlining_ifaces))
end
| uu____7046 -> begin
()
end));
((all_files), ((mk_deps dep_graph file_system_map all_cmd_line_files1 all_files inlining_ifaces parse_results)));
)
end)));
)));
)))))))))


let deps_of : deps  ->  Prims.string  ->  Prims.string Prims.list = (fun deps f -> (dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f))


let print_digest : (Prims.string * Prims.string) Prims.list  ->  Prims.string = (fun dig -> (

let uu____7094 = (FStar_All.pipe_right dig (FStar_List.map (fun uu____7120 -> (match (uu____7120) with
| (m, d) -> begin
(

let uu____7134 = (FStar_Util.base64_encode d)
in (FStar_Util.format2 "%s:%s" m uu____7134))
end))))
in (FStar_All.pipe_right uu____7094 (FStar_String.concat "\n"))))


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

let uu____7169 = (deps_try_find deps1 f)
in (FStar_All.pipe_right uu____7169 FStar_Option.get))
in (

let files = (FStar_List.map (file_of_dep file_system_map all_cmd_line_files) dep_node.edges)
in (

let files1 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s 32 (* *) "\\ ")) files)
in (FStar_Util.print2 "%s: %s\n\n" f (FStar_String.concat " " files1)))))))))))))


let print_raw : deps  ->  unit = (fun deps -> (

let uu____7198 = deps.dep_graph
in (match (uu____7198) with
| Deps (deps1) -> begin
(

let uu____7202 = (

let uu____7204 = (FStar_Util.smap_fold deps1 (fun k dep_node out -> (

let uu____7222 = (

let uu____7224 = (

let uu____7226 = (FStar_List.map dep_to_string dep_node.edges)
in (FStar_All.pipe_right uu____7226 (FStar_String.concat ";\n\t")))
in (FStar_Util.format2 "%s -> [\n\t%s\n] " k uu____7224))
in (uu____7222)::out)) [])
in (FStar_All.pipe_right uu____7204 (FStar_String.concat ";;\n")))
in (FStar_All.pipe_right uu____7202 FStar_Util.print_endline))
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

let uu____7298 = (FStar_Util.smap_try_find remaining_output_files lc_module_name)
in (FStar_Option.isSome uu____7298)) || (

let uu____7305 = (FStar_Util.smap_try_find visited_other_modules lc_module_name)
in (FStar_Option.isNone uu____7305))))
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

let uu____7348 = (

let uu____7352 = (FStar_ST.op_Bang order)
in (ml_file)::uu____7352)
in (FStar_ST.op_Colon_Equals order uu____7348))
end))
in (

let rec aux = (fun uu___15_7415 -> (match (uu___15_7415) with
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

let uu____7443 = (deps_try_find deps.dep_graph file_name)
in (match (uu____7443) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7446 = (FStar_Util.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
in (failwith uu____7446))
end
| FStar_Pervasives_Native.Some ({edges = immediate_deps; color = uu____7450}) -> begin
(

let immediate_deps1 = (FStar_List.map (fun x -> (FStar_String.lowercase (module_name_of_dep x))) immediate_deps)
in (aux immediate_deps1))
end))
end))
in ((

let uu____7459 = (should_visit lc_module_name)
in (match (uu____7459) with
| true -> begin
(

let ml_file_opt = (mark_visiting lc_module_name)
in ((

let uu____7467 = (implementation_of deps lc_module_name)
in (visit_file uu____7467));
(

let uu____7472 = (interface_of deps lc_module_name)
in (visit_file uu____7472));
(emit_output_file_opt ml_file_opt);
))
end
| uu____7476 -> begin
()
end));
(aux modules_to_extract);
))
end))
in (

let all_extracted_modules = (FStar_Util.smap_keys orig_output_file_map)
in ((aux all_extracted_modules);
(

let uu____7484 = (FStar_ST.op_Bang order)
in (FStar_List.rev uu____7484));
))))))))))
in (

let sb = (

let uu____7515 = (FStar_BigInt.of_int_fs (Prims.parse_int "10000"))
in (FStar_StringBuffer.create uu____7515))
in (

let pr = (fun str -> (

let uu____7525 = (FStar_StringBuffer.add str sb)
in (FStar_All.pipe_left (fun a1 -> ()) uu____7525)))
in (

let print_entry = (fun target first_dep all_deps -> ((pr target);
(pr ": ");
(pr first_dep);
(pr "\\\n\t");
(pr all_deps);
(pr "\n\n");
))
in (

let keys = (deps_keys deps.dep_graph)
in (

let output_file = (fun ext fst_file -> (

let ml_base_name = (

let uu____7578 = (

let uu____7580 = (

let uu____7584 = (FStar_Util.basename fst_file)
in (check_and_strip_suffix uu____7584))
in (FStar_Option.get uu____7580))
in (FStar_Util.replace_chars uu____7578 46 (*.*) "_"))
in (

let uu____7589 = (FStar_String.op_Hat ml_base_name ext)
in (FStar_Options.prepend_output_dir uu____7589))))
in (

let norm_path = (fun s -> (FStar_Util.replace_chars s 92 (*\*) "/"))
in (

let output_ml_file = (fun f -> (

let uu____7611 = (output_file ".ml" f)
in (norm_path uu____7611)))
in (

let output_krml_file = (fun f -> (

let uu____7623 = (output_file ".krml" f)
in (norm_path uu____7623)))
in (

let output_cmx_file = (fun f -> (

let uu____7635 = (output_file ".cmx" f)
in (norm_path uu____7635)))
in (

let cache_file = (fun f -> (

let uu____7647 = (cache_file_name f)
in (norm_path uu____7647)))
in (

let uu____7649 = (phase1 deps.file_system_map deps.dep_graph deps.interfaces_with_inlining true)
in (match (uu____7649) with
| (widened, dep_graph) -> begin
(

let all_checked_files = (FStar_All.pipe_right keys (FStar_List.fold_left (fun all_checked_files file_name -> (

let process_one_key = (fun uu____7691 -> (

let dep_node = (

let uu____7693 = (deps_try_find deps.dep_graph file_name)
in (FStar_All.pipe_right uu____7693 FStar_Option.get))
in (

let iface_deps = (

let uu____7703 = (is_interface file_name)
in (match (uu____7703) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____7712 -> begin
(

let uu____7714 = (

let uu____7718 = (lowercase_module_name file_name)
in (interface_of deps uu____7718))
in (match (uu____7714) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (iface) -> begin
(

let uu____7730 = (

let uu____7733 = (

let uu____7734 = (deps_try_find deps.dep_graph iface)
in (FStar_Option.get uu____7734))
in uu____7733.edges)
in FStar_Pervasives_Native.Some (uu____7730))
end))
end))
in (

let iface_deps1 = (FStar_Util.map_opt iface_deps (FStar_List.filter (fun iface_dep -> (

let uu____7751 = (FStar_Util.for_some (dep_subsumed_by iface_dep) dep_node.edges)
in (not (uu____7751))))))
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

let cache_file_name1 = (cache_file file_name)
in (

let all_checked_files1 = (

let uu____7816 = (

let uu____7818 = (

let uu____7820 = (module_name_of_file file_name)
in (FStar_Options.should_be_already_cached uu____7820))
in (not (uu____7818)))
in (match (uu____7816) with
| true -> begin
((print_entry cache_file_name1 norm_f files4);
(cache_file_name1)::all_checked_files;
)
end
| uu____7828 -> begin
all_checked_files
end))
in (

let uu____7830 = (

let uu____7839 = (FStar_Options.cmi ())
in (match (uu____7839) with
| true -> begin
(profile (fun uu____7860 -> (

let uu____7861 = (dep_graph_copy dep_graph)
in (topological_dependences_of' deps.file_system_map uu____7861 deps.interfaces_with_inlining ((file_name)::[]) widened))) "FStar.Parser.Dep.topological_dependences_of_2")
end
| uu____7865 -> begin
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

let uu____7899 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x y)) (FStar_List.append fst_files fst_files_from_iface))
in ((uu____7899), (false))))))
end))
in (match (uu____7830) with
| (all_fst_files_dep, widened1) -> begin
(

let all_checked_fst_dep_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.map cache_file))
in (

let all_checked_fst_dep_files_string = (FStar_String.concat " \\\n\t" all_checked_fst_dep_files)
in ((

let uu____7946 = (is_implementation file_name)
in (match (uu____7946) with
| true -> begin
((

let uu____7950 = ((FStar_Options.cmi ()) && widened1)
in (match (uu____7950) with
| true -> begin
((

let uu____7954 = (output_ml_file file_name)
in (print_entry uu____7954 cache_file_name1 all_checked_fst_dep_files_string));
(

let uu____7956 = (output_krml_file file_name)
in (print_entry uu____7956 cache_file_name1 all_checked_fst_dep_files_string));
)
end
| uu____7958 -> begin
((

let uu____7961 = (output_ml_file file_name)
in (print_entry uu____7961 cache_file_name1 ""));
(

let uu____7964 = (output_krml_file file_name)
in (print_entry uu____7964 cache_file_name1 ""));
)
end));
(

let cmx_files = (

let extracted_fst_files = (FStar_All.pipe_right all_fst_files_dep (FStar_List.filter (fun df -> ((

let uu____7989 = (lowercase_module_name df)
in (

let uu____7991 = (lowercase_module_name file_name)
in (Prims.op_disEquality uu____7989 uu____7991))) && (

let uu____7995 = (lowercase_module_name df)
in (FStar_Options.should_extract uu____7995))))))
in (FStar_All.pipe_right extracted_fst_files (FStar_List.map output_cmx_file)))
in (

let uu____8005 = (

let uu____8007 = (lowercase_module_name file_name)
in (FStar_Options.should_extract uu____8007))
in (match (uu____8005) with
| true -> begin
(

let cmx_files1 = (FStar_String.concat "\\\n\t" cmx_files)
in (

let uu____8013 = (output_cmx_file file_name)
in (

let uu____8015 = (output_ml_file file_name)
in (print_entry uu____8013 uu____8015 cmx_files1))))
end
| uu____8017 -> begin
()
end)));
)
end
| uu____8019 -> begin
(

let uu____8021 = ((

let uu____8025 = (

let uu____8027 = (lowercase_module_name file_name)
in (has_implementation deps.file_system_map uu____8027))
in (not (uu____8025))) && (is_interface file_name))
in (match (uu____8021) with
| true -> begin
(

let uu____8030 = ((FStar_Options.cmi ()) && (widened1 || true))
in (match (uu____8030) with
| true -> begin
(

let uu____8034 = (output_krml_file file_name)
in (print_entry uu____8034 cache_file_name1 all_checked_fst_dep_files_string))
end
| uu____8036 -> begin
(

let uu____8038 = (output_krml_file file_name)
in (print_entry uu____8038 cache_file_name1 ""))
end))
end
| uu____8041 -> begin
()
end))
end));
all_checked_files1;
)))
end))))))))))))))
in (profile process_one_key "FStar.Parser.Dep.process_one_key"))) []))
in (

let all_fst_files = (

let uu____8052 = (FStar_All.pipe_right keys (FStar_List.filter is_implementation))
in (FStar_All.pipe_right uu____8052 (FStar_Util.sort_with FStar_String.compare)))
in (

let all_fsti_files = (

let uu____8074 = (FStar_All.pipe_right keys (FStar_List.filter is_interface))
in (FStar_All.pipe_right uu____8074 (FStar_Util.sort_with FStar_String.compare)))
in (

let all_ml_files = (

let ml_file_map = (FStar_Util.smap_create (Prims.parse_int "41"))
in ((FStar_All.pipe_right all_fst_files (FStar_List.iter (fun fst_file -> (

let mname = (lowercase_module_name fst_file)
in (

let uu____8115 = (FStar_Options.should_extract mname)
in (match (uu____8115) with
| true -> begin
(

let uu____8118 = (output_ml_file fst_file)
in (FStar_Util.smap_add ml_file_map mname uu____8118))
end
| uu____8121 -> begin
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

let uu____8145 = (output_krml_file fst_file)
in (FStar_Util.smap_add krml_file_map mname uu____8145))))));
(sort_output_files krml_file_map);
))
in (

let print_all = (fun tag files -> ((pr tag);
(pr "=\\\n\t");
(FStar_List.iter (fun f -> ((pr (norm_path f));
(pr " \\\n\t");
)) files);
(pr "\n");
))
in ((print_all "ALL_FST_FILES" all_fst_files);
(print_all "ALL_FSTI_FILES" all_fsti_files);
(print_all "ALL_CHECKED_FILES" all_checked_files);
(print_all "ALL_ML_FILES" all_ml_files);
(print_all "ALL_KRML_FILES" all_krml_files);
(FStar_StringBuffer.output_channel FStar_Util.stdout sb);
)))))))
end))))))))))))))


let print : deps  ->  unit = (fun deps -> (

let uu____8195 = (FStar_Options.dep ())
in (match (uu____8195) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make deps)
end
| FStar_Pervasives_Native.Some ("full") -> begin
(profile (fun uu____8204 -> (print_full deps)) "FStar.Parser.Deps.print_full_deps")
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph deps.dep_graph)
end
| FStar_Pervasives_Native.Some ("raw") -> begin
(print_raw deps)
end
| FStar_Pervasives_Native.Some (uu____8210) -> begin
(FStar_Errors.raise_err ((FStar_Errors.Fatal_UnknownToolForDep), ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end)))


let print_fsmap : (Prims.string FStar_Pervasives_Native.option * Prims.string FStar_Pervasives_Native.option) FStar_Util.smap  ->  Prims.string = (fun fsmap -> (FStar_Util.smap_fold fsmap (fun k uu____8265 s -> (match (uu____8265) with
| (v0, v1) -> begin
(

let uu____8294 = (

let uu____8296 = (FStar_Util.format3 "%s -> (%s, %s)" k (FStar_Util.dflt "_" v0) (FStar_Util.dflt "_" v1))
in (FStar_String.op_Hat "; " uu____8296))
in (FStar_String.op_Hat s uu____8294))
end)) ""))


let module_has_interface : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let uu____8317 = (

let uu____8319 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8319))
in (has_interface deps.file_system_map uu____8317)))


let deps_has_implementation : deps  ->  FStar_Ident.lident  ->  Prims.bool = (fun deps module_name -> (

let m = (

let uu____8335 = (FStar_Ident.string_of_lid module_name)
in (FStar_String.lowercase uu____8335))
in (FStar_All.pipe_right deps.all_files (FStar_Util.for_some (fun f -> ((is_implementation f) && (

let uu____8346 = (

let uu____8348 = (module_name_of_file f)
in (FStar_String.lowercase uu____8348))
in (Prims.op_Equality uu____8346 m))))))))





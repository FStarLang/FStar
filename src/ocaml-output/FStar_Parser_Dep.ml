
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

type open_kind =
| Open_module
| Open_namespace


let uu___is_Open_module : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_module -> begin
true
end
| uu____33 -> begin
false
end))


let uu___is_Open_namespace : open_kind  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Open_namespace -> begin
true
end
| uu____37 -> begin
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

let uu____54 = ((l > lext) && (

let uu____60 = (FStar_String.substring f (l - lext) lext)
in (uu____60 = ext)))
in (match (uu____54) with
| true -> begin
(

let uu____69 = (FStar_String.substring f (Prims.parse_int "0") (l - lext))
in FStar_Pervasives_Native.Some (uu____69))
end
| uu____75 -> begin
FStar_Pervasives_Native.None
end))))) suffixes)
in (

let uu____76 = (FStar_List.filter FStar_Util.is_some matches)
in (match (uu____76) with
| (FStar_Pervasives_Native.Some (m))::uu____82 -> begin
FStar_Pervasives_Native.Some (m)
end
| uu____86 -> begin
FStar_Pervasives_Native.None
end)))))


let is_interface : Prims.string  ->  Prims.bool = (fun f -> (

let uu____92 = (FStar_String.get f ((FStar_String.length f) - (Prims.parse_int "1")))
in (uu____92 = 'i')))


let is_implementation : Prims.string  ->  Prims.bool = (fun f -> (

let uu____99 = (is_interface f)
in (not (uu____99))))


let list_of_option = (fun uu___84_108 -> (match (uu___84_108) with
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end
| FStar_Pervasives_Native.None -> begin
[]
end))


let list_of_pair = (fun uu____122 -> (match (uu____122) with
| (intf, impl) -> begin
(FStar_List.append (list_of_option intf) (list_of_option impl))
end))


let lowercase_module_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____136 = (

let uu____138 = (FStar_Util.basename f)
in (check_and_strip_suffix uu____138))
in (match (uu____136) with
| FStar_Pervasives_Native.Some (longname) -> begin
(FStar_String.lowercase longname)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____140 = (

let uu____141 = (FStar_Util.format1 "not a valid FStar file: %s\n" f)
in FStar_Errors.Err (uu____141))
in (FStar_Pervasives.raise uu____140))
end)))


let build_map : Prims.string Prims.list  ->  map = (fun filenames -> (

let include_directories = (FStar_Options.include_path ())
in (

let include_directories1 = (FStar_List.map FStar_Util.normalize_file_path include_directories)
in (

let include_directories2 = (FStar_List.unique include_directories1)
in (

let cwd = (

let uu____154 = (FStar_Util.getcwd ())
in (FStar_Util.normalize_file_path uu____154))
in (

let map1 = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let add_entry = (fun key full_path -> (

let uu____172 = (FStar_Util.smap_try_find map1 key)
in (match (uu____172) with
| FStar_Pervasives_Native.Some (intf, impl) -> begin
(

let uu____192 = (is_interface full_path)
in (match (uu____192) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (impl)))
end
| uu____199 -> begin
(FStar_Util.smap_add map1 key ((intf), (FStar_Pervasives_Native.Some (full_path))))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____210 = (is_interface full_path)
in (match (uu____210) with
| true -> begin
(FStar_Util.smap_add map1 key ((FStar_Pervasives_Native.Some (full_path)), (FStar_Pervasives_Native.None)))
end
| uu____217 -> begin
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

let uu____230 = (check_and_strip_suffix f1)
in (match (uu____230) with
| FStar_Pervasives_Native.Some (longname) -> begin
(

let full_path = (match ((d = cwd)) with
| true -> begin
f1
end
| uu____234 -> begin
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
| uu____236 -> begin
(

let uu____237 = (

let uu____238 = (FStar_Util.format1 "not a valid include directory: %s\n" d)
in FStar_Errors.Err (uu____238))
in (FStar_Pervasives.raise uu____237))
end)) include_directories2);
(FStar_List.iter (fun f -> (

let uu____241 = (lowercase_module_name f)
in (add_entry uu____241 f))) filenames);
map1;
))))))))


let enter_namespace : map  ->  map  ->  Prims.string  ->  Prims.bool = (fun original_map working_map prefix1 -> (

let found = (FStar_Util.mk_ref false)
in (

let prefix2 = (Prims.strcat prefix1 ".")
in ((

let uu____256 = (

let uu____258 = (FStar_Util.smap_keys original_map)
in (FStar_List.unique uu____258))
in (FStar_List.iter (fun k -> (match ((FStar_Util.starts_with k prefix2)) with
| true -> begin
(

let suffix = (FStar_String.substring k (FStar_String.length prefix2) ((FStar_String.length k) - (FStar_String.length prefix2)))
in (

let filename = (

let uu____278 = (FStar_Util.smap_try_find original_map k)
in (FStar_Util.must uu____278))
in ((FStar_Util.smap_add working_map suffix filename);
(FStar_ST.write found true);
)))
end
| uu____299 -> begin
()
end)) uu____256));
(FStar_ST.read found);
))))


let string_of_lid : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let suffix = (match (last1) with
| true -> begin
(l.FStar_Ident.ident.FStar_Ident.idText)::[]
end
| uu____311 -> begin
[]
end)
in (

let names = (

let uu____314 = (FStar_List.map (fun x -> x.FStar_Ident.idText) l.FStar_Ident.ns)
in (FStar_List.append uu____314 suffix))
in (FStar_String.concat "." names))))


let lowercase_join_longident : FStar_Ident.lident  ->  Prims.bool  ->  Prims.string = (fun l last1 -> (

let uu____323 = (string_of_lid l last1)
in (FStar_String.lowercase uu____323)))


let namespace_of_lid : FStar_Ident.lident  ->  Prims.string = (fun l -> (

let uu____327 = (FStar_List.map FStar_Ident.text_of_id l.FStar_Ident.ns)
in (FStar_String.concat "_" uu____327)))


let check_module_declaration_against_filename : FStar_Ident.lident  ->  Prims.string  ->  Prims.unit = (fun lid filename -> (

let k' = (lowercase_join_longident lid true)
in (

let uu____336 = (

let uu____337 = (

let uu____338 = (

let uu____339 = (

let uu____341 = (FStar_Util.basename filename)
in (check_and_strip_suffix uu____341))
in (FStar_Util.must uu____339))
in (FStar_String.lowercase uu____338))
in (uu____337 <> k'))
in (match (uu____336) with
| true -> begin
(

let uu____342 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: the module declaration \"module %s\" found in file %s does not match its filename. Dependencies will be incorrect.\n" uu____342 filename))
end
| uu____343 -> begin
()
end))))

exception Exit


let uu___is_Exit : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Exit -> begin
true
end
| uu____347 -> begin
false
end))


let hard_coded_dependencies : Prims.string  ->  (FStar_Ident.lident * open_kind) Prims.list = (fun filename -> (

let filename1 = (FStar_Util.basename filename)
in (

let corelibs = (

let uu____357 = (FStar_Options.prims_basename ())
in (

let uu____358 = (

let uu____360 = (FStar_Options.pervasives_basename ())
in (

let uu____361 = (

let uu____363 = (FStar_Options.pervasives_native_basename ())
in (uu____363)::[])
in (uu____360)::uu____361))
in (uu____357)::uu____358))
in (match ((FStar_List.mem filename1 corelibs)) with
| true -> begin
[]
end
| uu____369 -> begin
(((FStar_Parser_Const.fstar_ns_lid), (Open_namespace)))::(((FStar_Parser_Const.prims_lid), (Open_module)))::(((FStar_Parser_Const.pervasives_lid), (Open_module)))::[]
end))))


let collect_one : (Prims.string * Prims.bool FStar_ST.ref) Prims.list  ->  verify_mode  ->  Prims.bool  ->  map  ->  Prims.string  ->  Prims.string Prims.list = (fun verify_flags verify_mode is_user_provided_filename original_map filename -> (

let deps = (FStar_Util.mk_ref [])
in (

let add_dep = (fun d -> (

let uu____412 = (

let uu____413 = (

let uu____414 = (FStar_ST.read deps)
in (FStar_List.existsML (fun d' -> (d' = d)) uu____414))
in (not (uu____413)))
in (match (uu____412) with
| true -> begin
(

let uu____420 = (

let uu____422 = (FStar_ST.read deps)
in (d)::uu____422)
in (FStar_ST.write deps uu____420))
end
| uu____430 -> begin
()
end)))
in (

let working_map = (FStar_Util.smap_copy original_map)
in (

let record_open_module = (fun let_open lid -> (

let key = (lowercase_join_longident lid true)
in (

let uu____449 = (FStar_Util.smap_try_find working_map key)
in (match (uu____449) with
| FStar_Pervasives_Native.Some (pair) -> begin
((FStar_List.iter (fun f -> (

let uu____470 = (lowercase_module_name f)
in (add_dep uu____470))) (list_of_pair pair));
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
| uu____477 -> begin
(

let uu____478 = (string_of_lid lid true)
in (FStar_Util.print2_warning "Warning: in %s: no modules in namespace %s and no file with that name either\n" filename uu____478))
end)
end
| uu____479 -> begin
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

let uu____492 = (string_of_lid lid true)
in (FStar_Util.print1_warning "Warning: no modules in namespace %s and no file with that name either\n" uu____492))
end)
end
| uu____493 -> begin
()
end))))
in (

let record_open = (fun let_open lid -> (

let uu____501 = (record_open_module let_open lid)
in (match (uu____501) with
| true -> begin
()
end
| uu____502 -> begin
(

let msg = (match (let_open) with
| true -> begin
FStar_Pervasives_Native.Some ("let-open only supported for modules, not namespaces")
end
| uu____506 -> begin
FStar_Pervasives_Native.None
end)
in (record_open_namespace msg lid))
end)))
in (

let record_open_module_or_namespace = (fun uu____512 -> (match (uu____512) with
| (lid, kind) -> begin
(match (kind) with
| Open_namespace -> begin
(record_open_namespace FStar_Pervasives_Native.None lid)
end
| Open_module -> begin
(

let uu____517 = (record_open_module false lid)
in ())
end)
end))
in (

let record_module_alias = (fun ident lid -> (

let key = (FStar_String.lowercase (FStar_Ident.text_of_id ident))
in (

let alias = (lowercase_join_longident lid true)
in (

let uu____527 = (FStar_Util.smap_try_find original_map alias)
in (match (uu____527) with
| FStar_Pervasives_Native.Some (deps_of_aliased_module) -> begin
(FStar_Util.smap_add working_map key deps_of_aliased_module)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____554 = (

let uu____555 = (FStar_Util.format1 "module not found in search path: %s\n" alias)
in FStar_Errors.Err (uu____555))
in (FStar_Pervasives.raise uu____554))
end)))))
in (

let record_lid = (fun lid -> (

let try_key = (fun key -> (

let uu____564 = (FStar_Util.smap_try_find working_map key)
in (match (uu____564) with
| FStar_Pervasives_Native.Some (pair) -> begin
(FStar_List.iter (fun f -> (

let uu____584 = (lowercase_module_name f)
in (add_dep uu____584))) (list_of_pair pair))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____589 = (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0")) && (FStar_Options.debug_any ()))
in (match (uu____589) with
| true -> begin
(

let uu____593 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid lid))
in (

let uu____594 = (string_of_lid lid false)
in (FStar_Util.print2_warning "%s (Warning): unbound module reference %s\n" uu____593 uu____594)))
end
| uu____595 -> begin
()
end))
end)))
in (

let uu____597 = (lowercase_join_longident lid false)
in (try_key uu____597))))
in (

let auto_open = (hard_coded_dependencies filename)
in ((FStar_List.iter record_open_module_or_namespace auto_open);
(

let num_of_toplevelmods = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let rec collect_fragment = (fun uu___85_676 -> (match (uu___85_676) with
| FStar_Util.Inl (file) -> begin
(collect_file file)
end
| FStar_Util.Inr (decls) -> begin
(collect_decls decls)
end))
and collect_file = (fun uu___86_689 -> (match (uu___86_689) with
| (modul)::[] -> begin
(collect_module modul)
end
| modules -> begin
((FStar_Util.print1_warning "Warning: file %s does not respect the one module per file convention\n" filename);
(FStar_List.iter collect_module modules);
)
end))
and collect_module = (fun uu___87_695 -> (match (uu___87_695) with
| FStar_Parser_AST.Module (lid, decls) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____705 = (

let uu____706 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____706))
in ())
end
| uu____707 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____709 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____709))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____710 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____710))
end
| uu____711 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____715 -> (match (uu____715) with
| (m, r) -> begin
(

let uu____723 = (

let uu____724 = (

let uu____725 = (string_of_lid lid true)
in (FStar_String.lowercase uu____725))
in ((FStar_String.lowercase m) = uu____724))
in (match (uu____723) with
| true -> begin
(FStar_ST.write r true)
end
| uu____728 -> begin
()
end))
end)) verify_flags)
end);
(collect_decls decls);
)
end
| FStar_Parser_AST.Interface (lid, decls, uu____731) -> begin
((check_module_declaration_against_filename lid filename);
(match (((FStar_List.length lid.FStar_Ident.ns) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____739 = (

let uu____740 = (namespace_of_lid lid)
in (enter_namespace original_map working_map uu____740))
in ())
end
| uu____741 -> begin
()
end);
(match (verify_mode) with
| VerifyAll -> begin
(

let uu____743 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____743))
end
| VerifyFigureItOut -> begin
(match (is_user_provided_filename) with
| true -> begin
(

let uu____744 = (string_of_lid lid true)
in (FStar_Options.add_verify_module uu____744))
end
| uu____745 -> begin
()
end)
end
| VerifyUserList -> begin
(FStar_List.iter (fun uu____749 -> (match (uu____749) with
| (m, r) -> begin
(

let uu____757 = (

let uu____758 = (

let uu____759 = (string_of_lid lid true)
in (FStar_String.lowercase uu____759))
in ((FStar_String.lowercase m) = uu____758))
in (match (uu____757) with
| true -> begin
(FStar_ST.write r true)
end
| uu____762 -> begin
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
and collect_decl = (fun uu___88_767 -> (match (uu___88_767) with
| FStar_Parser_AST.Include (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.Open (lid) -> begin
(record_open false lid)
end
| FStar_Parser_AST.ModuleAbbrev (ident, lid) -> begin
((

let uu____773 = (lowercase_join_longident lid true)
in (add_dep uu____773));
(record_module_alias ident lid);
)
end
| FStar_Parser_AST.TopLevelLet (uu____774, patterms) -> begin
(FStar_List.iter (fun uu____784 -> (match (uu____784) with
| (pat, t) -> begin
((collect_pattern pat);
(collect_term t);
)
end)) patterms)
end
| FStar_Parser_AST.Main (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assume (uu____791, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____793; FStar_Parser_AST.mdest = uu____794; FStar_Parser_AST.lift_op = FStar_Parser_AST.NonReifiableLift (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____796; FStar_Parser_AST.mdest = uu____797; FStar_Parser_AST.lift_op = FStar_Parser_AST.LiftForFree (t)}) -> begin
(collect_term t)
end
| FStar_Parser_AST.Val (uu____799, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.SubEffect ({FStar_Parser_AST.msource = uu____801; FStar_Parser_AST.mdest = uu____802; FStar_Parser_AST.lift_op = FStar_Parser_AST.ReifiableLift (t0, t1)}) -> begin
((collect_term t0);
(collect_term t1);
)
end
| FStar_Parser_AST.Tycon (uu____806, ts) -> begin
(

let ts1 = (FStar_List.map (fun uu____821 -> (match (uu____821) with
| (x, doc1) -> begin
x
end)) ts)
in (FStar_List.iter collect_tycon ts1))
end
| FStar_Parser_AST.Exception (uu____829, t) -> begin
(FStar_Util.iter_opt t collect_term)
end
| FStar_Parser_AST.NewEffect (ed) -> begin
(collect_effect_decl ed)
end
| FStar_Parser_AST.Fsdoc (uu____834) -> begin
()
end
| FStar_Parser_AST.Pragma (uu____835) -> begin
()
end
| FStar_Parser_AST.TopLevelModule (lid) -> begin
((FStar_Util.incr num_of_toplevelmods);
(

let uu____841 = (

let uu____842 = (FStar_ST.read num_of_toplevelmods)
in (uu____842 > (Prims.parse_int "1")))
in (match (uu____841) with
| true -> begin
(

let uu____845 = (

let uu____846 = (

let uu____847 = (string_of_lid lid true)
in (FStar_Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" uu____847))
in FStar_Errors.Err (uu____846))
in (FStar_Pervasives.raise uu____845))
end
| uu____848 -> begin
()
end));
)
end))
and collect_tycon = (fun uu___89_849 -> (match (uu___89_849) with
| FStar_Parser_AST.TyconAbstract (uu____850, binders, k) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
)
end
| FStar_Parser_AST.TyconAbbrev (uu____858, binders, k, t) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(collect_term t);
)
end
| FStar_Parser_AST.TyconRecord (uu____868, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____892 -> (match (uu____892) with
| (uu____897, t, uu____899) -> begin
(collect_term t)
end)) identterms);
)
end
| FStar_Parser_AST.TyconVariant (uu____902, binders, k, identterms) -> begin
((collect_binders binders);
(FStar_Util.iter_opt k collect_term);
(FStar_List.iter (fun uu____932 -> (match (uu____932) with
| (uu____939, t, uu____941, uu____942) -> begin
(FStar_Util.iter_opt t collect_term)
end)) identterms);
)
end))
and collect_effect_decl = (fun uu___90_947 -> (match (uu___90_947) with
| FStar_Parser_AST.DefineEffect (uu____948, binders, t, decls) -> begin
((collect_binders binders);
(collect_term t);
(collect_decls decls);
)
end
| FStar_Parser_AST.RedefineEffect (uu____958, binders, t) -> begin
((collect_binders binders);
(collect_term t);
)
end))
and collect_binders = (fun binders -> (FStar_List.iter collect_binder binders))
and collect_binder = (fun uu___91_966 -> (match (uu___91_966) with
| {FStar_Parser_AST.b = FStar_Parser_AST.Annotated (uu____967, t); FStar_Parser_AST.brange = uu____969; FStar_Parser_AST.blevel = uu____970; FStar_Parser_AST.aqual = uu____971} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.TAnnotated (uu____972, t); FStar_Parser_AST.brange = uu____974; FStar_Parser_AST.blevel = uu____975; FStar_Parser_AST.aqual = uu____976} -> begin
(collect_term t)
end
| {FStar_Parser_AST.b = FStar_Parser_AST.NoName (t); FStar_Parser_AST.brange = uu____978; FStar_Parser_AST.blevel = uu____979; FStar_Parser_AST.aqual = uu____980} -> begin
(collect_term t)
end
| uu____981 -> begin
()
end))
and collect_term = (fun t -> (collect_term' t.FStar_Parser_AST.tm))
and collect_constant = (fun uu___92_983 -> (match (uu___92_983) with
| FStar_Const.Const_int (uu____984, FStar_Pervasives_Native.Some (signedness, width)) -> begin
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

let uu____994 = (FStar_Util.format2 "fstar.%sint%s" u w)
in (add_dep uu____994))))
end
| uu____995 -> begin
()
end))
and collect_term' = (fun uu___93_996 -> (match (uu___93_996) with
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

let uu____1003 = (

let uu____1004 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text "FStar.List.Tot.Base.append") FStar_Range.dummyRange)
in FStar_Parser_AST.Name (uu____1004))
in (collect_term' uu____1003))
end
| uu____1005 -> begin
()
end);
(FStar_List.iter collect_term ts);
)
end
| FStar_Parser_AST.Tvar (uu____1006) -> begin
()
end
| FStar_Parser_AST.Uvar (uu____1007) -> begin
()
end
| FStar_Parser_AST.Var (lid) -> begin
(record_lid lid)
end
| FStar_Parser_AST.Projector (lid, uu____1010) -> begin
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
| uu____1026 -> begin
()
end);
(FStar_List.iter (fun uu____1029 -> (match (uu____1029) with
| (t, uu____1033) -> begin
(collect_term t)
end)) termimps);
)
end
| FStar_Parser_AST.Abs (pats, t) -> begin
((collect_patterns pats);
(collect_term t);
)
end
| FStar_Parser_AST.App (t1, t2, uu____1041) -> begin
((collect_term t1);
(collect_term t2);
)
end
| FStar_Parser_AST.Let (uu____1043, patterms, t) -> begin
((FStar_List.iter (fun uu____1055 -> (match (uu____1055) with
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
| FStar_Parser_AST.Bind (uu____1064, t1, t2) -> begin
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
(FStar_List.iter (fun uu____1125 -> (match (uu____1125) with
| (uu____1128, t1) -> begin
(collect_term t1)
end)) idterms);
)
end
| FStar_Parser_AST.Project (t, uu____1131) -> begin
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
| FStar_Parser_AST.NamedTyp (uu____1169, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Paren (t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Assign (uu____1172, t) -> begin
(collect_term t)
end
| FStar_Parser_AST.Requires (t, uu____1175) -> begin
(collect_term t)
end
| FStar_Parser_AST.Ensures (t, uu____1179) -> begin
(collect_term t)
end
| FStar_Parser_AST.Labeled (t, uu____1183, uu____1184) -> begin
(collect_term t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.iter collect_term cattributes)
end))
and collect_patterns = (fun ps -> (FStar_List.iter collect_pattern ps))
and collect_pattern = (fun p -> (collect_pattern' p.FStar_Parser_AST.pat))
and collect_pattern' = (fun uu___94_1190 -> (match (uu___94_1190) with
| FStar_Parser_AST.PatWild -> begin
()
end
| FStar_Parser_AST.PatOp (uu____1191) -> begin
()
end
| FStar_Parser_AST.PatConst (uu____1192) -> begin
()
end
| FStar_Parser_AST.PatApp (p, ps) -> begin
((collect_pattern p);
(collect_patterns ps);
)
end
| FStar_Parser_AST.PatVar (uu____1198) -> begin
()
end
| FStar_Parser_AST.PatName (uu____1202) -> begin
()
end
| FStar_Parser_AST.PatTvar (uu____1203) -> begin
()
end
| FStar_Parser_AST.PatList (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatOr (ps) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatTuple (ps, uu____1212) -> begin
(collect_patterns ps)
end
| FStar_Parser_AST.PatRecord (lidpats) -> begin
(FStar_List.iter (fun uu____1221 -> (match (uu____1221) with
| (uu____1224, p) -> begin
(collect_pattern p)
end)) lidpats)
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
((collect_pattern p);
(collect_term t);
)
end))
and collect_branches = (fun bs -> (FStar_List.iter collect_branch bs))
and collect_branch = (fun uu____1239 -> (match (uu____1239) with
| (pat, t1, t2) -> begin
((collect_pattern pat);
(FStar_Util.iter_opt t1 collect_term);
(collect_term t2);
)
end))
in (

let uu____1251 = (FStar_Parser_Driver.parse_file filename)
in (match (uu____1251) with
| (ast, uu____1259) -> begin
((collect_file ast);
(FStar_ST.read deps);
)
end))));
))))))))))))


let print_graph = (fun graph -> ((FStar_Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph");
(FStar_Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph");
(FStar_Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims");
(

let uu____1288 = (

let uu____1289 = (

let uu____1290 = (

let uu____1291 = (

let uu____1293 = (

let uu____1295 = (FStar_Util.smap_keys graph)
in (FStar_List.unique uu____1295))
in (FStar_List.collect (fun k -> (

let deps = (

let uu____1303 = (

let uu____1307 = (FStar_Util.smap_try_find graph k)
in (FStar_Util.must uu____1307))
in (FStar_Pervasives_Native.fst uu____1303))
in (

let r = (fun s -> (FStar_Util.replace_char s '.' '_'))
in (FStar_List.map (fun dep1 -> (FStar_Util.format2 "  %s -> %s" (r k) (r dep1))) deps)))) uu____1293))
in (FStar_String.concat "\n" uu____1291))
in (Prims.strcat uu____1290 "\n}\n"))
in (Prims.strcat "digraph {\n" uu____1289))
in (FStar_Util.write_file "dep.graph" uu____1288));
))


let collect : verify_mode  ->  Prims.string Prims.list  ->  ((Prims.string * Prims.string Prims.list) Prims.list * Prims.string Prims.list * (Prims.string Prims.list * color) FStar_Util.smap) = (fun verify_mode filenames -> (

let graph = (FStar_Util.smap_create (Prims.parse_int "41"))
in (

let verify_flags = (

let uu____1369 = (FStar_Options.verify_module ())
in (FStar_List.map (fun f -> (

let uu____1375 = (FStar_Util.mk_ref false)
in ((f), (uu____1375)))) uu____1369))
in (

let partial_discovery = (

let uu____1382 = ((FStar_Options.verify_all ()) || (FStar_Options.extract_all ()))
in (not (uu____1382)))
in (

let m = (build_map filenames)
in (

let file_names_of_key = (fun k -> (

let uu____1388 = (

let uu____1393 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1393))
in (match (uu____1388) with
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
| (FStar_Pervasives_Native.Some (i), uu____1424) when partial_discovery -> begin
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

let uu____1450 = (

let uu____1451 = (FStar_Util.smap_try_find graph key)
in (uu____1451 = FStar_Pervasives_Native.None))
in (match (uu____1450) with
| true -> begin
(

let uu____1466 = (

let uu____1471 = (FStar_Util.smap_try_find m key)
in (FStar_Util.must uu____1471))
in (match (uu____1466) with
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
| (FStar_Pervasives_Native.Some (impl1), FStar_Pervasives_Native.Some (uu____1501)) when interface_only -> begin
[]
end
| (FStar_Pervasives_Native.Some (impl1), uu____1505) -> begin
(collect_one1 is_user_provided_filename m impl1)
end
| (FStar_Pervasives_Native.None, uu____1509) -> begin
[]
end)
in (

let deps = (FStar_List.unique (FStar_List.append impl_deps intf_deps))
in ((FStar_Util.smap_add graph key ((deps), (White)));
(FStar_List.iter (discover_one false partial_discovery) deps);
))))
end))
end
| uu____1520 -> begin
()
end)))
in (

let discover_command_line_argument = (fun f -> (

let m1 = (lowercase_module_name f)
in (

let interface_only = ((is_interface f) && (

let uu____1527 = (FStar_List.existsML (fun f1 -> ((

let uu____1529 = (lowercase_module_name f1)
in (uu____1529 = m1)) && (is_implementation f1))) filenames)
in (not (uu____1527))))
in (discover_one true interface_only m1))))
in ((FStar_List.iter discover_command_line_argument filenames);
(

let immediate_graph = (FStar_Util.smap_copy graph)
in (

let topologically_sorted = (FStar_Util.mk_ref [])
in (

let rec discover = (fun cycle key -> (

let uu____1554 = (

let uu____1558 = (FStar_Util.smap_try_find graph key)
in (FStar_Util.must uu____1558))
in (match (uu____1554) with
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

let uu____1591 = (

let uu____1593 = (FStar_List.map (fun dep1 -> (

let uu____1598 = (discover ((key)::cycle) dep1)
in (dep1)::uu____1598)) direct_deps)
in (FStar_List.flatten uu____1593))
in (FStar_List.unique uu____1591))
in ((FStar_Util.smap_add graph key ((all_deps), (Black)));
(

let uu____1606 = (

let uu____1608 = (FStar_ST.read topologically_sorted)
in (key)::uu____1608)
in (FStar_ST.write topologically_sorted uu____1606));
all_deps;
));
)
end)
end)))
in (

let discover1 = (discover [])
in (

let must_find = (fun k -> (

let uu____1625 = (

let uu____1630 = (FStar_Util.smap_try_find m k)
in (FStar_Util.must uu____1630))
in (match (uu____1625) with
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when ((not (partial_discovery)) && (

let uu____1649 = (FStar_List.existsML (fun f -> (

let uu____1651 = (lowercase_module_name f)
in (uu____1651 = k))) filenames)
in (not (uu____1649)))) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), FStar_Pervasives_Native.Some (impl)) when (FStar_List.existsML (fun f -> ((is_implementation f) && (

let uu____1657 = (lowercase_module_name f)
in (uu____1657 = k)))) filenames) -> begin
(intf)::(impl)::[]
end
| (FStar_Pervasives_Native.Some (intf), uu____1659) -> begin
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

let uu____1673 = (must_find f)
in (FStar_List.rev uu____1673)))
in (

let by_target = (

let uu____1680 = (

let uu____1682 = (FStar_Util.smap_keys graph)
in (FStar_List.sortWith (fun x y -> (FStar_String.compare x y)) uu____1682))
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

let uu____1706 = (

let uu____1711 = (FStar_Util.smap_try_find m k1)
in (FStar_Util.must uu____1711))
in (match (uu____1706) with
| (FStar_Pervasives_Native.Some (intf), uu____1727) when should_append_fsti -> begin
(intf)::[]
end
| uu____1731 -> begin
[]
end))
in (

let deps = (

let uu____1738 = (discover1 k1)
in (FStar_List.rev uu____1738))
in (

let deps_as_filenames = (

let uu____1742 = (FStar_List.collect must_find deps)
in (FStar_List.append uu____1742 suffix))
in ((f), (deps_as_filenames)))))))) as_list)))) uu____1680))
in (

let topologically_sorted1 = (

let uu____1747 = (FStar_ST.read topologically_sorted)
in (FStar_List.collect must_find_r uu____1747))
in ((FStar_List.iter (fun uu____1756 -> (match (uu____1756) with
| (m1, r) -> begin
(

let uu____1764 = ((

let uu____1765 = (FStar_ST.read r)
in (not (uu____1765))) && (

let uu____1768 = (FStar_Options.interactive ())
in (not (uu____1768))))
in (match (uu____1764) with
| true -> begin
(

let maybe_fst = (

let k = (FStar_String.length m1)
in (

let uu____1772 = ((k > (Prims.parse_int "4")) && (

let uu____1776 = (FStar_String.substring m1 (k - (Prims.parse_int "4")) (Prims.parse_int "4"))
in (uu____1776 = ".fst")))
in (match (uu____1772) with
| true -> begin
(

let uu____1780 = (FStar_String.substring m1 (Prims.parse_int "0") (k - (Prims.parse_int "4")))
in (FStar_Util.format1 " Did you mean %s ?" uu____1780))
end
| uu____1784 -> begin
""
end)))
in (

let uu____1785 = (

let uu____1786 = (FStar_Util.format3 "You passed --verify_module %s but I found no file that contains [module %s] in the dependency graph.%s\n" m1 m1 maybe_fst)
in FStar_Errors.Err (uu____1786))
in (FStar_Pervasives.raise uu____1785)))
end
| uu____1787 -> begin
()
end))
end)) verify_flags);
((by_target), (topologically_sorted1), (immediate_graph));
)))))))));
))))))))))


let print_make : (Prims.string * Prims.string Prims.list) Prims.list  ->  Prims.unit = (fun deps -> (FStar_List.iter (fun uu____1811 -> (match (uu____1811) with
| (f, deps1) -> begin
(

let deps2 = (FStar_List.map (fun s -> (FStar_Util.replace_chars s ' ' "\\ ")) deps1)
in (FStar_Util.print2 "%s: %s\n" f (FStar_String.concat " " deps2)))
end)) deps))


let print = (fun uu____1841 -> (match (uu____1841) with
| (make_deps, uu____1854, graph) -> begin
(

let uu____1872 = (FStar_Options.dep ())
in (match (uu____1872) with
| FStar_Pervasives_Native.Some ("make") -> begin
(print_make make_deps)
end
| FStar_Pervasives_Native.Some ("graph") -> begin
(print_graph graph)
end
| FStar_Pervasives_Native.Some (uu____1874) -> begin
(FStar_Pervasives.raise (FStar_Errors.Err ("unknown tool for --dep\n")))
end
| FStar_Pervasives_Native.None -> begin
()
end))
end))





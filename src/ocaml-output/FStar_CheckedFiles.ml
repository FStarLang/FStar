
open Prims
open FStar_Pervasives

let cache_version_number : Prims.int = (Prims.parse_int "11")

type tc_result =
{checked_module : FStar_Syntax_Syntax.modul; mii : FStar_Syntax_DsEnv.module_inclusion_info; smt_decls : (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding Prims.list); tc_time : Prims.int; extraction_time : Prims.int}


let __proj__Mktc_result__item__checked_module : tc_result  ->  FStar_Syntax_Syntax.modul = (fun projectee -> (match (projectee) with
| {checked_module = checked_module; mii = mii; smt_decls = smt_decls; tc_time = tc_time; extraction_time = extraction_time} -> begin
checked_module
end))


let __proj__Mktc_result__item__mii : tc_result  ->  FStar_Syntax_DsEnv.module_inclusion_info = (fun projectee -> (match (projectee) with
| {checked_module = checked_module; mii = mii; smt_decls = smt_decls; tc_time = tc_time; extraction_time = extraction_time} -> begin
mii
end))


let __proj__Mktc_result__item__smt_decls : tc_result  ->  (FStar_SMTEncoding_Term.decls_t * FStar_SMTEncoding_Env.fvar_binding Prims.list) = (fun projectee -> (match (projectee) with
| {checked_module = checked_module; mii = mii; smt_decls = smt_decls; tc_time = tc_time; extraction_time = extraction_time} -> begin
smt_decls
end))


let __proj__Mktc_result__item__tc_time : tc_result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {checked_module = checked_module; mii = mii; smt_decls = smt_decls; tc_time = tc_time; extraction_time = extraction_time} -> begin
tc_time
end))


let __proj__Mktc_result__item__extraction_time : tc_result  ->  Prims.int = (fun projectee -> (match (projectee) with
| {checked_module = checked_module; mii = mii; smt_decls = smt_decls; tc_time = tc_time; extraction_time = extraction_time} -> begin
extraction_time
end))


type checked_file_entry =
(Prims.int * (Prims.string * Prims.string) Prims.list * Prims.string * FStar_Parser_Dep.parsing_data * tc_result)

type tc_result_t =
| Unknown
| Invalid of Prims.string
| Valid of Prims.string


let uu___is_Unknown : tc_result_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____192 -> begin
false
end))


let uu___is_Invalid : tc_result_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Invalid (_0) -> begin
true
end
| uu____205 -> begin
false
end))


let __proj__Invalid__item___0 : tc_result_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| Invalid (_0) -> begin
_0
end))


let uu___is_Valid : tc_result_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Valid (_0) -> begin
true
end
| uu____228 -> begin
false
end))


let __proj__Valid__item___0 : tc_result_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| Valid (_0) -> begin
_0
end))


type cache_t =
(tc_result_t * (Prims.string, FStar_Parser_Dep.parsing_data) FStar_Util.either)


let mcache : cache_t FStar_Util.smap = (FStar_Util.smap_create (Prims.parse_int "50"))


let hash_dependences : FStar_Parser_Dep.deps  ->  Prims.string  ->  (Prims.string, (Prims.string * Prims.string) Prims.list) FStar_Util.either = (fun deps fn -> (

let fn1 = (

let uu____294 = (FStar_Options.find_file fn)
in (match (uu____294) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____302 -> begin
fn
end))
in (

let module_name = (FStar_Parser_Dep.lowercase_module_name fn1)
in (

let source_hash = (FStar_Util.digest_of_file fn1)
in (

let has_interface = (

let uu____312 = (FStar_Parser_Dep.interface_of deps module_name)
in (FStar_Option.isSome uu____312))
in (

let interface_hash = (

let uu____326 = ((FStar_Parser_Dep.is_implementation fn1) && has_interface)
in (match (uu____326) with
| true -> begin
(

let uu____337 = (

let uu____344 = (

let uu____346 = (

let uu____348 = (FStar_Parser_Dep.interface_of deps module_name)
in (FStar_Option.get uu____348))
in (FStar_Util.digest_of_file uu____346))
in (("interface"), (uu____344)))
in (uu____337)::[])
end
| uu____368 -> begin
[]
end))
in (

let binary_deps = (

let uu____380 = (FStar_Parser_Dep.deps_of deps fn1)
in (FStar_All.pipe_right uu____380 (FStar_List.filter (fun fn2 -> (

let uu____395 = ((FStar_Parser_Dep.is_interface fn2) && (

let uu____398 = (FStar_Parser_Dep.lowercase_module_name fn2)
in (Prims.op_Equality uu____398 module_name)))
in (not (uu____395)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____414 = (FStar_Parser_Dep.lowercase_module_name fn11)
in (

let uu____416 = (FStar_Parser_Dep.lowercase_module_name fn2)
in (FStar_String.compare uu____414 uu____416)))) binary_deps)
in (

let rec hash_deps = (fun out uu___0_452 -> (match (uu___0_452) with
| [] -> begin
FStar_Util.Inr ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps1 -> begin
(

let cache_fn = (FStar_Parser_Dep.cache_file_name fn2)
in (

let digest = (

let uu____518 = (FStar_Util.smap_try_find mcache cache_fn)
in (match (uu____518) with
| FStar_Pervasives_Native.None -> begin
(

let msg = (FStar_Util.format2 "For dependency %s, cache file %s is not loaded" fn2 cache_fn)
in ((

let uu____531 = (FStar_Options.debug_any ())
in (match (uu____531) with
| true -> begin
(FStar_Util.print1 "%s\\m" msg)
end
| uu____535 -> begin
()
end));
FStar_Util.Inl (msg);
))
end
| FStar_Pervasives_Native.Some (Invalid (msg), uu____540) -> begin
FStar_Util.Inl (msg)
end
| FStar_Pervasives_Native.Some (Valid (dig), uu____555) -> begin
FStar_Util.Inr (dig)
end
| FStar_Pervasives_Native.Some (Unknown, uu____569) -> begin
(

let uu____580 = (FStar_Util.format2 "Impossible: unknown entry in the cache for dependence %s of module %s" fn2 module_name)
in (failwith uu____580))
end))
in (match (digest) with
| FStar_Util.Inl (msg) -> begin
FStar_Util.Inl (msg)
end
| FStar_Util.Inr (dig) -> begin
(

let uu____619 = (

let uu____628 = (

let uu____635 = (FStar_Parser_Dep.lowercase_module_name fn2)
in ((uu____635), (dig)))
in (uu____628)::out)
in (hash_deps uu____619 deps1))
end)))
end))
in (hash_deps [] binary_deps1))))))))))


let load_checked_file : Prims.string  ->  Prims.string  ->  cache_t = (fun fn checked_fn -> (

let elt = (FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache))
in (

let uu____672 = (FStar_All.pipe_right elt FStar_Util.is_some)
in (match (uu____672) with
| true -> begin
(FStar_All.pipe_right elt FStar_Util.must)
end
| uu____680 -> begin
(

let add_and_return = (fun elt1 -> ((FStar_Util.smap_add mcache checked_fn elt1);
elt1;
))
in (match ((not ((FStar_Util.file_exists checked_fn)))) with
| true -> begin
(

let msg = (FStar_Util.format1 "checked file %s does not exist" checked_fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))))
end
| uu____699 -> begin
(

let entry = (FStar_Util.load_value_from_file checked_fn)
in (match (entry) with
| FStar_Pervasives_Native.None -> begin
(

let msg = (FStar_Util.format1 "checked file %s is corrupt" checked_fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))))
end
| FStar_Pervasives_Native.Some (vnum, uu____714, dig, parsing_data, uu____717) -> begin
(match ((Prims.op_disEquality vnum cache_version_number)) with
| true -> begin
(

let msg = (FStar_Util.format1 "checked file %s has incorrect version" checked_fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))))
end
| uu____749 -> begin
(

let current_dig = (FStar_Util.digest_of_file fn)
in (match ((Prims.op_disEquality dig current_dig)) with
| true -> begin
((

let uu____756 = (FStar_Options.debug_any ())
in (match (uu____756) with
| true -> begin
(FStar_Util.print4 "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n" checked_fn fn current_dig dig)
end
| uu____760 -> begin
()
end));
(

let msg = (FStar_Util.format2 "checked file %s is stale (digest mismatch for %s)" checked_fn fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))));
)
end
| uu____771 -> begin
(add_and_return ((Unknown), (FStar_Util.Inr (parsing_data))))
end))
end)
end))
end))
end))))


let load_checked_file_with_tc_result : FStar_Parser_Dep.deps  ->  Prims.string  ->  Prims.string  ->  (Prims.string, tc_result) FStar_Util.either = (fun deps fn checked_fn -> (

let load_tc_result = (fun fn1 -> (

let entry = (FStar_Util.load_value_from_file checked_fn)
in (match (entry) with
| FStar_Pervasives_Native.Some (uu____856, deps_dig, uu____858, uu____859, tc_result) -> begin
((deps_dig), (tc_result))
end
| uu____889 -> begin
(failwith "Impossible! if first phase of loading was unknown, it should have succeeded")
end)))
in (

let elt = (load_checked_file fn checked_fn)
in (match (elt) with
| (Invalid (msg), uu____912) -> begin
FStar_Util.Inl (msg)
end
| (Valid (uu____925), uu____926) -> begin
(

let uu____938 = (

let uu____939 = (FStar_All.pipe_right checked_fn load_tc_result)
in (FStar_All.pipe_right uu____939 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____938 (fun _991 -> FStar_Util.Inr (_991))))
end
| (Unknown, parsing_data) -> begin
(

let uu____1003 = (hash_dependences deps fn)
in (match (uu____1003) with
| FStar_Util.Inl (msg) -> begin
(

let elt1 = ((Invalid (msg)), (parsing_data))
in ((FStar_Util.smap_add mcache checked_fn elt1);
FStar_Util.Inl (msg);
))
end
| FStar_Util.Inr (deps_dig') -> begin
(

let uu____1068 = (FStar_All.pipe_right checked_fn load_tc_result)
in (match (uu____1068) with
| (deps_dig, tc_result) -> begin
(match ((Prims.op_Equality deps_dig deps_dig')) with
| true -> begin
(

let elt1 = (

let uu____1141 = (

let uu____1142 = (FStar_Util.digest_of_file checked_fn)
in Valid (uu____1142))
in ((uu____1141), (parsing_data)))
in ((FStar_Util.smap_add mcache checked_fn elt1);
(

let validate_iface_cache = (fun uu____1155 -> (

let iface1 = (

let uu____1160 = (FStar_All.pipe_right fn FStar_Parser_Dep.lowercase_module_name)
in (FStar_All.pipe_right uu____1160 (FStar_Parser_Dep.interface_of deps)))
in (match (iface1) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (iface2) -> begin
(FStar_All.try_with (fun uu___136_1177 -> (match (()) with
| () -> begin
(

let iface_checked_fn = (FStar_All.pipe_right iface2 FStar_Parser_Dep.cache_file_name)
in (

let uu____1182 = (FStar_Util.smap_try_find mcache iface_checked_fn)
in (match (uu____1182) with
| FStar_Pervasives_Native.Some (Unknown, parsing_data1) -> begin
(

let uu____1196 = (

let uu____1197 = (

let uu____1198 = (FStar_Util.digest_of_file iface_checked_fn)
in Valid (uu____1198))
in ((uu____1197), (parsing_data1)))
in (FStar_Util.smap_add mcache iface_checked_fn uu____1196))
end
| uu____1205 -> begin
()
end)))
end)) (fun uu___135_1209 -> ()))
end)))
in ((validate_iface_cache ());
FStar_Util.Inr (tc_result);
));
))
end
| uu____1212 -> begin
((

let uu____1215 = (FStar_Options.debug_any ())
in (match (uu____1215) with
| true -> begin
((

let uu____1219 = (FStar_Util.string_of_int (FStar_List.length deps_dig'))
in (

let uu____1227 = (FStar_Parser_Dep.print_digest deps_dig')
in (

let uu____1229 = (FStar_Util.string_of_int (FStar_List.length deps_dig))
in (

let uu____1237 = (FStar_Parser_Dep.print_digest deps_dig)
in (FStar_Util.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n" uu____1219 uu____1227 uu____1229 uu____1237)))));
(match ((Prims.op_Equality (FStar_List.length deps_dig) (FStar_List.length deps_dig'))) with
| true -> begin
(FStar_List.iter2 (fun uu____1273 uu____1274 -> (match (((uu____1273), (uu____1274))) with
| ((x, y), (x', y')) -> begin
(match (((Prims.op_disEquality x x') || (Prims.op_disEquality y y'))) with
| true -> begin
(

let uu____1326 = (FStar_Parser_Dep.print_digest ((((x), (y)))::[]))
in (

let uu____1342 = (FStar_Parser_Dep.print_digest ((((x'), (y')))::[]))
in (FStar_Util.print2 "Differ at: Expected %s\n Got %s\n" uu____1326 uu____1342)))
end
| uu____1359 -> begin
()
end)
end)) deps_dig deps_dig')
end
| uu____1361 -> begin
()
end);
)
end
| uu____1363 -> begin
()
end));
(

let msg = (FStar_Util.format1 "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)" checked_fn)
in (

let elt1 = ((Invalid (msg)), (FStar_Util.Inl (msg)))
in ((FStar_Util.smap_add mcache checked_fn elt1);
FStar_Util.Inl (msg);
)));
)
end)
end))
end))
end))))


let load_parsing_data_from_cache : Prims.string  ->  FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option = (fun file_name -> (

let cache_file = (FStar_All.try_with (fun uu___165_1405 -> (match (()) with
| () -> begin
(

let uu____1409 = (FStar_Parser_Dep.cache_file_name file_name)
in (FStar_All.pipe_right uu____1409 (fun _1416 -> FStar_Pervasives_Native.Some (_1416))))
end)) (fun uu___164_1418 -> FStar_Pervasives_Native.None))
in (match (cache_file) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (cache_file1) -> begin
(

let uu____1429 = (load_checked_file file_name cache_file1)
in (match (uu____1429) with
| (uu____1432, FStar_Util.Inl (msg)) -> begin
FStar_Pervasives_Native.None
end
| (uu____1441, FStar_Util.Inr (data)) -> begin
FStar_Pervasives_Native.Some (data)
end))
end)))


let load_module_from_cache : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string  ->  tc_result FStar_Pervasives_Native.option = (

let already_failed = (FStar_Util.mk_ref false)
in (fun env fn -> (

let load_it = (fun uu____1477 -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let fail1 = (fun msg cache_file1 -> (

let suppress_warning = ((FStar_Options.should_verify_file fn) || (FStar_ST.op_Bang already_failed))
in (match ((not (suppress_warning))) with
| true -> begin
((FStar_ST.op_Colon_Equals already_failed true);
(

let uu____1542 = (

let uu____1543 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1546 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1543 uu____1546)))
in (

let uu____1549 = (

let uu____1555 = (FStar_Util.format3 "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)" cache_file1 msg fn)
in ((FStar_Errors.Warning_CachedFile), (uu____1555)))
in (FStar_Errors.log_issue uu____1542 uu____1549)));
)
end
| uu____1559 -> begin
()
end)))
in (

let uu____1561 = (

let uu____1567 = (FStar_TypeChecker_Env.dep_graph env.FStar_Extraction_ML_UEnv.env_tcenv)
in (load_checked_file_with_tc_result uu____1567 fn cache_file))
in (match (uu____1561) with
| FStar_Util.Inl (msg) -> begin
((fail1 msg cache_file);
FStar_Pervasives_Native.None;
)
end
| FStar_Util.Inr (tc_result) -> begin
((

let uu____1577 = (FStar_Options.debug_any ())
in (match (uu____1577) with
| true -> begin
(FStar_Util.print1 "Successfully loaded module from checked file %s\n" cache_file)
end
| uu____1581 -> begin
()
end));
FStar_Pervasives_Native.Some (tc_result);
)
end
| uu____1583 -> begin
(failwith "load_checked_file_tc_result must have an Invalid or Valid entry")
end)))))
in (FStar_Options.profile load_it (fun res -> (

let msg = (match ((FStar_Option.isSome res)) with
| true -> begin
"ok"
end
| uu____1605 -> begin
"failed"
end)
in (

let uu____1608 = (FStar_Parser_Dep.cache_file_name fn)
in (FStar_Util.format2 "Loading checked file %s ... %s" uu____1608 msg))))))))


let store_value_to_cache : Prims.string  ->  checked_file_entry  ->  unit = (fun cache_file data -> (FStar_Util.save_value_to_file cache_file data))


let store_module_to_cache : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  tc_result  ->  unit = (fun env fn parsing_data tc_result -> (

let uu____1647 = ((FStar_Options.cache_checked_modules ()) && (

let uu____1650 = (FStar_Options.cache_off ())
in (not (uu____1650))))
in (match (uu____1647) with
| true -> begin
(

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let digest = (

let uu____1669 = (FStar_TypeChecker_Env.dep_graph env.FStar_Extraction_ML_UEnv.env_tcenv)
in (hash_dependences uu____1669 fn))
in (match (digest) with
| FStar_Util.Inr (hashes) -> begin
(

let tc_result1 = (

let uu___217_1689 = tc_result
in {checked_module = uu___217_1689.checked_module; mii = uu___217_1689.mii; smt_decls = uu___217_1689.smt_decls; tc_time = (Prims.parse_int "0"); extraction_time = (Prims.parse_int "0")})
in (

let uu____1692 = (

let uu____1693 = (FStar_Util.digest_of_file fn)
in ((cache_version_number), (hashes), (uu____1693), (parsing_data), (tc_result1)))
in (store_value_to_cache cache_file uu____1692)))
end
| FStar_Util.Inl (msg) -> begin
(

let uu____1716 = (

let uu____1717 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1720 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1717 uu____1720)))
in (

let uu____1723 = (

let uu____1729 = (FStar_Util.format2 "%s was not written since %s" cache_file msg)
in ((FStar_Errors.Warning_FileNotWritten), (uu____1729)))
in (FStar_Errors.log_issue uu____1716 uu____1723)))
end)))
end
| uu____1733 -> begin
()
end)))





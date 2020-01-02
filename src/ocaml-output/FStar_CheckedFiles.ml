
open Prims
open FStar_Pervasives

let cache_version_number : Prims.int = (Prims.parse_int "15")

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

type checked_file_entry_stage1 =
{version : Prims.int; digest : Prims.string; parsing_data : FStar_Parser_Dep.parsing_data}


let __proj__Mkchecked_file_entry_stage1__item__version : checked_file_entry_stage1  ->  Prims.int = (fun projectee -> (match (projectee) with
| {version = version; digest = digest; parsing_data = parsing_data} -> begin
version
end))


let __proj__Mkchecked_file_entry_stage1__item__digest : checked_file_entry_stage1  ->  Prims.string = (fun projectee -> (match (projectee) with
| {version = version; digest = digest; parsing_data = parsing_data} -> begin
digest
end))


let __proj__Mkchecked_file_entry_stage1__item__parsing_data : checked_file_entry_stage1  ->  FStar_Parser_Dep.parsing_data = (fun projectee -> (match (projectee) with
| {version = version; digest = digest; parsing_data = parsing_data} -> begin
parsing_data
end))

type checked_file_entry_stage2 =
{deps_dig : (Prims.string * Prims.string) Prims.list; tc_res : tc_result}


let __proj__Mkchecked_file_entry_stage2__item__deps_dig : checked_file_entry_stage2  ->  (Prims.string * Prims.string) Prims.list = (fun projectee -> (match (projectee) with
| {deps_dig = deps_dig; tc_res = tc_res} -> begin
deps_dig
end))


let __proj__Mkchecked_file_entry_stage2__item__tc_res : checked_file_entry_stage2  ->  tc_result = (fun projectee -> (match (projectee) with
| {deps_dig = deps_dig; tc_res = tc_res} -> begin
tc_res
end))

type tc_result_t =
| Unknown
| Invalid of Prims.string
| Valid of Prims.string


let uu___is_Unknown : tc_result_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unknown -> begin
true
end
| uu____297 -> begin
false
end))


let uu___is_Invalid : tc_result_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Invalid (_0) -> begin
true
end
| uu____310 -> begin
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
| uu____333 -> begin
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

let uu____399 = (FStar_Options.find_file fn)
in (match (uu____399) with
| FStar_Pervasives_Native.Some (fn1) -> begin
fn1
end
| uu____407 -> begin
fn
end))
in (

let module_name = (FStar_Parser_Dep.lowercase_module_name fn1)
in (

let source_hash = (FStar_Util.digest_of_file fn1)
in (

let has_interface = (

let uu____417 = (FStar_Parser_Dep.interface_of deps module_name)
in (FStar_Option.isSome uu____417))
in (

let interface_hash = (

let uu____431 = ((FStar_Parser_Dep.is_implementation fn1) && has_interface)
in (match (uu____431) with
| true -> begin
(

let uu____442 = (

let uu____449 = (

let uu____451 = (

let uu____453 = (FStar_Parser_Dep.interface_of deps module_name)
in (FStar_Option.get uu____453))
in (FStar_Util.digest_of_file uu____451))
in (("interface"), (uu____449)))
in (uu____442)::[])
end
| uu____473 -> begin
[]
end))
in (

let binary_deps = (

let uu____485 = (FStar_Parser_Dep.deps_of deps fn1)
in (FStar_All.pipe_right uu____485 (FStar_List.filter (fun fn2 -> (

let uu____500 = ((FStar_Parser_Dep.is_interface fn2) && (

let uu____503 = (FStar_Parser_Dep.lowercase_module_name fn2)
in (Prims.op_Equality uu____503 module_name)))
in (not (uu____500)))))))
in (

let binary_deps1 = (FStar_List.sortWith (fun fn11 fn2 -> (

let uu____519 = (FStar_Parser_Dep.lowercase_module_name fn11)
in (

let uu____521 = (FStar_Parser_Dep.lowercase_module_name fn2)
in (FStar_String.compare uu____519 uu____521)))) binary_deps)
in (

let rec hash_deps = (fun out uu___0_557 -> (match (uu___0_557) with
| [] -> begin
FStar_Util.Inr ((FStar_List.append (((("source"), (source_hash)))::interface_hash) out))
end
| (fn2)::deps1 -> begin
(

let cache_fn = (FStar_Parser_Dep.cache_file_name fn2)
in (

let digest = (

let uu____623 = (FStar_Util.smap_try_find mcache cache_fn)
in (match (uu____623) with
| FStar_Pervasives_Native.None -> begin
(

let msg = (FStar_Util.format2 "For dependency %s, cache file %s is not loaded" fn2 cache_fn)
in ((

let uu____636 = (FStar_Options.debug_any ())
in (match (uu____636) with
| true -> begin
(FStar_Util.print1 "%s\\m" msg)
end
| uu____640 -> begin
()
end));
FStar_Util.Inl (msg);
))
end
| FStar_Pervasives_Native.Some (Invalid (msg), uu____645) -> begin
FStar_Util.Inl (msg)
end
| FStar_Pervasives_Native.Some (Valid (dig), uu____660) -> begin
FStar_Util.Inr (dig)
end
| FStar_Pervasives_Native.Some (Unknown, uu____674) -> begin
(

let uu____685 = (FStar_Util.format2 "Impossible: unknown entry in the cache for dependence %s of module %s" fn2 module_name)
in (failwith uu____685))
end))
in (match (digest) with
| FStar_Util.Inl (msg) -> begin
FStar_Util.Inl (msg)
end
| FStar_Util.Inr (dig) -> begin
(

let uu____724 = (

let uu____733 = (

let uu____740 = (FStar_Parser_Dep.lowercase_module_name fn2)
in ((uu____740), (dig)))
in (uu____733)::out)
in (hash_deps uu____724 deps1))
end)))
end))
in (hash_deps [] binary_deps1))))))))))


let load_checked_file : Prims.string  ->  Prims.string  ->  cache_t = (fun fn checked_fn -> (

let elt = (FStar_All.pipe_right checked_fn (FStar_Util.smap_try_find mcache))
in (

let uu____777 = (FStar_All.pipe_right elt FStar_Util.is_some)
in (match (uu____777) with
| true -> begin
(FStar_All.pipe_right elt FStar_Util.must)
end
| uu____785 -> begin
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
| uu____804 -> begin
(

let entry = (FStar_Util.load_value_from_file checked_fn)
in (match (entry) with
| FStar_Pervasives_Native.None -> begin
(

let msg = (FStar_Util.format1 "checked file %s is corrupt" checked_fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))))
end
| FStar_Pervasives_Native.Some (x) -> begin
(match ((Prims.op_disEquality x.version cache_version_number)) with
| true -> begin
(

let msg = (FStar_Util.format1 "checked file %s has incorrect version" checked_fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))))
end
| uu____830 -> begin
(

let current_digest = (FStar_Util.digest_of_file fn)
in (match ((Prims.op_disEquality x.digest current_digest)) with
| true -> begin
((

let uu____837 = (FStar_Options.debug_any ())
in (match (uu____837) with
| true -> begin
(FStar_Util.print4 "Checked file %s is stale since incorrect digest of %s, expected: %s, found: %s\n" checked_fn fn current_digest x.digest)
end
| uu____841 -> begin
()
end));
(

let msg = (FStar_Util.format2 "checked file %s is stale (digest mismatch for %s)" checked_fn fn)
in (add_and_return ((Invalid (msg)), (FStar_Util.Inl (msg)))));
)
end
| uu____852 -> begin
(add_and_return ((Unknown), (FStar_Util.Inr (x.parsing_data))))
end))
end)
end))
end))
end))))


let load_checked_file_with_tc_result : FStar_Parser_Dep.deps  ->  Prims.string  ->  Prims.string  ->  (Prims.string, tc_result) FStar_Util.either = (fun deps fn checked_fn -> (

let load_tc_result = (fun fn1 -> (

let entry = (FStar_Util.load_2values_from_file checked_fn)
in (match (entry) with
| FStar_Pervasives_Native.Some (uu____941, s2) -> begin
((s2.deps_dig), (s2.tc_res))
end
| uu____955 -> begin
(failwith "Impossible! if first phase of loading was unknown, it should have succeeded")
end)))
in (

let elt = (load_checked_file fn checked_fn)
in (match (elt) with
| (Invalid (msg), uu____982) -> begin
FStar_Util.Inl (msg)
end
| (Valid (uu____995), uu____996) -> begin
(

let uu____1008 = (

let uu____1009 = (FStar_All.pipe_right checked_fn load_tc_result)
in (FStar_All.pipe_right uu____1009 FStar_Pervasives_Native.snd))
in (FStar_All.pipe_right uu____1008 (fun _1061 -> FStar_Util.Inr (_1061))))
end
| (Unknown, parsing_data) -> begin
(

let uu____1073 = (hash_dependences deps fn)
in (match (uu____1073) with
| FStar_Util.Inl (msg) -> begin
(

let elt1 = ((Invalid (msg)), (parsing_data))
in ((FStar_Util.smap_add mcache checked_fn elt1);
FStar_Util.Inl (msg);
))
end
| FStar_Util.Inr (deps_dig') -> begin
(

let uu____1138 = (FStar_All.pipe_right checked_fn load_tc_result)
in (match (uu____1138) with
| (deps_dig, tc_result) -> begin
(match ((Prims.op_Equality deps_dig deps_dig')) with
| true -> begin
(

let elt1 = (

let uu____1211 = (

let uu____1212 = (FStar_Util.digest_of_file checked_fn)
in Valid (uu____1212))
in ((uu____1211), (parsing_data)))
in ((FStar_Util.smap_add mcache checked_fn elt1);
(

let validate_iface_cache = (fun uu____1225 -> (

let iface1 = (

let uu____1230 = (FStar_All.pipe_right fn FStar_Parser_Dep.lowercase_module_name)
in (FStar_All.pipe_right uu____1230 (FStar_Parser_Dep.interface_of deps)))
in (match (iface1) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (iface2) -> begin
(FStar_All.try_with (fun uu___143_1247 -> (match (()) with
| () -> begin
(

let iface_checked_fn = (FStar_All.pipe_right iface2 FStar_Parser_Dep.cache_file_name)
in (

let uu____1252 = (FStar_Util.smap_try_find mcache iface_checked_fn)
in (match (uu____1252) with
| FStar_Pervasives_Native.Some (Unknown, parsing_data1) -> begin
(

let uu____1266 = (

let uu____1267 = (

let uu____1268 = (FStar_Util.digest_of_file iface_checked_fn)
in Valid (uu____1268))
in ((uu____1267), (parsing_data1)))
in (FStar_Util.smap_add mcache iface_checked_fn uu____1266))
end
| uu____1275 -> begin
()
end)))
end)) (fun uu___142_1279 -> ()))
end)))
in ((validate_iface_cache ());
FStar_Util.Inr (tc_result);
));
))
end
| uu____1282 -> begin
((

let uu____1285 = (FStar_Options.debug_any ())
in (match (uu____1285) with
| true -> begin
((

let uu____1289 = (FStar_Util.string_of_int (FStar_List.length deps_dig'))
in (

let uu____1297 = (FStar_Parser_Dep.print_digest deps_dig')
in (

let uu____1299 = (FStar_Util.string_of_int (FStar_List.length deps_dig))
in (

let uu____1307 = (FStar_Parser_Dep.print_digest deps_dig)
in (FStar_Util.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n" uu____1289 uu____1297 uu____1299 uu____1307)))));
(match ((Prims.op_Equality (FStar_List.length deps_dig) (FStar_List.length deps_dig'))) with
| true -> begin
(FStar_List.iter2 (fun uu____1343 uu____1344 -> (match (((uu____1343), (uu____1344))) with
| ((x, y), (x', y')) -> begin
(match (((Prims.op_disEquality x x') || (Prims.op_disEquality y y'))) with
| true -> begin
(

let uu____1396 = (FStar_Parser_Dep.print_digest ((((x), (y)))::[]))
in (

let uu____1412 = (FStar_Parser_Dep.print_digest ((((x'), (y')))::[]))
in (FStar_Util.print2 "Differ at: Expected %s\n Got %s\n" uu____1396 uu____1412)))
end
| uu____1429 -> begin
()
end)
end)) deps_dig deps_dig')
end
| uu____1431 -> begin
()
end);
)
end
| uu____1433 -> begin
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

let cache_file = (FStar_All.try_with (fun uu___172_1475 -> (match (()) with
| () -> begin
(

let uu____1479 = (FStar_Parser_Dep.cache_file_name file_name)
in (FStar_All.pipe_right uu____1479 (fun _1486 -> FStar_Pervasives_Native.Some (_1486))))
end)) (fun uu___171_1488 -> FStar_Pervasives_Native.None))
in (match (cache_file) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (cache_file1) -> begin
(

let uu____1499 = (load_checked_file file_name cache_file1)
in (match (uu____1499) with
| (uu____1502, FStar_Util.Inl (msg)) -> begin
FStar_Pervasives_Native.None
end
| (uu____1511, FStar_Util.Inr (data)) -> begin
FStar_Pervasives_Native.Some (data)
end))
end)))


let load_module_from_cache : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string  ->  tc_result FStar_Pervasives_Native.option = (

let already_failed = (FStar_Util.mk_ref false)
in (fun env fn -> (

let load_it = (fun uu____1547 -> (

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let fail1 = (fun msg cache_file1 -> (

let suppress_warning = ((FStar_Options.should_verify_file fn) || (FStar_ST.op_Bang already_failed))
in (match ((not (suppress_warning))) with
| true -> begin
((FStar_ST.op_Colon_Equals already_failed true);
(

let uu____1612 = (

let uu____1613 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1616 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1613 uu____1616)))
in (

let uu____1619 = (

let uu____1625 = (FStar_Util.format3 "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)" cache_file1 msg fn)
in ((FStar_Errors.Warning_CachedFile), (uu____1625)))
in (FStar_Errors.log_issue uu____1612 uu____1619)));
)
end
| uu____1629 -> begin
()
end)))
in (

let uu____1631 = (

let uu____1637 = (FStar_TypeChecker_Env.dep_graph env.FStar_Extraction_ML_UEnv.env_tcenv)
in (load_checked_file_with_tc_result uu____1637 fn cache_file))
in (match (uu____1631) with
| FStar_Util.Inl (msg) -> begin
((fail1 msg cache_file);
FStar_Pervasives_Native.None;
)
end
| FStar_Util.Inr (tc_result) -> begin
((

let uu____1647 = (FStar_Options.debug_any ())
in (match (uu____1647) with
| true -> begin
(FStar_Util.print1 "Successfully loaded module from checked file %s\n" cache_file)
end
| uu____1651 -> begin
()
end));
FStar_Pervasives_Native.Some (tc_result);
)
end)))))
in (FStar_Profiling.profile load_it FStar_Pervasives_Native.None "FStar.CheckedFiles"))))


let store_values_to_cache : Prims.string  ->  checked_file_entry_stage1  ->  checked_file_entry_stage2  ->  unit = (fun cache_file stage1 stage2 -> (FStar_Util.save_2values_to_file cache_file stage1 stage2))


let store_module_to_cache : FStar_Extraction_ML_UEnv.uenv  ->  Prims.string  ->  FStar_Parser_Dep.parsing_data  ->  tc_result  ->  unit = (fun env fn parsing_data tc_result -> (

let uu____1698 = ((FStar_Options.cache_checked_modules ()) && (

let uu____1701 = (FStar_Options.cache_off ())
in (not (uu____1701))))
in (match (uu____1698) with
| true -> begin
(

let cache_file = (FStar_Parser_Dep.cache_file_name fn)
in (

let digest = (

let uu____1720 = (FStar_TypeChecker_Env.dep_graph env.FStar_Extraction_ML_UEnv.env_tcenv)
in (hash_dependences uu____1720 fn))
in (match (digest) with
| FStar_Util.Inr (hashes) -> begin
(

let tc_result1 = (

let uu___221_1740 = tc_result
in {checked_module = uu___221_1740.checked_module; mii = uu___221_1740.mii; smt_decls = uu___221_1740.smt_decls; tc_time = (Prims.parse_int "0"); extraction_time = (Prims.parse_int "0")})
in (

let stage1 = (

let uu____1744 = (FStar_Util.digest_of_file fn)
in {version = cache_version_number; digest = uu____1744; parsing_data = parsing_data})
in (

let stage2 = {deps_dig = hashes; tc_res = tc_result1}
in (store_values_to_cache cache_file stage1 stage2))))
end
| FStar_Util.Inl (msg) -> begin
(

let uu____1758 = (

let uu____1759 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (

let uu____1762 = (FStar_Range.mk_pos (Prims.parse_int "0") (Prims.parse_int "0"))
in (FStar_Range.mk_range fn uu____1759 uu____1762)))
in (

let uu____1765 = (

let uu____1771 = (FStar_Util.format2 "%s was not written since %s" cache_file msg)
in ((FStar_Errors.Warning_FileNotWritten), (uu____1771)))
in (FStar_Errors.log_issue uu____1758 uu____1765)))
end)))
end
| uu____1775 -> begin
()
end)))






open Prims
open FStar_Pervasives

let find_deps_if_needed : Prims.string Prims.list  ->  (Prims.string  ->  FStar_Parser_Dep.parsing_data FStar_Pervasives_Native.option)  ->  (Prims.string Prims.list * FStar_Parser_Dep.deps) = (fun files get_parsing_data_from_cache -> (

let uu____34 = (FStar_Parser_Dep.collect files get_parsing_data_from_cache)
in (match (uu____34) with
| (all_files, deps) -> begin
(match (all_files) with
| [] -> begin
((FStar_Errors.log_issue FStar_Range.dummyRange ((FStar_Errors.Error_DependencyAnalysisFailed), ("Dependency analysis failed; reverting to using only the files provided\n")));
((files), (deps));
)
end
| uu____71 -> begin
(((FStar_List.rev all_files)), (deps))
end)
end)))





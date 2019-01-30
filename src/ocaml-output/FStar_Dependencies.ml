open Prims
let (find_deps_if_needed :
  Prims.string Prims.list ->
    (Prims.string Prims.list * FStar_Parser_Dep.deps))
  =
  fun files  ->
    let uu____19 = FStar_Parser_Dep.collect files  in
    match uu____19 with
    | (all_files,deps) ->
        (match all_files with
         | [] ->
             (FStar_Errors.log_issue FStar_Range.dummyRange
                (FStar_Errors.Error_DependencyAnalysisFailed,
                  "Dependency analysis failed; reverting to using only the files provided\n");
              (files, deps))
         | uu____56 -> ((FStar_List.rev all_files), deps))
  
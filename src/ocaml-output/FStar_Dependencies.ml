open Prims
let (find_deps_if_needed :
  Prims.string Prims.list ->
    (Prims.string Prims.list,FStar_Parser_Dep.deps)
      FStar_Pervasives_Native.tuple2)
  =
  fun files  ->
    let uu____16 = FStar_Parser_Dep.collect files  in
    match uu____16 with
    | (all_files,deps) ->
        (match all_files with
         | [] ->
             let uu____41 =
               FStar_Errors.log_issue FStar_Range.dummyRange
                 (FStar_Errors.Error_DependencyAnalysisFailed,
                   "Dependency analysis failed; reverting to using only the files provided\n")
                in
             (files, deps)
         | uu____44 -> ((FStar_List.rev all_files), deps))
  
open Prims
let find_deps_if_needed:
  Prims.string Prims.list ->
    (Prims.string Prims.list,FStar_Parser_Dep.deps)
      FStar_Pervasives_Native.tuple2
  =
  fun files  ->
    let uu____14 = FStar_Parser_Dep.collect files in
    match uu____14 with
    | (all_files,deps) ->
        (match all_files with
         | [] ->
             (FStar_Util.print_error
                "Dependency analysis failed; reverting to using only the files provided\n";
              (files, deps))
         | uu____42 -> ((FStar_List.rev all_files), deps))
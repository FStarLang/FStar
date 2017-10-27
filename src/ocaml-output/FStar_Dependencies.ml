open Prims
let find_deps_if_needed: Prims.string Prims.list -> Prims.string Prims.list =
  fun files  ->
    let all_files = FStar_Parser_Dep.collect_and_memoize files in
    match all_files with
    | [] ->
        (FStar_Util.print_error
           "Dependency analysis failed; reverting to using only the files provided\n";
         files)
    | uu____16 ->
        let all_files1 = FStar_List.rev all_files in
        let all_files_except_prims =
          let prims1 = FStar_Options.prims_basename () in
          let uu____26 =
            let uu____27 =
              let uu____28 = FStar_List.hd all_files1 in
              FStar_Util.basename uu____28 in
            uu____27 = prims1 in
          if uu____26
          then FStar_List.tl all_files1
          else
            (FStar_Util.print1_error
               "Dependency analysis did not find prims module %s?!\n" prims1;
             FStar_All.exit (Prims.parse_int "1")) in
        all_files_except_prims
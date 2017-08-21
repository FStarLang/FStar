open Prims
let find_deps_if_needed :
  FStar_Parser_Dep.verify_mode ->
    Prims.string Prims.list -> Prims.string Prims.list
  =
  fun verify_mode  ->
    fun files  ->
      let uu____15 = FStar_Options.explicit_deps ()  in
      if uu____15
      then files
      else
        (let uu____19 = FStar_Parser_Dep.collect verify_mode files  in
         match uu____19 with
         | (uu____46,deps,uu____48) ->
             (match deps with
              | [] ->
                  (FStar_Util.print_error
                     "Dependency analysis failed; reverting to using only the files provided";
                   files)
              | uu____88 ->
                  let deps1 = FStar_List.rev deps  in
                  let deps2 =
                    let prims1 = FStar_Options.prims_basename ()  in
                    let uu____98 =
                      let uu____99 =
                        let uu____100 = FStar_List.hd deps1  in
                        FStar_Util.basename uu____100  in
                      uu____99 = prims1  in
                    if uu____98
                    then FStar_List.tl deps1
                    else
                      (FStar_Util.print1_error
                         "dependency analysis did not find prims module %s?!"
                         prims1;
                       FStar_All.exit (Prims.parse_int "1"))
                     in
                  deps2))
  
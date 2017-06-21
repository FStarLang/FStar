open Prims
let has_cygpath: Prims.bool =
  try
    let uu____7 = FStar_Util.run_proc "which" "cygpath" "" in
    match uu____7 with
    | (uu____11,t_out,uu____13) ->
        (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____17 -> false
let try_convert_file_name_to_mixed: Prims.string -> Prims.string =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun s  ->
    if has_cygpath
    then
<<<<<<< HEAD
      let uu____23 = FStar_Util.smap_try_find cache s in
      match uu____23 with
      | Some s1 -> s1
      | None  ->
          let uu____26 =
            FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "" in
          (match uu____26 with
           | (uu____30,out,uu____32) ->
=======
      let uu____17 = FStar_Util.smap_try_find cache s in
      match uu____17 with
      | Some s1 -> s1
      | None  ->
          let uu____20 =
            FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "" in
          (match uu____20 with
           | (uu____24,out,uu____26) ->
>>>>>>> origin/guido_tactics
               let out1 = FStar_Util.trim_string out in
               (FStar_Util.smap_add cache s out1; out1))
    else s
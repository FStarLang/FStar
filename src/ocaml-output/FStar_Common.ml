open Prims
let has_cygpath: Prims.bool =
  try
    let uu____7 = FStar_Util.run_proc "which" "cygpath" "" in
    match uu____7 with
    | (uu____14,t_out,uu____16) ->
        (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____20 -> false
let try_convert_file_name_to_mixed: Prims.string -> Prims.string =
  let cache = FStar_Util.smap_create (Prims.parse_int "20") in
  fun s  ->
    if has_cygpath
    then
      let uu____27 = FStar_Util.smap_try_find cache s in
      match uu____27 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let uu____31 =
            FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "" in
          (match uu____31 with
           | (uu____38,out,uu____40) ->
               let out1 = FStar_Util.trim_string out in
               (FStar_Util.smap_add cache s out1; out1))
    else s
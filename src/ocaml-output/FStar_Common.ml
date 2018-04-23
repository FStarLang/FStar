open Prims
let has_cygpath : Prims.bool =
  try
    let uu____7 = FStar_Util.run_proc "which" "cygpath" ""  in
    match uu____7 with
    | (uu____14,t_out,uu____16) ->
        (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____20 -> false 
let try_convert_file_name_to_mixed : Prims.string -> Prims.string =
  let cache = FStar_Util.smap_create (Prims.lift_native_int (20))  in
  fun s  ->
    if has_cygpath && (FStar_Util.starts_with s "/")
    then
      let uu____29 = FStar_Util.smap_try_find cache s  in
      match uu____29 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let uu____33 =
            FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) ""  in
          (match uu____33 with
           | (uu____40,out,uu____42) ->
               let out1 = FStar_Util.trim_string out  in
               (FStar_Util.smap_add cache s out1; out1))
    else s
  
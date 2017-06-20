open Prims
let has_cygpath : Prims.bool =
  try
    let uu____2 = FStar_Util.run_proc "which" "cygpath" ""  in
    match uu____2 with
    | (uu____6,t_out,uu____8) ->
        (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____10 -> false 
let try_convert_file_name_to_mixed : Prims.string -> Prims.string =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun s  ->
    if has_cygpath
    then
      let uu____17 = FStar_Util.smap_try_find cache s  in
      match uu____17 with
      | Some s1 -> s1
      | None  ->
          let uu____20 =
            FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) ""  in
          (match uu____20 with
           | (uu____24,out,uu____26) ->
               let out1 = FStar_Util.trim_string out  in
               (FStar_Util.smap_add cache s out1; out1))
    else s
  
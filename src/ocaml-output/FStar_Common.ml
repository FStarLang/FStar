open Prims
let has_cygpath: Prims.bool =
  try
    let uu____2 = FStar_Util.run_proc "which" "cygpath" "" in
    match uu____2 with
    | (uu____6,t_out,uu____8) ->
        (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____10 -> false
let try_convert_file_name_to_mixed: Prims.string -> Prims.string =
  fun s  ->
    if has_cygpath
    then
      let uu____14 = FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "" in
      match uu____14 with
      | (uu____18,t_out,uu____20) -> FStar_Util.trim_string t_out
    else s
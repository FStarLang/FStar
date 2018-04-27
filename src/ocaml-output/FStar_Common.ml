open Prims
let (has_cygpath : Prims.bool) =
  try
    let t_out =
      FStar_Util.run_process "has_cygpath" "which" ["cygpath"]
        FStar_Pervasives_Native.None
       in
    (FStar_Util.trim_string t_out) = "/usr/bin/cygpath"
  with | uu____8 -> false 
let (try_convert_file_name_to_mixed : Prims.string -> Prims.string) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun s  ->
    if has_cygpath && (FStar_Util.starts_with s "/")
    then
      let uu____15 = FStar_Util.smap_try_find cache s  in
      match uu____15 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let label = "try_convert_file_name_to_mixed"  in
          let out =
            let uu____21 =
              FStar_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____21 FStar_Util.trim_string  in
          (FStar_Util.smap_add cache s out; out)
    else s
  
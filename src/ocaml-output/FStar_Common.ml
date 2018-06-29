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
      let uu____17 = FStar_Util.smap_try_find cache s  in
      match uu____17 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let label = "try_convert_file_name_to_mixed"  in
          let out =
            let uu____23 =
              FStar_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____23 FStar_Util.trim_string  in
          (FStar_Util.smap_add cache s out; out)
    else s
  
let snapshot :
  'a 'b 'c .
    ('a -> 'b) ->
      'c Prims.list FStar_ST.ref ->
        'a -> (Prims.int,'b) FStar_Pervasives_Native.tuple2
  =
  fun push  ->
    fun stackref  ->
      fun arg  ->
        FStar_Util.atomically
          (fun uu____102  ->
             let len =
               let uu____104 = FStar_ST.op_Bang stackref  in
               FStar_List.length uu____104  in
             let arg' = push arg  in (len, arg'))
  
let rollback :
  'a 'c .
    (unit -> 'a) ->
      'c Prims.list FStar_ST.ref ->
        Prims.int FStar_Pervasives_Native.option -> 'a
  =
  fun pop  ->
    fun stackref  ->
      fun depth  ->
        let rec aux n1 =
          if n1 <= (Prims.parse_int "0")
          then failwith "Too many pops"
          else
            if n1 = (Prims.parse_int "1")
            then pop ()
            else
              ((let uu____236 = pop ()  in ());
               aux (n1 - (Prims.parse_int "1")))
           in
        let curdepth =
          let uu____238 = FStar_ST.op_Bang stackref  in
          FStar_List.length uu____238  in
        let n1 =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None  -> (Prims.parse_int "1")  in
        FStar_Util.atomically (fun uu____299  -> aux n1)
  
let raise_failed_assertion : 'Auu____304 . Prims.string -> 'Auu____304 =
  fun msg  ->
    let uu____310 = FStar_Util.format1 "Assertion failed: %s" msg  in
    failwith uu____310
  
let (runtime_assert : Prims.bool -> Prims.string -> unit) =
  fun b  ->
    fun msg  ->
      if Prims.op_Negation b then raise_failed_assertion msg else ()
  
let string_of_list :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun l  ->
      let uu____348 =
        let uu____349 =
          let uu____350 = FStar_List.map f l  in
          FStar_String.concat ", " uu____350  in
        Prims.strcat uu____349 "]"  in
      Prims.strcat "[" uu____348
  
type 'a thunk = (unit -> 'a,'a) FStar_Util.either FStar_ST.ref
let mk_thunk : 'a . (unit -> 'a) -> 'a thunk =
  fun f  -> FStar_Util.mk_ref (FStar_Util.Inl f) 
let force_thunk : 'a . 'a thunk -> 'a =
  fun t  ->
    let uu____487 = FStar_ST.op_Bang t  in
    match uu____487 with
    | FStar_Util.Inr a -> a
    | FStar_Util.Inl f ->
        let a = f ()  in (FStar_ST.op_Colon_Equals t (FStar_Util.Inr a); a)
  
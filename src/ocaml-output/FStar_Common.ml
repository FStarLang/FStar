open Prims
let (has_cygpath : Prims.bool) =
  try
    (fun uu___4_5  ->
       match () with
       | () ->
           let t_out =
             FStar_Util.run_process "has_cygpath" "which" ["cygpath"]
               FStar_Pervasives_Native.None
              in
           (FStar_Util.trim_string t_out) = "/usr/bin/cygpath") ()
  with | uu___3_18 -> false 
let (try_convert_file_name_to_mixed : Prims.string -> Prims.string) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun s  ->
    if has_cygpath && (FStar_Util.starts_with s "/")
    then
      let uu____39 = FStar_Util.smap_try_find cache s  in
      match uu____39 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let label = "try_convert_file_name_to_mixed"  in
          let out =
            let uu____54 =
              FStar_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____54 FStar_Util.trim_string  in
          (FStar_Util.smap_add cache s out; out)
    else s
  
let snapshot :
  'a 'b 'c .
    ('a -> 'b) -> 'c Prims.list FStar_ST.ref -> 'a -> (Prims.int * 'b)
  =
  fun push  ->
    fun stackref  ->
      fun arg  ->
        FStar_Util.atomically
          (fun uu____146  ->
             let len =
               let uu____148 = FStar_ST.op_Bang stackref  in
               FStar_List.length uu____148  in
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
              ((let uu____289 = pop ()  in ());
               aux (n1 - (Prims.parse_int "1")))
           in
        let curdepth =
          let uu____292 = FStar_ST.op_Bang stackref  in
          FStar_List.length uu____292  in
        let n1 =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None  -> (Prims.parse_int "1")  in
        FStar_Util.atomically (fun uu____355  -> aux n1)
  
let raise_failed_assertion : 'Auu____361 . Prims.string -> 'Auu____361 =
  fun msg  ->
    let uu____369 = FStar_Util.format1 "Assertion failed: %s" msg  in
    failwith uu____369
  
let (runtime_assert : Prims.bool -> Prims.string -> unit) =
  fun b  ->
    fun msg  ->
      if Prims.op_Negation b then raise_failed_assertion msg else ()
  
let string_of_list :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun l  ->
      let uu____420 =
        let uu____422 =
          let uu____424 = FStar_List.map f l  in
          FStar_String.concat ", " uu____424  in
        Prims.op_Hat uu____422 "]"  in
      Prims.op_Hat "[" uu____420
  
let list_of_option : 'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun o  ->
    match o with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let string_of_option :
  'Auu____459 .
    ('Auu____459 -> Prims.string) ->
      'Auu____459 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___2_476  ->
      match uu___2_476 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____484 = f x  in Prims.op_Hat "Some " uu____484
  
type 'a thunk = (unit -> 'a,'a) FStar_Util.either FStar_ST.ref
let mk_thunk : 'a . (unit -> 'a) -> 'a thunk =
  fun f  -> FStar_Util.mk_ref (FStar_Util.Inl f) 
let force_thunk : 'a . 'a thunk -> 'a =
  fun t  ->
    let uu____623 = FStar_ST.op_Bang t  in
    match uu____623 with
    | FStar_Util.Inr a -> a
    | FStar_Util.Inl f ->
        let a = f ()  in (FStar_ST.op_Colon_Equals t (FStar_Util.Inr a); a)
  
let tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____835 = f i  in
          let uu____836 = aux (i + (Prims.parse_int "1"))  in uu____835 ::
            uu____836
        else []  in
      aux (Prims.parse_int "0")
  
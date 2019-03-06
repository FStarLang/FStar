open Prims
let (has_cygpath : Prims.bool) =
  try
    (fun uu___291_30469  ->
       match () with
       | () ->
           let t_out =
             FStar_Util.run_process "has_cygpath" "which" ["cygpath"]
               FStar_Pervasives_Native.None
              in
           (FStar_Util.trim_string t_out) = "/usr/bin/cygpath") ()
  with | uu___290_30482 -> false 
let (try_convert_file_name_to_mixed : Prims.string -> Prims.string) =
  let cache = FStar_Util.smap_create (Prims.parse_int "20")  in
  fun s  ->
    if has_cygpath && (FStar_Util.starts_with s "/")
    then
      let uu____30503 = FStar_Util.smap_try_find cache s  in
      match uu____30503 with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None  ->
          let label = "try_convert_file_name_to_mixed"  in
          let out =
            let uu____30518 =
              FStar_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____30518 FStar_Util.trim_string  in
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
          (fun uu____30588  ->
             let len =
               let uu____30590 = FStar_ST.op_Bang stackref  in
               FStar_List.length uu____30590  in
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
              ((let uu____30683 = pop ()  in ());
               aux (n1 - (Prims.parse_int "1")))
           in
        let curdepth =
          let uu____30686 = FStar_ST.op_Bang stackref  in
          FStar_List.length uu____30686  in
        let n1 =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None  -> (Prims.parse_int "1")  in
        FStar_Util.atomically (fun uu____30721  -> aux n1)
  
let raise_failed_assertion : 'Auu____30727 . Prims.string -> 'Auu____30727 =
  fun msg  ->
    let uu____30735 = FStar_Util.format1 "Assertion failed: %s" msg  in
    failwith uu____30735
  
let (runtime_assert : Prims.bool -> Prims.string -> unit) =
  fun b  ->
    fun msg  ->
      if Prims.op_Negation b then raise_failed_assertion msg else ()
  
let string_of_list :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f  ->
    fun l  ->
      let uu____30786 =
        let uu____30788 =
          let uu____30790 = FStar_List.map f l  in
          FStar_String.concat ", " uu____30790  in
        Prims.op_Hat uu____30788 "]"  in
      Prims.op_Hat "[" uu____30786
  
let list_of_option : 'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun o  ->
    match o with
    | FStar_Pervasives_Native.None  -> []
    | FStar_Pervasives_Native.Some x -> [x]
  
let string_of_option :
  'Auu____30825 .
    ('Auu____30825 -> Prims.string) ->
      'Auu____30825 FStar_Pervasives_Native.option -> Prims.string
  =
  fun f  ->
    fun uu___289_30842  ->
      match uu___289_30842 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu____30850 = f x  in Prims.op_Hat "Some " uu____30850
  
type 'a thunk = (unit -> 'a,'a) FStar_Util.either FStar_ST.ref
let mk_thunk : 'a . (unit -> 'a) -> 'a thunk =
  fun f  -> FStar_Util.mk_ref (FStar_Util.Inl f) 
let force_thunk : 'a . 'a thunk -> 'a =
  fun t  ->
    let uu____30909 = FStar_ST.op_Bang t  in
    match uu____30909 with
    | FStar_Util.Inr a -> a
    | FStar_Util.Inl f ->
        let a = f ()  in (FStar_ST.op_Colon_Equals t (FStar_Util.Inr a); a)
  
let tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n1  ->
    fun f  ->
      let rec aux i =
        if i < n1
        then
          let uu____31041 = f i  in
          let uu____31042 = aux (i + (Prims.parse_int "1"))  in uu____31041
            :: uu____31042
        else []  in
      aux (Prims.parse_int "0")
  
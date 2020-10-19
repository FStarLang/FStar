open Prims
let (has_cygpath : Prims.bool) =
  try
    (fun uu___ ->
       match () with
       | () ->
           let t_out =
             FStar_Util.run_process "has_cygpath" "which" ["cygpath"]
               FStar_Pervasives_Native.None in
           (FStar_Util.trim_string t_out) = "/usr/bin/cygpath") ()
  with | uu___ -> false
let (try_convert_file_name_to_mixed : Prims.string -> Prims.string) =
  let cache = FStar_Util.smap_create (Prims.of_int (20)) in
  fun s ->
    if has_cygpath && (FStar_Util.starts_with s "/")
    then
      let uu___ = FStar_Util.smap_try_find cache s in
      match uu___ with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None ->
          let label = "try_convert_file_name_to_mixed" in
          let out =
            let uu___1 =
              FStar_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None in
            FStar_All.pipe_right uu___1 FStar_Util.trim_string in
          (FStar_Util.smap_add cache s out; out)
    else s
let snapshot :
  'a 'b 'c .
    ('a -> 'b) -> 'c Prims.list FStar_ST.ref -> 'a -> (Prims.int * 'b)
  =
  fun push ->
    fun stackref ->
      fun arg ->
        FStar_Util.atomically
          (fun uu___ ->
             let len =
               let uu___1 = FStar_ST.op_Bang stackref in
               FStar_List.length uu___1 in
             let arg' = push arg in (len, arg'))
let rollback :
  'a 'c .
    (unit -> 'a) ->
      'c Prims.list FStar_ST.ref ->
        Prims.int FStar_Pervasives_Native.option -> 'a
  =
  fun pop ->
    fun stackref ->
      fun depth ->
        let rec aux n =
          if n <= Prims.int_zero
          then failwith "Too many pops"
          else
            if n = Prims.int_one
            then pop ()
            else ((let uu___3 = pop () in ()); aux (n - Prims.int_one)) in
        let curdepth =
          let uu___ = FStar_ST.op_Bang stackref in FStar_List.length uu___ in
        let n =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None -> Prims.int_one in
        FStar_Util.atomically (fun uu___ -> aux n)
let raise_failed_assertion : 'uuuuu . Prims.string -> 'uuuuu =
  fun msg ->
    let uu___ = FStar_Util.format1 "Assertion failed: %s" msg in
    failwith uu___
let (runtime_assert : Prims.bool -> Prims.string -> unit) =
  fun b ->
    fun msg -> if Prims.op_Negation b then raise_failed_assertion msg else ()
let string_of_list :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f ->
    fun l ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_List.map f l in FStar_String.concat ", " uu___2 in
        Prims.op_Hat uu___1 "]" in
      Prims.op_Hat "[" uu___
let list_of_option : 'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun o ->
    match o with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some x -> [x]
let string_of_option :
  'uuuuu .
    ('uuuuu -> Prims.string) ->
      'uuuuu FStar_Pervasives_Native.option -> Prims.string
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___1 = f x in Prims.op_Hat "Some " uu___1
let tabulate : 'a . Prims.int -> (Prims.int -> 'a) -> 'a Prims.list =
  fun n ->
    fun f ->
      let rec aux i =
        if i < n
        then
          let uu___ = f i in
          let uu___1 = aux (i + Prims.int_one) in uu___ :: uu___1
        else [] in
      aux Prims.int_zero
let rec max_prefix :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun xs ->
      match xs with
      | [] -> ([], [])
      | x::xs1 when f x ->
          let uu___ = max_prefix f xs1 in
          (match uu___ with | (l, r) -> ((x :: l), r))
      | x::xs1 -> ([], (x :: xs1))
let max_suffix :
  'a . ('a -> Prims.bool) -> 'a Prims.list -> ('a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun xs ->
      let rec aux acc xs1 =
        match xs1 with
        | [] -> (acc, [])
        | x::xs2 when f x -> aux (x :: acc) xs2
        | x::xs2 -> (acc, (x :: xs2)) in
      let uu___ =
        let uu___1 = FStar_All.pipe_right xs FStar_List.rev in
        FStar_All.pipe_right uu___1 (aux []) in
      FStar_All.pipe_right uu___
        (fun uu___1 ->
           match uu___1 with | (xs1, ys) -> ((FStar_List.rev ys), xs1))
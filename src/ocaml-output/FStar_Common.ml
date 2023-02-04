open Prims
let (has_cygpath : Prims.bool) =
  try
    (fun uu___ ->
       match () with
       | () ->
           let t_out =
             FStar_Compiler_Util.run_process "has_cygpath" "which"
               ["cygpath"] FStar_Pervasives_Native.None in
           (FStar_Compiler_Util.trim_string t_out) = "/usr/bin/cygpath") ()
  with | uu___ -> false
let (try_convert_file_name_to_mixed : Prims.string -> Prims.string) =
  let cache = FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
  fun s ->
    if has_cygpath && (FStar_Compiler_Util.starts_with s "/")
    then
      let uu___ = FStar_Compiler_Util.smap_try_find cache s in
      match uu___ with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None ->
          let label = "try_convert_file_name_to_mixed" in
          let out =
            let uu___1 =
              FStar_Compiler_Util.run_process label "cygpath" ["-m"; s]
                FStar_Pervasives_Native.None in
            FStar_Compiler_Effect.op_Bar_Greater uu___1
              FStar_Compiler_Util.trim_string in
          (FStar_Compiler_Util.smap_add cache s out; out)
    else s
let snapshot :
  'a 'b 'c .
    ('a -> 'b) ->
      'c Prims.list FStar_Compiler_Effect.ref -> 'a -> (Prims.int * 'b)
  =
  fun push ->
    fun stackref ->
      fun arg ->
        FStar_Compiler_Util.atomically
          (fun uu___ ->
             let len =
               let uu___1 = FStar_Compiler_Effect.op_Bang stackref in
               FStar_Compiler_List.length uu___1 in
             let arg' = push arg in (len, arg'))
let rollback :
  'a 'c .
    (unit -> 'a) ->
      'c Prims.list FStar_Compiler_Effect.ref ->
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
          let uu___ = FStar_Compiler_Effect.op_Bang stackref in
          FStar_Compiler_List.length uu___ in
        let n =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None -> Prims.int_one in
        FStar_Compiler_Util.atomically (fun uu___ -> aux n)
let raise_failed_assertion : 'uuuuu . Prims.string -> 'uuuuu =
  fun msg ->
    let uu___ = FStar_Compiler_Util.format1 "Assertion failed: %s" msg in
    failwith uu___
let (runtime_assert : Prims.bool -> Prims.string -> unit) =
  fun b ->
    fun msg -> if Prims.op_Negation b then raise_failed_assertion msg else ()
let __string_of_list :
  'a . Prims.string -> ('a -> Prims.string) -> 'a Prims.list -> Prims.string
  =
  fun delim ->
    fun f ->
      fun l ->
        match l with
        | [] -> "[]"
        | x::xs ->
            let strb = FStar_Compiler_Util.new_string_builder () in
            (FStar_Compiler_Util.string_builder_append strb "[";
             (let uu___2 = f x in
              FStar_Compiler_Util.string_builder_append strb uu___2);
             FStar_Compiler_List.iter
               (fun x1 ->
                  FStar_Compiler_Util.string_builder_append strb delim;
                  (let uu___4 = f x1 in
                   FStar_Compiler_Util.string_builder_append strb uu___4)) xs;
             FStar_Compiler_Util.string_builder_append strb "]";
             FStar_Compiler_Util.string_of_string_builder strb)
let string_of_list :
  'uuuuu .
    unit -> ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
  = fun uu___ -> __string_of_list ", "
let string_of_list' :
  'uuuuu .
    unit -> ('uuuuu -> Prims.string) -> 'uuuuu Prims.list -> Prims.string
  = fun uu___ -> __string_of_list "; "
let string_of_set :
  'a . ('a -> Prims.string) -> 'a FStar_Compiler_Util.set -> Prims.string =
  fun f ->
    fun l ->
      let uu___ = FStar_Compiler_Util.set_elements l in
      match uu___ with
      | [] -> "{}"
      | x::xs ->
          let strb = FStar_Compiler_Util.new_string_builder () in
          (FStar_Compiler_Util.string_builder_append strb "{";
           (let uu___3 = f x in
            FStar_Compiler_Util.string_builder_append strb uu___3);
           FStar_Compiler_List.iter
             (fun x1 ->
                FStar_Compiler_Util.string_builder_append strb ", ";
                (let uu___5 = f x1 in
                 FStar_Compiler_Util.string_builder_append strb uu___5)) xs;
           FStar_Compiler_Util.string_builder_append strb "}";
           FStar_Compiler_Util.string_of_string_builder strb)
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
        let uu___1 =
          FStar_Compiler_Effect.op_Bar_Greater xs FStar_Compiler_List.rev in
        FStar_Compiler_Effect.op_Bar_Greater uu___1 (aux []) in
      FStar_Compiler_Effect.op_Bar_Greater uu___
        (fun uu___1 ->
           match uu___1 with
           | (xs1, ys) -> ((FStar_Compiler_List.rev ys), xs1))
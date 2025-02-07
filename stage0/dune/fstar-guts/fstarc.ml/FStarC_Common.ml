open Prims
let snapshot :
  'a 'b 'c .
    ('a -> 'b) -> 'c Prims.list FStarC_Effect.ref -> 'a -> (Prims.int * 'b)
  =
  fun push ->
    fun stackref ->
      fun arg ->
        FStarC_Util.atomically
          (fun uu___ ->
             let len =
               let uu___1 = FStarC_Effect.op_Bang stackref in
               FStarC_List.length uu___1 in
             let arg' = push arg in (len, arg'))
let rollback :
  'a 'c .
    (unit -> 'a) ->
      'c Prims.list FStarC_Effect.ref ->
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
          let uu___ = FStarC_Effect.op_Bang stackref in
          FStarC_List.length uu___ in
        let n =
          match depth with
          | FStar_Pervasives_Native.Some d -> curdepth - d
          | FStar_Pervasives_Native.None -> Prims.int_one in
        FStarC_Util.atomically (fun uu___ -> aux n)
let raise_failed_assertion : 'uuuuu . Prims.string -> 'uuuuu =
  fun msg ->
    let uu___ = FStarC_Util.format1 "Assertion failed: %s" msg in
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
            let strb = FStarC_Util.new_string_builder () in
            (FStarC_Util.string_builder_append strb "[";
             (let uu___2 = f x in
              FStarC_Util.string_builder_append strb uu___2);
             FStarC_List.iter
               (fun x1 ->
                  FStarC_Util.string_builder_append strb delim;
                  (let uu___4 = f x1 in
                   FStarC_Util.string_builder_append strb uu___4)) xs;
             FStarC_Util.string_builder_append strb "]";
             FStarC_Util.string_of_string_builder strb)
let string_of_list :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f -> fun l -> __string_of_list ", " f l
let string_of_list' :
  'a . ('a -> Prims.string) -> 'a Prims.list -> Prims.string =
  fun f -> fun l -> __string_of_list "; " f l
let list_of_option : 'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun o ->
    match o with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some x -> [x]
let string_of_option :
  'a .
    ('a -> Prims.string) -> 'a FStar_Pervasives_Native.option -> Prims.string
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.None -> "None"
      | FStar_Pervasives_Native.Some x ->
          let uu___1 = f x in Prims.strcat "Some " uu___1
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
      let uu___ = aux [] (FStarC_List.rev xs) in
      match uu___ with | (xs1, ys) -> ((FStarC_List.rev ys), xs1)
let rec eq_list :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        match (l1, l2) with
        | ([], []) -> true
        | ([], uu___) -> false
        | (uu___, []) -> false
        | (x1::t1, x2::t2) -> (f x1 x2) && (eq_list f t1 t2)
let psmap_to_list :
  'a . 'a FStarC_Util.psmap -> (Prims.string * 'a) Prims.list =
  fun m ->
    FStarC_Util.psmap_fold m (fun k -> fun v -> fun a1 -> (k, v) :: a1) []
let psmap_keys : 'a . 'a FStarC_Util.psmap -> Prims.string Prims.list =
  fun m -> FStarC_Util.psmap_fold m (fun k -> fun v -> fun a1 -> k :: a1) []
let psmap_values : 'a . 'a FStarC_Util.psmap -> 'a Prims.list =
  fun m -> FStarC_Util.psmap_fold m (fun k -> fun v -> fun a1 -> v :: a1) []
let option_to_list : 'a . 'a FStar_Pervasives_Native.option -> 'a Prims.list
  =
  fun uu___ ->
    match uu___ with
    | FStar_Pervasives_Native.None -> []
    | FStar_Pervasives_Native.Some x -> [x]
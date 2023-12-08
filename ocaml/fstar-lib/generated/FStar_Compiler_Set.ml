open Prims
type 't set = 't FStar_Compiler_Util.set
type 'a t = 'a set
let add : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> 'a set =
  fun uu___ -> fun x -> fun s -> FStar_Compiler_Util.set_add x s
let empty : 'a . 'a FStar_Class_Ord.ord -> unit -> 'a set =
  fun uu___ ->
    fun uu___1 ->
      FStar_Compiler_Util.new_set
        (fun x ->
           fun y ->
             let uu___2 = FStar_Class_Ord.cmp uu___ x y in
             match uu___2 with
             | FStar_Compiler_Order.Lt -> ~- Prims.int_one
             | FStar_Compiler_Order.Eq -> Prims.int_zero
             | FStar_Compiler_Order.Gt -> Prims.int_one)
let from_list : 'a . 'a FStar_Class_Ord.ord -> 'a Prims.list -> 'a set =
  fun uu___ ->
    fun xs ->
      FStar_Compiler_Util.as_set xs
        (fun x ->
           fun y ->
             let uu___1 = FStar_Class_Ord.cmp uu___ x y in
             match uu___1 with
             | FStar_Compiler_Order.Lt -> ~- Prims.int_one
             | FStar_Compiler_Order.Eq -> Prims.int_zero
             | FStar_Compiler_Order.Gt -> Prims.int_one)
let mem : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> Prims.bool =
  fun uu___ -> fun x -> fun s -> FStar_Compiler_Util.set_mem x s
let singleton : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set =
  fun uu___ ->
    fun x ->
      let uu___1 = empty uu___ () in FStar_Compiler_Util.set_add x uu___1
let is_empty : 'a . 'a FStar_Class_Ord.ord -> 'a set -> Prims.bool =
  fun uu___ -> fun s -> FStar_Compiler_Util.set_is_empty s
let addn : 'a . 'a FStar_Class_Ord.ord -> 'a Prims.list -> 'a set -> 'a set =
  fun uu___ ->
    fun xs -> fun ys -> FStar_Compiler_List.fold_right (add uu___) xs ys
let remove : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> 'a set =
  fun uu___ -> fun x -> fun s -> FStar_Compiler_Util.set_remove x s
let equal : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> Prims.bool =
  fun uu___ -> fun s1 -> fun s2 -> FStar_Compiler_Util.set_eq s1 s2
let inter : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ -> fun s1 -> fun s2 -> FStar_Compiler_Util.set_intersect s1 s2
let union : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ -> fun s1 -> fun s2 -> FStar_Compiler_Util.set_union s1 s2
let diff : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ -> fun s1 -> fun s2 -> FStar_Compiler_Util.set_difference s1 s2
let subset : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> Prims.bool =
  fun uu___ -> fun s1 -> fun s2 -> FStar_Compiler_Util.set_is_subset_of s1 s2
let elems : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a Prims.list =
  fun uu___ -> fun s -> FStar_Compiler_Util.set_elements s
let for_all :
  'a . 'a FStar_Class_Ord.ord -> ('a -> Prims.bool) -> 'a set -> Prims.bool =
  fun uu___ ->
    fun p ->
      fun s ->
        let uu___1 = elems uu___ s in
        FStar_Compiler_Effect.op_Bar_Greater uu___1
          (FStar_Compiler_List.for_all p)
let for_any :
  'a . 'a FStar_Class_Ord.ord -> ('a -> Prims.bool) -> 'a set -> Prims.bool =
  fun uu___ ->
    fun p ->
      fun s ->
        let uu___1 = elems uu___ s in
        FStar_Compiler_Effect.op_Bar_Greater uu___1
          (FStar_Compiler_List.existsb p)
let collect :
  'a 'b . 'b FStar_Class_Ord.ord -> ('a -> 'b set) -> 'a Prims.list -> 'b set
  =
  fun uu___ ->
    fun f ->
      fun l ->
        let uu___1 = empty uu___ () in
        FStar_Compiler_List.fold_right
          (fun x -> fun acc -> let uu___2 = f x in union uu___ uu___2 acc) l
          uu___1
let showable_set :
  'a .
    'a FStar_Class_Ord.ord ->
      'a FStar_Class_Show.showable -> 'a set FStar_Class_Show.showable
  =
  fun uu___ ->
    fun uu___1 ->
      {
        FStar_Class_Show.show =
          (fun s ->
             let uu___2 = elems uu___ s in
             FStar_Class_Show.show (FStar_Class_Show.show_list uu___1) uu___2)
      }
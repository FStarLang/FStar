open Prims
type 't set = 't Prims.list
type 'a t = 'a set
let rec add : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> 'a set =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | [] -> [x]
        | y::yy ->
            let uu___1 =
              FStar_Class_Deq.op_Equals_Question
                (FStar_Class_Ord.ord_eq uu___) x y in
            if uu___1
            then s
            else (let uu___3 = add uu___ x yy in y :: uu___3)
let empty : 'a . 'a FStar_Class_Ord.ord -> unit -> 'a set =
  fun uu___ -> fun uu___1 -> []
let from_list : 'a . 'a FStar_Class_Ord.ord -> 'a Prims.list -> 'a set =
  fun uu___ -> fun xs -> FStar_Class_Ord.dedup uu___ xs
let mem : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun s ->
        FStar_Compiler_List.existsb
          (fun y ->
             FStar_Class_Deq.op_Equals_Question
               (FStar_Class_Ord.ord_eq uu___) x y) s
let singleton : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set =
  fun uu___ -> fun x -> [x]
let is_empty : 'a . 'a FStar_Class_Ord.ord -> 'a set -> Prims.bool =
  fun uu___ -> fun s -> Prims.uu___is_Nil s
let addn : 'a . 'a FStar_Class_Ord.ord -> 'a Prims.list -> 'a set -> 'a set =
  fun uu___ ->
    fun xs -> fun ys -> FStar_Compiler_List.fold_right (add uu___) xs ys
let rec remove : 'a . 'a FStar_Class_Ord.ord -> 'a -> 'a set -> 'a set =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | [] -> []
        | y::yy ->
            let uu___1 =
              FStar_Class_Deq.op_Equals_Question
                (FStar_Class_Ord.ord_eq uu___) x y in
            if uu___1
            then yy
            else (let uu___3 = remove uu___ x yy in y :: uu___3)
let elems : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a Prims.list =
  fun uu___ -> fun s -> s
let for_all :
  'a . 'a FStar_Class_Ord.ord -> ('a -> Prims.bool) -> 'a set -> Prims.bool =
  fun uu___ ->
    fun p ->
      fun s ->
        let uu___1 = elems uu___ s in FStar_Compiler_List.for_all p uu___1
let for_any :
  'a . 'a FStar_Class_Ord.ord -> ('a -> Prims.bool) -> 'a set -> Prims.bool =
  fun uu___ ->
    fun p ->
      fun s ->
        let uu___1 = elems uu___ s in FStar_Compiler_List.existsb p uu___1
let subset : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> Prims.bool =
  fun uu___ -> fun s1 -> fun s2 -> for_all uu___ (fun y -> mem uu___ y s2) s1
let equal : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        let uu___1 = FStar_Class_Ord.sort uu___ s1 in
        let uu___2 = FStar_Class_Ord.sort uu___ s2 in
        FStar_Class_Deq.op_Equals_Question
          (FStar_Class_Ord.ord_eq (FStar_Class_Ord.ord_list uu___)) uu___1
          uu___2
let union : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        FStar_Compiler_List.fold_left (fun s -> fun x -> add uu___ x s) s1 s2
let inter : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ ->
    fun s1 ->
      fun s2 -> FStar_Compiler_List.filter (fun y -> mem uu___ y s2) s1
let diff : 'a . 'a FStar_Class_Ord.ord -> 'a set -> 'a set -> 'a set =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        FStar_Compiler_List.filter
          (fun y -> let uu___1 = mem uu___ y s2 in Prims.op_Negation uu___1)
          s1
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
open Prims
type 't flat_set = 't Prims.list
type 'a t = 'a flat_set
let rec add :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | [] -> [x]
        | y::yy ->
            let uu___1 =
              FStarC_Class_Deq.op_Equals_Question
                (FStarC_Class_Ord.ord_eq uu___) x y in
            if uu___1
            then s
            else (let uu___3 = add uu___ x yy in y :: uu___3)
let empty : 'a . unit -> 'a flat_set = fun uu___ -> []
let from_list : 'a . 'a FStarC_Class_Ord.ord -> 'a Prims.list -> 'a flat_set
  = fun uu___ -> fun xs -> FStarC_Class_Ord.dedup uu___ xs
let mem : 'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun s ->
        FStarC_Compiler_List.existsb
          (fun y ->
             FStarC_Class_Deq.op_Equals_Question
               (FStarC_Class_Ord.ord_eq uu___) x y) s
let singleton : 'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set =
  fun uu___ -> fun x -> [x]
let is_empty : 'a . 'a flat_set -> Prims.bool = fun s -> Prims.uu___is_Nil s
let addn :
  'a . 'a FStarC_Class_Ord.ord -> 'a Prims.list -> 'a flat_set -> 'a flat_set
  =
  fun uu___ ->
    fun xs -> fun ys -> FStarC_Compiler_List.fold_right (add uu___) xs ys
let rec remove :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | [] -> []
        | y::yy ->
            let uu___1 =
              FStarC_Class_Deq.op_Equals_Question
                (FStarC_Class_Ord.ord_eq uu___) x y in
            if uu___1
            then yy
            else (let uu___3 = remove uu___ x yy in y :: uu___3)
let elems : 'a . 'a flat_set -> 'a Prims.list = fun s -> s
let for_all : 'a . ('a -> Prims.bool) -> 'a flat_set -> Prims.bool =
  fun p ->
    fun s -> let uu___ = elems s in FStarC_Compiler_List.for_all p uu___
let for_any : 'a . ('a -> Prims.bool) -> 'a flat_set -> Prims.bool =
  fun p ->
    fun s -> let uu___ = elems s in FStarC_Compiler_List.existsb p uu___
let subset :
  'a . 'a FStarC_Class_Ord.ord -> 'a flat_set -> 'a flat_set -> Prims.bool =
  fun uu___ -> fun s1 -> fun s2 -> for_all (fun y -> mem uu___ y s2) s1
let equal :
  'a . 'a FStarC_Class_Ord.ord -> 'a flat_set -> 'a flat_set -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        let uu___1 = FStarC_Class_Ord.sort uu___ s1 in
        let uu___2 = FStarC_Class_Ord.sort uu___ s2 in
        FStarC_Class_Deq.op_Equals_Question
          (FStarC_Class_Ord.ord_eq (FStarC_Class_Ord.ord_list uu___)) uu___1
          uu___2
let union :
  'a . 'a FStarC_Class_Ord.ord -> 'a flat_set -> 'a flat_set -> 'a flat_set =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        FStarC_Compiler_List.fold_left (fun s -> fun x -> add uu___ x s) s1
          s2
let inter :
  'a . 'a FStarC_Class_Ord.ord -> 'a flat_set -> 'a flat_set -> 'a flat_set =
  fun uu___ ->
    fun s1 ->
      fun s2 -> FStarC_Compiler_List.filter (fun y -> mem uu___ y s2) s1
let diff :
  'a . 'a FStarC_Class_Ord.ord -> 'a flat_set -> 'a flat_set -> 'a flat_set =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        FStarC_Compiler_List.filter
          (fun y -> let uu___1 = mem uu___ y s2 in Prims.op_Negation uu___1)
          s1
let collect :
  'a 'b .
    'b FStarC_Class_Ord.ord ->
      ('a -> 'b flat_set) -> 'a Prims.list -> 'b flat_set
  =
  fun uu___ ->
    fun f ->
      fun l ->
        let uu___1 = empty () in
        FStarC_Compiler_List.fold_right
          (fun x -> fun acc -> let uu___2 = f x in union uu___ uu___2 acc) l
          uu___1
let showable_set :
  'a .
    'a FStarC_Class_Ord.ord ->
      'a FStarC_Class_Show.showable -> 'a flat_set FStarC_Class_Show.showable
  =
  fun uu___ ->
    fun uu___1 ->
      {
        FStarC_Class_Show.show =
          (fun s ->
             let uu___2 = elems s in
             FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___1)
               uu___2)
      }
let setlike_flat_set :
  'a .
    'a FStarC_Class_Ord.ord -> ('a, 'a flat_set) FStarC_Class_Setlike.setlike
  =
  fun uu___ ->
    {
      FStarC_Class_Setlike.empty = empty;
      FStarC_Class_Setlike.singleton = (singleton uu___);
      FStarC_Class_Setlike.is_empty = is_empty;
      FStarC_Class_Setlike.add = (add uu___);
      FStarC_Class_Setlike.remove = (remove uu___);
      FStarC_Class_Setlike.mem = (mem uu___);
      FStarC_Class_Setlike.equal = (equal uu___);
      FStarC_Class_Setlike.subset = (subset uu___);
      FStarC_Class_Setlike.union = (union uu___);
      FStarC_Class_Setlike.inter = (inter uu___);
      FStarC_Class_Setlike.diff = (diff uu___);
      FStarC_Class_Setlike.for_all = for_all;
      FStarC_Class_Setlike.for_any = for_any;
      FStarC_Class_Setlike.elems = elems;
      FStarC_Class_Setlike.filter = FStarC_Compiler_List.filter;
      FStarC_Class_Setlike.collect = (collect uu___);
      FStarC_Class_Setlike.from_list = (from_list uu___);
      FStarC_Class_Setlike.addn = (addn uu___)
    }
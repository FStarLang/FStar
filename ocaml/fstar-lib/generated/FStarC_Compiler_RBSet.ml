open Prims
type color =
  | R 
  | B 
let (uu___is_R : color -> Prims.bool) =
  fun projectee -> match projectee with | R -> true | uu___ -> false
let (uu___is_B : color -> Prims.bool) =
  fun projectee -> match projectee with | B -> true | uu___ -> false
type 'a rbset =
  | L 
  | N of (color * 'a rbset * 'a * 'a rbset) 
let uu___is_L : 'a . 'a rbset -> Prims.bool =
  fun projectee -> match projectee with | L -> true | uu___ -> false
let uu___is_N : 'a . 'a rbset -> Prims.bool =
  fun projectee -> match projectee with | N _0 -> true | uu___ -> false
let __proj__N__item___0 : 'a . 'a rbset -> (color * 'a rbset * 'a * 'a rbset)
  = fun projectee -> match projectee with | N _0 -> _0
type 'a t = 'a rbset
let empty : 'uuuuu . unit -> 'uuuuu rbset = fun uu___ -> L
let singleton : 'a . 'a -> 'a rbset = fun x -> N (R, L, x, L)
let is_empty : 'uuuuu . unit -> 'uuuuu rbset -> Prims.bool =
  fun uu___ -> uu___is_L
let balance :
  'uuuuu . color -> 'uuuuu rbset -> 'uuuuu -> 'uuuuu rbset -> 'uuuuu rbset =
  fun c ->
    fun l ->
      fun x ->
        fun r ->
          match (c, l, x, r) with
          | (B, N (R, N (R, a, x1, b), y, c1), z, d) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, a, x1, N (R, N (R, b, y, c1), z, d)) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, N (R, a, x1, N (R, b, y, c1)), z, d) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (B, a, x1, N (R, b, y, N (R, c1, z, d))) ->
              N (R, (N (B, a, x1, b)), y, (N (B, c1, z, d)))
          | (c1, l1, x1, r1) -> N (c1, l1, x1, r1)
let blackroot : 'a . 'a rbset -> 'a rbset =
  fun t1 -> match t1 with | N (uu___, l, x, r) -> N (B, l, x, r)
let add : 'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a rbset -> 'a rbset =
  fun uu___ ->
    fun x ->
      fun s ->
        let rec add' s1 =
          match s1 with
          | L -> N (R, L, x, L)
          | N (c, a1, y, b) ->
              let uu___1 = FStarC_Class_Ord.op_Less_Question uu___ x y in
              if uu___1
              then let uu___2 = add' a1 in balance c uu___2 y b
              else
                (let uu___3 = FStarC_Class_Ord.op_Greater_Question uu___ x y in
                 if uu___3
                 then let uu___4 = add' b in balance c a1 y uu___4
                 else s1) in
        let uu___1 = add' s in blackroot uu___1
let filter :
  'a . 'a FStarC_Class_Ord.ord -> ('a -> Prims.bool) -> 'a rbset -> 'a rbset
  =
  fun uu___ ->
    fun predicate ->
      fun set ->
        let rec aux acc uu___1 =
          match uu___1 with
          | L -> acc
          | N (uu___2, l, v, r) ->
              let uu___3 =
                let uu___4 =
                  let uu___5 = predicate v in
                  if uu___5 then add uu___ v acc else acc in
                aux uu___4 l in
              aux uu___3 r in
        aux (empty ()) set
let rec extract_min :
  'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> ('a rbset * 'a) =
  fun uu___ ->
    fun t1 ->
      match t1 with
      | N (uu___1, L, x, r) -> (r, x)
      | N (c, a1, x, b) ->
          let uu___1 = extract_min uu___ a1 in
          (match uu___1 with | (a', y) -> ((balance c a' x b), y))
let rec remove : 'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a rbset -> 'a rbset =
  fun uu___ ->
    fun x ->
      fun t1 ->
        match t1 with
        | L -> L
        | N (c, l, y, r) ->
            let uu___1 = FStarC_Class_Ord.op_Less_Question uu___ x y in
            if uu___1
            then let uu___2 = remove uu___ x l in balance c uu___2 y r
            else
              (let uu___3 = FStarC_Class_Ord.op_Greater_Question uu___ x y in
               if uu___3
               then let uu___4 = remove uu___ x r in balance c l y uu___4
               else
                 if uu___is_L r
                 then l
                 else
                   (let uu___6 = extract_min uu___ r in
                    match uu___6 with | (r', y') -> balance c l y' r'))
let rec mem : 'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a rbset -> Prims.bool =
  fun uu___ ->
    fun x ->
      fun s ->
        match s with
        | L -> false
        | N (uu___1, a1, y, b) ->
            let uu___2 = FStarC_Class_Ord.op_Less_Question uu___ x y in
            if uu___2
            then mem uu___ x a1
            else
              (let uu___4 = FStarC_Class_Ord.op_Greater_Question uu___ x y in
               if uu___4 then mem uu___ x b else true)
let rec elems : 'a . 'a rbset -> 'a Prims.list =
  fun s ->
    match s with
    | L -> []
    | N (uu___, a1, x, b) ->
        let uu___1 = elems a1 in
        let uu___2 =
          let uu___3 = elems b in FStar_List_Tot_Base.append [x] uu___3 in
        FStar_List_Tot_Base.append uu___1 uu___2
let equal :
  'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> 'a rbset -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        let uu___1 = elems s1 in
        let uu___2 = elems s2 in
        FStarC_Class_Deq.op_Equals_Question
          (FStarC_Class_Ord.ord_eq (FStarC_Class_Ord.ord_list uu___)) uu___1
          uu___2
let rec union :
  'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> 'a rbset -> 'a rbset =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | L -> s2
        | N (c, a1, x, b) ->
            let uu___1 = let uu___2 = add uu___ x s2 in union uu___ b uu___2 in
            union uu___ a1 uu___1
let inter : 'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> 'a rbset -> 'a rbset
  =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        let rec aux s11 acc =
          match s11 with
          | L -> acc
          | N (uu___1, a1, x, b) ->
              let uu___2 = mem uu___ x s2 in
              if uu___2
              then
                let uu___3 = let uu___4 = aux b acc in aux a1 uu___4 in
                add uu___ x uu___3
              else (let uu___4 = aux b acc in aux a1 uu___4) in
        aux s1 L
let rec diff :
  'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> 'a rbset -> 'a rbset =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s2 with
        | L -> s1
        | N (uu___1, a1, x, b) ->
            let uu___2 =
              let uu___3 = remove uu___ x s1 in diff uu___ uu___3 a1 in
            diff uu___ uu___2 b
let rec subset :
  'a . 'a FStarC_Class_Ord.ord -> 'a rbset -> 'a rbset -> Prims.bool =
  fun uu___ ->
    fun s1 ->
      fun s2 ->
        match s1 with
        | L -> true
        | N (uu___1, a1, x, b) ->
            ((mem uu___ x s2) && (subset uu___ a1 s2)) && (subset uu___ b s2)
let rec for_all : 'a . ('a -> Prims.bool) -> 'a rbset -> Prims.bool =
  fun p ->
    fun s ->
      match s with
      | L -> true
      | N (uu___, a1, x, b) -> ((p x) && (for_all p a1)) && (for_all p b)
let rec for_any : 'a . ('a -> Prims.bool) -> 'a rbset -> Prims.bool =
  fun p ->
    fun s ->
      match s with
      | L -> false
      | N (uu___, a1, x, b) -> ((p x) || (for_any p a1)) || (for_any p b)
let from_list : 'a . 'a FStarC_Class_Ord.ord -> 'a Prims.list -> 'a rbset =
  fun uu___ ->
    fun xs ->
      FStarC_Compiler_List.fold_left (fun s -> fun e -> add uu___ e s) L xs
let addn :
  'a . 'a FStarC_Class_Ord.ord -> 'a Prims.list -> 'a rbset -> 'a rbset =
  fun uu___ ->
    fun xs ->
      fun s ->
        FStarC_Compiler_List.fold_left (fun s1 -> fun e -> add uu___ e s1) s
          xs
let collect :
  'a .
    'a FStarC_Class_Ord.ord -> ('a -> 'a rbset) -> 'a Prims.list -> 'a rbset
  =
  fun uu___ ->
    fun f ->
      fun l ->
        FStarC_Compiler_List.fold_left
          (fun s -> fun e -> let uu___1 = f e in union uu___ uu___1 s) L l
let setlike_rbset :
  'a . 'a FStarC_Class_Ord.ord -> ('a, 'a t) FStarC_Class_Setlike.setlike =
  fun uu___ ->
    {
      FStarC_Class_Setlike.empty = empty;
      FStarC_Class_Setlike.singleton = singleton;
      FStarC_Class_Setlike.is_empty = (is_empty ());
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
      FStarC_Class_Setlike.filter = (filter uu___);
      FStarC_Class_Setlike.collect = (collect uu___);
      FStarC_Class_Setlike.from_list = (from_list uu___);
      FStarC_Class_Setlike.addn = (addn uu___)
    }
let showable_rbset :
  'a . 'a FStarC_Class_Show.showable -> 'a t FStarC_Class_Show.showable =
  fun uu___ ->
    {
      FStarC_Class_Show.show =
        (fun s ->
           let uu___1 =
             let uu___2 = elems s in
             FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___)
               uu___2 in
           Prims.strcat "RBSet " uu___1)
    }
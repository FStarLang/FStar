open Prims
type 't flat_set = 't Prims.list
type 'a t = 'a flat_set
let rec add :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ x s ->
    match s with
    | [] -> [x]
    | y::yy ->
        let uu___1 =
          FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___)
            x y in
        if uu___1 then s else (let uu___3 = add uu___ x yy in y :: uu___3)
let empty (uu___ : unit) : 'a flat_set= []
let from_list (uu___ : 'a FStarC_Class_Ord.ord) (xs : 'a Prims.list) :
  'a flat_set= FStarC_Class_Ord.dedup uu___ xs
let mem (uu___ : 'a FStarC_Class_Ord.ord) (x : 'a) (s : 'a flat_set) :
  Prims.bool=
  FStarC_List.existsb
    (fun y ->
       FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___) x
         y) s
let singleton (uu___ : 'a FStarC_Class_Ord.ord) (x : 'a) : 'a flat_set= [x]
let is_empty (s : 'a flat_set) : Prims.bool= Prims.uu___is_Nil s
let addn (uu___ : 'a FStarC_Class_Ord.ord) (xs : 'a Prims.list)
  (ys : 'a flat_set) : 'a flat_set= FStarC_List.fold_right (add uu___) xs ys
let rec remove :
  'a . 'a FStarC_Class_Ord.ord -> 'a -> 'a flat_set -> 'a flat_set =
  fun uu___ x s ->
    match s with
    | [] -> []
    | y::yy ->
        let uu___1 =
          FStarC_Class_Deq.op_Equals_Question (FStarC_Class_Ord.ord_eq uu___)
            x y in
        if uu___1
        then yy
        else (let uu___3 = remove uu___ x yy in y :: uu___3)
let elems (s : 'a flat_set) : 'a Prims.list= s
let for_all (p : 'a -> Prims.bool) (s : 'a flat_set) : Prims.bool=
  let uu___ = elems s in FStarC_List.for_all p uu___
let for_any (p : 'a -> Prims.bool) (s : 'a flat_set) : Prims.bool=
  let uu___ = elems s in FStarC_List.existsb p uu___
let subset (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : Prims.bool= for_all (fun y -> mem uu___ y s2) s1
let equal (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : Prims.bool=
  let uu___1 = FStarC_Class_Ord.sort uu___ s1 in
  let uu___2 = FStarC_Class_Ord.sort uu___ s2 in
  FStarC_Class_Deq.op_Equals_Question
    (FStarC_Class_Ord.ord_eq (FStarC_Class_Ord.ord_list uu___)) uu___1 uu___2
let union (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.fold_left (fun s x -> add uu___ x s) s1 s2
let inter (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.filter (fun y -> mem uu___ y s2) s1
let diff (uu___ : 'a FStarC_Class_Ord.ord) (s1 : 'a flat_set)
  (s2 : 'a flat_set) : 'a flat_set=
  FStarC_List.filter
    (fun y -> let uu___1 = mem uu___ y s2 in Prims.op_Negation uu___1) s1
let collect (uu___ : 'b FStarC_Class_Ord.ord) (f : 'a -> 'b flat_set)
  (l : 'a Prims.list) : 'b flat_set=
  let uu___1 = empty () in
  FStarC_List.fold_right
    (fun x acc -> let uu___2 = f x in union uu___ uu___2 acc) l uu___1
let showable_set (uu___ : 'a FStarC_Class_Ord.ord)
  (uu___1 : 'a FStarC_Class_Show.showable) :
  'a flat_set FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun s ->
         let uu___2 = elems s in
         FStarC_Class_Show.show (FStarC_Class_Show.show_list uu___1) uu___2)
  }
let setlike_flat_set (uu___ : 'a FStarC_Class_Ord.ord) :
  ('a, 'a flat_set) FStarC_Class_Setlike.setlike=
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
    FStarC_Class_Setlike.filter = FStarC_List.filter;
    FStarC_Class_Setlike.collect = (collect uu___);
    FStarC_Class_Setlike.from_list = (from_list uu___);
    FStarC_Class_Setlike.addn = (addn uu___)
  }
